/-
Functions for handling metavariables

All the functions starting with `try` resume their inner monadic state.
-/
import Pantograph.Protocol
import Lean

def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
  {
    msgs := log.msgs.filter fun m => match m.severity with | MessageSeverity.error => true | _ => false
  }


namespace Pantograph
open Lean

def filename: String := "<pantograph>"

/--
Represents an interconnected set of metavariables, or a state in proof search
 -/
structure GoalState where
  savedState : Elab.Tactic.SavedState

  -- The root hole which is the search target
  root: MVarId
  -- New metavariables acquired in this state
  newMVars: SSet MVarId

  -- Parent state metavariable source
  parentMVar: Option MVarId

protected def GoalState.create (expr: Expr): Elab.TermElabM GoalState := do
  -- May be necessary to immediately synthesise all metavariables if we need to leave the elaboration context.
  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070

  --Elab.Term.synthesizeSyntheticMVarsNoPostponing
  --let expr ← instantiateMVars expr
  let goal ← Meta.mkFreshExprMVar expr (kind := MetavarKind.synthetic) (userName := .anonymous)
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let root := goal.mvarId!
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [root]}
  return {
    savedState,
    root,
    newMVars := SSet.insert .empty root,
    parentMVar := .none,
  }
protected def GoalState.goals (state: GoalState): List MVarId :=
  state.savedState.tactic.goals
protected def GoalState.mctx (state: GoalState): MetavarContext :=
  state.savedState.term.meta.meta.mctx
protected def GoalState.env (state: GoalState): Environment :=
  state.savedState.term.meta.core.env
private def GoalState.mvars (state: GoalState): SSet MVarId :=
  state.mctx.decls.foldl (init := .empty) fun acc k _ => acc.insert k
private def GoalState.restoreElabM (state: GoalState): Elab.TermElabM Unit :=
  state.savedState.term.restore
protected def GoalState.restoreMetaM (state: GoalState): MetaM Unit :=
  state.savedState.term.meta.restore

/-- Inner function for executing tactic on goal state -/
def executeTactic (state: Elab.Tactic.SavedState) (goal: MVarId) (tactic: Syntax) :
    Elab.TermElabM (Except (Array String) Elab.Tactic.SavedState):= do
  let tacticM (stx: Syntax):  Elab.Tactic.TacticM (Except (Array String) Elab.Tactic.SavedState) := do
    state.restore
    Elab.Tactic.setGoals [goal]
    try
      Elab.Tactic.evalTactic stx
      if (← getThe Core.State).messages.hasErrors then
        let messages := (← getThe Core.State).messages.getErrorMessages |>.toList.toArray
        let errors ← (messages.map Message.data).mapM fun md => md.toString
        return .error errors
      else
        return .ok (← MonadBacktrack.saveState)
    catch exception =>
      return .error #[← exception.toMessageData.toString]
  tacticM tactic { elaborator := .anonymous } |>.run' state.tactic

/-- Response for executing a tactic -/
inductive TacticResult where
  -- Goes to next state
  | success (state: GoalState)
  -- Tactic failed with messages
  | failure (messages: Array String)
  -- Could not parse tactic
  | parseError (message: String)
  -- The goal index is out of bounds
  | indexError (goalId: Nat)

/-- Execute tactic on given state -/
protected def GoalState.tryTactic (state: GoalState) (goalId: Nat) (tactic: String):
    Elab.TermElabM TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure $ goal
    | .none => return .indexError goalId
  goal.checkNotAssigned `GoalState.tryTactic
  let tactic ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `tactic)
    (input := tactic)
    (fileName := filename) with
    | .ok stx => pure $ stx
    | .error error => return .parseError error
  match (← executeTactic (state := state.savedState) (goal := goal) (tactic := tactic)) with
  | .error errors =>
    return .failure errors
  | .ok nextSavedState =>
    -- Assert that the definition of metavariables are the same
    let nextMCtx := nextSavedState.term.meta.meta.mctx
    let prevMCtx := state.savedState.term.meta.meta.mctx
    -- Generate a list of mvarIds that exist in the parent state; Also test the
    -- assertion that the types have not changed on any mvars.
    let newMVars ← nextMCtx.decls.foldlM (fun acc mvarId mvarDecl => do
      if let .some prevMVarDecl := prevMCtx.decls.find? mvarId then
        assert! prevMVarDecl.type == mvarDecl.type
        return acc
      else
        return acc.insert mvarId
      ) SSet.empty
    return .success {
      root := state.root,
      savedState := nextSavedState
      newMVars,
      parentMVar := .some goal,
    }

/-- Assumes elabM has already been restored. Assumes expr has already typechecked -/
protected def GoalState.assign (state: GoalState) (goal: MVarId) (expr: Expr):
      Elab.TermElabM TacticResult := do
  let goalType ← goal.getType
  try
    -- For some reason this is needed. One of the unit tests will fail if this isn't here
    let error?: Option String ← goal.withContext (do
      let exprType ← Meta.inferType expr
      if ← Meta.isDefEq goalType exprType then
        pure .none
      else do
        return .some s!"{← Meta.ppExpr expr} : {← Meta.ppExpr exprType} != {← Meta.ppExpr goalType}"
    )
    if let .some error := error? then
      return .failure #["Type unification failed", error]
    goal.checkNotAssigned `GoalState.assign
    goal.assign expr
    if (← getThe Core.State).messages.hasErrors then
      let messages := (← getThe Core.State).messages.getErrorMessages |>.toList.toArray
      let errors ← (messages.map Message.data).mapM fun md => md.toString
      return .failure errors
    else
      let prevMCtx := state.savedState.term.meta.meta.mctx
      let nextMCtx ← getMCtx
      -- Generate a list of mvarIds that exist in the parent state; Also test the
      -- assertion that the types have not changed on any mvars.
      let newMVars ← nextMCtx.decls.foldlM (fun acc mvarId mvarDecl => do
        if let .some prevMVarDecl := prevMCtx.decls.find? mvarId then
          assert! prevMVarDecl.type == mvarDecl.type
          return acc
        else
          return mvarId :: acc
        ) []
      let nextGoals ← newMVars.filterM (λ mvar => do pure !(← mvar.isAssigned))
      return .success {
        root := state.root,
        savedState := {
          term := ← MonadBacktrack.saveState,
          tactic := { goals := nextGoals }
        },
        newMVars := newMVars.toSSet,
        parentMVar := .some goal,
      }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]

protected def GoalState.tryAssign (state: GoalState) (goalId: Nat) (expr: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  let expr ← match Parser.runParserCategory
    (env := state.env)
    (catName := `term)
    (input := expr)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  let goalType ← goal.getType
  try
    let expr ← goal.withContext $
      Elab.Term.elabTermAndSynthesize (stx := expr) (expectedType? := .some goalType)
    state.assign goal expr
  catch exception =>
    return .failure #[← exception.toMessageData.toString]

-- Specialized Tactics

protected def GoalState.tryHave (state: GoalState) (goalId: Nat) (binderName: String) (type: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  let type ← match Parser.runParserCategory
    (env := state.env)
    (catName := `term)
    (input := type)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  let binderName := binderName.toName
  try
    -- Implemented similarly to the intro tactic
    let nextGoals: List MVarId ← goal.withContext $ (do
      let type ← Elab.Term.elabType (stx := type)
      let lctx ← MonadLCtx.getLCtx

      -- The branch goal inherits the same context, but with a different type
      let mvarBranch ← Meta.mkFreshExprMVarAt lctx (← Meta.getLocalInstances) type

      -- Create the context for the `upstream` goal
      let fvarId ← mkFreshFVarId
      let lctxUpstream := lctx.mkLocalDecl fvarId binderName type
      let fvar   := mkFVar fvarId
      let mvarUpstream ←
        withTheReader Meta.Context (fun ctx => { ctx with lctx := lctxUpstream }) do
          Meta.withNewLocalInstances #[fvar] 0 (do
            let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
              (← goal.getType) (kind := MetavarKind.synthetic) (userName := .anonymous)
            let expr: Expr := .app (.lam binderName type mvarBranch .default) mvarUpstream
            goal.assign expr
            pure mvarUpstream)

      pure [mvarBranch.mvarId!, mvarUpstream.mvarId!]
    )
    return .success {
      root := state.root,
      savedState := {
        term := ← MonadBacktrack.saveState,
        tactic := { goals := nextGoals }
      },
      newMVars := nextGoals.toSSet,
      parentMVar := .some goal,
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]


/--
Brings into scope a list of goals
-/
protected def GoalState.resume (state: GoalState) (goals: List MVarId): Except String GoalState :=
  if ¬ (goals.all (λ goal => state.mvars.contains goal)) then
    .error s!"Goals not in scope"
  else
    -- Set goals to the goals that have not been assigned yet, similar to the `focus` tactic.
    let unassigned := goals.filter (λ goal =>
      let mctx := state.mctx
      ¬(mctx.eAssignment.contains goal || mctx.dAssignment.contains goal))
    .ok {
      state with
      savedState := {
        term := state.savedState.term,
        tactic := { goals := unassigned },
      },
    }

/--
Brings into scope all goals from `branch`
-/
protected def GoalState.continue (target: GoalState) (branch: GoalState): Except String GoalState :=
  if !target.goals.isEmpty then
    .error s!"Target state has unresolved goals"
  else if target.root != branch.root then
    .error s!"Roots of two continued goal states do not match: {target.root.name} != {branch.root.name}"
  else
    target.resume (goals := branch.goals)

protected def GoalState.rootExpr? (goalState: GoalState): Option Expr := do
  let expr ← goalState.mctx.eAssignment.find? goalState.root
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  if expr.hasMVar then
    -- Must not assert that the goal state is empty here. We could be in a branch goal.
    --assert! ¬goalState.goals.isEmpty
    .none
  else
    assert! goalState.goals.isEmpty
    return expr
protected def GoalState.parentExpr? (goalState: GoalState): Option Expr := do
  let parent ← goalState.parentMVar
  let expr := goalState.mctx.eAssignment.find! parent
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  return expr
protected def GoalState.assignedExprOf? (goalState: GoalState) (mvar: MVarId): Option Expr := do
  let expr ← goalState.mctx.eAssignment.find? mvar
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  return expr


end Pantograph
