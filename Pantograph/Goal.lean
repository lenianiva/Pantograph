import Lean

def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
  {
    msgs := log.msgs.filter fun m => match m.severity with | MessageSeverity.error => true | _ => false
  }


namespace Pantograph
open Lean

structure GoalState where
  savedState : Elab.Tactic.SavedState

  -- The root hole which is the search target
  root: MVarId
  -- New metavariables acquired in this state
  newMVars: SSet MVarId

  -- The id of the goal in the parent
  parentGoalId: Nat := 0

abbrev M := Elab.TermElabM

protected def GoalState.create (expr: Expr): M GoalState := do
  -- May be necessary to immediately synthesise all metavariables if we need to leave the elaboration context.
  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070

  --Elab.Term.synthesizeSyntheticMVarsNoPostponing
  --let expr ← instantiateMVars expr
  let goal := (← Meta.mkFreshExprMVar expr (kind := MetavarKind.synthetic) (userName := .anonymous))
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let root := goal.mvarId!
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [root]}
  return {
    savedState,
    root,
    newMVars := SSet.insert .empty root,
  }
protected def GoalState.goals (state: GoalState): List MVarId := state.savedState.tactic.goals

protected def GoalState.runM {α: Type} (state: GoalState) (m: Elab.TermElabM α) : M α := do
  state.savedState.term.restore
  m

protected def GoalState.mctx (state: GoalState): MetavarContext :=
  state.savedState.term.meta.meta.mctx
protected def GoalState.env (state: GoalState): Environment :=
  state.savedState.term.meta.core.env
private def GoalState.mvars (state: GoalState): SSet MVarId :=
  state.mctx.decls.foldl (init := .empty) fun acc k _ => acc.insert k
private def GoalState.restoreElabM (state: GoalState): Elab.TermElabM Unit :=
  state.savedState.term.restore
def GoalState.restoreMetaM (state: GoalState): MetaM Unit :=
  state.savedState.term.meta.restore

/-- Inner function for executing tactic on goal state -/
def executeTactic (state: Elab.Tactic.SavedState) (goal: MVarId) (tactic: Syntax) :
    M (Except (Array String) Elab.Tactic.SavedState):= do
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
protected def GoalState.execute (state: GoalState) (goalId: Nat) (tactic: String):
    M TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure $ goal
    | .none => return .indexError goalId
  let tactic ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `tactic)
    (input := tactic)
    (fileName := "<stdin>") with
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
      state with
      savedState := nextSavedState
      newMVars,
      parentGoalId := goalId,
    }

protected def GoalState.tryAssign (state: GoalState) (goalId: Nat) (expr: String): M TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  let expr ← match Parser.runParserCategory
    (env := state.env)
    (catName := `term)
    (input := expr)
    (fileName := "<stdin>") with
    | .ok syn => pure syn
    | .error error => return .parseError error
  let tacticM:  Elab.Tactic.TacticM TacticResult := do
    state.savedState.restore
    Elab.Tactic.setGoals [goal]
    try
      let expr ← Elab.Term.elabTerm (stx := expr) (expectedType? := .none)
      -- Attempt to unify the expression
      let goalType ← goal.getType
      let exprType ← Meta.inferType expr
      if !(← Meta.isDefEq goalType exprType) then
        return .failure #["Type unification failed", toString (← Meta.ppExpr goalType), toString (← Meta.ppExpr exprType)]
      goal.checkNotAssigned `GoalState.tryAssign
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
        -- The new goals are the newMVars that lack an assignment
        Elab.Tactic.setGoals (← newMVars.filterM (λ mvar => do pure !(← mvar.isAssigned)))
        let nextSavedState ← MonadBacktrack.saveState
        return .success {
          state with
          savedState := nextSavedState,
          newMVars := newMVars.toSSet,
          parentGoalId := goalId,
        }
    catch exception =>
      return .failure #[← exception.toMessageData.toString]
  tacticM { elaborator := .anonymous } |>.run' state.savedState.tactic

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

protected def GoalState.rootExpr? (goalState: GoalState): Option Expr :=
  let expr := goalState.mctx.eAssignment.find! goalState.root
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  if expr.hasMVar then
    -- Must not assert that the goal state is empty here. We could be in a branch goal.
    --assert! ¬goalState.goals.isEmpty
    .none
  else
    assert! goalState.goals.isEmpty
    .some expr

end Pantograph
