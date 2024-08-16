/-
Functions for handling metavariables

All the functions starting with `try` resume their inner monadic state.
-/
import Pantograph.Protocol
import Pantograph.Tactic
import Lean


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
  parentMVar?: Option MVarId

  -- Existence of this field shows that we are currently in `conv` mode.
  convMVar?: Option (MVarId × MVarId) := .none
  -- Previous RHS for calc, so we don't have to repeat it every time
  -- WARNING: If using `state with` outside of `calc`, this must be set to `.none`
  calcPrevRhs?: Option Expr := .none

@[export pantograph_goal_state_create_m]
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
    root,
    savedState,
    newMVars := SSet.insert .empty root,
    parentMVar? := .none,
  }
protected def GoalState.isConv (state: GoalState): Bool :=
  state.convMVar?.isSome
protected def GoalState.goals (state: GoalState): List MVarId :=
  state.savedState.tactic.goals
@[export pantograph_goal_state_goals]
protected def GoalState.goalsArray (state: GoalState): Array MVarId := state.goals.toArray
protected def GoalState.mctx (state: GoalState): MetavarContext :=
  state.savedState.term.meta.meta.mctx
protected def GoalState.env (state: GoalState): Environment :=
  state.savedState.term.meta.core.env

@[export pantograph_goal_state_meta_context_of_goal]
protected def GoalState.metaContextOfGoal (state: GoalState) (mvarId: MVarId): Option Meta.Context := do
  let mvarDecl ← state.mctx.findDecl? mvarId
  return { lctx := mvarDecl.lctx, localInstances := mvarDecl.localInstances }
@[export pantograph_goal_state_meta_state]
protected def GoalState.metaState (state: GoalState): Meta.State :=
  state.savedState.term.meta.meta

protected def GoalState.withContext (state: GoalState) (mvarId: MVarId) (m: MetaM α): MetaM α := do
  mvarId.withContext m |>.run' (← read) state.metaState

protected def GoalState.withParentContext (state: GoalState) (m: MetaM α): MetaM α := do
  state.withContext state.parentMVar?.get! m
protected def GoalState.withRootContext (state: GoalState) (m: MetaM α): MetaM α := do
  state.withContext state.root m

private def GoalState.mvars (state: GoalState): SSet MVarId :=
  state.mctx.decls.foldl (init := .empty) fun acc k _ => acc.insert k
protected def GoalState.restoreMetaM (state: GoalState): MetaM Unit :=
  state.savedState.term.meta.restore
protected def GoalState.restoreElabM (state: GoalState): Elab.TermElabM Unit :=
  state.savedState.term.restore
private def GoalState.restoreTacticM (state: GoalState) (goal: MVarId): Elab.Tactic.TacticM Unit := do
  state.savedState.restore
  Elab.Tactic.setGoals [goal]


private def newMVarSet (mctxOld: @&MetavarContext) (mctxNew: @&MetavarContext): SSet MVarId :=
  mctxNew.decls.foldl (fun acc mvarId mvarDecl =>
    if let .some prevMVarDecl := mctxOld.decls.find? mvarId then
      assert! prevMVarDecl.type == mvarDecl.type
      acc
    else
      acc.insert mvarId
    ) SSet.empty

protected def GoalState.focus (state: GoalState) (goalId: Nat): Option GoalState := do
  let goal ← state.savedState.tactic.goals.get? goalId
  return {
    state with
    savedState := {
      state.savedState with
      tactic := { goals := [goal] },
    },
    calcPrevRhs? := .none,
  }

/--
Brings into scope a list of goals
-/
@[export pantograph_goal_state_resume]
protected def GoalState.resume (state: GoalState) (goals: List MVarId): Except String GoalState :=
  if ¬ (goals.all (λ goal => state.mvars.contains goal)) then
    let invalid_goals := goals.filter (λ goal => ¬ state.mvars.contains goal) |>.map (·.name.toString)
    .error s!"Goals {invalid_goals} are not in scope"
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
      calcPrevRhs? := .none,
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

@[export pantograph_goal_state_root_expr]
protected def GoalState.rootExpr? (goalState: GoalState): Option Expr := do
  let expr ← goalState.mctx.eAssignment.find? goalState.root
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  if expr.hasExprMVar then
    -- Must not assert that the goal state is empty here. We could be in a branch goal.
    --assert! ¬goalState.goals.isEmpty
    .none
  else
    assert! goalState.goals.isEmpty
    return expr
@[export pantograph_goal_state_parent_expr]
protected def GoalState.parentExpr? (goalState: GoalState): Option Expr := do
  let parent ← goalState.parentMVar?
  let expr := goalState.mctx.eAssignment.find! parent
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  return expr
@[export pantograph_goal_state_get_mvar_e_assignment]
protected def GoalState.getMVarEAssignment (goalState: GoalState) (mvar: MVarId): Option Expr := do
  let expr ← goalState.mctx.eAssignment.find? mvar
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  return expr

--- Tactic execution functions ---

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
  -- The given action cannot be executed in the state
  | invalidAction (message: String)

/-- Executes a `TacticM` monads on this `GoalState`, collecting the errors as necessary -/
protected def GoalState.executeTactic (state: GoalState) (goalId: Nat) (tacticM: Elab.Tactic.TacticM Unit):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure $ goal
    | .none => return .indexError goalId
  goal.checkNotAssigned `GoalState.executeTactic
  try
    let (_, newGoals) ← tacticM { elaborator := .anonymous } |>.run { goals := [goal] }
    if (← getThe Core.State).messages.hasErrors then
      let messages := (← getThe Core.State).messages.toArray
      let errors ← (messages.map (·.data)).mapM fun md => md.toString
      return .failure errors
    let nextElabState ← MonadBacktrack.saveState
    let nextMCtx := nextElabState.meta.meta.mctx
    let prevMCtx := state.mctx
    return .success {
      state with
      savedState := { term := nextElabState, tactic := newGoals },
      newMVars := newMVarSet prevMCtx nextMCtx,
      parentMVar? := .some goal,
      calcPrevRhs? := .none,
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]

/-- Execute a string tactic on given state -/
protected def GoalState.tryTactic (state: GoalState) (goalId: Nat) (tactic: String):
    Elab.TermElabM TacticResult := do
  let tactic ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := if state.isConv then `conv else `tactic)
    (input := tactic)
    (fileName := filename) with
    | .ok stx => pure $ stx
    | .error error => return .parseError error
  state.executeTactic goalId $ Elab.Tactic.evalTactic tactic

protected def GoalState.tryAssign (state: GoalState) (goalId: Nat) (expr: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let expr ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := expr)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.executeTactic goalId $ Tactic.evalAssign expr

-- Specialized Tactics

protected def GoalState.tryHave (state: GoalState) (goalId: Nat) (binderName: String) (type: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  goal.checkNotAssigned `GoalState.tryHave
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
    let nextGoals: List MVarId ← goal.withContext do
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
          Meta.withNewLocalInstances #[fvar] 0 do
            let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
              (← goal.getType) (kind := MetavarKind.synthetic) (userName := .anonymous)
            let expr: Expr := .app (.lam binderName type mvarBranch .default) mvarUpstream
            goal.assign expr
            pure mvarUpstream

      pure [mvarBranch.mvarId!, mvarUpstream.mvarId!]
    return .success {
      root := state.root,
      savedState := {
        term := ← MonadBacktrack.saveState,
        tactic := { goals := nextGoals }
      },
      newMVars := nextGoals.toSSet,
      parentMVar? := .some goal,
      calcPrevRhs? := .none
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]
protected def GoalState.tryLet (state: GoalState) (goalId: Nat) (binderName: String) (type: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  goal.checkNotAssigned `GoalState.tryLet
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
    let nextGoals: List MVarId ← goal.withContext do
      let type ← Elab.Term.elabType (stx := type)
      let lctx ← MonadLCtx.getLCtx

      -- The branch goal inherits the same context, but with a different type
      let mvarBranch ← Meta.mkFreshExprMVarAt lctx (← Meta.getLocalInstances) type

      let upstreamType := .letE binderName type mvarBranch (← goal.getType) false
      let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
        upstreamType (kind := MetavarKind.synthetic) (userName := (← goal.getTag))

      goal.assign mvarUpstream

      pure [mvarBranch.mvarId!, mvarUpstream.mvarId!]
    return .success {
      root := state.root,
      savedState := {
        term := ← MonadBacktrack.saveState,
        tactic := { goals := nextGoals }
      },
      newMVars := nextGoals.toSSet,
      parentMVar? := .some goal,
      calcPrevRhs? := .none
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]

/-- Enter conv tactic mode -/
protected def GoalState.conv (state: GoalState) (goalId: Nat):
      Elab.TermElabM TacticResult := do
  if state.convMVar?.isSome then
    return .invalidAction "Already in conv state"
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  goal.checkNotAssigned `GoalState.conv
  let tacticM :  Elab.Tactic.TacticM (Elab.Tactic.SavedState × MVarId) := do
    state.restoreTacticM goal

    -- See Lean.Elab.Tactic.Conv.convTarget
    let convMVar ← Elab.Tactic.withMainContext do
      let (rhs, newGoal) ← Elab.Tactic.Conv.mkConvGoalFor (← Elab.Tactic.getMainTarget)
      Elab.Tactic.setGoals [newGoal.mvarId!]
      pure rhs.mvarId!
    return (← MonadBacktrack.saveState, convMVar)
  try
    let (nextSavedState, convRhs) ← tacticM { elaborator := .anonymous } |>.run' state.savedState.tactic
    let prevMCtx := state.mctx
    let nextMCtx := nextSavedState.term.meta.meta.mctx
    return .success {
      root := state.root,
      savedState := nextSavedState
      newMVars := newMVarSet prevMCtx nextMCtx,
      parentMVar? := .some goal,
      convMVar? := .some (convRhs, goal),
      calcPrevRhs? := .none
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]

/-- Exit from `conv` mode. Resumes all goals before the mode starts and applys the conv -/
protected def GoalState.convExit (state: GoalState):
      Elab.TermElabM TacticResult := do
  let (convRhs, convGoal) ← match state.convMVar? with
    | .some mvar => pure mvar
    | .none => return .invalidAction "Not in conv state"
  let tacticM :  Elab.Tactic.TacticM Elab.Tactic.SavedState:= do
    -- Vide `Lean.Elab.Tactic.Conv.convert`
    state.savedState.restore

    -- Close all existing goals with `refl`
    for mvarId in (← Elab.Tactic.getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    Elab.Tactic.pruneSolvedGoals
    unless (← Elab.Tactic.getGoals).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{Elab.goalsToMessageData (← Elab.Tactic.getGoals)}"

    Elab.Tactic.setGoals [convGoal]

    let targetNew ← instantiateMVars (.mvar convRhs)
    let proof ← instantiateMVars (.mvar convGoal)

    Elab.Tactic.liftMetaTactic1 fun mvarId => mvarId.replaceTargetEq targetNew proof
    MonadBacktrack.saveState
  try
    let nextSavedState ← tacticM { elaborator := .anonymous } |>.run' state.savedState.tactic
    let nextMCtx := nextSavedState.term.meta.meta.mctx
    let prevMCtx := state.savedState.term.meta.meta.mctx
    return .success {
      root := state.root,
      savedState := nextSavedState
      newMVars := newMVarSet prevMCtx nextMCtx,
      parentMVar? := .some convGoal,
      convMVar? := .none
      calcPrevRhs? := .none
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]

protected def GoalState.calcPrevRhsOf? (state: GoalState) (goalId: Nat) :=
  if goalId == 1 then
    state.calcPrevRhs?
  else
    .none
protected def GoalState.tryCalc (state: GoalState) (goalId: Nat) (pred: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  if state.convMVar?.isSome then
    return .invalidAction "Cannot initiate `calc` while in `conv` state"
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure goal
    | .none => return .indexError goalId
  let `(term|$pred) ← match Parser.runParserCategory
    (env := state.env)
    (catName := `term)
    (input := pred)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  goal.checkNotAssigned `GoalState.tryCalc
  let calcPrevRhs? := state.calcPrevRhsOf? goalId
  let target ← instantiateMVars (← goal.getDecl).type
  let tag := (← goal.getDecl).userName
  try
    goal.withContext do

    let mut step ← Elab.Term.elabType <| ← do
      if let some prevRhs := calcPrevRhs? then
        Elab.Term.annotateFirstHoleWithType pred (← Meta.inferType prevRhs)
      else
        pure pred

    let some (_, lhs, rhs) ← Elab.Term.getCalcRelation? step |
      throwErrorAt pred "invalid 'calc' step, relation expected{indentExpr step}"
    if let some prevRhs := calcPrevRhs? then
      unless ← Meta.isDefEqGuarded lhs prevRhs do
        throwErrorAt pred "invalid 'calc' step, left-hand-side is{indentD m!"{lhs} : {← Meta.inferType lhs}"}\nprevious right-hand-side is{indentD m!"{prevRhs} : {← Meta.inferType prevRhs}"}" -- "

    -- Creates a mvar to represent the proof that the calc tactic solves the
    -- current branch
    -- In the Lean `calc` tactic this is gobbled up by
    -- `withCollectingNewGoalsFrom`
    let mut proof ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances) step
      (userName := tag ++ `calc)
    let mvarBranch := proof.mvarId!

    let calcPrevRhs? := Option.some rhs
    let mut proofType ← Meta.inferType proof
    let mut remainder := Option.none

    -- The calc tactic either solves the main goal or leaves another relation.
    -- Replace the main goal, and save the new goal if necessary
    unless ← Meta.isDefEq proofType target do
      let rec throwFailed :=
        throwError "'calc' tactic failed, has type{indentExpr proofType}\nbut it is expected to have type{indentExpr target}"
      let some (_, _, rhs) ← Elab.Term.getCalcRelation? proofType | throwFailed
      let some (r, _, rhs') ← Elab.Term.getCalcRelation? target | throwFailed
      let lastStep := mkApp2 r rhs rhs'
      let lastStepGoal ← Meta.mkFreshExprSyntheticOpaqueMVar lastStep tag
      (proof, proofType) ← Elab.Term.mkCalcTrans proof proofType lastStepGoal lastStep
      unless ← Meta.isDefEq proofType target do throwFailed
      remainder := .some lastStepGoal.mvarId!
    goal.assign proof

    let goals := [ mvarBranch ] ++ remainder.toList
    return .success {
      root := state.root,
      savedState := {
        term := ← MonadBacktrack.saveState,
        tactic := { goals },
      },
      newMVars := goals.toSSet,
      parentMVar? := .some goal,
      calcPrevRhs?
    }
  catch exception =>
    return .failure #[← exception.toMessageData.toString]


protected def GoalState.tryMotivatedApply (state: GoalState) (goalId: Nat) (recursor: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let recursor ← match Parser.runParserCategory
    (env := state.env)
    (catName := `term)
    (input := recursor)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.executeTactic goalId (tacticM := Tactic.motivatedApply recursor)
protected def GoalState.tryNoConfuse (state: GoalState) (goalId: Nat) (eq: String):
      Elab.TermElabM TacticResult := do
  state.restoreElabM
  let recursor ← match Parser.runParserCategory
    (env := state.env)
    (catName := `term)
    (input := eq)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.executeTactic goalId (tacticM := Tactic.noConfuse recursor)

end Pantograph
