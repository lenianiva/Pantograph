import Lean

import Pantograph.Symbol
import Pantograph.Serial
import Pantograph.Protocol

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
private def GoalState.mvars (state: GoalState): SSet MVarId :=
  state.mctx.decls.foldl (init := .empty) fun acc k _ => acc.insert k

def executeTactic (state: Elab.Tactic.SavedState) (goal: MVarId) (tactic: Syntax) :
    M (Except (Array String) (Elab.Tactic.SavedState × List MVarId)):= do
  let tacticM (stx: Syntax):  Elab.Tactic.TacticM (Except (Array String) (Elab.Tactic.SavedState × List MVarId)) := do
    state.restore
    Elab.Tactic.setGoals [goal]
    try
      Elab.Tactic.evalTactic stx
      if (← getThe Core.State).messages.hasErrors then
        let messages := (← getThe Core.State).messages.getErrorMessages |>.toList.toArray
        let errors ← (messages.map Message.data).mapM fun md => md.toString
        return .error errors
      else
        let unsolved ← Elab.Tactic.getUnsolvedGoals
        -- The order of evaluation is important here, since `getUnsolvedGoals` prunes the goals set
        return .ok (← MonadBacktrack.saveState, unsolved)
    catch exception =>
      return .error #[← exception.toMessageData.toString]
  tacticM tactic { elaborator := .anonymous } |>.run' state.tactic

/-- Response for executing a tactic -/
inductive TacticResult where
  -- Goes to next state
  | success (state: GoalState) (goals: Array Protocol.Goal)
  -- Tactic failed with messages
  | failure (messages: Array String)
  -- Could not parse tactic
  | parseError (message: String)
  -- The goal index is out of bounds
  | indexError (goalId: Nat)

/-- Execute tactic on given state -/
protected def GoalState.execute (state: GoalState) (goalId: Nat) (tactic: String):
    Protocol.OptionsT M TacticResult := do
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
  let options ← read
  match (← executeTactic (state := state.savedState) (goal := goal) (tactic := tactic)) with
  | .error errors =>
    return .failure errors
  | .ok (nextSavedState, nextGoals) =>
    assert! nextSavedState.tactic.goals.length == nextGoals.length
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
    let nextState: GoalState := {
      savedState := nextSavedState
      root := state.root,
      newMVars,
    }
    nextSavedState.term.restore
    let parentDecl? := (← MonadMCtx.getMCtx).findDecl? goal
    let goals ← nextGoals.mapM fun nextGoal => do
      match (← MonadMCtx.getMCtx).findDecl? nextGoal with
      | .some mvarDecl =>
        let serializedGoal ← serialize_goal options mvarDecl (parentDecl? := parentDecl?)
        return serializedGoal
      | .none => throwError s!"Parent mvar id does not exist {nextGoal.name}"
    return .success nextState goals.toArray

/-- After finishing one branch of a proof (`graftee`), pick up from the point where the proof was left off (`target`) -/
protected def GoalState.continue (target: GoalState) (graftee: GoalState): Except String GoalState :=
  if target.root != graftee.root then
    .error s!"Roots of two continued goal states do not match: {target.root.name} != {graftee.root.name}"
  -- Ensure goals are not dangling
  else if ¬ (target.goals.all (λ goal => graftee.mvars.contains goal)) then
    .error s!"Some goals in target are not present in the graftee"
  else
    -- Set goals to the goals that have not been assigned yet, similar to the `focus` tactic.
    let unassigned := target.goals.filter (λ goal =>
      let mctx := graftee.mctx
      ¬(mctx.eAssignment.contains goal || mctx.dAssignment.contains goal))
    .ok {
      savedState := {
        term := graftee.savedState.term,
        tactic := { goals := unassigned },
      },
      root := target.root,
      newMVars := graftee.newMVars,
    }

protected def GoalState.rootExpr (goalState: GoalState): Option Expr :=
  let expr := goalState.mctx.eAssignment.find! goalState.root
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  if expr.hasMVar then
    .none
  else
    .some expr

-- Diagnostics functions

/-- Print the metavariables in a readable format -/
protected def GoalState.print (goalState: GoalState) (options: Protocol.GoalPrint := {}): M Unit := do
  let savedState := goalState.savedState
  savedState.term.restore
  let goals := savedState.tactic.goals
  let mctx ← getMCtx
  let root := goalState.root
  -- Print the root
  match mctx.decls.find? root with
  | .some decl => printMVar ">" root decl
  | .none => IO.println s!">{root.name}: ??"
  goals.forM (fun mvarId => do
    if mvarId != root then
      match mctx.decls.find? mvarId with
      | .some decl => printMVar "⊢" mvarId decl
      | .none => IO.println s!"⊢{mvarId.name}: ??"
  )
  let goals := goals.toSSet
  mctx.decls.forM (fun mvarId decl => do
    if goals.contains mvarId || mvarId == root then
      pure ()
    -- Always print the root goal
    else if mvarId == goalState.root then
      printMVar (pref := ">") mvarId decl
    -- Print the remainig ones that users don't see in Lean
    else if options.printNonVisible then
      let pref := if goalState.newMVars.contains mvarId then "~" else " "
      printMVar pref mvarId decl
    else
      pure ()
      --IO.println s!" {mvarId.name}{userNameToString decl.userName}"
  )
  where
    printMVar (pref: String) (mvarId: MVarId) (decl: MetavarDecl): Elab.TermElabM Unit := do
      if options.printContext then
        decl.lctx.fvarIdToDecl.forM printFVar
      let type_sexp := serialize_expression_ast (← instantiateMVars decl.type) (sanitize := false)
      IO.println s!"{pref}{mvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type} {type_sexp}"
      if options.printValue then
        if let Option.some value := (← getMCtx).eAssignment.find? mvarId then
          IO.println s!"  = {← Meta.ppExpr value}"
    printFVar (fvarId: FVarId) (decl: LocalDecl): Elab.TermElabM Unit := do
      IO.println s!" | {fvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type}"
    userNameToString : Name → String
      | .anonymous => ""
      | other => s!"[{other}]"

end Pantograph
