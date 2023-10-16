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
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [goal.mvarId!]}
  return {
    savedState,
    root := goal.mvarId!,
    newMVars := SSet.empty,
  }
protected def GoalState.goals (goalState: GoalState): List MVarId := goalState.savedState.tactic.goals

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
    let newMVars := (← nextMCtx.decls.foldlM (fun acc mvarId mvarDecl => do
      if let .some prevMVarDecl := prevMCtx.decls.find? mvarId then
        assert! prevMVarDecl.type == mvarDecl.type
        return acc
      else
        return mvarId :: acc
      ) []).toSSet
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

-- Diagnostics functions

/-- Print the metavariables in a readable format -/
protected def GoalState.print (goalState: GoalState) (options: Protocol.GoalPrint := {}): Elab.TermElabM Unit := do
  let savedState := goalState.savedState
  savedState.term.restore
  let goals := savedState.tactic.goals
  let mctx ← getMCtx
  goals.forM (fun mvarId => do
    let pref := "⊢"
    match mctx.decls.find? mvarId with
    | .some decl => printMVar pref mvarId decl
    | .none => IO.println s!"{pref}{mvarId.name}: ??"
  )
  let goals := goals.toSSet
  mctx.decls.forM (fun mvarId decl => do
    if goals.contains mvarId then
      pure ()
    else if mvarId == goalState.root then
      printMVar (pref := ">") mvarId decl
    else if ¬(goalState.newMVars.contains mvarId) then
      printMVar (pref := " ") mvarId decl
    else if options.printNonVisible then
      printMVar (pref := "~") mvarId decl
    else
      IO.println s!" {mvarId.name}{userNameToString decl.userName}"
  )
  where
    printMVar (pref: String) (mvarId: MVarId) (decl: MetavarDecl): Elab.TermElabM Unit := do
      if options.printContext then
        decl.lctx.fvarIdToDecl.forM printFVar
      IO.println s!"{pref}{mvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type} {← serialize_expression_ast decl.type}"
      if options.printValue then
        if let Option.some value := (← getMCtx).eAssignment.find? mvarId then
          IO.println s!"  = {← Meta.ppExpr value}"
    printFVar (fvarId: FVarId) (decl: LocalDecl): Elab.TermElabM Unit := do
      IO.println s!" | {fvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type}"
    userNameToString : Name → String
      | .anonymous => ""
      | other => s!"[{other}]"

end Pantograph
