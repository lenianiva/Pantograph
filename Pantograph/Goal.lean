import Lean

import Pantograph.Symbols
import Pantograph.Serial

/-
The proof state manipulation system

A proof state is launched by providing
1. Environment: `Environment`
2. Expression: `Expr`
The expression becomes the first meta variable in the saved tactic state
`Elab.Tactic.SavedState`.
From this point on, any proof which extends
`Elab.Term.Context` and
-/

def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
  {
    msgs := log.msgs.filter fun m => match m.severity with | MessageSeverity.error => true | _ => false
  }


namespace Pantograph
open Lean

structure GoalState where
  mvarId: MVarId
  savedState : Elab.Tactic.SavedState

abbrev M := Elab.TermElabM

def GoalState.create (expr: Expr): M GoalState := do
  -- Immediately synthesise all metavariables if we need to leave the elaboration context.
  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070
  --Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expr ← instantiateMVars expr
  let goal := (← Meta.mkFreshExprMVar expr (kind := MetavarKind.synthetic) (userName := .anonymous))
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [goal.mvarId!]}
  return {
    savedState,
    mvarId := goal.mvarId!
  }

def execute_tactic (state: Elab.Tactic.SavedState) (goal: MVarId) (tactic: String) :
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
        -- The order of evaluation is important here
        return .ok (← MonadBacktrack.saveState, unsolved)
    catch exception =>
      return .error #[← exception.toMessageData.toString]
  match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `tactic)
    (input := tactic)
    (fileName := "<stdin>") with
  | Except.error err => return .error #[err]
  | Except.ok stx    => tacticM stx { elaborator := .anonymous } |>.run' state.tactic

/-- Response for executing a tactic -/
inductive TacticResult where
  -- Goes to next state
  | success (goals: Array (GoalState × Commands.Goal))
  -- Fails with messages
  | failure (messages: Array String)

namespace TacticResult

def is_success: TacticResult → Bool
  | .success _ => true
  | .failure _ => false

end TacticResult

/-- Execute tactic on given state -/
def GoalState.execute (goal: GoalState) (tactic: String):
    Commands.OptionsT M TacticResult := do
  let options ← read
  match (← execute_tactic (state := goal.savedState) (goal := goal.mvarId) (tactic := tactic)) with
  | .error errors =>
    return .failure errors
  | .ok (nextState, nextGoals) =>
    if nextGoals.isEmpty then
      return .success #[]
    else
      let nextGoals: List GoalState := nextGoals.map fun mvarId => { mvarId, savedState := nextState }
      let parentDecl? := (← MonadMCtx.getMCtx).findDecl? goal.mvarId
      let goals ← nextGoals.mapM fun nextGoal => do
        match (← MonadMCtx.getMCtx).findDecl? nextGoal.mvarId with
        | .some mvarDecl =>
          let serializedGoal ← serialize_goal options mvarDecl (parentDecl? := parentDecl?)
          return (nextGoal, serializedGoal)
        | .none => throwError nextGoal.mvarId
      return .success goals.toArray

end Pantograph
