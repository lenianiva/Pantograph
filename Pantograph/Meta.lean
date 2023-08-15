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

structure ProofState where
  goals : List MVarId
  savedState : Elab.Tactic.SavedState
  parent : Option Nat := none
  parentGoalId : Nat  := 0
structure ProofTree where
  -- All parameters needed to run a `TermElabM` monad
  name: Name

  -- Set of proof states
  states : Array ProofState := #[]

abbrev M := Elab.TermElabM

def ProofTree.create (name: Name) (expr: Expr): M ProofTree := do
  let expr ← instantiateMVars expr
  let goal := (← Meta.mkFreshExprMVar expr (kind := MetavarKind.synthetic))
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [goal.mvarId!]}
  return {
    name := name,
    states := #[{
      savedState := savedState,
      goals := [goal.mvarId!]
    }]
  }

-- Print the tree structures in readable form
def ProofTree.structure_array (tree: ProofTree): Array String :=
  tree.states.map λ state => match state.parent with
    | .none => ""
    | .some parent => s!"{parent}.{state.parentGoalId}"

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
        return .ok (← MonadBacktrack.saveState, ← Elab.Tactic.getUnsolvedGoals)
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
  -- Invalid id
  | invalid (message: String): TacticResult
  -- Goes to next state
  | success (nextId?: Option Nat) (goals: Array Commands.Goal)
  -- Fails with messages
  | failure (messages: Array String)

/-- Execute tactic on given state -/
def ProofTree.execute (stateId: Nat) (goalId: Nat) (tactic: String): StateRefT ProofTree M TacticResult := do
  -- TODO: Replace with actual options
  let options: Commands.Options := {}
  let tree ← get
  match tree.states.get? stateId with
  | .none => return .invalid s!"Invalid state id {stateId}"
  | .some state =>
    match state.goals.get? goalId with
    | .none => return .invalid s!"Invalid goal id {goalId}"
    | .some goal =>
      match (← execute_tactic (state := state.savedState) (goal := goal) (tactic := tactic)) with
      | .error errors =>
        return .failure errors
      | .ok (nextState, nextGoals) =>
        let nextId := tree.states.size
        if nextGoals.isEmpty then
          return .success .none #[]
        else
          let proofState: ProofState := {
            savedState := nextState,
            goals := nextGoals,
            parent := stateId,
            parentGoalId := goalId
          }
          modify fun s => { s with states := s.states.push proofState }
        let goals ← nextGoals.mapM fun mvarId => do
          match (← MonadMCtx.getMCtx).findDecl? mvarId with
          | .some mvarDecl => serialize_goal options mvarDecl
          | .none => throwError mvarId
        return .success (.some nextId) goals.toArray

end Pantograph
