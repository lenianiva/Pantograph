import Lean

import Pantograph.Symbols


/-
The proof state manipulation system

A proof state is launched by providing
1. Environment: `Lean.Environment`
2. Expression: `Lean.Expr`
The expression becomes the first meta variable in the saved tactic state
`Lean.Elab.Tactic.SavedState`.
From this point on, any proof which extends
`Lean.Elab.Term.Context` and
-/

def Lean.MessageLog.getErrorMessages (log : Lean.MessageLog) : Lean.MessageLog :=
{ msgs := log.msgs.filter fun m => match m.severity with | Lean.MessageSeverity.error => true | _ => false }


namespace Pantograph.Meta

structure ProofState where
  goals : List Lean.MVarId
  savedState : Lean.Elab.Tactic.SavedState
  parent : Option Nat := none
  parentGoalId : Nat  := 0
structure ProofTree where
  -- All parameters needed to run a `TermElabM` monad
  name: Lean.Name

  -- Set of proof states
  states : Array ProofState := #[]

abbrev M := Lean.Elab.TermElabM

def ProofTree.create (name: Lean.Name) (expr: Lean.Expr): M ProofTree := do
  let expr ← Lean.instantiateMVars expr
  let goal := (← Lean.Meta.mkFreshExprMVar expr (kind := Lean.MetavarKind.synthetic))
  let savedStateMonad: Lean.Elab.Tactic.TacticM Lean.Elab.Tactic.SavedState := Lean.MonadBacktrack.saveState
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

-- Parsing syntax under the environment
def syntax_to_expr (syn: Lean.Syntax): Lean.Elab.TermElabM (Except String Lean.Expr) := do
  try
    let expr ← Lean.Elab.Term.elabType syn
    -- Immediately synthesise all metavariables if we need to leave the elaboration context.
    -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070
    --Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← Lean.instantiateMVars expr
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)

def execute_tactic (state: Lean.Elab.Tactic.SavedState) (goal: Lean.MVarId) (tactic: String) :
    M (Except (Array String) (Lean.Elab.Tactic.SavedState × List Lean.MVarId)):= do
  let tacticM (stx: Lean.Syntax):  Lean.Elab.Tactic.TacticM (Except (Array String) (Lean.Elab.Tactic.SavedState × List Lean.MVarId)) := do
    state.restore
    Lean.Elab.Tactic.setGoals [goal]
    try
      Lean.Elab.Tactic.evalTactic stx
      if (← getThe Lean.Core.State).messages.hasErrors then
        let messages := (← getThe Lean.Core.State).messages.getErrorMessages |>.toList.toArray
        let errors ← (messages.map Lean.Message.data).mapM fun md => md.toString
        return .error errors
      else
        return .ok (← Lean.MonadBacktrack.saveState, ← Lean.Elab.Tactic.getUnsolvedGoals)
    catch exception =>
      return .error #[← exception.toMessageData.toString]
  match Lean.Parser.runParserCategory
    (env := ← Lean.MonadEnv.getEnv)
    (catName := `tactic)
    (input := tactic)
    (fileName := "<stdin>") with
  | Except.error err => return .error #[err]
  | Except.ok stx    => tacticM stx { elaborator := .anonymous } |>.run' state.tactic

def goals_to_string (goals: List Lean.MVarId): M (Array String) := do
  let goals ← goals.mapM fun g => do pure $ toString (← Lean.Meta.ppGoal g)
  pure goals.toArray


/-- Response for executing a tactic -/
inductive TacticResult where
  -- Invalid id
  | invalid (message: String): TacticResult
  -- Goes to next state
  | success (nextId?: Option Nat) (goals: Array String)
  -- Fails with messages
  | failure (messages: Array String)

/-- Execute tactic on given state -/
def ProofTree.execute (stateId: Nat) (goalId: Nat) (tactic: String): StateRefT ProofTree M TacticResult := do
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
        return .success (.some nextId) (← goals_to_string nextGoals)

end Pantograph.Meta
