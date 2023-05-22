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
  savedState : Lean.Elab.Tactic.SavedState
  parent : Option Nat := none
  parentGoalId : Nat  := 0
structure ProofTree where
  -- All parameters needed to run a `TermElabM` monad
  env: Lean.Environment
  name: Lean.Name
  coreContext : Lean.Core.Context
  elabContext : Lean.Elab.Term.Context

  -- Set of proof states
  states : Array ProofState := #[]

abbrev ProofM := StateRefT ProofTree IO

def createProofTree (name: Lean.Name) (env: Lean.Environment) (coreContext: Lean.Core.Context): ProofTree :=
  {
    env := env,
    name := name,
    coreContext := coreContext,
    elabContext := {
      declName? := some (name ++ "_pantograph"),
      errToSorry := false
    }
  }

-- Executing a `TermElabM`
def ProofM.runTermElabM (termElabM: Lean.Elab.TermElabM α): ProofM (α × Lean.Core.State) := do
  let context ← get
  let metaM : Lean.MetaM α := termElabM.run' (ctx := context.elabContext)
  let coreM : Lean.CoreM α := metaM.run'
  let coreState : Lean.Core.State := { env := context.env }
  coreM.toIO context.coreContext coreState
def ProofM.runTermElabM' (termElabM: Lean.Elab.TermElabM α): ProofM α := do
  return Prod.fst <| ← ProofM.runTermElabM termElabM

-- Parsing syntax under the environment
def ProofM.syntax_to_expr (syn: Lean.Syntax): ProofM (Except String Lean.Expr) := do
  let termElabM : Lean.Elab.TermElabM (Except String Lean.Expr) :=
    try
      --let expr ← Lean.Elab.Term.elabTerm syn
      --  (expectedType? := none)
      --  (catchExPostpone := false)
      --  (implicitLambda := true)
      let expr ← Lean.Elab.Term.elabType syn

      -- Immediately synthesise all metavariables since we need to leave the elaboration context.
      -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← Lean.instantiateMVars expr

      return .ok expr

    catch ex => return .error (← ex.toMessageData.toString)
  ProofM.runTermElabM' <| termElabM

def start_tactic_state (expr: Lean.Expr): Lean.Elab.TermElabM Lean.Elab.Tactic.SavedState := do
    let mvar ← Lean.Meta.mkFreshExprMVar (some expr) (kind := Lean.MetavarKind.synthetic)
    let termState : Lean.Elab.Term.SavedState ← Lean.Elab.Term.saveState
    let tacticState : Lean.Elab.Tactic.SavedState := { term := termState, tactic := { goals := [mvar.mvarId!] }}
    return tacticState
/-- Create the initial proof state of the proof tree -/
def ProofM.start (expr: Lean.Expr): ProofM Unit := do
  let state: ProofState := {
    savedState := (← ProofM.runTermElabM' <| start_tactic_state expr),
    parent := none
  }
  let tree ← get
  set { tree with states := #[state] }


def execute_tactic (env: Lean.Environment) (state: Lean.Elab.Tactic.SavedState) (goalId: Nat) (tactic: String) :
    Lean.Elab.TermElabM (Except (Array String) Lean.Elab.Tactic.SavedState):= do
  -- Factor this one out to allow for direct syntactic communication
  match Lean.Parser.runParserCategory
    (env := env)
    (catName := `tactic)
    (input := tactic)
    (fileName := "<stdin>") with
  | Except.error err => return .error #[err]
  | Except.ok stx    => do
    state.term.restore
    let tac : Lean.Elab.Tactic.TacticM Unit := set state.tactic *> Lean.Elab.Tactic.evalTactic stx
    match state.tactic.goals.get? goalId with
    | .none => return .error #[s!"Invalid goalId {goalId}"]
    | .some mvarId =>
      try
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let unsolvedGoals ← Lean.Elab.Tactic.run mvarId tac
        if (← getThe Lean.Core.State).messages.hasErrors then
          let messages := (← getThe Lean.Core.State).messages.getErrorMessages |>.toList.toArray
          let errors ← (messages.map Lean.Message.data).mapM fun md => md.toString
          return .error errors
        else
          unsolvedGoals.forM Lean.instantiateMVarDeclMVars
          let nextState : Lean.Elab.Tactic.SavedState := {
            term := (← Lean.Elab.Term.saveState),
            tactic := { goals := unsolvedGoals }
          }
          return .ok nextState
      catch ex =>
        return .error #[← ex.toMessageData.toString]

def extract_goals (state: Lean.Elab.Tactic.SavedState): Lean.Elab.TermElabM (Array String) := do
  state.term.restore
  let goals ← state.tactic.goals.mapM fun g => do pure $ toString (← Lean.Meta.ppGoal g)
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
def ProofM.execute (stateId: Nat) (goalId: Nat) (tactic: String): ProofM TacticResult := do
  let context ← get
  match context.states.get? stateId with
  | .none => return .invalid s!"Invalid state id {stateId}"
  | .some state =>
    match (← ProofM.runTermElabM' <| execute_tactic (env := context.env) (state := state.savedState) (goalId := goalId) (tactic := tactic)) with
    | .error errors =>
      return .failure errors
    | .ok nextState =>
      let nextId := context.states.size
      -- Return goals
      let goals ← ProofM.runTermElabM' <| extract_goals nextState

      if goals.size = 0 then
        return .success .none #[]
      else
        -- Create next proof state node
        let proofState: ProofState := {
          savedState := nextState,
          parent := stateId,
          parentGoalId := goalId
        }
        modify fun s => { s with states := s.states.push proofState }

        return .success (.some nextId) goals


end Pantograph.Meta
