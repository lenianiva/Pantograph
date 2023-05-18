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

namespace Pantograph



-- All parameters needed to run a `TermElabM` monad
structure Context where
  env: Lean.Environment
  name: Lean.Name
  coreContext : Lean.Core.Context
  elabContext: Lean.Elab.Term.Context

-- Tactic execution response
structure Response : Type where
  goals    : Array String := #[]
  errors   : Array String := #[]


def createContext (name: Lean.Name) (env: Lean.Environment): Context :=
  {
    env := env,
    name := name,
    coreContext := {
      currNamespace := strToName "Aniva",
      openDecls := [],     -- No 'open' directives needed
      fileName := "<Gym>",
      fileMap := { source := "", positions := #[0], lines := #[1] }
    },
    elabContext := {
      declName? := some (name ++ "_pantograph"),
      errToSorry := false
    }
  }

def Context.runTermElabM (termElabM: Lean.Elab.TermElabM α): ReaderT Context IO (α × Lean.Core.State) := do
  let context ← read
  let metaM : Lean.MetaM α := termElabM.run' (ctx := context.elabContext)
  let coreM : Lean.CoreM α := metaM.run'
  let coreState : Lean.Core.State := { env := context.env }
  coreM.toIO context.coreContext coreState
def Context.runTermElabM' (termElabM: Lean.Elab.TermElabM α): ReaderT Context IO α := do
  let context ← read
  let (result, _) ← context.runTermElabM termElabM
  return result


def start_proof_state: ReaderT Context IO Lean.Elab.Tactic.SavedState := do
  let context ← read
  let name := context.name
  let termElabM : Lean.Elab.TermElabM Lean.Elab.Tactic.SavedState := do
    match context.env.find? name with
    | none       => throwError "decl {name} not found"
    | some cInfo =>
      if ¬ (← Lean.Meta.isProp cInfo.type) then throwError "decl {name} not a theorem"
      let mvar ← Lean.Meta.mkFreshExprMVar (some cInfo.type) (kind := Lean.MetavarKind.synthetic)
      let termState : Lean.Elab.Term.SavedState ← Lean.Elab.Term.saveState
      let tacticState : Lean.Elab.Tactic.SavedState := { term := termState, tactic := { goals := [mvar.mvarId!] }}
      return tacticState
  Context.runTermElabM' termElabM

def execute_tactic (state: Lean.Elab.Tactic.SavedState) (tacticString : String) : ReaderT Context IO (Lean.Elab.Tactic.SavedState × Response) := do
  let context ← read
  match Lean.Parser.runParserCategory
    (env := context.env)
    (catName := `tactic)
    (input := tacticString)
    (fileName := "<stdin>") with
  | Except.error err => pure (state, { errors := #[err] })
  | Except.ok stx    => Context.runTermElabM' <| do
    state.term.restore
    let tac : Lean.Elab.Tactic.TacticM Unit := set state.tactic *> Lean.Elab.Tactic.evalTactic stx
    let mvarId : Lean.MVarId := state.tactic.goals.head!
    try
      let unsolvedGoals ← Lean.Elab.Tactic.run mvarId tac
      if (← getThe Lean.Core.State).messages.hasErrors then
        let messages := (← getThe Lean.Core.State).messages.getErrorMessages |>.toList.toArray
        pure (state, { errors := ← (messages.map Lean.Message.data).mapM fun md => md.toString })
      else
        let nextState : Lean.Elab.Tactic.SavedState := { term := (← Lean.Elab.Term.saveState), tactic := { goals := unsolvedGoals}}
        let goals ← nextState.tactic.goals.mapM fun g => do pure $ toString (← Lean.Meta.ppGoal g)
        pure (nextState, { goals := goals.toArray })
    catch ex =>
      pure (state, { errors := #[← ex.toMessageData.toString] })



end Pantograph
