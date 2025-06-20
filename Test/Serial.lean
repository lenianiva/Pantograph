import LSpec
import Test.Common
import Lean
import Pantograph.Library

open Lean

namespace Pantograph.Test.Serial

structure MultiState where
  coreContext : Core.Context
  env: Environment

abbrev TestM := TestT $ StateRefT MultiState $ IO

instance : MonadEnv TestM where
  getEnv      := return (← getThe MultiState).env
  modifyEnv f := do modifyThe MultiState fun s => { s with env := f s.env }

def runCoreM { α } (state : Core.State) (testCoreM : TestT CoreM α) : TestM (α × Core.State) := do
  let multiState ← getThe MultiState
  let coreM := runTestWithResult testCoreM
  match ← (coreM.run multiState.coreContext state).toBaseIO with
  | .error e => do
    throw $ .userError $ ← e.toMessageData.toString
  | .ok ((a, tests), state') => do
    set $ (← getThe LSpec.TestSeq) ++ tests
    return (a, state')

def test_pickling_environment : TestM Unit := do
  let coreSrc : Core.State := { env := ← getEnv }
  let coreDst : Core.State := { env := ← getEnv }

  let name := `mystery
  IO.FS.withTempFile λ _ envPicklePath => do
  let ((), _) ← runCoreM coreSrc do
    let type: Expr := .forallE `p (.sort 0) (.forallE `h (.bvar 0) (.bvar 1) .default) .default
    let value: Expr := .lam `p (.sort 0) (.lam `h (.bvar 0) (.bvar 0) .default) .default
    let c := Declaration.defnDecl <| mkDefinitionValEx
      (name := name)
      (levelParams := [])
      (type := type)
      (value := value)
      (hints := mkReducibilityHintsRegularEx 1)
      (safety := .safe)
      (all := [])
    addDecl c
    environmentPickle (← getEnv) envPicklePath

  let _ ← runCoreM coreDst do
    let (env', _) ← environmentUnpickle envPicklePath
    checkTrue s!"Has symbol {name}" (env'.find? name).isSome
    let anotherName := `mystery2
    checkTrue s!"Doesn't have symbol {anotherName}" (env'.find? anotherName).isNone

def test_goal_state_simple : TestM Unit := do
  let coreSrc : Core.State := { env := ← getEnv }
  let coreDst : Core.State := { env := ← getEnv }
  IO.FS.withTempFile λ _ statePath => do
  let type: Expr := .forallE `p (.sort 0) (.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let stateGenerate : MetaM GoalState := runTermElabMInMeta do
    GoalState.create type

  let ((), _) ← runCoreM coreSrc do
    let state ← stateGenerate.run'
    goalStatePickle state statePath

  let ((), _) ← runCoreM coreDst do
    let (goalState, _) ← goalStateUnpickle statePath (← getEnv)
    let metaM : MetaM (List Expr) := do
      goalState.goals.mapM λ goal => goalState.withContext goal goal.getType
    let types ← metaM.run'
    checkTrue "Goals" $ types[0]!.equal type

def test_pickling_env_extensions : TestM Unit := do
  let coreSrc : Core.State := { env := ← getEnv }
  let ((), _) ← runCoreM coreSrc $ transformTestT runTermElabMInCore do
    let .ok e ← elabTerm (← `(term|2 ≤ 5)) .none | unreachable!
    let state ← GoalState.create e
    let .success state _ ← state.tacticOn' 0 (← `(tactic|apply Nat.le_trans)) | unreachable!
    let .success state' _ ← state.tacticOn' 2 (← `(tactic|exact 3)) | unreachable!
    let state := state'.immediateResume state
    let .success state1 _ ← state.tacticOn' 1 (← `(tactic|simp)) | unreachable!
    let parentExpr := state1.parentExpr?.get!
    IO.println s!"{parentExpr}"
    checkTrue "has aux lemma" $ parentExpr.getUsedConstants.any λ name => name.isAuxLemma

    let state1 := state1.immediateResume state
    let .success stateT _ ← state.tacticOn' 0 (← `(tactic|simp)) | unreachable!
    let rootExpr:= stateT.rootExpr?.get!
    IO.println s!"root is {rootExpr}"
    checkTrue "has aux lemma" $ rootExpr.getUsedConstants.any λ name => name.isAuxLemma
  return ()

structure Test where
  name : String
  routine: TestM Unit

protected def Test.run (test: Test) (env: Environment) : IO LSpec.TestSeq := do
  -- Create the state
  let state : MultiState := {
    coreContext := ← createCoreContext #[],
    env,
  }
  match ← ((runTest $ test.routine).run' state).toBaseIO with
  | .ok e => return e
  | .error e =>
    return LSpec.check s!"Emitted exception: {e.toString}" (e.toString == "")

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests: List Test := [
    { name := "environment", routine := test_pickling_environment, },
    { name := "goal simple", routine := test_goal_state_simple, },
    { name := "extensions", routine := test_pickling_env_extensions, },
  ]
  tests.map (fun test => (test.name, test.run env))

end Pantograph.Test.Serial
