import LSpec
import Test.Common
import Lean
import Pantograph.Library

open Lean

namespace Pantograph.Test.Serial

def tempPath : IO System.FilePath := do
  Prod.snd <$> IO.FS.createTempFile

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

def test_environment_pickling : TestM Unit := do
  let stateSrc: Core.State := { env := ← getEnv }
  let stateDst: Core.State := { env := ← getEnv }

  let name := `mystery
  let envPicklePath ← tempPath
  let ((), _) ← runCoreM stateSrc do
    let type: Expr := .forallE `p (.sort 0) (.forallE `h (.bvar 0) (.bvar 1) .default) .default
    let value: Expr := .lam `p (.sort 0) (.lam `h (.bvar 0) (.bvar 0) .default) .default
    let c := Lean.Declaration.defnDecl <| Lean.mkDefinitionValEx
      (name := name)
      (levelParams := [])
      (type := type)
      (value := value)
      (hints := Lean.mkReducibilityHintsRegularEx 1)
      (safety := Lean.DefinitionSafety.safe)
      (all := [])
    let env' ← match (← getEnv).addDecl (← getOptions) c with
      | .error e => do
        let error ← (e.toMessageData (← getOptions)).toString
        throwError error
      | .ok env' => pure env'
    environmentPickle env' envPicklePath

  let _ ← runCoreM stateDst do
    let (env', _) ← environmentUnpickle envPicklePath
    checkTrue s!"Has symbol {name}" (env'.find? name).isSome
    let anotherName := `mystery2
    checkTrue s!"Doesn't have symbol {anotherName}" (env'.find? anotherName).isNone

  IO.FS.removeFile envPicklePath

structure Test where
  name : String
  nInstances : Nat
  routine: TestM Unit

protected def Test.run (test: Test) (env: Lean.Environment) : IO LSpec.TestSeq := do
  -- Create the state
  let state : MultiState := {
    coreContext := ← createCoreContext #[],
    env,
  }
  match ← ((runTest $ test.routine).run' state).toBaseIO with
  | .ok e => return e
  | .error e =>
    return LSpec.check "Emitted exception" (e.toString == "")

def suite (env : Lean.Environment): List (String × IO LSpec.TestSeq) :=
  let tests: List Test := [
    { name := "environment_pickling", nInstances := 2, routine := test_environment_pickling },
  ]
  tests.map (fun test => (test.name, test.run env))

end Pantograph.Test.Serial
