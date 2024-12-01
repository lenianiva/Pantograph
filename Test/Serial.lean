import LSpec
import Test.Common
import Lean
import Pantograph.Library

open Lean

namespace Pantograph.Test.Serial

structure MultiState where
  coreContext : Core.Context
  coreStates : Array Core.State

abbrev TestM := StateRefT MultiState $ TestT $ EIO LSpec.TestSeq

def runCoreM { α } (id : Nat) (testCoreM: TestT CoreM α) : TestM α := do
  let multiState ← get
  let state ← match multiState.coreStates[id]? with
    | .some state => pure state
    | .none =>
      let test := LSpec.test "Invalid index" (id < multiState.coreStates.size)
      throw test
  let coreM := runTestWithResult testCoreM
  match ← (coreM.run' multiState.coreContext state).toBaseIO with
  | .error _ => do
    let test := LSpec.test "Exception" false
    throw test
  | .ok (a, tests) => do
    set $ (← getThe LSpec.TestSeq) ++ tests
    return a

def simple : TestM Unit := do
  return

structure Test where
  name : String
  nInstances : Nat
  routine: TestM Unit

protected def Test.run (test: Test) (env: Lean.Environment) : IO LSpec.TestSeq := do
  -- Create the state
  let state : MultiState := {
    coreContext := ← createCoreContext #[],
    coreStates := Array.range test.nInstances |>.map λ _ => { env },
  }
  match ← (runTest $ test.routine.run' state).toBaseIO with
  | .ok e => return e
  | .error e => return e

def suite (env : Lean.Environment): List (String × IO LSpec.TestSeq) :=
  let tests: List Test := [
    { name := "simple", nInstances := 2, routine := simple }
  ]
  tests.map (fun test => (test.name, test.run env))

end Pantograph.Test.Serial
