import LSpec
import Test.Delate
import Test.Environment
import Test.Frontend
import Test.Integration
import Test.Library
import Test.Metavar
import Test.Proofs
import Test.Serial
import Test.Tactic

-- Test running infrastructure

namespace Pantograph.Test

def addPrefix (pref: String) (tests: List (String × α)): List (String  × α) :=
  tests.map (λ (name, x) => (pref ++ "/" ++ name, x))

/-- Runs test in parallel. Filters test name if given -/
def runTestGroup (nameFilter?: Option String) (tests: List (String × IO LSpec.TestSeq)): IO LSpec.TestSeq := do
  let tests: List (String × IO LSpec.TestSeq) := match nameFilter? with
    | .some nameFilter => tests.filter (λ (name, _) => nameFilter.isPrefixOf name)
    | .none => tests
  let tasks: List (String × Task _) ← tests.mapM (λ (name, task) => do
    return (name, ← EIO.asTask task))
  let all := tasks.foldl (λ acc (name, task) =>
    let v: Except IO.Error LSpec.TestSeq := Task.get task
    match v with
    | .ok case => acc ++ (LSpec.group name case)
    | .error e => acc ++ (expectationFailure name e.toString)
    ) LSpec.TestSeq.done
  return all

end Pantograph.Test

open Pantograph.Test

/-- Main entry of tests; Provide an argument to filter tests by prefix -/
def main (args: List String) := do
  let nameFilter? := args.head?
  Lean.initSearchPath (← Lean.findSysroot)
  let env_default: Lean.Environment ← Lean.importModules
    (imports := #[`Init])
    (opts := {})
    (trustLevel := 1)

  let suites: List (String × List (String × IO LSpec.TestSeq)) := [
    ("Environment", Environment.suite),
    ("Frontend", Frontend.suite env_default),
    ("Integration", Integration.suite env_default),
    ("Library", Library.suite env_default),
    ("Metavar", Metavar.suite env_default),
    ("Proofs", Proofs.suite env_default),
    ("Delate", Delate.suite env_default),
    ("Serial", Serial.suite env_default),
    ("Tactic/Assign", Tactic.Assign.suite env_default),
    ("Tactic/Prograde", Tactic.Prograde.suite env_default),
    ("Tactic/Special", Tactic.Special.suite env_default),
  ]
  let tests: List (String × IO LSpec.TestSeq) := suites.foldl (λ acc (name, suite) => acc ++ (addPrefix name suite)) []
  LSpec.lspecEachIO [()] (λ () => runTestGroup nameFilter? tests)
