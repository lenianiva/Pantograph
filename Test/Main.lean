import LSpec
import Test.Environment
import Test.Integration
import Test.Library
import Test.Metavar
import Test.Proofs
import Test.Serial

open Pantograph.Test

def main (args: List String) := do
  let name_filter := args.head?
  Lean.initSearchPath (← Lean.findSysroot)
  let env_default: Lean.Environment ← Lean.importModules
    (imports := #[`Init])
    (opts := {})
    (trustLevel := 1)

  let suites: List (String × List (String × IO LSpec.TestSeq)) := [
    ("Environment", Environment.suite),
    ("Integration", Integration.suite),
    ("Library", Library.suite env_default),
    ("Metavar", Metavar.suite env_default),
    ("Proofs", Proofs.suite env_default),
    ("Serial", Serial.suite env_default),
  ]
  let tests: List (String × IO LSpec.TestSeq) := suites.foldl (λ acc (name, suite) => acc ++ (addPrefix name suite)) []
  LSpec.lspecIO (← runTestGroup name_filter tests)
