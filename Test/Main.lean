import LSpec
import Test.Environment
import Test.Metavar
import Test.Integration
import Test.Proofs
import Test.Serial

open Pantograph.Test

def main := do
  Lean.initSearchPath (← Lean.findSysroot)

  let suites := [
    Metavar.suite,
    Integration.suite,
    Proofs.suite,
    Serial.suite,
    Environment.suite
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
