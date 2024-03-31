import LSpec
import Test.Environment
import Test.Integration
import Test.Library
import Test.Metavar
import Test.Proofs
import Test.Serial

open Pantograph.Test

def main := do
  Lean.initSearchPath (← Lean.findSysroot)

  let suites := [
    Environment.suite,
    Integration.suite,
    Library.suite,
    Metavar.suite,
    Proofs.suite,
    Serial.suite,
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
