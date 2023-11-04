import LSpec
import Test.Holes
import Test.Integration
import Test.Proofs
import Test.Serial

open Pantograph.Test

unsafe def main := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

  let suites := [
    Holes.suite,
    Integration.suite,
    Proofs.suite,
    Serial.suite
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
