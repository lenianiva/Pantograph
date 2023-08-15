import LSpec
import Test.Integration
import Test.Proofs
import Test.Serial

open Pantograph.Test

unsafe def main := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

  let suites := [
    test_integration,
    test_proofs,
    test_serial
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
