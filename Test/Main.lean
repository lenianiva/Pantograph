import LSpec
import Test.Integration
import Test.Proofs
import Test.Serial

open Pantograph.Test

unsafe def main := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

	-- TODO: Add proper testing
  let suites := [
    test_serial,
    test_proofs
    --test_integration
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
