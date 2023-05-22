import LSpec
import Pantograph.Symbols
import Test.Proofs
import Test.Serial

open Pantograph.Test

unsafe def main := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

  let suites := [
    test_serial,
    test_proofs
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
