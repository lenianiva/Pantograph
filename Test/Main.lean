import LSpec
import Test.Catalog
import Test.Holes
import Test.Integration
import Test.Proofs
import Test.Serial

open Pantograph.Test

def main := do
  Lean.initSearchPath (← Lean.findSysroot)

  let suites := [
    Holes.suite,
    Integration.suite,
    Proofs.suite,
    Serial.suite,
    Catalog.suite
  ]
  let all ← suites.foldlM (λ acc m => do pure $ acc ++ (← m)) LSpec.TestSeq.done
  LSpec.lspecIO $ all
