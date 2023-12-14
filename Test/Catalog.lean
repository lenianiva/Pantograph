import LSpec
import Pantograph.Serial
import Pantograph.Symbol

namespace Pantograph.Test.Catalog

open Pantograph
open Lean

def test_symbol_visibility (env: Environment): IO LSpec.TestSeq := do
  let entries: List (Name × Bool) := [
    ("Nat.add_comm".toName, false),
    ("Lean.Name".toName, true)
  ]
  let suite := entries.foldl (λ suites (symbol, target) =>
    let constant := env.constants.find! symbol
    let test := LSpec.check symbol.toString ((is_symbol_unsafe_or_internal symbol constant) == target)
    LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  return suite

def suite: IO LSpec.TestSeq := do
  let env: Environment ← importModules
    (imports := #["Init"].map (λ str => { module := str.toName, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)

  return LSpec.group "Catalog" $
    (LSpec.group "Symbol visibility" (← test_symbol_visibility env))

end Pantograph.Test.Catalog
