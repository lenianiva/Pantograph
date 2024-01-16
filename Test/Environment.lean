import LSpec
import Pantograph.Serial
import Pantograph.Environment
import Test.Common

namespace Pantograph.Test.Environment

open Pantograph
open Lean

deriving instance DecidableEq, Repr for Protocol.InductInfo
deriving instance DecidableEq, Repr for Protocol.EnvInspectResult

def test_symbol_visibility (env: Environment): IO LSpec.TestSeq := do
  let entries: List (Name × Bool) := [
    ("Nat.add_comm".toName, false),
    ("Lean.Name".toName, true)
  ]
  let suite := entries.foldl (λ suites (symbol, target) =>
    let constant := env.constants.find! symbol
    let test := LSpec.check symbol.toString ((Environment.is_symbol_unsafe_or_internal symbol constant) == target)
    LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  return suite

def test_inspect (env: Environment): IO LSpec.TestSeq := do
  let inner: CoreM LSpec.TestSeq := do
    let args: Protocol.EnvInspect := { name := "Or" }
    let result ← match ← Environment.inspect args (options := {}) with
      | .ok result => pure $ result
      | .error e => panic! s!"Error: {e.desc}"
    --IO.println s!"{reprStr result.inductInfo?}"
    let test := LSpec.check "Or" (result.inductInfo? == .some {
      numParams := 2,
      numIndices := 0,
      all := ["Or"],
      ctors := ["Or.inl", "Or.inr"],
    })
    return LSpec.TestSeq.append LSpec.TestSeq.done test
  runCoreMSeq env inner

def suite: IO LSpec.TestSeq := do
  let env: Environment ← importModules
    (imports := #["Init"].map (λ str => { module := str.toName, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)

  return LSpec.group "Environment" $
    (LSpec.group "Symbol visibility" (← test_symbol_visibility env)) ++
    (LSpec.group "Inspect" (← test_inspect env))

end Pantograph.Test.Environment
