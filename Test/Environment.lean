import LSpec
import Pantograph.Serial
import Pantograph.Environment
import Test.Common
import Lean

open Lean
namespace Pantograph.Test.Environment

open Pantograph

deriving instance DecidableEq, Repr for Protocol.InductInfo
deriving instance DecidableEq, Repr for Protocol.ConstructorInfo
deriving instance DecidableEq, Repr for Protocol.RecursorInfo
deriving instance DecidableEq, Repr for Protocol.EnvInspectResult

def test_catalog: IO LSpec.TestSeq := do
  let env: Environment ← importModules
    (imports := #[`Init])
    (opts := {})
    (trustLevel := 1)
  let inner: CoreM LSpec.TestSeq := do
    let catalogResult ← Environment.catalog {}
    let symbolsWithNum := env.constants.fold (init := #[]) (λ acc name info =>
      match (Environment.toFilteredSymbol name info).isSome && (name matches .num _ _) with
      | false => acc
      | true => acc.push name
      )
    return LSpec.check "No num symbols" (symbolsWithNum.size == 0)
  runCoreMSeq env inner

def test_symbol_visibility: IO LSpec.TestSeq := do
  let entries: List (Name × Bool) := [
    ("Nat.add_comm".toName, false),
    ("Lean.Name".toName, true),
    ("Init.Data.Nat.Basic._auxLemma.4".toName, true),
  ]
  let suite := entries.foldl (λ suites (symbol, target) =>
    let test := LSpec.check symbol.toString ((Environment.isNameInternal symbol) == target)
    LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  return suite

inductive ConstantCat where
  | induct (info: Protocol.InductInfo)
  | ctor (info: Protocol.ConstructorInfo)
  | recursor (info: Protocol.RecursorInfo)

def test_inspect: IO LSpec.TestSeq := do
  let env: Environment ← importModules
    (imports := #[`Init])
    (opts := {})
    (trustLevel := 1)
  let testCases: List (String × ConstantCat) := [
    ("Or", ConstantCat.induct {
      numParams := 2,
      numIndices := 0,
      all := #["Or"],
      ctors := #["Or.inl", "Or.inr"],
    }),
    ("Except.ok", ConstantCat.ctor {
      induct := "Except",
      cidx := 1,
      numParams := 2,
      numFields := 1,
    }),
    ("Eq.rec", ConstantCat.recursor {
      all := #["Eq"],
      numParams := 2,
      numIndices := 1,
      numMotives := 1,
      numMinors := 1,
      k := true,
    }),
    ("ForM.rec", ConstantCat.recursor {
      all := #["ForM"],
      numParams := 3,
      numIndices := 0,
      numMotives := 1,
      numMinors := 1,
      k := false,
    })
  ]
  let inner: CoreM LSpec.TestSeq := do
    testCases.foldlM (λ acc (name, cat) => do
      let args: Protocol.EnvInspect := { name := name }
      let result ← match ← Environment.inspect args (options := {}) with
        | .ok result => pure $ result
        | .error e => panic! s!"Error: {e.desc}"
      let p := match cat with
        | .induct info => LSpec.test name (result.inductInfo? == .some info)
        | .ctor info => LSpec.test name (result.constructorInfo? == .some info)
        | .recursor info => LSpec.test name (result.recursorInfo? == .some info)
      return LSpec.TestSeq.append acc p
    ) LSpec.TestSeq.done
  runCoreMSeq env inner

def suite: IO LSpec.TestSeq := do
  return LSpec.group "Environment" $
    (LSpec.group "Catalog" (← test_catalog)) ++
    (LSpec.group "Symbol visibility" (← test_symbol_visibility)) ++
    (LSpec.group "Inspect" (← test_inspect))

end Pantograph.Test.Environment
