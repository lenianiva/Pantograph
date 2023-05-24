import LSpec
import Pantograph.Serial
import Pantograph.Symbols

namespace Pantograph.Test

open Pantograph
open Lean

deriving instance Repr, DecidableEq for BoundExpression

def test_expr_to_binder (env: Environment): IO LSpec.TestSeq := do
  let cases: List (String × BoundExpression) := [
    ("Nat.add_comm", { binders := #[("n", "Nat"), ("m", "Nat")], target := "n + m = m + n" }),
    ("Nat.le_of_succ_le", { binders := #[("n", "Nat"), ("m", "Nat"), ("h", "Nat.succ n ≤ m")], target := "n ≤ m" })
  ]
  let coreM := cases.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := str_to_name symbol |> env.find? |>.get! |>.type
    let test := LSpec.check symbol ((← type_expr_to_bound expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done |>.run'
  let coreContext: Core.Context := {
    currNamespace := str_to_name "Aniva",
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0], lines := #[1] }
  }
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok a            => return a

def test_serial: IO LSpec.TestSeq := do
  let env: Environment ← importModules
    (imports := ["Init"].map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)

  return LSpec.group "Serialisation" $
    (LSpec.group "Expression binder" (← test_expr_to_binder env)) ++
    LSpec.test "Symbol parsing" (Name.str (.str (.str .anonymous "Lean") "Meta") "run" = Pantograph.str_to_name "Lean.Meta.run")

end Pantograph.Test
