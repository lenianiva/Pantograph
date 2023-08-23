import LSpec
import Pantograph.Serial
import Pantograph.Symbols

namespace Pantograph.Test

open Pantograph
open Lean

deriving instance Repr, DecidableEq for Commands.BoundExpression

def test_str_to_name: LSpec.TestSeq :=
    LSpec.test "Symbol parsing" (Name.str (.str (.str .anonymous "Lean") "Meta") "run" = Pantograph.str_to_name "Lean.Meta.run")

def test_expr_to_binder (env: Environment): IO LSpec.TestSeq := do
  let entries: List (String × Commands.BoundExpression) := [
    ("Nat.add_comm", { binders := #[("n", "Nat"), ("m", "Nat")], target := "n + m = m + n" }),
    ("Nat.le_of_succ_le", { binders := #[("n", "Nat"), ("m", "Nat"), ("h", "Nat.succ n ≤ m")], target := "n ≤ m" })
  ]
  let coreM := entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := str_to_name symbol |> env.find? |>.get! |>.type
    let test := LSpec.check symbol ((← type_expr_to_bound expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done |>.run'
  let coreContext: Core.Context := {
    currNamespace := Lean.Name.str .anonymous "Aniva"
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph/Test>",
    fileMap := { source := "", positions := #[0], lines := #[1] }
  }
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok a            => return a

def test_sexp_of_symbol (env: Environment): IO LSpec.TestSeq := do
  let entries: List (String × String) := [
    -- This one contains unhygienic variable names which must be suppressed
    ("Nat.add", "(:forall :anon (:c Nat) (:forall :anon (:c Nat) (:c Nat)))"),
    -- These ones are normal and easy
    ("Nat.add_one", "(:forall n (:c Nat) ((((:c Eq) (:c Nat)) (((((((:c HAdd.hAdd) (:c Nat)) (:c Nat)) (:c Nat)) (((:c instHAdd) (:c Nat)) (:c instAddNat))) 0) ((((:c OfNat.ofNat) (:c Nat)) (:lit 1)) ((:c instOfNatNat) (:lit 1))))) ((:c Nat.succ) 0)))"),
    ("Nat.le_of_succ_le", "(:forall n (:c Nat) (:forall m (:c Nat) (:forall h (((((:c LE.le) (:c Nat)) (:c instLENat)) ((:c Nat.succ) 1)) 0) (((((:c LE.le) (:c Nat)) (:c instLENat)) 2) 1)) :implicit) :implicit)"),
    -- Handling of higher order types
    ("Or", "(:forall a (:sort 0) (:forall b (:sort 0) (:sort 0)))"),
    ("List", "(:forall α (:sort (+ u 1)) (:sort (+ u 1)))")
  ]
  let metaM: MetaM LSpec.TestSeq := entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := str_to_name symbol |> env.find? |>.get! |>.type
    let test := LSpec.check symbol ((← serialize_expression_ast expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done |>.run'
  let coreM := metaM.run'
  let coreContext: Core.Context := {
    currNamespace := Lean.Name.str .anonymous "Aniva"
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph/Test>",
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
    (LSpec.group "str_to_name" test_str_to_name) ++
    (LSpec.group "Expression binder" (← test_expr_to_binder env)) ++
    (LSpec.group "Sexp from symbol" (← test_sexp_of_symbol env))

end Pantograph.Test
