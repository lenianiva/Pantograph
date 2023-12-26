import LSpec
import Pantograph.Serial

namespace Pantograph.Test.Serial

open Pantograph
open Lean

deriving instance Repr, DecidableEq for Protocol.BoundExpression

def test_name_to_ast: LSpec.TestSeq :=
  let quote := "\""
  let escape := "\\"
  LSpec.test "a.b.1" (name_to_ast (Name.num (.str (.str .anonymous "a") "b") 1) = "a.b.1") ++
  LSpec.test "seg.«a.b»" (name_to_ast (Name.str (.str .anonymous "seg") "a.b") = s!"{quote}seg.«a.b»{quote}") ++
  -- Pathological test case
  LSpec.test s!"«̈{escape}{quote}»" (name_to_ast (Name.str .anonymous s!"{escape}{quote}") = s!"{quote}«{escape}{quote}»{quote}")

def test_expr_to_binder (env: Environment): IO LSpec.TestSeq := do
  let entries: List (Name × Protocol.BoundExpression) := [
    ("Nat.add_comm".toName, { binders := #[("n", "Nat"), ("m", "Nat")], target := "n + m = m + n" }),
    ("Nat.le_of_succ_le".toName, { binders := #[("n", "Nat"), ("m", "Nat"), ("h", "Nat.succ n ≤ m")], target := "n ≤ m" })
  ]
  let coreM: CoreM LSpec.TestSeq := entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := env.find? symbol |>.get! |>.type
    let test := LSpec.check symbol.toString ((← type_expr_to_bound expr) = target)
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
    ("Nat.add", "(:forall _ (:c Nat) (:forall _ (:c Nat) (:c Nat)))"),
    -- These ones are normal and easy
    ("Nat.add_one", "(:forall n (:c Nat) ((:c Eq) (:c Nat) ((:c HAdd.hAdd) (:c Nat) (:c Nat) (:c Nat) ((:c instHAdd) (:c Nat) (:c instAddNat)) 0 ((:c OfNat.ofNat) (:c Nat) (:lit 1) ((:c instOfNatNat) (:lit 1)))) ((:c Nat.succ) 0)))"),
    ("Nat.le_of_succ_le", "(:forall n (:c Nat) (:forall m (:c Nat) (:forall h ((:c LE.le) (:c Nat) (:c instLENat) ((:c Nat.succ) 1) 0) ((:c LE.le) (:c Nat) (:c instLENat) 2 1)) :implicit) :implicit)"),
    -- Handling of higher order types
    ("Or", "(:forall a (:sort 0) (:forall b (:sort 0) (:sort 0)))"),
    ("List", "(:forall α (:sort (+ u 1)) (:sort (+ u 1)))")
  ]
  let metaM: MetaM LSpec.TestSeq := entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := env.find? symbol.toName |>.get! |>.type
    let test := LSpec.check symbol ((← serialize_expression_ast expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done
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

def test_sexp_of_expr (env: Environment): IO LSpec.TestSeq := do
  let entries: List (String × String) := [
    ("λ x: Nat × Bool => x.1", "(:lambda x ((:c Prod) (:c Nat) (:c Bool)) ((:c Prod.fst) (:c Nat) (:c Bool) 0))"),
    ("λ x: Array Nat => x.data", "(:lambda x ((:c Array) (:c Nat)) ((:c Array.data) (:c Nat) 0))")
  ]
  let termElabM: Elab.TermElabM LSpec.TestSeq := entries.foldlM (λ suites (source, target) => do
    let env ← MonadEnv.getEnv
    let s := syntax_from_str env source |>.toOption |>.get!
    let expr := (← syntax_to_expr s) |>.toOption |>.get!
    let test := LSpec.check source ((← serialize_expression_ast expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  let metaM := termElabM.run' (ctx := {
    declName? := some "_pantograph",
    errToSorry := false
  })
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

def suite: IO LSpec.TestSeq := do
  let env: Environment ← importModules
    (imports := #["Init"].map (λ str => { module := str.toName, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)

  return LSpec.group "Serialization" $
    (LSpec.group "name_to_ast" test_name_to_ast) ++
    (LSpec.group "Expression binder" (← test_expr_to_binder env)) ++
    (LSpec.group "Sexp from symbol" (← test_sexp_of_symbol env)) ++
    (LSpec.group "Sexp from expr" (← test_sexp_of_expr env))

end Pantograph.Test.Serial
