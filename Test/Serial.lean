import LSpec
import Pantograph.Serial
import Test.Common
import Lean

open Lean
namespace Pantograph.Test.Serial

open Pantograph

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
    ("Nat.le_of_succ_le".toName, { binders := #[("n", "Nat"), ("m", "Nat"), ("h", "n.succ ≤ m")], target := "n ≤ m" })
  ]
  let coreM: CoreM LSpec.TestSeq := entries.foldlM (λ suites (symbol, target) => do
    let env ← MonadEnv.getEnv
    let expr := env.find? symbol |>.get! |>.type
    let test := LSpec.check symbol.toString ((← type_expr_to_bound expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done |>.run'
  runCoreMSeq env coreM

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
  runMetaMSeq env metaM

def test_sexp_of_expr (env: Environment): IO LSpec.TestSeq := do
  let entries: List (String × String) := [
    ("λ x: Nat × Bool => x.1", "(:lambda x ((:c Prod) (:c Nat) (:c Bool)) ((:c Prod.fst) (:c Nat) (:c Bool) 0))"),
    ("λ x: Array Nat => x.data", "(:lambda x ((:c Array) (:c Nat)) ((:c Array.data) (:c Nat) 0))")
  ]
  let termElabM: Elab.TermElabM LSpec.TestSeq := entries.foldlM (λ suites (source, target) => do
    let env ← MonadEnv.getEnv
    let s := parseTerm env source |>.toOption |>.get!
    let expr := (← elabTerm s) |>.toOption |>.get!
    let test := LSpec.check source ((← serialize_expression_ast expr) = target)
    return LSpec.TestSeq.append suites test) LSpec.TestSeq.done
  let metaM := termElabM.run' (ctx := defaultTermElabMContext)
  runMetaMSeq env metaM

-- Instance parsing
def test_instance (env: Environment): IO LSpec.TestSeq := do
  let metaM: MetaM LSpec.TestSeq := do
    let env ← MonadEnv.getEnv
    let source := "λ x y: Nat => HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) x y"
    let s := parseTerm env source |>.toOption |>.get!
    let _expr := (← runTermElabMInMeta <| elabTerm s) |>.toOption |>.get!
    return LSpec.TestSeq.done
  runMetaMSeq env metaM

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("name_to_ast", do pure test_name_to_ast),
    ("Expression binder", test_expr_to_binder env),
    ("Sexp from symbol", test_sexp_of_symbol env),
    ("Sexp from expr", test_sexp_of_expr env),
    ("Instance", test_instance env),
  ]

end Pantograph.Test.Serial
