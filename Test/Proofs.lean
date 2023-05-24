import LSpec
import Pantograph.Meta
import Pantograph.Serial

namespace Pantograph.Test
open Pantograph
open Lean

inductive Start where
  | copy (name: String) -- Start from some name in the environment
  | expr (expr: String) -- Start from some expression

abbrev TestM := StateRefT ProofTree M

def start_proof (start: Start): M (LSpec.TestSeq × Option ProofTree) := do
  let env ← Lean.MonadEnv.getEnv
  let mut testSeq := LSpec.TestSeq.done
  match start with
  | .copy name =>
    let cInfo? := str_to_name name |> env.find?
    testSeq := testSeq ++ LSpec.check s!"Symbol exists {name}" cInfo?.isSome
    match cInfo? with
    | .some cInfo =>
      let state ← ProofTree.create
        (name := str_to_name "TestExample")
        (expr := cInfo.type)
      return (testSeq, Option.some state)
    | .none =>
      return (testSeq, Option.none)
  | .expr expr =>
    let syn? := syntax_from_str env expr
    testSeq := testSeq ++ LSpec.check s!"Parsing {expr}" (syn?.isOk)
    match syn? with
    | .error error =>
      IO.println error
      return (testSeq, Option.none)
    | .ok syn =>
      let expr? ← syntax_to_expr syn
      testSeq := testSeq ++ LSpec.check s!"Elaborating" expr?.isOk
      match expr? with
      | .error error =>
        IO.println error
        return (testSeq, Option.none)
      | .ok expr =>
        let state ← ProofTree.create
          (name := str_to_name "TestExample")
          (expr := expr)
        return (testSeq, Option.some state)

deriving instance DecidableEq, Repr for TacticResult

def proof_step (stateId: Nat) (goalId: Nat) (tactic: String)
    (expected: TacticResult) : TestM LSpec.TestSeq := do
  let result: TacticResult ← ProofTree.execute stateId goalId tactic
  match expected, result with
  | .success (.some i) #[], .success (.some _) goals =>
    -- If the goals are omitted but the next state is specified, we imply that
    -- the tactic succeeded.
    let expected := .success (.some i) goals
    return LSpec.test s!"{stateId}.{goalId} {tactic}"   (result = expected)
  | _, _ =>
    return LSpec.test s!"{stateId}.{goalId} {tactic}"   (result = expected)

def proof_inspect (expected: Array String) : TestM LSpec.TestSeq := do
  let result := (← get).structure_array
  return LSpec.test s!"tree structure" (result = expected)

def proof_runner (env: Lean.Environment) (start: Start) (steps: List (TestM LSpec.TestSeq)): IO LSpec.TestSeq := do
  let termElabM := do
    let (testSeq, state?) ← start_proof start
    match state? with
    | .none => return testSeq
    | .some state => steps.foldlM (fun tests m => do pure $ tests ++ (← m)) testSeq |>.run' state

  let coreContext: Lean.Core.Context := {
    currNamespace := str_to_name "Aniva",
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0], lines := #[1] }
  }
  let metaM := termElabM.run' (ctx := {
    declName? := some "_pantograph",
    errToSorry := false
  })
  let coreM := metaM.run'
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok a            => return a


example: ∀ (a b: Nat), a + b = b + a := by
  intro n m
  rw [Nat.add_comm]
def proof_nat_add_comm (env: Lean.Environment): IO LSpec.TestSeq :=
  let goal1 := "n m : Nat\n⊢ n + m = m + n"
  proof_runner env (.copy "Nat.add_comm") [
    proof_step 0 0 "intro n m"
      (.success (.some 1) #[goal1]),
    proof_step 1 0 "assumption"
      (.failure #[s!"tactic 'assumption' failed\n{goal1}"]),
    proof_step 1 0 "rw [Nat.add_comm]"
      (.success .none #[])
  ]
def proof_nat_add_comm_manual (env: Lean.Environment): IO LSpec.TestSeq := do
  let goal1 := "n m : Nat\n⊢ n + m = m + n"
  proof_runner env (.expr "∀ (a b: Nat), a + b = b + a") [
    proof_step 0 0 "intro n m"
      (.success (.some 1) #[goal1]),
    proof_step 1 0 "assumption"
      (.failure #[s!"tactic 'assumption' failed\n{goal1}"]),
    proof_step 1 0 "rw [Nat.add_comm]"
      (.success .none #[])
  ]

-- Two ways to write the same theorem
example: ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
example: ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption
def proof_or_comm (env: Lean.Environment): IO LSpec.TestSeq := do
  proof_runner env (.expr "∀ (p q: Prop), p ∨ q → q ∨ p") [
    proof_step 0 0 "intro p q h"
      (.success (.some 1) #["p q : Prop\nh : p ∨ q\n⊢ q ∨ p"]),
    proof_step 1 0 "cases h"
      (.success (.some 2) #[]),
    proof_inspect #["", "0.0", "1.0"],
    proof_step 2 0 "apply Or.inr"
      (.success (.some 3) #[]),
    proof_inspect #["", "0.0", "1.0", "2.0"],
    proof_step 3 0 "assumption"
      (.success .none #[]),
    proof_step 2 1 "apply Or.inl"
      (.success (.some 4) #[]),
    proof_step 4 0 "assumption"
      (.success .none #[]),
    proof_inspect #["", "0.0", "1.0", "2.0", "2.1"]
  ]

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *
  assumption
def proof_arith_1 (env: Lean.Environment): IO LSpec.TestSeq := do
  proof_runner env (.expr "∀ (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x)), p (x * w * z + y * x)") [
    proof_step 0 0 "intros"
      (.success (.some 1) #[]),
    proof_step 1 0 "simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *"
      (.success (.some 2) #[]),
    proof_step 2 0 "assumption"
      (.success .none #[])
  ]

def test_proofs : IO LSpec.TestSeq := do
  let env: Lean.Environment ← Lean.importModules
    (imports := ["Init"].map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)

  return LSpec.group "Proofs" $
    (LSpec.group "Nat.add_comm" $ (← proof_nat_add_comm env)) ++
    (LSpec.group "Nat.add_comm manual" $ (← proof_nat_add_comm_manual env)) ++
    (LSpec.group "Or.comm" $ (← proof_or_comm env)) ++
    (LSpec.group "Arithmetic 1" $ (← proof_arith_1 env))

end Pantograph.Test

