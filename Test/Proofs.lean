import LSpec
import Pantograph.Meta
import Pantograph.Serial

namespace Pantograph.Test
open Pantograph

inductive Start where
  | copy (name: String) -- Start from some name in the environment
  | expr (expr: String) -- Start from some expression

def start_proof (start: Start): IO (LSpec.TestSeq × Option Meta.ProofTree) := do
  let imports := ["Init"]
  let env: Lean.Environment ← Lean.importModules
    (imports := imports.map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  let state := Meta.createProofTree
    (name := str_to_name "TestExample") env
    (coreContext := {
      currNamespace := str_to_name "Aniva",
      openDecls := [],     -- No 'open' directives needed
      fileName := "<Pantograph>",
      fileMap := { source := "", positions := #[0], lines := #[1] }
    })
  let mut testSeq := LSpec.TestSeq.done
  match start with
  | .copy name =>
    let cInfo? := str_to_name name |> env.find?
    testSeq := testSeq ++ LSpec.check s!"Symbol exists {name}" cInfo?.isSome
    match cInfo? with
    | .some cinfo =>
      let (_, state) ← Meta.ProofM.start cinfo.type |>.run state
      return (testSeq, Option.some state)
    | .none =>
      return (testSeq, Option.none)
  | .expr expr =>
    let syn? := Serial.syntax_from_str env expr
    testSeq := testSeq ++ LSpec.check s!"Parsing {expr}" (syn?.isOk)
    match syn? with
    | .error error =>
      IO.println error
      return (testSeq, Option.none)
    | .ok syn =>
      let expr? := (← Meta.ProofM.syntax_to_expr syn |>.run' state)
      testSeq := testSeq ++ LSpec.check s!"Elaborating" expr?.isOk
      match expr? with
      | .error error =>
        IO.println error
        return (testSeq, Option.none)
      | .ok expr =>
        let (_, state) ← Meta.ProofM.start expr |>.run state
        return (testSeq, Option.some state)

deriving instance DecidableEq, Repr for Meta.TacticResult

def proof_step (stateId: Nat) (goalId: Nat) (tactic: String)
    (expected: Meta.TacticResult) : Meta.ProofM LSpec.TestSeq := do
  let result: Meta.TacticResult ← Meta.ProofM.execute stateId goalId tactic
  match expected, result with
  | .success (.some i) #[], .success (.some _) goals =>
    -- If the goals are omitted but the next state is specified, we imply that
    -- the tactic succeeded.
    let expected := .success (.some i) goals
    return LSpec.test s!"{stateId}.{goalId} {tactic}"   (result = expected)
  | _, _ =>
    return LSpec.test s!"{stateId}.{goalId} {tactic}"   (result = expected)

def proof_runner (start: Start) (steps: List (Meta.ProofM LSpec.TestSeq)): IO LSpec.TestSeq := do
  let (testSeq, state?) ← start_proof start
  match state? with
  | .none => return testSeq
  | .some state => steps.foldlM (fun tests m => do pure $ tests ++ (← m)) testSeq |>.run' state

example: ∀ (a b: Nat), a + b = b + a := by
  intro n m
  rw [Nat.add_comm]
def proof_nat_add_comm: IO LSpec.TestSeq :=
  let goal1 := "n m : Nat\n⊢ n + m = m + n"
  proof_runner (.copy "Nat.add_comm") [
    proof_step 0 0 "intro n m"
      (.success (.some 1) #[goal1]),
    proof_step 1 0 "assumption"
      (.failure #[s!"tactic 'assumption' failed\n{goal1}"]),
    proof_step 1 0 "rw [Nat.add_comm]"
      (.success .none #[])
  ]
def proof_nat_add_comm_manual: IO LSpec.TestSeq := do
  let goal1 := "n m : Nat\n⊢ n + m = m + n"
  proof_runner (.expr "∀ (a b: Nat), a + b = b + a") [
    proof_step 0 0 "intro n m"
      (.success (.some 1) #[goal1]),
    proof_step 1 0 "assumption"
      (.failure #[s!"tactic 'assumption' failed\n{goal1}"]),
    proof_step 1 0 "rw [Nat.add_comm]"
      (.success .none #[])
  ]

example: ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
def proof_or_comm: IO LSpec.TestSeq := do
  proof_runner (.expr "∀ (p q: Prop), p ∨ q → q ∨ p") [
    proof_step 0 0 "intro p q h"
      (.success (.some 1) #["p q : Prop\nh : p ∨ q\n⊢ q ∨ p"]),
    proof_step 1 0 "cases h"
      (.success (.some 2) #[]),
    proof_step 2 0 "apply Or.inr"
      (.success (.some 3) #[]),
    proof_step 3 0 "assumption"
      (.success .none #[]),
    proof_step 2 1 "apply Or.inl"
      (.success (.some 4) #[]),
    proof_step 4 0 "assumption"
      (.success .none #[])
  ]

def test_proofs : IO LSpec.TestSeq := do
  return LSpec.group "proofs" $
    (LSpec.group "Nat.add_comm" $ (← proof_nat_add_comm)) ++
    (LSpec.group "Nat.add_comm manual" $ (← proof_nat_add_comm_manual)) ++
    (LSpec.group "Or.comm" $ (← proof_or_comm))

end Pantograph.Test

