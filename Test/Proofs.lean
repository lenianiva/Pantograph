import LSpec
import Pantograph.Goal
import Pantograph.Serial

namespace Pantograph.Test.Proofs
open Pantograph
open Lean

inductive Start where
  | copy (name: String) -- Start from some name in the environment
  | expr (expr: String) -- Start from some expression

abbrev TestM := StateRefT LSpec.TestSeq (ReaderT Commands.Options M)

deriving instance DecidableEq, Repr for Commands.Expression
deriving instance DecidableEq, Repr for Commands.Variable
deriving instance DecidableEq, Repr for Commands.Goal

def add_test (test: LSpec.TestSeq): TestM Unit := do
  set $ (← get) ++ test

def start_proof (start: Start): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  match start with
  | .copy name =>
    let cInfo? := str_to_name name |> env.find?
    add_test $ LSpec.check s!"Symbol exists {name}" cInfo?.isSome
    match cInfo? with
    | .some cInfo =>
      let goal ← GoalState.create (expr := cInfo.type)
      return Option.some goal
    | .none =>
      return Option.none
  | .expr expr =>
    let syn? := syntax_from_str env expr
    add_test $ LSpec.check s!"Parsing {expr}" (syn?.isOk)
    match syn? with
    | .error error =>
      IO.println error
      return Option.none
    | .ok syn =>
      let expr? ← syntax_to_expr_type syn
      add_test $ LSpec.check s!"Elaborating" expr?.isOk
      match expr? with
      | .error error =>
        IO.println error
        return Option.none
      | .ok expr =>
        let goal ← GoalState.create (expr := expr)
        return Option.some goal

def assert_unreachable (message: String): LSpec.TestSeq := LSpec.check message false

def build_goal (nameType: List (String × String)) (target: String): Commands.Goal :=
  {
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      name := x.fst,
      type? := .some { pp? := .some x.snd },
      isInaccessible? := .some false
    })).toArray
  }
-- Like `build_goal` but allow certain variables to be elided.
def build_goal_selective (nameType: List (String × Option String)) (target: String): Commands.Goal :=
  {
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      name := x.fst,
      type? := x.snd.map (λ type => { pp? := type }),
      isInaccessible? := x.snd.map (λ _ => false)
    })).toArray
  }


-- Individual test cases
example: ∀ (a b: Nat), a + b = b + a := by
  intro n m
  rw [Nat.add_comm]
def proof_nat_add_comm: TestM Unit := do
  let goal? ← start_proof (.copy "Nat.add_comm")
  add_test $ LSpec.check "Start goal" goal?.isSome
  if let .some goal := goal? then
    if let .success #[(goal, sGoal)] ← goal.execute "intro n m" then
      let sGoal1e: Commands.Goal := build_goal [("n", "Nat"), ("m", "Nat")] "n + m = m + n"
      add_test $ LSpec.check "intro n m" (sGoal = sGoal1e)

      if let .failure #[message] ← goal.execute "assumption" then
        add_test $ LSpec.check "assumption" (message = "tactic 'assumption' failed\nn m : Nat\n⊢ n + m = m + n")
      else
        add_test $ assert_unreachable "assumption"

      if let .success #[] ← goal.execute "rw [Nat.add_comm]" then
        return ()
      else
        add_test $ assert_unreachable "rw [Nat.add_comm]"
    else
      add_test $ assert_unreachable "intro n m"
def proof_nat_add_comm_manual: TestM Unit := do
  let goal? ← start_proof (.expr "∀ (a b: Nat), a + b = b + a")
  add_test $ LSpec.check "Start goal" goal?.isSome
  if let .some goal := goal? then
    if let .success #[(goal, sGoal)] ← goal.execute "intro n m" then
      let sGoal1e: Commands.Goal := build_goal [("n", "Nat"), ("m", "Nat")] "n + m = m + n"
      add_test $ LSpec.check "intro n m" (sGoal = sGoal1e)

      if let .failure #[message] ← goal.execute "assumption" then
        add_test $ LSpec.check "assumption" (message = "tactic 'assumption' failed\nn m : Nat\n⊢ n + m = m + n")
      else
        add_test $ assert_unreachable "assumption"

      if let .success #[] ← goal.execute "rw [Nat.add_comm]" then
        return ()
      else
        add_test $ assert_unreachable "rw [Nat.add_comm]"
    else
      add_test $ assert_unreachable "intro n m"


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
def proof_or_comm: TestM Unit := do
  let typeProp: Commands.Expression := { pp? := .some "Prop" }
  let branchGoal (caseName name: String): Commands.Goal := {
    caseName? := .some caseName,
    target := { pp? := .some "q ∨ p" },
    vars := #[
      { name := "p", type? := .some typeProp, isInaccessible? := .some false },
      { name := "q", type? := .some typeProp, isInaccessible? := .some false },
      { name := "h✝", type? := .some { pp? := .some name }, isInaccessible? := .some true }
    ]
  }
  let goal? ← start_proof (.expr "∀ (p q: Prop), p ∨ q → q ∨ p")
  add_test $ LSpec.check "Start goal" goal?.isSome
  if let .some goal := goal? then
    if let .success #[(goal, sGoal)] ← goal.execute "intro p q h" then
      let sGoal1e := build_goal [("p", "Prop"), ("q", "Prop"), ("h", "p ∨ q")] "q ∨ p"
      add_test $ LSpec.check "intro p q h" (sGoal = sGoal1e)

      if let .success #[(goal1, sGoal1), (goal2, sGoal2)] ← goal.execute "cases h" then
        add_test $ LSpec.check "cases h/1" (sGoal1 = branchGoal "inl" "p")
        if let .success #[(goal, _)] ← goal1.execute "apply Or.inr" then
          if let .success #[] ← goal.execute "assumption" then
            return ()
          else
            add_test $ assert_unreachable "assumption"
        else
          add_test $ assert_unreachable "apply Or.inr"


        add_test $ LSpec.check "cases h/2" (sGoal2 = branchGoal "inr" "q")
        if let .success #[(goal, _)] ← goal2.execute "apply Or.inl" then
          if let .success #[] ← goal.execute "assumption" then
            return ()
          else
            add_test $ assert_unreachable "assumption"
        else
          add_test $ assert_unreachable "apply Or.inl"

      else
        add_test $ assert_unreachable "cases h"
    else
      add_test $ assert_unreachable "intro p q h"

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *
  assumption
def proof_arith_1: TestM Unit := do
  let goal? ← start_proof (.expr "∀ (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x)), p (x * w * z + y * x)")
  add_test $ LSpec.check "Start goal" goal?.isSome
  if let .some goal := goal? then
    if let .success #[(goal, _)] ← goal.execute "intros" then
      if let .success #[(goal, _)] ← goal.execute "simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *" then
        if let .success #[] ← goal.execute "assumption" then
          return ()
        else
          add_test $ assert_unreachable "assumption"
      else
        add_test $ assert_unreachable "simp ..."
    else
      add_test $ assert_unreachable "intros"

def proof_delta_variable: TestM Unit := withReader (fun _ => {proofVariableDelta := true}) do
  let goal? ← start_proof (.expr "∀ (a b: Nat), a + b = b + a")
  add_test $ LSpec.check "Start goal" goal?.isSome
  if let .some goal := goal? then
    if let .success #[(goal, sGoal)] ← goal.execute "intro n" then
      let sGoal1e: Commands.Goal := build_goal_selective [("n", .some "Nat")] "∀ (b : Nat), n + b = b + n"
      add_test $ LSpec.check "intro n" (sGoal = sGoal1e)

      if let .success #[(_, sGoal)] ← goal.execute "intro m" then
        let sGoal2e: Commands.Goal := build_goal_selective [("n", .none), ("m", .some "Nat")] "n + m = m + n"
        add_test $ LSpec.check "intro m" (sGoal = sGoal2e)
      else
        add_test $ assert_unreachable "intro m"
    else
      add_test $ assert_unreachable "intro n"

def proof_runner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
  let termElabM := tests.run LSpec.TestSeq.done |>.run {} -- with default options

  let coreContext: Lean.Core.Context := {
    currNamespace := Name.append .anonymous "Aniva",
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
  | .ok (_, a) =>
    return a

/-- Tests the most basic form of proofs whose goals do not relate to each other -/
def suite: IO LSpec.TestSeq := do
  let env: Lean.Environment ← Lean.importModules
    (imports := #[{ module := Name.append .anonymous "Init", runtimeOnly := false}])
    (opts := {})
    (trustLevel := 1)
  let tests := [
    ("Nat.add_comm", proof_nat_add_comm),
    ("nat.add_comm manual", proof_nat_add_comm_manual),
    ("Or.comm", proof_or_comm),
    ("arithmetic 1", proof_arith_1),
    ("delta variable", proof_delta_variable)
  ]
  let tests ← tests.foldlM (fun acc tests => do
    let (name, tests) := tests
    let tests ← proof_runner env tests
    return acc ++ (LSpec.group name tests)) LSpec.TestSeq.done

  return LSpec.group "Proofs" tests

end Pantograph.Test.Proofs
