/-
Tests pertaining to goals with no interdependencies
-/
import LSpec
import Pantograph.Goal
import Pantograph.Serial
import Test.Common

namespace Pantograph

def TacticResult.toString : TacticResult → String
  | .success _ goals => s!".success ({goals.size} goals)"
  | .failure messages =>
    let messages := "\n".intercalate messages.toList
    s!".failure {messages}"
  | .parseError error => s!".parseError {error}"
  | .indexError index => s!".indexError {index}"
end Pantograph

namespace Pantograph.Test.Proofs
open Pantograph
open Lean

inductive Start where
  | copy (name: String) -- Start from some name in the environment
  | expr (expr: String) -- Start from some expression

abbrev TestM := StateRefT LSpec.TestSeq (ReaderT Protocol.Options M)

deriving instance DecidableEq, Repr for Protocol.Expression
deriving instance DecidableEq, Repr for Protocol.Variable
deriving instance DecidableEq, Repr for Protocol.Goal

def addTest (test: LSpec.TestSeq): TestM Unit := do
  set $ (← get) ++ test

def startProof (start: Start): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  match start with
  | .copy name =>
    let cInfo? := str_to_name name |> env.find?
    addTest $ LSpec.check s!"Symbol exists {name}" cInfo?.isSome
    match cInfo? with
    | .some cInfo =>
      let goal ← GoalState.create (expr := cInfo.type)
      return Option.some goal
    | .none =>
      return Option.none
  | .expr expr =>
    let syn? := syntax_from_str env expr
    addTest $ LSpec.check s!"Parsing {expr}" (syn?.isOk)
    match syn? with
    | .error error =>
      IO.println error
      return Option.none
    | .ok syn =>
      let expr? ← syntax_to_expr_type syn
      addTest $ LSpec.check s!"Elaborating" expr?.isOk
      match expr? with
      | .error error =>
        IO.println error
        return Option.none
      | .ok expr =>
        let goal ← GoalState.create (expr := expr)
        return Option.some goal

def assertUnreachable (message: String): LSpec.TestSeq := LSpec.check message false

def buildGoal (nameType: List (String × String)) (target: String): Protocol.Goal :=
  {
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
      isInaccessible? := .some false
    })).toArray
  }
-- Like `buildGoal` but allow certain variables to be elided.
def buildGoalSelective (nameType: List (String × Option String)) (target: String): Protocol.Goal :=
  {
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := x.snd.map (λ type => { pp? := type }),
      isInaccessible? := x.snd.map (λ _ => false)
    })).toArray
  }
def proofRunner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
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

-- Individual test cases
example: ∀ (a b: Nat), a + b = b + a := by
  intro n m
  rw [Nat.add_comm]
def proof_nat_add_comm (manual: Bool): TestM Unit := do
  let state? ← startProof <| match manual with
    | false => .copy "Nat.add_comm"
    | true => .expr "∀ (a b: Nat), a + b = b + a"
  addTest $ LSpec.check "Start goal" state?.isSome
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let (state1, goal1) ← match ← state0.execute (goalId := 0) (tactic := "intro n m") with
    | .success state #[goal] => pure (state, goal)
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "intro n m" (goal1.devolatilize = buildGoal [("n", "Nat"), ("m", "Nat")] "n + m = m + n")

  match ← state1.execute (goalId := 0) (tactic := "assumption") with
  | .failure #[message] =>
    addTest $ LSpec.check "assumption" (message = "tactic 'assumption' failed\nn m : Nat\n⊢ n + m = m + n")
  | other => do
    addTest $ assertUnreachable $ other.toString

  let state2 ← match ← state1.execute (goalId := 0) (tactic := "rw [Nat.add_comm]") with
    | .success state #[] => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  return ()


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
  let state? ← startProof (.expr "∀ (p q: Prop), p ∨ q → q ∨ p")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let (state1, goal1) ← match ← state0.execute (goalId := 0) (tactic := "intro p q h") with
    | .success state #[goal] => pure (state, goal)
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "p q h" (goal1.devolatilize = buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p ∨ q")] "q ∨ p")
  let (state2, goal1, goal2) ← match ← state1.execute (goalId := 0) (tactic := "cases h") with
    | .success state #[goal1, goal2] => pure (state, goal1, goal2)
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "cases h/1" (goal1.devolatilize = branchGoal "inl" "p")
  addTest $ LSpec.check "cases h/2" (goal2.devolatilize = branchGoal "inr" "q")

  let (state3_1, _goal) ← match ← state2.execute (goalId := 0) (tactic := "apply Or.inr") with
    | .success state #[goal] => pure (state, goal)
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state4_1 ← match ← state3_1.execute (goalId := 0) (tactic := "assumption") with
    | .success state #[] => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let (state3_2, _goal) ← match ← state2.execute (goalId := 1) (tactic := "apply Or.inl") with
    | .success state #[goal] => pure (state, goal)
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state4_2 ← match ← state3_2.execute (goalId := 0) (tactic := "assumption") with
    | .success state #[] => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  addTest $ LSpec.check "4_2 root" state4_2.rootExpr.isNone
  -- Ensure the proof can continue from `state4_2`.
  let state2b ← match state2.continue state4_2 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.test "state2b" (state2b.goals == [state2.goals.get! 0])
  let (state3_1, _goal) ← match ← state2b.execute (goalId := 0) (tactic := "apply Or.inr") with
    | .success state #[goal] => pure (state, goal)
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state4_1 ← match ← state3_1.execute (goalId := 0) (tactic := "assumption") with
    | .success state #[] => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  state4_1.print
  addTest $ LSpec.check "4_1 root" state4_1.rootExpr.isSome

  return ()
  where
    typeProp: Protocol.Expression := { pp? := .some "Prop" }
    branchGoal (caseName name: String): Protocol.Goal := {
      caseName? := .some caseName,
      target := { pp? := .some "q ∨ p" },
      vars := #[
        { userName := "p", type? := .some typeProp, isInaccessible? := .some false },
        { userName := "q", type? := .some typeProp, isInaccessible? := .some false },
        { userName := "h✝", type? := .some { pp? := .some name }, isInaccessible? := .some true }
      ]
    }

--example (w x y z : Nat) (p : Nat → Prop)
--        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
--  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *
--  assumption
--def proof_arith_1: TestM Unit := do
--  let goal? ← startProof (.expr "∀ (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x)), p (x * w * z + y * x)")
--  addTest $ LSpec.check "Start goal" goal?.isSome
--  if let .some goal := goal? then
--    if let .success #[(goal, _)] ← goal.execute "intros" then
--      if let .success #[(goal, _)] ← goal.execute "simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *" then
--        if let .success #[] ← goal.execute "assumption" then
--          return ()
--        else
--          addTest $ assertUnreachable "assumption"
--      else
--        addTest $ assertUnreachable "simp ..."
--    else
--      addTest $ assertUnreachable "intros"
--
--def proof_delta_variable: TestM Unit := withReader (fun _ => {proofVariableDelta := true}) do
--  let goal? ← startProof (.expr "∀ (a b: Nat), a + b = b + a")
--  addTest $ LSpec.check "Start goal" goal?.isSome
--  if let .some goal := goal? then
--    if let .success #[(goal, sGoal)] ← goal.execute "intro n" then
--      let sGoal1e: Protocol.Goal :=buildGoalSelective [("n", .some "Nat")] "∀ (b : Nat), n + b = b + n"
--      addTest $ LSpec.check "intro n" (sGoal = sGoal1e)
--
--      if let .success #[(_, sGoal)] ← goal.execute "intro m" then
--        let sGoal2e: Protocol.Goal :=buildGoalSelective [("n", .none), ("m", .some "Nat")] "n + m = m + n"
--        addTest $ LSpec.check "intro m" (sGoal = sGoal2e)
--      else
--        addTest $ assertUnreachable "intro m"
--    else
--      addTest $ assertUnreachable "intro n"

/-- Tests the most basic form of proofs whose goals do not relate to each other -/
def suite: IO LSpec.TestSeq := do
  let env: Lean.Environment ← Lean.importModules
    (imports := #[{ module := Name.append .anonymous "Init", runtimeOnly := false}])
    (opts := {})
    (trustLevel := 1)
  let tests := [
    ("Nat.add_comm", proof_nat_add_comm false),
    ("Nat.add_comm manual", proof_nat_add_comm true),
    ("Or.comm", proof_or_comm)
    --("arithmetic 1", proof_arith_1),
    --("delta variable", proof_delta_variable)
  ]
  let tests ← tests.foldlM (fun acc tests => do
    let (name, tests) := tests
    let tests ← proofRunner env tests
    return acc ++ (LSpec.group name tests)) LSpec.TestSeq.done

  return LSpec.group "Proofs" tests

end Pantograph.Test.Proofs
