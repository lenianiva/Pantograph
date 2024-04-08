/-
Tests pertaining to goals with no interdependencies
-/
import LSpec
import Pantograph.Goal
import Pantograph.Serial
import Test.Common

namespace Pantograph.Test.Proofs
open Pantograph
open Lean

inductive Start where
  | copy (name: String) -- Start from some name in the environment
  | expr (expr: String) -- Start from some expression

abbrev TestM := StateRefT LSpec.TestSeq (ReaderT Protocol.Options Elab.TermElabM)

def addTest (test: LSpec.TestSeq): TestM Unit := do
  set $ (← get) ++ test

def startProof (start: Start): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  match start with
  | .copy name =>
    let cInfo? := name.toName |> env.find?
    addTest $ LSpec.check s!"Symbol exists {name}" cInfo?.isSome
    match cInfo? with
    | .some cInfo =>
      let goal ← GoalState.create (expr := cInfo.type)
      return Option.some goal
    | .none =>
      return Option.none
  | .expr expr =>
    let syn? := parseTerm env expr
    addTest $ LSpec.check s!"Parsing {expr}" (syn?.isOk)
    match syn? with
    | .error error =>
      IO.println error
      return Option.none
    | .ok syn =>
      let expr? ← elabType syn
      addTest $ LSpec.check s!"Elaborating" expr?.isOk
      match expr? with
      | .error error =>
        IO.println error
        return Option.none
      | .ok expr =>
        let goal ← GoalState.create (expr := expr)
        return Option.some goal

def buildGoal (nameType: List (String × String)) (target: String) (userName?: Option String := .none): Protocol.Goal :=
  {
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
      isInaccessible? := .some false
    })).toArray
  }
def proofRunner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
  let termElabM := tests.run LSpec.TestSeq.done |>.run {} -- with default options

  let coreContext: Lean.Core.Context ← createCoreContext #[]
  let metaM := termElabM.run' (ctx := defaultTermElabMContext)
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
def test_nat_add_comm (manual: Bool): TestM Unit := do
  let state? ← startProof <| match manual with
    | false => .copy "Nat.add_comm"
    | true => .expr "∀ (a b: Nat), a + b = b + a"
  addTest $ LSpec.check "Start goal" state?.isSome
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := "intro n m") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "intro n m" ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("n", "Nat"), ("m", "Nat")] "n + m = m + n"])

  match ← state1.tryTactic (goalId := 0) (tactic := "assumption") with
  | .failure #[message] =>
    addTest $ LSpec.check "assumption" (message = "tactic 'assumption' failed\nn m : Nat\n⊢ n + m = m + n")
  | other => do
    addTest $ assertUnreachable $ other.toString

  let state2 ← match ← state1.tryTactic (goalId := 0) (tactic := "rw [Nat.add_comm]") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "rw [Nat.add_comm]" state2.goals.isEmpty

  return ()
def test_delta_variable: TestM Unit := do
  let options: Protocol.Options := { noRepeat := true }
  let state? ← startProof <| .expr "∀ (a b: Nat), a + b = b + a"
  addTest $ LSpec.check "Start goal" state?.isSome
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := "intro n") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "intro n" ((← state1.serializeGoals (parent := state0) options).map (·.devolatilize) =
    #[buildGoalSelective [("n", .some "Nat")] "∀ (b : Nat), n + b = b + n"])
  let state2 ← match ← state1.tryTactic (goalId := 0) (tactic := "intro m") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "intro m" ((← state2.serializeGoals (parent := state1) options).map (·.devolatilize) =
    #[buildGoalSelective [("n", .none), ("m", .some "Nat")] "n + m = m + n"])
  return ()
  where
-- Like `buildGoal` but allow certain variables to be elided.
  buildGoalSelective (nameType: List (String × Option String)) (target: String): Protocol.Goal :=
    {
      target := { pp? := .some target},
      vars := (nameType.map fun x => ({
        userName := x.fst,
        type? := x.snd.map (λ type => { pp? := type }),
        isInaccessible? := x.snd.map (λ _ => false)
      })).toArray
    }

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *
  assumption
def test_arith: TestM Unit := do
  let state? ← startProof (.expr "∀ (w x y z : Nat) (p : Nat → Prop) (h : p (x * y + z * w * x)), p (x * w * z + y * x)")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let tactic := "intros"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic (state1.goals.length = 1)
  addTest $ LSpec.test "(1 root)" state1.rootExpr?.isNone
  let state2 ← match ← state1.tryTactic (goalId := 0) (tactic := "simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "simp ..." (state2.goals.length = 1)
  addTest $ LSpec.check "(2 root)" state2.rootExpr?.isNone
  let tactic := "assumption"
  let state3 ← match ← state2.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test tactic state3.goals.isEmpty
  addTest $ LSpec.check "(3 root)" state3.rootExpr?.isSome
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
def test_or_comm: TestM Unit := do
  let state? ← startProof (.expr "∀ (p q: Prop), p ∨ q → q ∨ p")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  addTest $ LSpec.check "(0 parent)" state0.parentExpr?.isNone
  addTest $ LSpec.check "(0 root)" state0.rootExpr?.isNone

  let tactic := "intro p q h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p ∨ q")] "q ∨ p"])
  addTest $ LSpec.check "(1 parent)" state1.parentExpr?.isSome
  addTest $ LSpec.check "(1 root)" state1.rootExpr?.isNone

  let tactic := "cases h"
  let state2 ← match ← state1.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[branchGoal "inl" "p", branchGoal "inr" "q"])
  addTest $ LSpec.check "(2 parent)" state2.parentExpr?.isSome
  addTest $ LSpec.check "(2 root)" state2.rootExpr?.isNone

  let state2parent ← serialize_expression_ast state2.parentExpr?.get! (sanitize := false)
  -- This is due to delayed assignment
  addTest $ LSpec.test "(2 parent)" (state2parent ==
    "((:mv _uniq.43) (:fv _uniq.16) ((:c Eq.refl) ((:c Or) (:fv _uniq.10) (:fv _uniq.13)) (:fv _uniq.16)))")

  let state3_1 ← match ← state2.tryTactic (goalId := 0) (tactic := "apply Or.inr") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state3_1parent ← serialize_expression_ast state3_1.parentExpr?.get! (sanitize := false)
  addTest $ LSpec.test "(3_1 parent)" (state3_1parent == "((:c Or.inr) (:fv _uniq.13) (:fv _uniq.10) (:mv _uniq.78))")
  addTest $ LSpec.check "· apply Or.inr" (state3_1.goals.length = 1)
  let state4_1 ← match ← state3_1.tryTactic (goalId := 0) (tactic := "assumption") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_1.goals.isEmpty
  let state4_1parent ← serialize_expression_ast state4_1.parentExpr?.get! (sanitize := false)
  addTest $ LSpec.test "(4_1 parent)" (state4_1parent == "(:fv _uniq.47)")
  addTest $ LSpec.check "(4_1 root)" state4_1.rootExpr?.isNone
  let state3_2 ← match ← state2.tryTactic (goalId := 1) (tactic := "apply Or.inl") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "· apply Or.inl" (state3_2.goals.length = 1)
  let state4_2 ← match ← state3_2.tryTactic (goalId := 0) (tactic := "assumption") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_2.goals.isEmpty
  addTest $ LSpec.check "(4_2 root)" state4_2.rootExpr?.isNone
  -- Ensure the proof can continue from `state4_2`.
  let state2b ← match state4_2.continue state2 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.test "(resume)" (state2b.goals == [state2.goals.get! 0])
  let state3_1 ← match ← state2b.tryTactic (goalId := 0) (tactic := "apply Or.inr") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "· apply Or.inr" (state3_1.goals.length = 1)
  let state4_1 ← match ← state3_1.tryTactic (goalId := 0) (tactic := "assumption") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_1.goals.isEmpty
  addTest $ LSpec.check "(4_1 root)" state4_1.rootExpr?.isSome

  return ()
  where
    typeProp: Protocol.Expression := { pp? := .some "Prop" }
    branchGoal (caseName varName: String): Protocol.Goal := {
      userName? := .some caseName,
      target := { pp? := .some "q ∨ p" },
      vars := #[
        { userName := "p", type? := .some typeProp, isInaccessible? := .some false },
        { userName := "q", type? := .some typeProp, isInaccessible? := .some false },
        { userName := "h✝", type? := .some { pp? := .some varName }, isInaccessible? := .some true }
      ]
    }

def test_have: TestM Unit := do
  let state? ← startProof (.expr "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  let tactic := "intro p q h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p")] "(p ∨ q) ∨ p ∨ q"])

  let expr := "Or.inl (Or.inl h)"
  let state2 ← match ← state1.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  let haveBind := "y"
  let haveType := "p ∨ q"
  let state2 ← match ← state1.tryHave (goalId := 0) (binderName := haveBind) (type := haveType) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"have {haveBind}: {haveType}" ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[
      buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p")] "p ∨ q",
      buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p"), ("y", "p ∨ q")] "(p ∨ q) ∨ p ∨ q"
    ])

  let expr := "Or.inl h"
  let state3 ← match ← state2.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state3.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  let state2b ← match state3.continue state2 with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let expr := "Or.inl y"
  let state4 ← match ← state2b.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state4.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  addTest $ LSpec.check "(4 root)" state4.rootExpr?.isSome

example : ∀ (a b c1 c2: Nat), (b + a) + c1 = (b + a) + c2 → (a + b) + c1 = (b + a) + c2 := by
  intro a b c1 c2 h
  conv =>
    lhs
    congr
    . rw [Nat.add_comm]
    . rfl
  exact h

def test_conv: TestM Unit := do
  let state? ← startProof (.expr "∀ (a b c1 c2: Nat), (b + a) + c1 = (b + a) + c2 → (a + b) + c1 = (b + a) + c2")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let tactic := "intro a b c1 c2 h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[interiorGoal [] "a + b + c1 = b + a + c2"])

  let state2 ← match ← state1.conv (goalId := 0) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "conv => ..." ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "a + b + c1 = b + a + c2" with isConversion := true }])

  let convTactic := "rhs"
  let state3R ← match ← state2.tryTactic (goalId := 0) convTactic with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic} (discard)" ((← state3R.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "b + a + c2" with isConversion := true }])

  let convTactic := "lhs"
  let state3L ← match ← state2.tryTactic (goalId := 0) convTactic with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic}" ((← state3L.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "a + b + c1" with isConversion := true }])

  let convTactic := "congr"
  let state4 ← match ← state3L.tryTactic (goalId := 0) convTactic with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic}" ((← state4.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[
      { interiorGoal [] "a + b" with isConversion := true, userName? := .some "a" },
      { interiorGoal [] "c1" with isConversion := true, userName? := .some "a" }
    ])

  let convTactic := "rw [Nat.add_comm]"
  let state5_1 ← match ← state4.tryTactic (goalId := 0) convTactic with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  · {convTactic}" ((← state5_1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "b + a" with isConversion := true, userName? := .some "a" }])

  let convTactic := "rfl"
  let state6_1 ← match ← state5_1.tryTactic (goalId := 0) convTactic with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"    {convTactic}" ((← state6_1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  let state4_1 ← match state6_1.continue state4 with
    | .ok state => pure state
    | .error e => do
      addTest $ expectationFailure "continue" e
      return ()

  let convTactic := "rfl"
  let state6 ← match ← state4_1.tryTactic (goalId := 0) convTactic with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  · {convTactic}" ((← state6.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  let state1_1 ← match ← state6.convExit with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  let tactic := "exact h"
  let stateF ← match ← state1_1.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← stateF.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  where
    h := "b + a + c1 = b + a + c2"
    interiorGoal (free: List (String × String)) (target: String) :=
      let free := [("a", "Nat"), ("b", "Nat"), ("c1", "Nat"), ("c2", "Nat"), ("h", h)] ++ free
      buildGoal free target

example : ∀ (a: Nat), 1 + a + 1 = a + 2 := by
  intro a
  calc 1 + a + 1 = a + 1 + 1  := by conv =>
       rhs
       rw [Nat.add_comm]
    _ = a + 2 := by rw [Nat.add_assoc]

def test_calc: TestM Unit := do
  let state? ← startProof (.expr "∀ (a: Nat), 1 + a + 1 = a + 2")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  let tactic := "intro a"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("a", "Nat")] "1 + a + 1 = a + 2"])
  let tactic := "calc"
  let state2 ← match ← state1.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("a", "Nat")] "1 + a + 1 = a + 2"])

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("Nat.add_comm", test_nat_add_comm false),
    ("Nat.add_comm manual", test_nat_add_comm true),
    ("Nat.add_comm delta", test_delta_variable),
    ("arithmetic", test_arith),
    ("Or.comm", test_or_comm),
    ("have", test_have),
    ("conv", test_conv),
    ("calc", test_calc),
  ]
  tests.map (fun (name, test) => (name, proofRunner env test))



end Pantograph.Test.Proofs
