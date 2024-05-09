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

def buildNamedGoal (name: String) (nameType: List (String × String)) (target: String)
    (userName?: Option String := .none): Protocol.Goal :=
  {
    name,
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
      isInaccessible? := .some false
    })).toArray
  }
def buildGoal (nameType: List (String × String)) (target: String) (userName?: Option String := .none):
    Protocol.Goal :=
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

  let state2parent ← serializeExpressionSexp state2.parentExpr?.get! (sanitize := false)
  -- This is due to delayed assignment
  addTest $ LSpec.test "(2 parent)" (state2parent ==
    "((:mv) (:fv _uniq.16) ((:c Eq.refl) ((:c Or) (:fv _uniq.10) (:fv _uniq.13)) (:fv _uniq.16)))")

  let state3_1 ← match ← state2.tryTactic (goalId := 0) (tactic := "apply Or.inr") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state3_1parent ← serializeExpressionSexp state3_1.parentExpr?.get! (sanitize := false)
  addTest $ LSpec.test "(3_1 parent)" (state3_1parent == "((:c Or.inr) (:fv _uniq.13) (:fv _uniq.10) (:mv _uniq.78))")
  addTest $ LSpec.check "· apply Or.inr" (state3_1.goals.length = 1)
  let state4_1 ← match ← state3_1.tryTactic (goalId := 0) (tactic := "assumption") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_1.goals.isEmpty
  let state4_1parent ← serializeExpressionSexp state4_1.parentExpr?.get! (sanitize := false)
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

example : ∀ (a b c d: Nat), a + b = b + c → b + c = c + d → a + b = c + d := by
  intro a b c d h1 h2
  calc a + b = b + c := by apply h1
    _ = c + d := by apply h2

def test_calc: TestM Unit := do
  let state? ← startProof (.expr "∀ (a b c d: Nat), a + b = b + c → b + c = c + d → a + b = c + d")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  let tactic := "intro a b c d h1 h2"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[interiorGoal [] "a + b = c + d"])
  let pred := "a + b = b + c"
  let state2 ← match ← state1.tryCalc (goalId := 0) (pred := pred) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"calc {pred} := _" ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[
      interiorGoal [] "a + b = b + c" (.some "calc"),
      interiorGoal [] "b + c = c + d"
    ])
  addTest $ LSpec.test "(2.0 prev rhs)" (state2.calcPrevRhsOf? 0 |>.isNone)
  addTest $ LSpec.test "(2.1 prev rhs)" (state2.calcPrevRhsOf? 1 |>.isSome)

  let tactic := "apply h1"
  let state2m ← match ← state2.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state3 ← match state2m.continue state2 with
    | .ok state => pure state
    | .error e => do
      addTest $ expectationFailure "continue" e
      return ()
  let pred := "_ = c + d"
  let state4 ← match ← state3.tryCalc (goalId := 0) (pred := pred) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"calc {pred} := _" ((← state4.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[
      interiorGoal [] "b + c = c + d" (.some "calc")
    ])
  addTest $ LSpec.test "(4.0 prev rhs)" (state4.calcPrevRhsOf? 0 |>.isNone)
  let tactic := "apply h2"
  let state4m ← match ← state4.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "(4m root)" state4m.rootExpr?.isSome
  where
    interiorGoal (free: List (String × String)) (target: String) (userName?: Option String := .none) :=
      let free := [("a", "Nat"), ("b", "Nat"), ("c", "Nat"), ("d", "Nat"),
        ("h1", "a + b = b + c"), ("h2", "b + c = c + d")] ++ free
      buildGoal free target userName?

def test_let (specialized: Bool): TestM Unit := do
  let state? ← startProof (.expr "∀ (a: Nat) (p: Prop), p → p ∨ ¬p")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  let tactic := "intro a p h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[interiorGoal [] "p ∨ ¬p"])


  let letType := "Nat"
  let expr := s!"let b: {letType} := _; _"
  let result2 ← match specialized with
    | true => state1.tryLet (goalId := 0) (binderName := "b") (type := letType)
    | false => state1.tryAssign (goalId := 0) (expr := expr)
  let state2 ← match result2 with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let serializedState2 ← state2.serializeGoals (options := ← read)
  addTest $ LSpec.check expr (serializedState2.map (·.devolatilize) =
    #[
      interiorGoal [] letType,
      interiorGoal [] "let b := ?m.20;\np ∨ ¬p"
    ])
  -- Check that the goal mvar ids match up
  addTest $ LSpec.check "(mvarId)" ((serializedState2.map (·.name) |>.get! 0) = "_uniq.20")

  let tactic := "exact a"
  let state3 ← match ← state2.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3.serializeGoals (options := ← read)).map (·.devolatilize) = #[])

  let state3r ← match state3.continue state2 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "(continue)" ((← state3r.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[interiorGoal [] "let b := a;\np ∨ ¬p"])

  let tactic := "exact h"
  match ← state3r.tryTactic (goalId := 0) (tactic := tactic) with
  | .failure #[message] =>
    addTest $ LSpec.check tactic  (message = "type mismatch\n  h\nhas type\n  p : Prop\nbut is expected to have type\n  let b := a;\n  p ∨ ¬p : Prop")
  | other => do
    addTest $ assertUnreachable $ other.toString

  let tactic := "intro b"
  let state4 ← match ← state3r.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let tactic := "exact Or.inl h"
  let state5 ← match ← state4.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "(5 root)" state5.rootExpr?.isSome
  where
    interiorGoal (free: List (String × String)) (target: String) (userName?: Option String := .none) :=
      let free := [("a", "Nat"), ("p", "Prop"), ("h", "p")] ++ free
      buildGoal free target userName?

def test_nat_zero_add: TestM Unit := do
  let state? ← startProof (.expr "∀ (n: Nat), n + 0 = n")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  let tactic := "intro n"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("n", "Nat")] "n + 0 = n"])
  let recursor := "@Nat.brecOn"
  let state2 ← match ← state1.tryMotivatedApply (goalId := 0) (recursor := recursor) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"mapply {recursor}" ((← state2.serializeGoals (options := ← read)).map (·.devolatilizeVars) =
    #[
      buildNamedGoal "_uniq.67" [("n", "Nat")] "Nat → Prop" (.some "motive"),
      buildNamedGoal "_uniq.68" [("n", "Nat")] "Nat",
      buildNamedGoal "_uniq.69" [("n", "Nat")] "∀ (t : Nat), Nat.below t → ?motive t",
      buildNamedGoal "_uniq.70" [("n", "Nat")] "?motive ?m.68 = (n + 0 = n)" (.some "conduit")
    ])

  let tactic := "exact n"
  let state3b ← match ← state2.tryTactic (goalId := 1) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3b.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])
  let state2b ← match state3b.continue state2 with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let tactic := "exact (λ x => x + 0 = x)"
  let state3c ← match ← state2b.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3c.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])
  let state2c ← match state3c.continue state2b with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let tactic := "intro t h"
  let state3 ← match ← state2c.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("n", "Nat"), ("t", "Nat"), ("h", "Nat.below t")] "t + 0 = t"])

  let tactic := "simp"
  let state3d ← match ← state3.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state2d ← match state3d.continue state2c with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let tactic := "rfl"
  let stateF ← match ← state2d.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← stateF.serializeGoals (options := ← read)) =
    #[])

  let expr := stateF.mctx.eAssignment.find! stateF.root
  let (expr, _) := instantiateMVarsCore (mctx := stateF.mctx) (e := expr)
  addTest $ LSpec.check "(F root)" stateF.rootExpr?.isSome

def test_nat_zero_add_alt: TestM Unit := do
  let state? ← startProof (.expr "∀ (n: Nat), n + 0 = n")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()
  let tactic := "intro n"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("n", "Nat")] "n + 0 = n"])
  let recursor := "@Nat.brecOn"
  let state2 ← match ← state1.tryMotivatedApply (goalId := 0) (recursor := recursor) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"mapply {recursor}" ((← state2.serializeGoals (options := ← read)).map (·.devolatilizeVars) =
    #[
      buildNamedGoal "_uniq.67" [("n", "Nat")] "Nat → Prop" (.some "motive"),
      buildNamedGoal "_uniq.68" [("n", "Nat")] "Nat",
      buildNamedGoal "_uniq.69" [("n", "Nat")] "∀ (t : Nat), Nat.below t → ?motive t",
      buildNamedGoal "_uniq.70" [("n", "Nat")] "?motive ?m.68 = (n + 0 = n)" (.some "conduit")
    ])

  let tactic := "intro x"
  let state3m ← match ← state2.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3m.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("n", "Nat"), ("x", "Nat")] "Prop" (.some "motive")])
  let tactic := "apply Eq"
  let state3m2 ← match ← state3m.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state2b ← match state3m2.resume (state3m2.goals ++ state2.goals) with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  addTest $ LSpec.check "resume" ((← state2b.serializeGoals (options := ← read)).map (·.devolatilizeVars) =
    #[buildGoal [("n", "Nat"), ("t", "Nat"), ("h", "Nat.below t")] "t + 0 = t"])

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
    ("let via assign", test_let false),
    ("let via tryLet", test_let true),
    ("Nat.zero_add", test_nat_zero_add),
    ("Nat.zero_add alt", test_nat_zero_add_alt),
  ]
  tests.map (fun (name, test) => (name, proofRunner env test))



end Pantograph.Test.Proofs
