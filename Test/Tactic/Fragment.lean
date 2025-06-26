import Pantograph.Goal
import Test.Common

open Lean

namespace Pantograph.Test.Tactic.Fragment

private def buildGoal (nameType: List (String × String)) (target: String) (userName?: Option String := .none):
    Protocol.Goal :=
  {
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
    })).toArray
  }

abbrev TestM := TestT $ Elab.TermElabM

example : ∀ (a b c1 c2: Nat), (b + a) + c1 = (b + a) + c2 → (a + b) + c1 = (b + a) + c2 := by
  intro a b c1 c2 h
  conv =>
    lhs
    congr
    . rw [Nat.add_comm]
    . rfl
  exact h

def test_conv: TestM Unit := do
  let rootTarget ← parseSentence "∀ (a b c1 c2: Nat), (b + a) + c1 = (b + a) + c2 → (a + b) + c1 = (b + a) + c2"
  let state0 ← GoalState.create rootTarget

  let tactic := "intro a b c1 c2 h"
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals).map (·.devolatilize) =
    #[interiorGoal [] "a + b + c1 = b + a + c2"])

  let goalConv := state1.goals[0]!
  let state2 ← match ← state1.convEnter (state1.get! 0) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "conv => ..." ((← state2.serializeGoals).map (·.devolatilize) =
    #[{ interiorGoal [] "a + b + c1 = b + a + c2" with isConversion := true }])

  let convTactic := "rhs"
  let state3R ← match ← state2.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic} (discard)" ((← state3R.serializeGoals).map (·.devolatilize) =
    #[{ interiorGoal [] "b + a + c2" with isConversion := true }])

  let convTactic := "lhs"
  let state3L ← match ← state2.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic}" ((← state3L.serializeGoals).map (·.devolatilize) =
    #[{ interiorGoal [] "a + b + c1" with isConversion := true }])

  let convTactic := "congr"
  let state4 ← match ← state3L.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic}" ((← state4.serializeGoals).map (·.devolatilize) =
    #[
      { interiorGoal [] "a + b" with isConversion := true, userName? := .some "a" },
      { interiorGoal [] "c1" with isConversion := true, userName? := .some "a" }
    ])

  let convTactic := "rw [Nat.add_comm]"
  let state5_1 ← match ← state4.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  · {convTactic}" ((← state5_1.serializeGoals).map (·.devolatilize) =
    #[{ interiorGoal [] "b + a" with isConversion := true, userName? := .some "a" }])

  let convTactic := "rfl"
  let state6_1 ← match ← state5_1.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"    {convTactic}" ((← state6_1.serializeGoals).map (·.devolatilize) =
    #[])

  let state4_1 ← match state6_1.continue state4 with
    | .ok state => pure state
    | .error e => do
      addTest $ expectationFailure "continue" e
      return ()

  let convTactic := "rfl"
  let state6 ← match ← state4_1.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  · {convTactic}" ((← state6.serializeGoals).map (·.devolatilize) =
    #[])

  let state1_1 ← match ← state6.fragmentExit goalConv with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  let tactic := "exact h"
  let stateF ← match ← state1_1.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← stateF.serializeGoals).map (·.devolatilize) =
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
  let rootTarget ← parseSentence "∀ (a b c d: Nat), a + b = b + c → b + c = c + d → a + b = c + d"
  let state0 ← GoalState.create rootTarget
  let tactic := "intro a b c d h1 h2"
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals).map (·.devolatilize) =
    #[interiorGoal [] "a + b = c + d"])
  let pred := "a + b = b + c"
  let .success state1 _ ← state1.calcEnter state1.mainGoal?.get! | fail "Could not enter calc"
  let state2 ← match ← state1.tacticOn 0 pred with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"calc {pred} := _" ((← state2.serializeGoals).map (·.devolatilize) =
    #[
      interiorGoal [] "a + b = b + c" (.some "calc"),
      interiorGoal [] "b + c = c + d"
    ])
  addTest $ LSpec.test "(2.0 prev rhs)" (state2.calcPrevRhsOf? (state2.get! 0) |>.isNone)
  addTest $ LSpec.test "(2.1 prev rhs)" (state2.calcPrevRhsOf? (state2.get! 1) |>.isSome)

  let tactic := "apply h1"
  let state2m ← match ← state2.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state3 ← match state2m.continue state2 with
    | .ok state => pure state
    | .error e => do
      addTest $ expectationFailure "continue" e
      return ()
  let pred := "_ = c + d"
  let state4 ← match ← state3.tacticOn 0 pred with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"calc {pred} := _" ((← state4.serializeGoals).map (·.devolatilize) =
    #[
      interiorGoal [] "b + c = c + d" (.some "calc")
    ])
  addTest $ LSpec.test "(4.0 prev rhs)" (state4.calcPrevRhsOf? (state4.get! 0) |>.isNone)
  let tactic := "apply h2"
  let state4m ← match ← state4.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "(4m root)" state4m.rootExpr?.isSome
  where
    interiorGoal (free: List (String × String)) (target: String) (userName?: Option String := .none) :=
      let free := [("a", "Nat"), ("b", "Nat"), ("c", "Nat"), ("d", "Nat"),
        ("h1", "a + b = b + c"), ("h2", "b + c = c + d")] ++ free
      buildGoal free target userName?

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("conv", test_conv),
    ("calc", test_calc),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))

end Pantograph.Test.Tactic.Fragment
