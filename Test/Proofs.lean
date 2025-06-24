/-
Tests pertaining to goals with no interdependencies
-/
import LSpec
import Pantograph.Goal
import Pantograph.Delate
import Test.Common

namespace Pantograph.Test.Proofs
open Pantograph
open Lean

inductive Start where
  | copy (name: Name) -- Start from some name in the environment
  | expr (expr: String) -- Start from some expression

abbrev TestM := TestT $ ReaderT Protocol.Options $ Elab.TermElabM

def startProof (start: Start): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  match start with
  | .copy name =>
    let cInfo? := name |> env.find?
    addTest $ LSpec.check s!"Symbol exists {name}" cInfo?.isSome
    match cInfo? with
    | .some cInfo =>
      let goal ← GoalState.create (expr := cInfo.type)
      return Option.some goal
    | .none =>
      return Option.none
  | .expr expr =>
    let expr ← parseSentence expr
    return .some $ ← GoalState.create (expr := expr)

def buildNamedGoal (name: String) (nameType: List (String × String)) (target: String)
    (userName?: Option String := .none): Protocol.Goal :=
  {
    name,
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
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
    })).toArray
  }
def proofRunner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
  let termElabM := tests.run LSpec.TestSeq.done |>.run {} -- with default options

  let coreContext: Lean.Core.Context ← createCoreContext #[]
  let metaM := termElabM.run' (ctx := defaultElabContext)
  let coreM := metaM.run'
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok (_, a) =>
    return a

def test_identity: TestM Unit := do
  let rootTarget ← Elab.Term.elabTerm (← `(term|∀ (p: Prop), p → p)) .none
  let state0 ← GoalState.create (expr := rootTarget)
  let state1 ← match ← state0.tacticOn' 0 (← `(tactic|intro p h)) with
    | .success state _ => pure state
    | other => do
      fail other.toString
      return ()
  let inner := "_uniq.11"
  addTest $ LSpec.check "intro" ((← state1.serializeGoals (options := ← read)).map (·.name) =
    #[inner])
  let state1parent ← state1.withParentContext do
    serializeExpressionSexp (← instantiateAll state1.parentExpr?.get!)
  addTest $ LSpec.test "(1 parent)" (state1parent == s!"(:lambda p (:sort 0) (:lambda h 0 (:subst (:mv {inner}) 1 0)))")

-- Individual test cases
example: ∀ (a b: Nat), a + b = b + a := by
  intro n m
  rw [Nat.add_comm]
def test_nat_add_comm (manual: Bool): TestM Unit := do
  let state? ← startProof <| match manual with
    | false => .copy `Nat.add_comm
    | true => .expr "∀ (a b: Nat), a + b = b + a"
  addTest $ LSpec.check "Start goal" state?.isSome
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.tacticOn 0 "intro n m" with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "intro n m" ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[buildGoal [("n", "Nat"), ("m", "Nat")] "n + m = m + n"])

  match ← state1.tacticOn 0 "assumption" with
  | .failure #[message] =>
    addTest $ LSpec.check "assumption" (message = "tactic 'assumption' failed\nn m : Nat\n⊢ n + m = m + n")
  | other => do
    addTest $ assertUnreachable $ other.toString

  let state2 ← match ← state1.tacticOn 0 "rw [Nat.add_comm]" with
    | .success state _ => pure state
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

  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := "intro n") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "intro n" ((← state1.serializeGoals (parent := state0) options).map (·.devolatilize) =
    #[buildGoalSelective [("n", .some "Nat")] "∀ (b : Nat), n + b = b + n"])
  let state2 ← match ← state1.tacticOn (goalId := 0) (tactic := "intro m") with
    | .success state _ => pure state
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
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic (state1.goals.length = 1)
  checkTrue "(1 root)" state1.rootExpr?.get!.hasExprMVar
  let state2 ← match ← state1.tacticOn (goalId := 0) (tactic := "simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "simp ..." (state2.goals.length = 1)
  checkTrue "(2 root)" state2.rootExpr?.get!.hasExprMVar
  let tactic := "assumption"
  let state3 ← match ← state2.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test tactic state3.goals.isEmpty
  checkTrue "(3 root)" $ ¬ state3.rootExpr?.get!.hasExprMVar
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
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let [state1g0] := state1.goals | fail "Should have 1 goal"
  let (fvP, fvQ, fvH) ← state1.withContext state1g0 do
    let lctx ← getLCtx
    let #[fvP, fvQ, fvH] := lctx.getFVarIds.map (toString ·.name) |
      panic! "Incorrect number of decls"
    pure (fvP, fvQ, fvH)
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)) =
    #[{
      name := state1g0.name.toString,
      target := { pp? := .some "q ∨ p" },
      vars := #[
        { name := fvP, userName := "p", type? := .some { pp? := .some "Prop" } },
        { name := fvQ, userName := "q", type? := .some { pp? := .some "Prop" } },
        { name := fvH, userName := "h", type? := .some { pp? := .some "p ∨ q" } }
      ]
    }])
  checkTrue "(1 parent)" state1.parentExpr?.isSome
  checkTrue "(1 root)" $ ¬ state1.isSolved

  let state1parent ← state1.withParentContext do
    serializeExpressionSexp (← instantiateAll state1.parentExpr?.get!)
  addTest $ LSpec.test "(1 parent)" (state1parent == s!"(:lambda p (:sort 0) (:lambda q (:sort 0) (:lambda h ((:c Or) 1 0) (:subst (:mv {state1g0}) 2 1 0))))")
  let tactic := "cases h"
  let state2 ← match ← state1.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[branchGoal "inl" "p", branchGoal "inr" "q"])
  let [state2g0, state2g1] := state2.goals |
    fail s!"Should have 2 goals, but it has {state2.goals.length}"
  let (caseL, caseR) := (state2g0.name.toString, state2g1.name.toString)
  addTest $ LSpec.check tactic ((← state2.serializeGoals (options := ← read)).map (·.name) =
    #[caseL, caseR])
  checkTrue "(2 parent exists)" state2.parentExpr?.isSome
  checkTrue "(2 root)" $ ¬ state2.isSolved

  let state2parent ← state2.withParentContext do
    serializeExpressionSexp (← instantiateAll state2.parentExpr?.get!)
  let orPQ := s!"((:c Or) (:fv {fvP}) (:fv {fvQ}))"
  let orQP := s!"((:c Or) (:fv {fvQ}) (:fv {fvP}))"
  let motive := s!"(:lambda t {orPQ} (:forall h ((:c Eq) ((:c Or) (:fv {fvP}) (:fv {fvQ})) (:fv {fvH}) 0) {orQP}))"
  let caseL := s!"(:lambda h (:fv {fvP}) (:lambda h ((:c Eq) {orPQ} (:fv {fvH}) ((:c Or.inl) (:fv {fvP}) (:fv {fvQ}) 0)) (:subst (:mv {caseL}) (:fv {fvP}) (:fv {fvQ}) 1)))"
  let caseR := s!"(:lambda h (:fv {fvQ}) (:lambda h ((:c Eq) {orPQ} (:fv {fvH}) ((:c Or.inr) (:fv {fvP}) (:fv {fvQ}) 0)) (:subst (:mv {caseR}) (:fv {fvP}) (:fv {fvQ}) 1)))"
  let conduit := s!"((:c Eq.refl) {orPQ} (:fv {fvH}))"
  addTest $ LSpec.test "(2 parent)" (state2parent ==
    s!"((:c Or.casesOn) (:fv {fvP}) (:fv {fvQ}) {motive} (:fv {fvH}) {caseL} {caseR} {conduit})")

  let state3_1 ← match ← state2.tacticOn (goalId := 0) (tactic := "apply Or.inr") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state3_1parent ← state3_1.withParentContext do
    serializeExpressionSexp (← instantiateAll state3_1.parentExpr?.get!)
  let [state3_1goal0] := state3_1.goals | fail "Should have 1 goal"
  addTest $ LSpec.test "(3_1 parent)" (state3_1parent == s!"((:c Or.inr) (:fv {fvQ}) (:fv {fvP}) (:mv {state3_1goal0}))")
  addTest $ LSpec.check "· apply Or.inr" (state3_1.goals.length = 1)
  let state4_1 ← match ← state3_1.tacticOn (goalId := 0) (tactic := "assumption") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_1.goals.isEmpty
  let state4_1parent ← instantiateAll state4_1.parentExpr?.get!
  addTest $ LSpec.test "(4_1 parent)" state4_1parent.isFVar
  checkTrue "(4_1 root)" $ ¬ state4_1.isSolved
  let state3_2 ← match ← state2.tacticOn (goalId := 1) (tactic := "apply Or.inl") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "· apply Or.inl" (state3_2.goals.length = 1)
  let state4_2 ← match ← state3_2.tacticOn (goalId := 0) (tactic := "assumption") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_2.goals.isEmpty
  checkTrue "(4_2 root)" $ ¬ state4_2.isSolved
  -- Ensure the proof can continue from `state4_2`.
  let state2b ← match state4_2.continue state2 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.test "(resume)" (state2b.goals == [state2.goals[0]!])
  let state3_1 ← match ← state2b.tacticOn (goalId := 0) (tactic := "apply Or.inr") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "· apply Or.inr" (state3_1.goals.length = 1)
  let state4_1 ← match ← state3_1.tacticOn (goalId := 0) (tactic := "assumption") with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "  assumption" state4_1.goals.isEmpty
  checkTrue "(4_1 root)" $ ¬ state4_1.rootExpr?.get!.hasExprMVar

  return ()
  where
    typeProp: Protocol.Expression := { pp? := .some "Prop" }
    branchGoal (caseName varName: String): Protocol.Goal := {
      userName? := .some caseName,
      target := { pp? := .some "q ∨ p" },
      vars := #[
        { userName := "p", type? := .some typeProp },
        { userName := "q", type? := .some typeProp },
        { userName := "h✝", type? := .some { pp? := .some varName }, isInaccessible := true }
      ]
    }

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
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[interiorGoal [] "a + b + c1 = b + a + c2"])

  let goalConv := state1.goals[0]!
  let state2 ← match ← state1.conv (state1.get! 0) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "conv => ..." ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "a + b + c1 = b + a + c2" with isConversion := true }])

  let convTactic := "rhs"
  let state3R ← match ← state2.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic} (discard)" ((← state3R.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "b + a + c2" with isConversion := true }])

  let convTactic := "lhs"
  let state3L ← match ← state2.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic}" ((← state3L.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "a + b + c1" with isConversion := true }])

  let convTactic := "congr"
  let state4 ← match ← state3L.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  {convTactic}" ((← state4.serializeGoals (options := ← read)).map (·.devolatilize) =
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
  addTest $ LSpec.check s!"  · {convTactic}" ((← state5_1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[{ interiorGoal [] "b + a" with isConversion := true, userName? := .some "a" }])

  let convTactic := "rfl"
  let state6_1 ← match ← state5_1.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
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
  let state6 ← match ← state4_1.tacticOn (goalId := 0) convTactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"  · {convTactic}" ((← state6.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[])

  let state1_1 ← match ← state6.convExit goalConv with
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
  let state1 ← match ← state0.tacticOn (goalId := 0) (tactic := tactic) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[interiorGoal [] "a + b = c + d"])
  let pred := "a + b = b + c"
  let state2 ← match ← state1.tryCalc (state1.get! 0) (pred := pred) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"calc {pred} := _" ((← state2.serializeGoals (options := ← read)).map (·.devolatilize) =
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
  let state4 ← match ← state3.tryCalc (state3.get! 0) (pred := pred) with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"calc {pred} := _" ((← state4.serializeGoals (options := ← read)).map (·.devolatilize) =
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

def test_tactic_failure_unresolved_goals : TestM Unit := do
  let state? ← startProof (.expr "∀ (p : Nat → Prop), ∃ (x : Nat), p (0 + x + 0)")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let tactic := "intro p"
  let state1 ← match ← state0.tacticOn 0 tactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  let tactic := "exact ⟨0, by simp⟩"
  let .failure messages ← state1.tacticOn 0 tactic | addTest $ assertUnreachable s!"{tactic} should fail"
  checkEq s!"{tactic} fails" messages #[s!"{← getFileName}:0:12: error: unsolved goals\np : Nat → Prop\n⊢ p 0\n"]

def test_tactic_failure_synthesize_placeholder : TestM Unit := do
  let state? ← startProof (.expr "∀ (p q r : Prop) (h : p → q), q ∧ r")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let tactic := "intro p q r h"
  let state1 ← match ← state0.tacticOn 0 tactic with
    | .success state _ => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  let tactic := "simpa [h] using And.imp_left h _"
  --let state2 ← match ← state1.tacticOn 0 tactic with
  --  | .success state => pure state
  --  | other => do
  --    addTest $ assertUnreachable $ other.toString
  --    return ()

  -- Volatile behaviour. This easily changes across Lean versions

  --checkEq tactic ((← state2.serializeGoals).map (·.devolatilize))  #[
  --  buildGoal [("p", "Prop"), ("q", "Prop"), ("r", "Prop"), ("h", "p → q")] "p ∧ r"
  --]

  let .failure messages ← state1.tacticOn 0 tactic | addTest $ assertUnreachable s!"{tactic} should fail"
  let message := s!"<Pantograph>:0:31: error: don't know how to synthesize placeholder\ncontext:\np q r : Prop\nh : p → q\n⊢ p ∧ r\n"
  checkEq s!"{tactic} fails" messages #[message]

def test_deconstruct : TestM Unit := do
  let state? ← startProof (.expr "∀ (p q : Prop) (h : And p q), And q p")
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let tactic := "intro p q ⟨hp, hq⟩"
  let state1 ← match ← state0.tacticOn 0 tactic with
    | .success state _ => pure state
    | other => do
      fail other.toString
      return ()
  checkEq tactic ((← state1.serializeGoals (options := ← read)).map (·.devolatilize))
    #[
      buildGoal [("p", "Prop"), ("q", "Prop"), ("hp", "p"), ("hq", "q")] "q ∧ p"
    ]


def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("identity", test_identity),
    ("Nat.add_comm", test_nat_add_comm false),
    ("Nat.add_comm manual", test_nat_add_comm true),
    ("Nat.add_comm delta", test_delta_variable),
    ("arithmetic", test_arith),
    ("Or.comm", test_or_comm),
    ("conv", test_conv),
    ("calc", test_calc),
    ("tactic failure with unresolved goals", test_tactic_failure_unresolved_goals),
    ("tactic failure with synthesize placeholder", test_tactic_failure_synthesize_placeholder),
    ("deconstruct", test_deconstruct),
  ]
  tests.map (fun (name, test) => (name, proofRunner env test))



end Pantograph.Test.Proofs
