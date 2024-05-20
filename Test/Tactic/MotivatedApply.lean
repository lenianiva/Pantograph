import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.MotivatedApply

def test_type_extract (env: Environment): IO LSpec.TestSeq :=
  runMetaMSeq env do
    let mut tests := LSpec.TestSeq.done
    let recursor ← parseSentence "@Nat.brecOn"
    let recursorType ← Meta.inferType recursor
    tests := tests ++ LSpec.check "recursorType" ("{motive : Nat → Sort ?u.1} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t" =
      (← exprToStr recursorType))
    let info ← match Tactic.getRecursorInformation recursorType with
      | .some info => pure info
      | .none => throwError "Failed to extract recursor info"
    tests := tests ++ LSpec.check "iMotive" (info.iMotive = 2)
    let motiveType := info.getMotiveType
    tests := tests ++ LSpec.check "motiveType" ("Nat → Sort ?u.1" =
      (← exprToStr motiveType))
    return tests

def test_nat_brec_on (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (n t: Nat) => n + 0 = n"
  runMetaMSeq env do
    let expr ← parseSentence expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let recursor ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "@Nat.brecOn")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let tactic := Tactic.motivatedApply recursor
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar tactic target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
          [
            "Nat → Prop",
            "Nat",
            "∀ (t : Nat), Nat.below t → ?motive t",
            "?motive ?m.67 = (n + 0 = n)",
          ])
      tests := tests ++ test
      return tests

def test_list_brec_on (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ {α : Type} (l: List α) => l ++ [] = [] ++ l"
  runMetaMSeq env do
    let expr ← parseSentence expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let recursor ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "@List.brecOn")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let tactic := Tactic.motivatedApply recursor
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar tactic target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
          [
            "Type ?u.90",
            "List ?m.92 → Prop",
            "List ?m.92",
            "∀ (t : List ?m.92), List.below t → ?motive t",
            "?motive ?m.94 = (l ++ [] = [] ++ l)",
          ])
      tests := tests ++ test
      return tests

def test_partial_motive_instantiation (env: Environment): IO LSpec.TestSeq := do
  let expr := "λ (n t: Nat) => n + 0 = n"
  runMetaMSeq env $ runTermElabMInMeta do
    let recursor ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "@Nat.brecOn")
      (fileName := filename) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    let expr ← parseSentence expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let tactic := Tactic.motivatedApply recursor
      let newGoals ← runTacticOnMVar tactic target.mvarId!
      let majorId := 67
      tests := tests ++ (LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
        [
          "Nat → Prop",
          "Nat",
          "∀ (t : Nat), Nat.below t → ?motive t",
          s!"?motive ?m.{majorId} = (n + 0 = n)",
        ]))
      let [motive, major, step, conduit] := newGoals | panic! "Incorrect goal number"
      tests := tests ++ (LSpec.check "goal name" (major.name.toString = s!"_uniq.{majorId}"))

      -- Assign motive to `λ x => x + _`
      let motive_assign ← parseSentence "λ (x: Nat) => @Nat.add x + 0 = _"
      motive.assign motive_assign

      let test ← conduit.withContext do
        let t := toString (← Meta.ppExpr $ ← conduit.getType)
        return LSpec.check "conduit" (t = s!"(?m.{majorId}.add + 0 = ?m.138 ?m.{majorId}) = (n + 0 = n)")
      tests := tests ++ test

      return tests

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("type_extract", test_type_extract env),
    ("Nat.brecOn", test_nat_brec_on env),
    ("List.brecOn", test_list_brec_on env),
    ("Nat.brecOn partial motive instantiation", test_partial_motive_instantiation env),
  ]

end Pantograph.Test.Tactic.MotivatedApply
