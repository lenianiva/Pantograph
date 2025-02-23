import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.MotivatedApply

def test_type_extract : TestT Elab.TermElabM Unit := do
  let recursor ← parseSentence "@Nat.brecOn"
  let recursorType ← Meta.inferType recursor
  addTest $ LSpec.check "recursorType" ("{motive : Nat → Sort ?u.1} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t" =
    (← exprToStr recursorType))
  let info ← match Tactic.getRecursorInformation recursorType with
    | .some info => pure info
    | .none => throwError "Failed to extract recursor info"
  addTest $ LSpec.check "iMotive" (info.iMotive = 2)
  let motiveType := info.getMotiveType
  addTest $ LSpec.check "motiveType" ("Nat → Sort ?u.1" =
    (← exprToStr motiveType))

def test_nat_brec_on : TestT Elab.TermElabM Unit := do
  let expr := "λ (n t: Nat) => n + 0 = n"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let recursor ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "@Nat.brecOn")
      (fileName := ← getFileName) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let tactic := Tactic.evalMotivatedApply recursor
    let newGoals ← runTacticOnMVar tactic target.mvarId!
    let test :=  LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
      [
        "Nat → Prop",
        "Nat",
        "∀ (t : Nat), Nat.below t → ?motive t",
        "?motive ?m.74 = (n + 0 = n)",
      ])
    addTest test

def test_list_brec_on : TestT Elab.TermElabM Unit := do
  let expr := "λ {α : Type} (l: List α) => l ++ [] = [] ++ l"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let recursor ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "@List.brecOn")
      (fileName := ← getFileName) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let tactic := Tactic.evalMotivatedApply recursor
    let newGoals ← runTacticOnMVar tactic target.mvarId!
    addTest $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
      [
        "Type ?u.90",
        "List ?m.92 → Prop",
        "List ?m.92",
        "∀ (t : List ?m.92), List.below t → ?motive t",
        "?motive ?m.94 = (l ++ [] = [] ++ l)",
      ])

def test_partial_motive_instantiation : TestT Elab.TermElabM Unit := do
  let expr := "λ (n t: Nat) => n + 0 = n"
  let recursor ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := "@Nat.brecOn")
    (fileName := ← getFileName) with
    | .ok syn => pure syn
    | .error error => throwError "Failed to parse: {error}"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let tactic := Tactic.evalMotivatedApply recursor
    let newGoals ← runTacticOnMVar tactic target.mvarId!
    let majorId := 74
    addTest $ (LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
      [
        "Nat → Prop",
        "Nat",
        "∀ (t : Nat), Nat.below t → ?motive t",
        s!"?motive ?m.{majorId} = (n + 0 = n)",
      ]))
    let [motive, major, step, conduit] := newGoals | panic! "Incorrect goal number"
    addTest $ (LSpec.check "goal name" (major.name.toString = s!"_uniq.{majorId}"))

    -- Assign motive to `λ x => x + _`
    let motive_assign ← parseSentence "λ (x: Nat) => @Nat.add x + 0 = _"
    motive.assign motive_assign

    addTest $ ← conduit.withContext do
      let t := toString (← Meta.ppExpr $ ← conduit.getType)
      return LSpec.check "conduit" (t = s!"(Nat.add ?m.{majorId} + 0 = ?m.150 ?m.{majorId}) = (n + 0 = n)")

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("type_extract", test_type_extract),
    ("Nat.brecOn", test_nat_brec_on),
    ("List.brecOn", test_list_brec_on),
    ("Nat.brecOn partial motive instantiation", test_partial_motive_instantiation),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))

end Pantograph.Test.Tactic.MotivatedApply
