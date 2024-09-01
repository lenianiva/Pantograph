import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.NoConfuse

def test_nat : TestT Elab.TermElabM Unit := do
  let expr := "λ (n: Nat) (h: 0 = n + 1) => False"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let recursor ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "h")
      (fileName := filename) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let tactic := Tactic.evalNoConfuse recursor
    let newGoals ← runTacticOnMVar tactic target.mvarId!
    addTest $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) = [])

def test_nat_fail : TestT Elab.TermElabM Unit := do
  let expr := "λ (n: Nat) (h: n = n) => False"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let recursor ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "h")
      (fileName := filename) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    try
      let tactic := Tactic.evalNoConfuse recursor
      let _ ← runTacticOnMVar tactic target.mvarId!
      addTest $ assertUnreachable "Tactic should fail"
    catch _ =>
      addTest $ LSpec.check "Tactic should fail" true

def test_list : TestT Elab.TermElabM Unit := do
  let expr := "λ (l: List Nat) (h: [] = 1 :: l) => False"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let recursor ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "h")
      (fileName := filename) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let tactic := Tactic.evalNoConfuse recursor
    let newGoals ← runTacticOnMVar tactic target.mvarId!
    addTest $ LSpec.check "goals"
      ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) = [])

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("Nat", test_nat),
    ("Nat fail", test_nat_fail),
    ("List", test_list),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))

end Pantograph.Test.Tactic.NoConfuse
