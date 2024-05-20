import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.NoConfuse

def valueAndType (recursor: String): MetaM (Expr × Expr) := do
  let recursor ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := recursor)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => throwError "Failed to parse: {error}"
  runTermElabMInMeta do
    let recursor ← Elab.Term.elabTerm (stx := recursor) .none
    let recursorType ← Meta.inferType recursor
    return (recursor, recursorType)

def test_nat (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (n: Nat) (h: 0 = n + 1) => False"
  runMetaMSeq env do
    let (expr, exprType) ← valueAndType expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let recursor ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "h")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let tactic := Tactic.noConfuse recursor
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar tactic target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
          [])
      tests := tests ++ test
      return tests

def test_nat_fail (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (n: Nat) (h: n = n) => False"
  runMetaMSeq env do
    let (expr, _) ← valueAndType expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let recursor ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "h")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      try
        let tactic := Tactic.noConfuse recursor
        let _ ← runTermElabMInMeta $ runTacticOnMVar tactic target.mvarId!
        tests := tests ++ assertUnreachable "Tactic should fail"
      catch _ =>
        tests := tests ++ LSpec.check "Tactic should fail" true
        return tests
      return tests

def test_list (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (l: List Nat) (h: [] = 1 :: l) => False"
  runMetaMSeq env do
    let (expr, exprType) ← valueAndType expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let recursor ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "h")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let tactic := Tactic.noConfuse recursor
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar tactic target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
          [])
      tests := tests ++ test
      return tests

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("Nat", test_nat env),
    ("Nat fail", test_nat_fail env),
    ("List", test_list env),
  ]

end Pantograph.Test.Tactic.NoConfuse
