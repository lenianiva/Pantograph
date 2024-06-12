import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.Congruence

def test_congr_arg (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (n m: Nat) (h: n = m) => n * n = m * m"
  runMetaMSeq env do
    let expr ← parseSentence expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let mut tests := LSpec.TestSeq.done
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar Tactic.congruenceArg target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
          [
            (`α, "Sort ?u.70"),
            (`a₁, "?α"),
            (`a₂, "?α"),
            (`f, "?α → Nat"),
            (`h, "?a₁ = ?a₂"),
            (`conduit, "(?f ?a₁ = ?f ?a₂) = (n * n = m * m)"),
          ])
      tests := tests ++ test
      return tests
def test_congr_fun (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (n m: Nat) => (n + m) + (n + m) = (n + m) * 2"
  runMetaMSeq env do
    let expr ← parseSentence expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let mut tests := LSpec.TestSeq.done
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar Tactic.congruenceFun target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
          [
            (`α, "Sort ?u.159"),
            (`f₁, "?α → Nat"),
            (`f₂, "?α → Nat"),
            (`h, "?f₁ = ?f₂"),
            (`a, "?α"),
            (`conduit, "(?f₁ ?a = ?f₂ ?a) = (n + m + (n + m) = (n + m) * 2)"),
          ])
      tests := tests ++ test
      return tests
def test_congr (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (a b: Nat) => a = b"
  runMetaMSeq env do
    let expr ← parseSentence expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let mut tests := LSpec.TestSeq.done
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar Tactic.congruence target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
          [
            (`α, "Sort ?u.10"),
            (`f₁, "?α → Nat"),
            (`f₂, "?α → Nat"),
            (`a₁, "?α"),
            (`a₂, "?α"),
            (`h₁, "?f₁ = ?f₂"),
            (`h₂, "?a₁ = ?a₂"),
            (`conduit, "(?f₁ ?a₁ = ?f₂ ?a₂) = (a = b)"),
          ])
      tests := tests ++ test
      return tests

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("congrArg", test_congr_arg env),
    ("congrFun", test_congr_fun env),
    ("congr", test_congr env),
  ]

end Pantograph.Test.Tactic.Congruence
