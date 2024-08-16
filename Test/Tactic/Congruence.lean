import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.Congruence

def test_congr_arg_list : TestT Elab.TermElabM Unit := do
  let expr := "λ {α} (l1 l2 : List α) (h: l1 = l2) => l1.reverse = l2.reverse"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let newGoals ← runTacticOnMVar Tactic.evalCongruenceArg target.mvarId!
    addTest $ LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
      [
        (`α, "Sort ?u.30"),
        (`a₁, "?α"),
        (`a₂, "?α"),
        (`f, "?α → List α"),
        (`h, "?a₁ = ?a₂"),
        (`conduit, "(?f ?a₁ = ?f ?a₂) = (l1.reverse = l2.reverse)"),
      ])
    let f := newGoals.get! 3
    let h := newGoals.get! 4
    let c := newGoals.get! 5
    let results ← f.apply (← parseSentence "List.reverse")
    addTest $ LSpec.check "apply" (results.length = 0)
    addTest $ LSpec.check "h" ((← exprToStr $ ← h.getType) = "?a₁ = ?a₂")
    addTest $ LSpec.check "conduit" ((← exprToStr $ ← c.getType) = "(?a₁.reverse = ?a₂.reverse) = (l1.reverse = l2.reverse)")
def test_congr_arg : TestT Elab.TermElabM Unit := do
  let expr := "λ (n m: Nat) (h: n = m) => n * n = m * m"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let newGoals ← runTacticOnMVar Tactic.evalCongruenceArg target.mvarId!
    addTest $  LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
      [
        (`α, "Sort ?u.70"),
        (`a₁, "?α"),
        (`a₂, "?α"),
        (`f, "?α → Nat"),
        (`h, "?a₁ = ?a₂"),
        (`conduit, "(?f ?a₁ = ?f ?a₂) = (n * n = m * m)"),
      ])
def test_congr_fun : TestT Elab.TermElabM Unit := do
  let expr := "λ (n m: Nat) => (n + m) + (n + m) = (n + m) * 2"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let newGoals ← runTacticOnMVar Tactic.evalCongruenceFun target.mvarId!
    addTest $ LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
      [
        (`α, "Sort ?u.159"),
        (`f₁, "?α → Nat"),
        (`f₂, "?α → Nat"),
        (`h, "?f₁ = ?f₂"),
        (`a, "?α"),
        (`conduit, "(?f₁ ?a = ?f₂ ?a) = (n + m + (n + m) = (n + m) * 2)"),
      ])
def test_congr : TestT Elab.TermElabM Unit := do
  let expr := "λ (a b: Nat) => a = b"
  let expr ← parseSentence expr
  Meta.lambdaTelescope expr $ λ _ body => do
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let newGoals ← runTacticOnMVar Tactic.evalCongruence target.mvarId!
    addTest $  LSpec.check "goals" ((← newGoals.mapM (λ x => mvarUserNameAndType x)) =
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

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("congrArg List.reverse", test_congr_arg_list),
    ("congrArg", test_congr_arg),
    ("congrFun", test_congr_fun),
    ("congr", test_congr),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))

end Pantograph.Test.Tactic.Congruence
