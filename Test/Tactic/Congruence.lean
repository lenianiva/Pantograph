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

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("congrArg", test_congr_arg env),
  ]

end Pantograph.Test.Tactic.Congruence
