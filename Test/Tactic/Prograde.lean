import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.Prograde

def test_eval (env: Environment): IO LSpec.TestSeq :=
  let expr := "forall (p q : Prop) (h: p), And (Or p q) (Or p q)"
  runMetaMSeq env do
    let expr ← parseSentence expr
    Meta.forallTelescope expr $ λ _ body => do
      let e ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "Or.inl h")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let goal ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let target: Expr := mkAnd
        (mkOr (.fvar ⟨uniq 8⟩) (.fvar ⟨uniq 9⟩))
        (mkOr (.fvar ⟨uniq 8⟩) (.fvar ⟨uniq 9⟩))
      let h := .fvar ⟨uniq 8⟩
      let test := LSpec.test "goals before" ((← toCondensedGoal goal.mvarId!).devolatilize == {
        context := #[
          { userName := `p, type := .sort 0 },
          { userName := `q, type := .sort 0 },
          { userName := `h, type := h}
        ],
        target,
      })
      tests := tests ++ test
      let tactic := Tactic.evaluate `h2 e
      let m := .mvar ⟨uniq 13⟩
      let test ← runTermElabMInMeta do
        let [goal] ← runTacticOnMVar tactic goal.mvarId! | panic! "Incorrect goal number"
        pure $ LSpec.test "goals after" ((← toCondensedGoal goal).devolatilize == {
        context := #[
          { userName := `p, type := .sort 0 },
          { userName := `q, type := .sort 0 },
          { userName := `h, type := h},
          {
            userName := `h2,
            type := mkOr h m,
            value? := .some $ mkApp3 (mkConst `Or.inl) h m (.fvar ⟨uniq 10⟩)
          }
        ],
        target,
      })
      tests := tests ++ test
      return tests

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("eval", test_eval env),
  ]

end Pantograph.Test.Tactic.Prograde
