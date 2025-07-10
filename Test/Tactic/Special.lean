import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.Special

def test_exact_q : TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "1 + 2 = 2 + 3"
  let state0 ← GoalState.create rootExpr
  let tactic := "exact?"
  let state1? ← state0.tacticOn (goalId := 0) (tactic := tactic)
  let .failure messages := state1? | fail "Must fail"
  checkEq "messages"
    (← messages.mapM (·.toString))
    #[s!"{← getFileName}:0:0: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.\n"]

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("exact?", test_exact_q),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))

end Pantograph.Test.Tactic.Special
