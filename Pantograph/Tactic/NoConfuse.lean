import Lean

open Lean

namespace Pantograph.Tactic

def noConfuse: Elab.Tactic.Tactic := λ stx => do
  let goal ← Elab.Tactic.getMainGoal
  goal.withContext do
    let absurd ← Elab.Term.elabTerm (stx := stx) .none
    let noConfusion ← Meta.mkNoConfusion (target := ← goal.getType) (h := absurd)

    unless ← Meta.isDefEq (← Meta.inferType noConfusion) (← goal.getType) do
      throwError "invalid noConfuse call: The resultant type {← Meta.ppExpr $ ← Meta.inferType noConfusion} cannot be unified with {← Meta.ppExpr $ ← goal.getType}"
    goal.assign noConfusion
  Elab.Tactic.setGoals []

end Pantograph.Tactic
