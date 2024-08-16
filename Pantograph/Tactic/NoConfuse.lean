import Lean

open Lean

namespace Pantograph.Tactic

def noConfuse (mvarId: MVarId) (h: Expr): MetaM Unit := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.noConfuse
  let target ← mvarId.getType
  let noConfusion ← Meta.mkNoConfusion (target := target) (h := h)

  unless ← Meta.isDefEq (← Meta.inferType noConfusion) target do
    throwError "invalid noConfuse call: The resultant type {← Meta.ppExpr $ ← Meta.inferType noConfusion} cannot be unified with {← Meta.ppExpr target}"
  mvarId.assign noConfusion

def evalNoConfuse: Elab.Tactic.Tactic := λ stx => do
  let goal ← Elab.Tactic.getMainGoal
  let h ← goal.withContext $ Elab.Term.elabTerm (stx := stx) .none
  noConfuse goal h
  Elab.Tactic.setGoals []

end Pantograph.Tactic
