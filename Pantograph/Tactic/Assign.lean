import Lean

open Lean

namespace Pantograph.Tactic

/-- WARNING: This should be used with a function like `elabTermWithHoles` that properly collects the mvar information from `expr`. -/
def assign (goal: MVarId) (expr: Expr) (nextGoals: List MVarId): MetaM (List MVarId) := do
  goal.checkNotAssigned `Pantograph.Tactic.assign

  -- This run of the unifier is critical in resolving mvars in passing
  let exprType ← Meta.inferType expr
  let goalType ← goal.getType
  unless ← Meta.isDefEq goalType exprType do
    throwError s!"{← Meta.ppExpr expr} : {← Meta.ppExpr exprType} ≠ {← Meta.ppExpr goalType}"
  goal.assign expr
  nextGoals.filterM (not <$> ·.isAssigned)

def evalAssign : Elab.Tactic.Tactic := fun stx => Elab.Tactic.withMainContext do
  let target ← Elab.Tactic.getMainTarget
  let goal ← Elab.Tactic.getMainGoal
  goal.checkNotAssigned `Pantograph.Tactic.evalAssign
  let (expr, nextGoals) ← Elab.Tactic.elabTermWithHoles stx
    (expectedType? := .some target)
    (tagSuffix := .anonymous )
    (allowNaturalHoles := true)
  goal.assign expr
  Elab.Tactic.setGoals nextGoals


end Pantograph.Tactic
