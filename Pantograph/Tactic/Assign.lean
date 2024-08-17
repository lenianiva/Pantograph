import Lean

open Lean

namespace Pantograph.Tactic

def assign (goal: MVarId) (expr: Expr): MetaM (List MVarId) := do
  goal.checkNotAssigned `Pantograph.Tactic.assign

  -- This run of the unifier is critical in resolving mvars in passing
  let exprType ← Meta.inferType expr
  let goalType ← goal.getType
  unless ← Meta.isDefEq goalType exprType do
    throwError s!"{← Meta.ppExpr expr} : {← Meta.ppExpr exprType} ≠ {← Meta.ppExpr goalType}"

  -- FIXME: Use `withCollectingNewGoalsFrom`. Think about how this interacts with elaboration ...
  let nextGoals ← Meta.getMVarsNoDelayed expr
  goal.assign expr
  nextGoals.toList.filterM (not <$> ·.isAssigned)

def evalAssign : Elab.Tactic.Tactic := fun stx => Elab.Tactic.withMainContext do
  let target ← Elab.Tactic.getMainTarget
  let (expr, nextGoals) ← Elab.Tactic.elabTermWithHoles stx
    (expectedType? := .some target)
    (tagSuffix := .anonymous )
    (allowNaturalHoles := true)
  (← Elab.Tactic.getMainGoal).assign expr
  Elab.Tactic.setGoals nextGoals


end Pantograph.Tactic
