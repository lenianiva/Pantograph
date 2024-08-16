import Lean

open Lean

namespace Pantograph.Tactic

private def newMVarSet (mctxOld: @&MetavarContext) (mctxNew: @&MetavarContext): SSet MVarId :=
  mctxNew.decls.foldl (fun acc mvarId mvarDecl =>
    if let .some prevMVarDecl := mctxOld.decls.find? mvarId then
      assert! prevMVarDecl.type == mvarDecl.type
      acc
    else
      acc.insert mvarId
    ) SSet.empty
def assign (goal: MVarId) (expr: Expr): MetaM (List MVarId) := do
  goal.checkNotAssigned `Pantograph.Tactic.assign

  -- This run of the unifier is critical in resolving mvars in passing
  let exprType ← Meta.inferType expr
  let goalType ← goal.getType
  unless ← Meta.isDefEq goalType exprType do
    throwError s!"{← Meta.ppExpr expr} : {← Meta.ppExpr exprType} ≠ {← Meta.ppExpr goalType}"

  let nextGoals ← Meta.getMVars expr
  goal.assign expr
  nextGoals.toList.filterM (not <$> ·.isAssigned)

def evalAssign : Elab.Tactic.Tactic := fun stx => Elab.Tactic.withMainContext do
  let goalType ← Elab.Tactic.getMainTarget
  let expr ← Elab.Term.elabTermAndSynthesize (stx := stx) (expectedType? := .some goalType)
  let nextGoals ← assign (← Elab.Tactic.getMainGoal) expr
  Elab.Tactic.setGoals nextGoals


end Pantograph.Tactic
