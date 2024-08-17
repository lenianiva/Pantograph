/- Prograde (forward) reasoning tactics -/

import Lean
open Lean

namespace Pantograph.Tactic

/-- Introduces a fvar to the current mvar -/
def define (mvarId: MVarId) (binderName: Name) (expr: Expr): MetaM (FVarId × MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.define
  let type ← Meta.inferType expr

  Meta.withLetDecl binderName type expr λ fvar => do
    let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
      (← mvarId.getType) (kind := MetavarKind.synthetic) (userName := .anonymous)
    mvarId.assign mvarUpstream
    pure (fvar.fvarId!, mvarUpstream.mvarId!)

def evalDefine (binderName: Name) (expr: Syntax): Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let expr ← goal.withContext $ Elab.Term.elabTerm (stx := expr) (expectedType? := .none)
  let (_, mvarId) ← define goal binderName expr
  Elab.Tactic.setGoals [mvarId]

structure BranchResult where
  fvarId?: Option FVarId := .none
  main: MVarId
  branch: MVarId

def «have» (mvarId: MVarId) (binderName: Name) (type: Expr): MetaM BranchResult := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.have
  let lctx ← MonadLCtx.getLCtx
  -- The branch goal inherits the same context, but with a different type
  let mvarBranch ← Meta.mkFreshExprMVarAt lctx (← Meta.getLocalInstances) type

  -- Create the context for the `upstream` goal
  let fvarId ← mkFreshFVarId
  let lctxUpstream := lctx.mkLocalDecl fvarId binderName type
  let mvarUpstream ←
    withTheReader Meta.Context (fun ctx => { ctx with lctx := lctxUpstream }) do
      Meta.withNewLocalInstances #[.fvar fvarId] 0 do
        let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
          (← mvarId.getType) (kind := MetavarKind.synthetic) (userName := ← mvarId.getTag)
        --let expr: Expr := .app (.lam binderName type mvarBranch .default) mvarUpstream
        mvarId.assign mvarUpstream
        pure mvarUpstream

  return {
    fvarId? := .some fvarId,
    main := mvarUpstream.mvarId!,
    branch := mvarBranch.mvarId!,
  }

def evalHave (binderName: Name) (type: Syntax): Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals: List MVarId ← goal.withContext do
    let type ← Elab.Term.elabType (stx := type)
    let result ← «have» goal binderName type
    pure [result.branch, result.main]
  Elab.Tactic.setGoals nextGoals

def «let» (mvarId: MVarId) (binderName: Name) (type: Expr): MetaM BranchResult := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.let
  let lctx ← MonadLCtx.getLCtx

  -- The branch goal inherits the same context, but with a different type
  let mvarBranch ← Meta.mkFreshExprMVarAt lctx (← Meta.getLocalInstances) type (userName := binderName)

  assert! ¬ type.hasLooseBVars
  let mvarUpstream ← Meta.withLetDecl binderName type mvarBranch $ λ fvar => do
    let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
      (type := ← mvarId.getType) (kind := MetavarKind.synthetic) (userName := ← mvarId.getTag)
    mvarId.assign $ .letE binderName type fvar mvarUpstream (nonDep := false)
    pure mvarUpstream

  return {
    main := mvarUpstream.mvarId!,
    branch := mvarBranch.mvarId!,
  }

def evalLet (binderName: Name) (type: Syntax): Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let type ← goal.withContext $ Elab.Term.elabType (stx := type)
  let result ← «let» goal binderName type
  Elab.Tactic.setGoals [result.branch, result.main]

end Pantograph.Tactic
