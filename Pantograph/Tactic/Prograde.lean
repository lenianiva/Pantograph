/- Prograde (forward) reasoning tactics -/

import Lean
open Lean

namespace Pantograph.Tactic

def evaluate (binderName: Name) (expr: Syntax): Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals ← goal.withContext do
    let expr ← Elab.Term.elabTerm (stx := expr) (expectedType? := .none)
    let type ← Meta.inferType expr

    let mvarUpstream ← Meta.withLetDecl binderName type expr λ _ => do
      let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
        (← goal.getType) (kind := MetavarKind.synthetic) (userName := .anonymous)
      goal.assign mvarUpstream
      pure mvarUpstream
    pure [mvarUpstream.mvarId!]
  Elab.Tactic.setGoals nextGoals

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
  let mvarBranch ← Meta.mkFreshExprMVarAt lctx (← Meta.getLocalInstances) type

  assert! ¬ type.hasLooseBVars
  let upstreamType := .letE binderName type mvarBranch (← mvarId.getType) false
  let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
    upstreamType (kind := MetavarKind.synthetic) (userName := ← mvarId.getTag)
  mvarId.assign mvarUpstream

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
