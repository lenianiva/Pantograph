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

def «have» (binderName: Name) (type: Syntax): Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals: List MVarId ← goal.withContext do
    let type ← Elab.Term.elabType (stx := type)
    let lctx ← MonadLCtx.getLCtx

    -- The branch goal inherits the same context, but with a different type
    let mvarBranch ← Meta.mkFreshExprMVarAt lctx (← Meta.getLocalInstances) type

    -- Create the context for the `upstream` goal
    let fvarId ← mkFreshFVarId
    let lctxUpstream := lctx.mkLocalDecl fvarId binderName type
    let fvar   := mkFVar fvarId
    let mvarUpstream ←
      withTheReader Meta.Context (fun ctx => { ctx with lctx := lctxUpstream }) do
        Meta.withNewLocalInstances #[fvar] 0 do
          let mvarUpstream ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances)
            (← goal.getType) (kind := MetavarKind.synthetic) (userName := .anonymous)
          --let expr: Expr := .app (.lam binderName type mvarBranch .default) mvarUpstream
          goal.assign mvarUpstream
          pure mvarUpstream

    pure [mvarBranch.mvarId!, mvarUpstream.mvarId!]
  Elab.Tactic.setGoals nextGoals

end Pantograph.Tactic
