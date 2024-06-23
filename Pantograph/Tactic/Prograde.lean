/- Prograde (forward) reasoning tactics -/

import Lean
open Lean

namespace Pantograph.Tactic

def tacticEval (binderName: Name) (expr: Syntax): Elab.Tactic.TacticM Unit := do
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

end Pantograph.Tactic
