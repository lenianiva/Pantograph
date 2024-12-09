/- Adapted from https://github.com/semorrison/lean-training-data -/
import Lean.Elab.Import
import Lean.Elab.Command
import Lean.Elab.InfoTree

import Pantograph.Frontend.Basic
import Pantograph.Frontend.MetaTranslate
import Pantograph.Goal
import Pantograph.Protocol
import Pantograph.Frontend.InfoTree

open Lean

namespace Pantograph.Frontend

-- Info tree filtering functions

structure TacticInvocation where
  info : Elab.TacticInfo
  ctx : Elab.ContextInfo
  children : PersistentArray Elab.InfoTree
namespace TacticInvocation

/-- Return the range of the tactic, as a pair of file positions. -/
@[export pantograph_frontend_tactic_invocation_range]
protected def range (t : TacticInvocation) : Position × Position := t.ctx.fileMap.stxRange t.info.stx

/-- Pretty print a tactic. -/
protected def pp (t : TacticInvocation) : IO Format :=
  t.ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨t.info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

/-- Run a tactic on the goals stored in a `TacticInvocation`. -/
protected def runMetaMGoalsBefore (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxBefore <| x t.info.goalsBefore

/-- Run a tactic on the after goals stored in a `TacticInvocation`. -/
protected def runMetaMGoalsAfter (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxAfter <| x t.info.goalsAfter

/-- Run a tactic on the main goal stored in a `TacticInvocation`. -/
protected def runMetaM (t : TacticInvocation) (x : MVarId → MetaM α) : IO α := do
  match t.info.goalsBefore.head? with
  | none => throw <| IO.userError s!"No goals at {← t.pp}"
  | some g => t.runMetaMGoalsBefore fun _ => do g.withContext <| x g

protected def goalState (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsBefore (fun gs => gs.mapM fun g => do Meta.ppGoal g)

protected def goalStateAfter (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsAfter (fun gs => gs.mapM fun g => do Meta.ppGoal g)

protected def ppExpr (t : TacticInvocation) (e : Expr) : IO Format :=
  t.runMetaM (fun _ => do Meta.ppExpr (← instantiateMVars e))

protected def usedConstants (t: TacticInvocation) : NameSet :=
  let info := t.info
  info.goalsBefore
    |>.filterMap info.mctxAfter.getExprAssignmentCore?
    |>.map Expr.getUsedConstantsAsSet
    |>.foldl .union .empty

end TacticInvocation

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`, and any children info trees. -/
private def collectTacticNodes (t : Elab.InfoTree) : List TacticInvocation :=
  let infos := t.findAllInfo none false fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
    | (.ofTacticInfo i, some ctx, children) => .some ⟨i, ctx, children⟩
    | _ => none

def collectTactics (t : Elab.InfoTree) : List TacticInvocation :=
  collectTacticNodes t |>.filter fun i => i.info.isSubstantive

@[export pantograph_frontend_collect_tactics_from_compilation_step_m]
def collectTacticsFromCompilationStep (step : CompilationStep) : IO (List Protocol.InvokedTactic) := do
  let tacticInfoTrees := step.trees.bind λ tree => tree.filter λ
    | info@(.ofTacticInfo _) => info.isOriginal
    | _ => false
  let tactics := tacticInfoTrees.bind collectTactics
  tactics.mapM λ invocation => do
    let goalBefore := (Format.joinSep (← invocation.goalState) "\n").pretty
    let goalAfter := (Format.joinSep (← invocation.goalStateAfter) "\n").pretty
    let tactic ← invocation.ctx.runMetaM {} do
      let t ← PrettyPrinter.ppTactic ⟨invocation.info.stx⟩
      return t.pretty
    let usedConstants := invocation.usedConstants.toArray.map λ n => n.toString
    return {
      goalBefore,
      goalAfter,
      tactic,
      usedConstants,
    }

structure InfoWithContext where
  info: Elab.Info
  context?: Option Elab.ContextInfo := .none

private def collectSorrysInTree (t : Elab.InfoTree) : IO (List InfoWithContext) := do
  let infos ← t.findAllInfoM none true fun i ctx? => match i with
    | .ofTermInfo { expectedType?, expr, stx, lctx, .. } => do
      let .some expectedType := expectedType? | return false
      let .some ctx := ctx? | return false
      if expr.isSorry ∧ stx.isOfKind `Lean.Parser.Term.sorry then
        return true
      ctx.runMetaM lctx do
        let type ← Meta.inferType expr
        Bool.not <$> Meta.isDefEq type expectedType
    | .ofTacticInfo { stx, goalsBefore, .. } =>
      -- The `sorry` term is distinct from the `sorry` tactic
      let isSorry := stx.isOfKind `Lean.Parser.Tactic.tacticSorry
      return isSorry ∧ !goalsBefore.isEmpty
    | _ => return false
  return infos.map fun (info, context?, _) => { info, context? }

-- NOTE: Plural deliberately not spelled "sorries"
@[export pantograph_frontend_collect_sorrys_m]
def collectSorrys (step: CompilationStep) : IO (List InfoWithContext) := do
  return (← step.trees.mapM collectSorrysInTree).join

/--
Since we cannot directly merge `MetavarContext`s, we have to get creative. This
function duplicates frozen mvars in term and tactic info nodes, and add them to
the current `MetavarContext`.
-/
@[export pantograph_frontend_sorrys_to_goal_state]
def sorrysToGoalState (sorrys : List InfoWithContext) : MetaM GoalState := do
  assert! !sorrys.isEmpty
  let goalsM := sorrys.mapM λ i => do
    match i.info with
    | .ofTermInfo termInfo  => do
      let mvarId ← MetaTranslate.translateMVarFromTermInfo termInfo i.context?
      return [mvarId]
    | .ofTacticInfo tacticInfo => do
      MetaTranslate.translateMVarFromTacticInfoBefore tacticInfo i.context?
    | _ => panic! "Invalid info"
  let goals := List.join (← goalsM.run {} |>.run' {})
  let root := match goals with
    | [] => panic! "No MVars generated"
    | [g] => g
    | _ => { name := .anonymous }
  GoalState.createFromMVars goals root



end Pantograph.Frontend
