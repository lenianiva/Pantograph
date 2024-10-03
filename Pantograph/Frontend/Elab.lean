/- Adapted from https://github.com/semorrison/lean-training-data -/
import Lean.Elab.Import
import Lean.Elab.Command
import Lean.Elab.InfoTree

import Pantograph.Frontend.Basic
import Pantograph.Frontend.MetaTranslate
import Pantograph.Goal
import Pantograph.Protocol

open Lean

namespace Lean.Elab.Info
/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
protected def stx? : Info → Option Syntax
  | .ofTacticInfo         info => info.stx
  | .ofTermInfo           info => info.stx
  | .ofCommandInfo        info => info.stx
  | .ofMacroExpansionInfo info => info.stx
  | .ofOptionInfo         info => info.stx
  | .ofFieldInfo          info => info.stx
  | .ofCompletionInfo     info => info.stx
  | .ofUserWidgetInfo     info => info.stx
  | .ofCustomInfo         info => info.stx
  | .ofFVarAliasInfo      _    => none
  | .ofFieldRedeclInfo    info => info.stx
  | .ofOmissionInfo       info => info.stx
/-- Is the `Syntax` for this `Lean.Elab.Info` original, or synthetic? -/
protected def isOriginal (i : Info) : Bool :=
  match i.stx? with
  | none => true   -- Somewhat unclear what to do with `FVarAliasInfo`, so be conservative.
  | some stx => match stx.getHeadInfo with
    | .original .. => true
    | _ => false
end Lean.Elab.Info

namespace Lean.Elab.TacticInfo

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none
/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

end Lean.Elab.TacticInfo

namespace Lean.Elab.InfoTree

/--
Keep `.node` nodes and `.hole` nodes satisfying predicates.

Returns a `List InfoTree`, although in most situations this will be a singleton.
-/
partial def filter (p : Info → Bool) (m : MVarId → Bool := fun _ => false) :
    InfoTree → List InfoTree
  | .context ctx tree => tree.filter p m |>.map (.context ctx)
  | .node info children =>
    if p info then
      [.node info (children.toList.map (filter p m)).join.toPArray']
    else
      (children.toList.map (filter p m)).join
  | .hole mvar => if m mvar then [.hole mvar] else []

end Lean.Elab.InfoTree


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

end TacticInvocation

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def findAllInfo (t : Elab.InfoTree) (context?: Option Elab.ContextInfo) (pred : Elab.Info → Bool) :
    List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  match t with
  | .context inner t => findAllInfo t (inner.mergeIntoOuter? context?) pred
  | .node i children  =>
      (if pred i then [(i, context?, children)] else []) ++ children.toList.bind (fun t => findAllInfo t context? pred)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`, and any children info trees. -/
private def collectTacticNodes (t : Elab.InfoTree) : List TacticInvocation :=
  let infos := findAllInfo t none fun i => match i with
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
    return { goalBefore, goalAfter, tactic }

structure InfoWithContext where
  info: Elab.Info
  context?: Option Elab.ContextInfo := .none

private def collectSorrysInTree (t : Elab.InfoTree) : List InfoWithContext :=
  let infos := findAllInfo t none fun i => match i with
    | .ofTermInfo { expectedType?, expr, stx, .. } =>
      expr.isSorry ∧ expectedType?.isSome ∧ stx.isOfKind `Lean.Parser.Term.sorry
    | .ofTacticInfo { stx, .. } =>
      -- The `sorry` term is distinct from the `sorry` tactic
      stx.isOfKind `Lean.Parser.Tactic.tacticSorry
    | _ => false
  infos.map fun (info, context?, _) => { info, context? }

-- NOTE: Plural deliberately not spelled "sorries"
@[export pantograph_frontend_collect_sorrys_m]
def collectSorrys (step: CompilationStep) : List InfoWithContext :=
  step.trees.bind collectSorrysInTree



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
  let goals := (← goalsM.run {} |>.run' {}).bind id
  let root := match goals with
    | [] => panic! "This function cannot be called on an empty list"
    | [g] => g
    | _ => { name := .anonymous }
  GoalState.createFromMVars goals root



end Pantograph.Frontend
