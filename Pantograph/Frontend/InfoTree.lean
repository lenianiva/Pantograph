/- Adapted from lean-training-data by semorrison -/
import Lean.Elab.InfoTree
import Lean.Parser.Term

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

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def findAllInfo (t : InfoTree) (context?: Option Elab.ContextInfo) (pred : Elab.Info → Bool) :
    List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  match t with
  | .context inner t => findAllInfo t (inner.mergeIntoOuter? context?) pred
  | .node i children  =>
      (if pred i then [(i, context?, children)] else []) ++ children.toList.bind (fun t => findAllInfo t context? pred)
  | _ => []

end Lean.Elab.InfoTree
