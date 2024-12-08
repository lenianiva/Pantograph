/- Adapted from lean-training-data -/
import Lean.Elab.InfoTree
import Lean.Parser.Term
import Lean.PrettyPrinter

open Lean

namespace Lean.Elab

private def elaboratorToString : Name → String
  | .anonymous => ""
  | n => s!"[{n}]"
private def indent (s : String) : String := "\n".intercalate $ s.splitOn "\n" |>.map ("\t" ++ .)

/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
protected def Info.stx? : Info → Option Syntax
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
protected def Info.isOriginal (i : Info) : Bool :=
  match i.stx? with
  | none => true   -- Somewhat unclear what to do with `FVarAliasInfo`, so be conservative.
  | some stx => match stx.getHeadInfo with
    | .original .. => true
    | _ => false

def ContextInfo.ppExpr (ctx : ContextInfo) (lctx : LocalContext) (e : Expr) : IO Format :=
  ctx.runMetaM lctx (do Meta.ppExpr (← instantiateMVars e))

def CommandInfo.toString (info : CommandInfo) (ctx : ContextInfo) : IO String := do
  let stx := (← ctx.ppSyntax {} info.stx).pretty
  return s!"{stx}\n{elaboratorToString info.elaborator}"

def TermInfo.toString (info : TermInfo) (ctx : ContextInfo) : IO String := do
  let stx := (← ctx.ppSyntax info.lctx info.stx).pretty
  let expectedType ← info.expectedType?.mapM fun ty => do
    pure s!": {(← ctx.ppExpr info.lctx ty).pretty}"
  let expr := (← ctx.ppExpr info.lctx info.expr).pretty
  return s!"{stx}\n{elaboratorToString info.elaborator}{expr}{expectedType}"

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def TacticInfo.name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none
/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def TacticInfo.isSubstantive (t : TacticInfo) : Bool :=
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
def TacticInfo.pp (info : TacticInfo) (ctx : ContextInfo) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"
def TacticInfo.toString (i : TacticInfo) (ctx : ContextInfo) : IO String := do
  let name := i.name?
  let stx := Format.pretty (← i.pp ctx)
  return s!"{stx}\n{name} {stx}"

/--
Keep `.node` nodes and `.hole` nodes satisfying predicates.

Returns a `List InfoTree`, although in most situations this will be a singleton.
-/
partial def InfoTree.filter (p : Info → Bool) (m : MVarId → Bool := fun _ => false) :
    InfoTree → List InfoTree
  | .context ctx tree => tree.filter p m |>.map (.context ctx)
  | .node info children =>
    if p info then
      [.node info (children.toList.map (filter p m)).join.toPArray']
    else
      (children.toList.map (filter p m)).join
  | .hole mvar => if m mvar then [.hole mvar] else []

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def InfoTree.findAllInfo (t : InfoTree) (context?: Option Elab.ContextInfo) (pred : Elab.Info → Bool) :
    List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  match t with
  | .context inner t => findAllInfo t (inner.mergeIntoOuter? context?) pred
  | .node i children  =>
      (if pred i then [(i, context?, children)] else []) ++ children.toList.bind (fun t => findAllInfo t context? pred)
  | _ => []

@[export pantograph_infotree_to_string_m]
partial def InfoTree.toString (t : InfoTree) (ctx?: Option Elab.ContextInfo) : IO String := do
  match t with
  | .context ctx t => t.toString (ctx.mergeIntoOuter? ctx?)
  | .node info children =>
    if let some ctx := ctx? then
      let node : Option String ← match info with
      | .ofTermInfo    info => some <$> (do pure <| s!"[term] {(← info.toString ctx)}")
      | .ofCommandInfo info => some <$> (do pure <| s!"[command] {(← info.toString ctx)}")
      | .ofTacticInfo  info => some <$> (do pure <| s!"[tactic] {(← info.toString ctx)}")
      | _                   => pure none
      let children := "\n".intercalate (← children.toList.mapM λ t' => do pure $ indent $ ← t'.toString ctx)
      return s!"{node}\n{children}"
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
      let payload := (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty
      return s!"[hole] {payload}"
    else throw <| IO.userError "No `ContextInfo` available."

end Lean.Elab
