/- Adapted from lean-training-data by semorrison -/
import Lean.Parser
import Lean.Elab.Import
import Lean.Elab.Command
import Lean.Elab.Frontend
import Lean.Elab.InfoTree
import Lean.Util.Path

import Pantograph.Protocol


open Lean

namespace Lean.PersistentArray
/--
Drop the first `n` elements of a `PersistentArray`, returning the results as a `List`.
-/
-- We can't remove the `[Inhabited α]` hypotheses here until
-- `PersistentArray`'s `GetElem` instance also does.
def drop [Inhabited α] (t : PersistentArray α) (n : Nat) : List α :=
  List.range (t.size - n) |>.map fun i => t.get! (n + i)
end Lean.PersistentArray

namespace Lean.Elab.Info
/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
def stx? : Info → Option Syntax
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
def isOriginal (i : Info) : Bool :=
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

namespace Lean.FileMap

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.FileMap

-- Main

namespace Pantograph.Compile

structure CompilationStep where
  fileName : String
  fileMap : FileMap
  src : Substring
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List Elab.InfoTree


/--
Process one command, returning a `CompilationStep` and
`done : Bool`, indicating whether this was the last command.
-/
def processOneCommand: Elab.Frontend.FrontendM (CompilationStep × Bool) := do
  let s := (← get).commandState
  let before := s.env
  let done ← Elab.Frontend.processCommand
  let stx := (← get).commands.back
  let src := (← read).inputCtx.input.toSubstring.extract (← get).cmdPos (← get).parserState.pos
  let s' := (← get).commandState
  let after := s'.env
  let msgs := s'.messages.msgs.drop s.messages.msgs.size
  let trees := s'.infoState.trees.drop s.infoState.trees.size
  let ⟨_, fileName, fileMap⟩  := (← read).inputCtx
  return ({ fileName, fileMap, src, stx, before, after, msgs, trees }, done)

partial def processFile : Elab.Frontend.FrontendM (List CompilationStep) := do
  let (cmd, done) ← processOneCommand
  if done then
    return [cmd]
  else
    return cmd :: (← processFile)


def findSourcePath (module : Name) : IO System.FilePath := do
  return System.FilePath.mk ((← findOLean module).toString.replace ".lake/build/lib/" "") |>.withExtension "lean"

def processSource (module : Name) (opts : Options := {}) : IO (List CompilationStep) := unsafe do
  let file ← IO.FS.readFile (← findSourcePath module)
  let inputCtx := Parser.mkInputContext file module.toString

  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header opts messages inputCtx
  let commandState := Elab.Command.mkState env messages opts
  processFile.run { inputCtx }
    |>.run' {
    commandState := { commandState with infoState.enabled := true },
    parserState,
    cmdPos := parserState.pos
  }

-- Info tree filtering functions

structure TacticInvocation where
  info : Elab.TacticInfo
  ctx : Elab.ContextInfo
  children : PersistentArray Elab.InfoTree
namespace TacticInvocation

/-- Return the range of the tactic, as a pair of file positions. -/
def range (t : TacticInvocation) : Position × Position := t.ctx.fileMap.stxRange t.info.stx

/-- Pretty print a tactic. -/
def pp (t : TacticInvocation) : IO Format :=
  t.ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨t.info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

open Meta

/-- Run a tactic on the goals stored in a `TacticInvocation`. -/
def runMetaMGoalsBefore (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxBefore <| x t.info.goalsBefore

/-- Run a tactic on the after goals stored in a `TacticInvocation`. -/
def runMetaMGoalsAfter (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxAfter <| x t.info.goalsAfter

/-- Run a tactic on the main goal stored in a `TacticInvocation`. -/
def runMetaM (t : TacticInvocation) (x : MVarId → MetaM α) : IO α := do
  match t.info.goalsBefore.head? with
  | none => throw <| IO.userError s!"No goals at {← t.pp}"
  | some g => t.runMetaMGoalsBefore fun _ => do g.withContext <| x g

def mainGoal (t : TacticInvocation) : IO Expr :=
  t.runMetaM (fun g => do instantiateMVars (← g.getType))

def formatMainGoal (t : TacticInvocation) : IO Format :=
  t.runMetaM (fun g => do ppExpr (← instantiateMVars (← g.getType)))

def goalState (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsBefore (fun gs => gs.mapM fun g => do Meta.ppGoal g)

def goalStateAfter (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsAfter (fun gs => gs.mapM fun g => do Meta.ppGoal g)

def ppExpr (t : TacticInvocation) (e : Expr) : IO Format :=
  t.runMetaM (fun _ => do Meta.ppExpr (← instantiateMVars e))

end TacticInvocation

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def findAllInfo (t : Elab.InfoTree) (ctx : Option Elab.ContextInfo) (pred : Elab.Info → Bool) :
    List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  match t with
  | .context inner t => findAllInfo t (inner.mergeIntoOuter? ctx) pred
  | .node i children  =>
      (if pred i then [(i, ctx, children)] else []) ++ children.toList.bind (fun t => findAllInfo t ctx pred)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`, and any children info trees. -/
def collectTacticNodes (t : Elab.InfoTree) : List (Elab.TacticInfo × Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  let infos := findAllInfo t none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
    | (.ofTacticInfo i, some ctx, children) => (i, ctx, children)
    | _ => none

def collectTactics (t : Elab.InfoTree) : List TacticInvocation :=
  collectTacticNodes t |>.map (fun ⟨i, ctx, children⟩ => ⟨i, ctx, children⟩)
    |>.filter fun i => i.info.isSubstantive

def compileAndCollectTacticInvocations (module : Name) : IO Protocol.CompileTacticsResult := do
  let steps ← processSource module
  let infoTrees := steps.bind (·.trees)
  let tacticInfoTrees := infoTrees.bind λ tree => tree.filter λ
    | info@(.ofTacticInfo _) => true --info.isOriginal
    | _ => false
  let tactics := tacticInfoTrees.bind collectTactics
  IO.println s!"{steps.length} compilation steps, {infoTrees.length} trees found, {tacticInfoTrees.length} tactic trees, {tactics.length} tactics found"
  let invocations : List Protocol.InvokedTactic ← tactics.mapM λ invocation => do
    let goalBefore := (Format.joinSep (← invocation.goalState) "\n").pretty
    let goalAfter := (Format.joinSep (← invocation.goalStateAfter) "\n").pretty
    let tactic ← invocation.ctx.runMetaM {} do
      let t ← Lean.PrettyPrinter.ppTactic ⟨invocation.info.stx⟩
      return t.pretty
    return { goalBefore, goalAfter, tactic }
  return { invocations }


end Pantograph.Compile
