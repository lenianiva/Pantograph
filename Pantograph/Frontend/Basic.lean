import Lean.Parser
import Lean.Elab.Frontend

open Lean

namespace Lean.FileMap

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
@[export pantograph_frontend_stx_range]
protected def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.FileMap
namespace Lean.PersistentArray

/--
Drop the first `n` elements of a `PersistentArray`, returning the results as a `List`.

We can't remove the `[Inhabited α]` hypotheses here until
`PersistentArray`'s `GetElem` instance also does.
-/
protected def drop [Inhabited α] (t : PersistentArray α) (n : Nat) : List α :=
  List.range (t.size - n) |>.map fun i => t.get! (n + i)

end Lean.PersistentArray


namespace Pantograph.Frontend

@[export pantograph_frontend_stx_byte_range]
def stxByteRange (stx : Syntax) : String.Pos × String.Pos :=
  let pos := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD 0
  (pos, endPos)

structure Context where
  cancelTk? : Option IO.CancelToken := .none

/-- This `FrontendM` comes with more options. -/
abbrev FrontendM := ReaderT Context Elab.Frontend.FrontendM

structure CompilationStep where
  scope : Elab.Command.Scope
  fileName : String
  fileMap : FileMap
  src : Substring
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List Elab.InfoTree

/-- Like `Elab.Frontend.runCommandElabM`, but taking `cancelTk?` into account. -/
@[inline] def runCommandElabM (x : Elab.Command.CommandElabM α) : FrontendM α := do
  let config ← read
  let ctx ← readThe Elab.Frontend.Context
  let s ← get
  let cmdCtx : Elab.Command.Context := {
    cmdPos       := s.cmdPos
    fileName     := ctx.inputCtx.fileName
    fileMap      := ctx.inputCtx.fileMap
    snap?        := none
    cancelTk?    := config.cancelTk?
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run s.commandState) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, sNew) => Elab.Frontend.setCommandState sNew; return a

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM do
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    Elab.Command.elabCommandTopLevel stx
    let mut msgs := (← get).messages
    modify ({ · with messages := initMsgs ++ msgs })

open Elab.Frontend in
def processCommand : FrontendM Bool := do
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  match profileit "parsing" scope.opts fun _ => Parser.parseCommand ictx pmctx pstate cmdState.messages with
  | (cmd, ps, messages) =>
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    elabCommandAtFrontend cmd
    pure (Parser.isTerminalCommand cmd)

/--
Process one command, returning a `CompilationStep` and
`done : Bool`, indicating whether this was the last command.
-/
@[export pantograph_frontend_process_one_command_m]
def processOneCommand: FrontendM (CompilationStep × Bool) := do
  let s := (← get).commandState
  let before := s.env
  let done ← processCommand
  let stx := (← get).commands.back!
  let src := (← readThe Elab.Frontend.Context).inputCtx.input.toSubstring.extract
    (← get).cmdPos
    (← get).parserState.pos
  let s' := (← get).commandState
  let after := s'.env
  let msgs := s'.messages.toList.drop s.messages.toList.length
  let trees := s'.infoState.trees.drop s.infoState.trees.size
  let ⟨_, fileName, fileMap⟩  := (← readThe Elab.Frontend.Context).inputCtx
  return ({ scope := s.scopes.head!, fileName, fileMap, src, stx, before, after, msgs, trees }, done)

partial def mapCompilationSteps { α } (f: CompilationStep → FrontendM α) : FrontendM (List α) := do
  let (cmd, done) ← processOneCommand
  if done then
    if cmd.src.isEmpty then
      return []
    else
      return [← f cmd]
  else
    return (← f cmd) :: (← mapCompilationSteps f)


@[export pantograph_frontend_find_source_path_m]
def findSourcePath (module : Name) : IO System.FilePath := do
  return System.FilePath.mk ((← findOLean module).toString.replace ".lake/build/lib/" "") |>.withExtension "lean"

/--
Use with
```lean
let m: FrontendM α := ...
let (context, state) ← createContextStateFromFile ...
m.run context |>.run' state
```
-/
@[export pantograph_frontend_create_context_state_from_file_m]
def createContextStateFromFile
    (file : String) -- Content of the file
    (fileName : String := "<anonymous>")
    (env? : Option Lean.Environment := .none) -- If set to true, assume there's no header.
    (opts : Options := {})
    : IO (Elab.Frontend.Context × Elab.Frontend.State) := unsafe do
  --let file ← IO.FS.readFile (← findSourcePath module)
  let inputCtx := Parser.mkInputContext file fileName

  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, parserState, messages) ← match env? with
    | .some env => pure (env, {}, .empty)
    | .none =>
      -- Only process the header if we don't have an environment.
      let (env, messages) ← Elab.processHeader header opts messages inputCtx
      pure (env, parserState, messages)
  let commandState := Elab.Command.mkState env messages opts
  let context: Elab.Frontend.Context := { inputCtx }
  let state: Elab.Frontend.State := {
    commandState := { commandState with infoState.enabled := true },
    parserState,
    cmdPos := parserState.pos
  }
  return (context, state)

end Pantograph.Frontend
