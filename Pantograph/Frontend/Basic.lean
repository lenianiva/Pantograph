import Lean.Parser
import Lean.Elab.Frontend

open Lean

namespace Lean.FileMap

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
@[export pantograph_frontend_stx_range]
protected def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.FileMap
namespace Lean.PersistentArray

/--
Drop the first `n` elements of a `PersistentArray`, returning the results as a `List`.
-/
-- We can't remove the `[Inhabited α]` hypotheses here until
-- `PersistentArray`'s `GetElem` instance also does.
protected def drop [Inhabited α] (t : PersistentArray α) (n : Nat) : List α :=
  List.range (t.size - n) |>.map fun i => t.get! (n + i)

end Lean.PersistentArray


namespace Pantograph.Frontend

@[export pantograph_frontend_stx_byte_range]
def stxByteRange (stx : Syntax) : String.Pos × String.Pos :=
  let pos := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD 0
  (pos, endPos)


abbrev FrontendM := Elab.Frontend.FrontendM

structure CompilationStep where
  fileName : String
  fileMap : FileMap
  src : Substring
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List Elab.InfoTree

namespace CompilationStep

@[export pantograph_frontend_compilation_step_message_strings_m]
def messageStrings (step: CompilationStep) : IO (Array String) := do
  List.toArray <$> step.msgs.mapM (·.toString)

end CompilationStep


/--
Process one command, returning a `CompilationStep` and
`done : Bool`, indicating whether this was the last command.
-/
@[export pantograph_frontend_process_one_command_m]
def processOneCommand: FrontendM (CompilationStep × Bool) := do
  let s := (← get).commandState
  let before := s.env
  let done ← Elab.Frontend.processCommand
  let stx := (← get).commands.back
  let src := (← read).inputCtx.input.toSubstring.extract (← get).cmdPos (← get).parserState.pos
  let s' := (← get).commandState
  let after := s'.env
  let msgs := s'.messages.toList.drop s.messages.toList.length
  let trees := s'.infoState.trees.drop s.infoState.trees.size
  let ⟨_, fileName, fileMap⟩  := (← read).inputCtx
  return ({ fileName, fileMap, src, stx, before, after, msgs, trees }, done)

partial def mapCompilationSteps { α } (f: CompilationStep → IO α) : FrontendM (List α) := do
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

  let (env, parserState, messages) ← match env? with
    | .some env => pure (env, {}, .empty)
    | .none =>
      let (header, parserState, messages) ← Parser.parseHeader inputCtx
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
