import Lean.Parser
import Lean.Elab.Frontend

open Lean

namespace Lean.FileMap

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
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

partial def collectCompilationSteps : FrontendM (List CompilationStep) := do
  let (cmd, done) ← processOneCommand
  if done then
    return [cmd]
  else
    return cmd :: (← collectCompilationSteps)

def findSourcePath (module : Name) : IO System.FilePath := do
  return System.FilePath.mk ((← findOLean module).toString.replace ".lake/build/lib/" "") |>.withExtension "lean"

@[export pantograph_create_frontend_context_state_from_file_m]
unsafe def createFrontendContextStateFromFile (module : Name) (opts : Options := {})
  : IO (Elab.Frontend.Context × Elab.Frontend.State) := do
  let file ← IO.FS.readFile (← findSourcePath module)
  let inputCtx := Parser.mkInputContext file module.toString

  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header opts messages inputCtx
  let commandState := Elab.Command.mkState env messages opts
  let context: Elab.Frontend.Context := { inputCtx }
  let state: Elab.Frontend.State := {
    commandState := { commandState with infoState.enabled := true },
    parserState,
    cmdPos := parserState.pos
  }
  return (context, state)

partial def mapCompilationSteps { α } (f: CompilationStep → IO α) : FrontendM (List α) := do
  let (cmd, done) ← processOneCommand
  let result ← f cmd
  if done then
    return [result]
  else
    return result :: (← mapCompilationSteps f)

def runFrontendMInFile { α } (module : Name) (opts : Options := {}) (m : FrontendM α): IO α := unsafe do
  let (context, state) ← createFrontendContextStateFromFile module opts
  m.run context |>.run' state



end Pantograph.Frontend
