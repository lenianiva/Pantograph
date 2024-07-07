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
  let msgs := s'.messages.toList.drop s.messages.toList.length
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


end Pantograph.Compile
