import Lean.Data.Json
import Lean.Environment

import Pantograph
import Repl

-- Main IO functions
open Pantograph.Repl
open Pantograph.Protocol

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parseCommand (s: String): Except String Command := do
  match s.trim.get? 0 with
  | .some '{' =>
    -- Parse in Json mode
    Lean.fromJson? (← Lean.Json.parse s)
  | .some _ =>
    -- Parse in line mode
    let offset := s.posOf ' ' |> s.offsetOfPos
    if offset = s.length then
      return { cmd := s.take offset, payload := Lean.Json.null }
    else
      let payload ← s.drop offset |> Lean.Json.parse
      return { cmd := s.take offset, payload := payload }
  | .none =>
    throw "Command is empty"

partial def loop : MainM Unit := do repeat do
  let state ← get
  let command ← (← IO.getStdin).getLine
  -- Halt the program if empty line is given
  if command.trim.length = 0 then break
  match parseCommand command with
  | .error error =>
    let error  := Lean.toJson ({ error := "command", desc := error }: InteractionError)
    -- Using `Lean.Json.compress` here to prevent newline
    IO.println error.compress
  | .ok command =>
    try
      let ret ← execute command
      let str := match state.options.printJsonPretty with
        | true => ret.pretty
        | false => ret.compress
      IO.println str
    catch e =>
      let message ← e.toMessageData.toString
      let error  := Lean.toJson ({ error := "main", desc := message }: InteractionError)
      IO.println error.compress


unsafe def main (args: List String): IO Unit := do
  -- NOTE: A more sophisticated scheme of command line argument handling is needed.
  if args == ["--version"] then do
    IO.println s!"{Pantograph.version}"
    return

  Pantograph.initSearch ""

  -- Separate imports and options
  let (options, imports) := args.partition (·.startsWith "--")
  let coreContext ← options.map (·.drop 2) |>.toArray |> Pantograph.createCoreContext
  let coreState ← Pantograph.createCoreState imports.toArray
  let context: Context := {}
  try
    let coreM := loop.run context |>.run' {}
    IO.println "ready."
    discard <| coreM.toIO coreContext coreState
  catch ex =>
    let message := ex.toString
    let error  := Lean.toJson ({ error := "io", desc := message }: InteractionError)
    IO.println error.compress
