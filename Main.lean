import Lean.Data.Json
import Lean.Environment

import Pantograph.Commands
import Pantograph.IO
import Pantograph.Symbols

namespace Pantograph


structure Context where
  coreContext: Lean.Core.Context

/-- Stores state of the REPL -/
structure State where
  environments: Array Lean.Environment := #[]

-- State monad
abbrev Subroutine := ReaderT Context (StateT State IO)

def nextId (s: State): Nat := s.environments.size

def State.getEnv (state: State) (id: Nat): Except String Lean.Environment :=
  match state.environments.get? id with
  | .some env => return env
  | .none => throw s!"Invalid environment id {id}"


-- Utilities
def option_expect (o: Option α) (error: String): Except String α :=
  match o with
  | .some value => return value
  | .none => throw error


open Commands

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parse_command (s: String): Except String Command := do
  let s := s.trim
  match s.get? 0 with
  | .some '{' => -- Parse in Json mode
    Lean.fromJson? (← Lean.Json.parse s)
  | .some _ => -- Parse in line mode
    let offset := s.posOf ' ' |> s.offsetOfPos
    if offset = s.length then
      return { cmd := s.take offset, payload := Lean.Json.null }
    else
      let payload ← s.drop offset |> Lean.Json.parse
      return { cmd := s.take offset, payload := payload }
  | .none => throw "Command is empty"



unsafe def execute (command: Command): Subroutine Lean.Json := do
  match command.cmd with
  | "create" =>
    match Lean.fromJson? command.payload with
    | .ok args => create args
    | .error x => return errorJson x
  | "catalog" =>
    match Lean.fromJson? command.payload with
    | .ok args => catalog args
    | .error x => return errorJson x
  | "clear" =>
    -- Delete all the environments
    let ret ← clear
    return Lean.toJson ret
  | "inspect" =>
    match Lean.fromJson? command.payload with
    | .ok args => inspect args
    | .error x => return errorJson x
  | "proof.trace" =>
    match Lean.fromJson? command.payload with
    | .ok args => proof_trace args
    | .error x => return errorJson x
  | cmd =>
    let error: InteractionError := { error := "unknown", desc := s!"Unknown command {cmd}" }
      return Lean.toJson error
  where
  errorJson (s: String) := Lean.toJson ({ error := "json", desc := s }: InteractionError)
  errorIndex (s: String) := Lean.toJson ({ error := "index", desc := s }: InteractionError)
  create (args: Create): Subroutine Lean.Json := do
    let state ← get
    let id := nextId state
    let env ← Lean.importModules
      (imports := args.imports.map (λ str => { module := strToName str, runtimeOnly := false }))
      (opts := {})
      (trustLevel := 1)
    modify fun s => { environments := s.environments.push env }
    let num_filtered_symbols := env.constants.fold (init := 0) (λ acc name info =>
      acc + if is_symbol_unsafe_or_internal name info then 0 else 1)
    return Lean.toJson ({
      id := id,
      symbols := env.constants.size,
      filtered_symbols := num_filtered_symbols }: CreateResult)
  catalog (args: Catalog): Subroutine Lean.Json := do
    let state ← get
    match state.getEnv args.id with
    | .error error => return Lean.toJson <| errorIndex error
    | .ok env =>
      let names := env.constants.fold (init := []) (λ es name info =>
        match to_filtered_symbol name info with
        | .some x => x::es
        | .none => es)
      return Lean.toJson <| ({ theorems := names }: CatalogResult)
  clear: Subroutine Lean.Json := do
    let state ← get
    let nEnv := state.environments.size
    for env in state.environments do
      env.freeRegions
    set { state with environments := #[] }
    return Lean.toJson ({ nEnv := nEnv }: ClearResult)
  inspect (args: Inspect): Subroutine Lean.Json := do
    let context ← read
    let state ← get
    match state.getEnv args.id with
    | .error error => return Lean.toJson <| errorIndex error
    | .ok env =>
      let info? := env.find? <| strToName args.symbol
      match info? with
      | none => return Lean.toJson <| errorIndex s!"Symbol not found {args.symbol}"
      | some info =>
        let format ← IO.exprToStr
          (env := env)
          (coreContext := context.coreContext)
          (expr := info.toConstantVal.type)
        return Lean.toJson ({ type := format }: InspectResult)
  proof_trace (args: ProofTrace): Subroutine Lean.Json := do
    -- Step 1: Create tactic state
    -- Step 2: Execute tactic
    -- Step 3: ??
    return Lean.toJson ({ expr := "test" }: ProofTraceResult)


end Pantograph

open Pantograph



-- Main IO functions

unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

unsafe def loop : Subroutine Unit := do
  let command ← (← IO.getStdin).getLine
  match parse_command command with
  | .error _ =>
    -- Halt execution if command is empty
    return ()
  | .ok command =>
    let ret ← execute command
    IO.println <| toString <| ret
  loop

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let context: Context := {
    coreContext := {
      currNamespace := strToName "Aniva",
      openDecls := [],     -- No 'open' directives needed
      fileName := "<Pantograph>",
      fileMap := { source := "", positions := #[0], lines := #[1] }
    }
  }
  loop.run context |>.run' {}
