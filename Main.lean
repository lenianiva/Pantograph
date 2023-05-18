import Lean.Data.Json
import Lean.Environment

import Pantograph.Commands
import Pantograph.Symbols

namespace Pantograph

-- Utilities
def option_expect (o: Option α) (error: String): Except String α :=
  match o with
  | .some value => return value
  | .none => throw error


structure State where
  environments: Array Lean.Environment

-- State monad
abbrev T (m: Type → Type) := StateT State m
abbrev Subroutine α := ExceptT String (T IO) α

def nextId (s: State): Nat := s.environments.size

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

open Commands

unsafe def execute (command: String): ExceptT String (T IO) Lean.Json := do
  let obj ← Lean.Json.parse command
  let command: Command ← Lean.fromJson? obj
  match command.cmd with
  | "create" =>
    let args: Commands.Create ← Lean.fromJson? command.payload
    let ret ← create args
    return Lean.toJson ret
  | "catalog" =>
    let args: Commands.Catalog ← Lean.fromJson? command.payload
    let ret ← catalog args
    return Lean.toJson ret
  | "clear" =>
    -- Delete all the environments
    let ret ← clear
    return Lean.toJson ret
  | "proof.trace" =>
    let args: Commands.ProofTrace ← Lean.fromJson? command.payload
    let ret ← proof_trace args
    return Lean.toJson ret
  | cmd => throw s!"Unknown verb: {cmd}"
  where
  create (args: Create): Subroutine CreateResult := do
    let state ← get
    let id := nextId state
    let env ← Lean.importModules
      (imports := args.imports.map (λ str => { module := strToName str, runtimeOnly := false }))
      (opts := {})
      (trustLevel := 1)
    modify fun s => { environments := s.environments.push env }
    let num_filtered_symbols := env.constants.fold (init := 0) (λ acc name info =>
      acc + if is_symbol_unsafe_or_internal name info then 0 else 1)
    return {
      id := id,
      symbols := env.constants.size,
      filtered_symbols := num_filtered_symbols }
  catalog (args: Catalog): Subroutine CatalogResult := do
    let state ← get
    match state.environments.get? args.id with
    | .some env =>
      let names := env.constants.fold (init := []) (λ es name info =>
        match to_filtered_symbol name info with
        | .some x => x::es
        | .none => es)
      return { theorems := names }
    | .none => throw s!"Invalid environment id {args.id}"
  clear: Subroutine ClearResult := do
    let state ← get
    for env in state.environments do
      env.freeRegions
    return { n := state.environments.size }
  proof_trace (args: ProofTrace): Subroutine ProofTraceResult := do
    -- Step 1: Create tactic state
    -- Step 2: Execute tactic
    -- Step 3: ??
    return { expr := "test" }


end Pantograph

open Pantograph



-- Main IO functions

unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

unsafe def loop : T IO Unit := do
  let command ← getLines
  if command == "" then return ()
  let ret ← execute command
  match ret with
  | .error e => IO.println s!"Error: {e}"
  | .ok obj => IO.println <| toString <| obj
  loop

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  StateT.run' loop ⟨#[]⟩
