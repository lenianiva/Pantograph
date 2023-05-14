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

namespace Commands

def create (args: Create): Subroutine CreateResult := do
  let state ← get
  let id := nextId state
  let env ← Lean.importModules
    (imports := args.imports.map strTransform)
    (opts := {})
    (trustLevel := 1)
  modify fun s => { environments := s.environments.push env }
  let num_filtered_symbols := env.constants.fold (init := 0) (λ acc name info =>
    acc + if is_symbol_unsafe_or_internal name info then 0 else 1)
  return {
    id := id,
    symbols := env.constants.size,
    filtered_symbols := num_filtered_symbols }
  where strTransform (s: String): Lean.Import :=
      let li := s.split (λ c => c == '.')
      let name := li.foldl (λ pre segment => Lean.Name.str pre segment) Lean.Name.anonymous
      { module := name, runtimeOnly := false }

def catalog (args: Catalog): Subroutine CatalogResult := do
  let state ← get
  match state.environments.get? args.id with
  | .some env =>
    let names := env.constants.fold (init := []) (λ es name info =>
      match to_filtered_symbol name info with
      | .some x => x::es
      | .none => es)
    return { theorems := names }
  | .none => throw s!"Invalid environment id {args.id}"

unsafe def clear: Subroutine ClearResult := do
  let state ← get
  for env in state.environments do
    env.freeRegions
  return { n := state.environments.size }

end Commands
end Pantograph

open Pantograph

unsafe def execute (command: String): ExceptT String (T IO) Lean.Json := do
  let obj ← Lean.Json.parse command
  let command: Command ← Lean.fromJson? obj
  match command.cmd with
  | "create" =>
    let args: Commands.Create ← Lean.fromJson? command.payload
    let ret ← Commands.create args
    return Lean.toJson ret
  | "catalog" =>
    let args: Commands.Catalog ← Lean.fromJson? command.payload
    let ret ← Commands.catalog args
    return Lean.toJson ret
  | "clear" =>
    -- Delete all the environments
    let ret ← Commands.clear
    return Lean.toJson ret
  | cmd => throw s!"Unknown verb: {cmd}"


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
