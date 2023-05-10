import Lean.Data.Json
import Pantograph.Commands


namespace Pantograph

structure State where
  environments: Array String

-- State monad
abbrev T (m: Type → Type) := StateT State m
abbrev Subroutine := T (Except String) Lean.Json

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

--def create_environment (args: Create): Subroutine := do
--  let state ← get


end Pantograph

open Pantograph

def execute (command: String): T (ExceptT String IO) Lean.Json := do
  let state ← get
  let obj ← Lean.Json.parse command
  let command: Command ← Lean.fromJson? obj
  match command.cmd with
  | "create" =>
    let create: Commands.Create ← Lean.fromJson? command.payload
    return Lean.toJson create.imports
  | "catalog" =>
    let catalog: Commands.Catalog ← Lean.fromJson? command.payload
    return "catalog stub"
  | cmd => throw s!"Unknown verb: {cmd}"

-- Main IO functions

unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

unsafe def loop : T IO Unit := do
  let state ← get
  let command ← getLines
  if command == "" then return ()
  let ret ← execute command
  match ret with
  | .error e => IO.println s!"Could not parse json: {e}"
  | .ok obj => IO.println <| toString <| obj

unsafe def main : IO Unit :=
  StateT.run' loop ⟨#[]⟩
