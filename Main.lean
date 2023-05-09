import Pantograph
import Lean.Data.Json


namespace Pantograph

structure State where
  keys: Array String

-- State monad
abbrev T (m: Type → Type) := StateT State m

end Pantograph

open Pantograph


def execute (command: String): T (Except String) Lean.Json := do
  let state ← get
  let obj ← Lean.Json.parse command
  return "success"

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
  match (execute command).run' <| state with
  | .error e => IO.println s!"Could not parse json: {e}"
  | .ok obj => IO.println <| toString <| obj

unsafe def main : IO Unit :=
  StateT.run' loop ⟨#[]⟩
