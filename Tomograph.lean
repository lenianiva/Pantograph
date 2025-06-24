import Pantograph.Frontend

open Lean

namespace Pantograph

def fail (s : String) : IO Unit := do
  IO.eprintln s

def dissect (args: List String): IO Unit := do
  let fileName :: _args := args | fail s!"Must supply a file name"
  let file ← IO.FS.readFile fileName
  let (context, state) ← do Frontend.createContextStateFromFile file fileName (env? := .none) {}
  let frontendM: Elab.Frontend.FrontendM _ :=
    Frontend.mapCompilationSteps λ step => do
      for tree in step.trees do
        IO.println s!"{← tree.toString}"
  let (_, _) ← frontendM.run context |>.run state
  return ()

end Pantograph

open Pantograph

def main (args : List String) : IO Unit := do
  let command :: args := args | IO.eprintln "Must supply a command"
  match command with
  | "dissect" => dissect args
  | _ => IO.eprintln s!"Unknown command {command}"
