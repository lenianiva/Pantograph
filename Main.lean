import Lean.Data.Json
import Lean.Environment

import Pantograph.Version
import Pantograph

-- Main IO functions
open Pantograph

unsafe def loop : Subroutine Unit := do
  let command ← (← IO.getStdin).getLine
  if command.trim.length = 0 then return ()
  match parse_command command with
  | .error error =>
    let error  := Lean.toJson ({ error := "json", desc := error }: Commands.InteractionError)
    IO.println (toString error)
  | .ok command =>
    let ret ← execute command
    IO.println <| toString <| ret
  loop

namespace Lean

/-- This is better than the default version since it handles `.` and doesn't
 crash the program when it fails. -/
def setOptionFromString' (opts : Options) (entry : String) : ExceptT String IO Options := do
  let ps := (entry.splitOn "=").map String.trim
  let [key, val] ← pure ps | throw "invalid configuration option entry, it must be of the form '<key> = <value>'"
  let key := Pantograph.str_to_name key
  let defValue ← getOptionDefaultValue key
  match defValue with
  | DataValue.ofString _ => pure $ opts.setString key val
  | DataValue.ofBool _   =>
    match val with
    | "true" => pure $ opts.setBool key true
    | "false" => pure $ opts.setBool key false
    | _ => throw  s!"invalid Bool option value '{val}'"
  | DataValue.ofName _   => pure $ opts.setName key val.toName
  | DataValue.ofNat _    =>
    match val.toNat? with
    | none   => throw s!"invalid Nat option value '{val}'"
    | some v => pure $ opts.setNat key v
  | DataValue.ofInt _    =>
    match val.toInt? with
    | none   => throw s!"invalid Int option value '{val}'"
    | some v => pure $ opts.setInt key v
  | DataValue.ofSyntax _ => throw s!"invalid Syntax option value"

end Lean


unsafe def main (args: List String): IO Unit := do
  -- NOTE: A more sophisticated scheme of command line argument handling is needed.
  -- Separate imports and options
  if args == ["--version"] then do
    println! s!"{version}"
    return

  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

  let options? ← args.filterMap (λ s => if s.startsWith "--" then .some <| s.drop 2 else .none)
    |>.foldlM Lean.setOptionFromString' Lean.Options.empty
    |>.run
  let options ← match options? with
    | .ok options => pure options
    | .error e => throw $ IO.userError s!"Options cannot be parsed: {e}"
  let imports:= args.filter (λ s => ¬ (s.startsWith "--"))

  let env ← Lean.importModules
    (imports := imports.map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  let context: Context := {
    imports
  }
  let coreContext: Lean.Core.Context := {
    currNamespace := Lean.Name.str .anonymous "Aniva"
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0], lines := #[1] },
    options := options
  }
  try
    let termElabM := loop.run context |>.run' {}
    let metaM := termElabM.run' (ctx := {
      declName? := some "_pantograph",
      errToSorry := false
    })
    let coreM := metaM.run'
    discard <| coreM.toIO coreContext { env := env }
  catch ex =>
    IO.println "Uncaught IO exception"
    IO.println ex.toString
