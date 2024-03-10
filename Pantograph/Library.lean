import Pantograph.Version
import Pantograph.Environment
import Pantograph.Protocol
import Lean


namespace Lean

/-- This is better than the default version since it handles `.` and doesn't
 crash the program when it fails. -/
def setOptionFromString' (opts : Options) (entry : String) : ExceptT String IO Options := do
  let ps := (entry.splitOn "=").map String.trim
  let [key, val] ← pure ps | throw "invalid configuration option entry, it must be of the form '<key> = <value>'"
  let key := key.toName
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

namespace Pantograph

@[export pantograph_version]
def pantographVersion: String := version

/-- Creates a Core.Context object needed to run all monads -/
@[export pantograph_create_core_context]
def createCoreContext (options: Array String): IO Lean.Core.Context := do
  let options? ← options.foldlM Lean.setOptionFromString' Lean.Options.empty |>.run
  let options ← match options? with
    | .ok options => pure options
    | .error e => throw $ IO.userError s!"Options cannot be parsed: {e}"
  return {
    currNamespace := Lean.Name.str .anonymous "Aniva"
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0], lines := #[1] },
    options := options
  }

@[export pantograph_create_core_state]
def createCoreState (imports: Array String): IO Lean.Core.State := do
  let env ← Lean.importModules
    (imports := imports.map (λ str => { module := str.toName, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  return { env := env }

@[export pantograph_catalog]
def catalog (cc: Lean.Core.Context) (cs: Lean.Core.State): IO Protocol.EnvCatalogResult := do
  let coreM: Lean.CoreM _ := Environment.catalog ({}: Protocol.EnvCatalog)
  let (result, _) ← coreM.toIO cc cs
  return result

end Pantograph
