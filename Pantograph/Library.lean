import Pantograph.Environment
import Pantograph.Goal
import Pantograph.Protocol
import Pantograph.Version
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

def runMetaM { α } (metaM: Lean.MetaM α): Lean.CoreM α :=
  metaM.run'
def runTermElabM { α } (termElabM: Lean.Elab.TermElabM α): Lean.CoreM α :=
  termElabM.run' (ctx := {
    declName? := .none,
    errToSorry := false,
  }) |>.run'

def errorI (type desc: String): Protocol.InteractionError := { error := type, desc := desc }
def errorCommand := errorI "command"
def errorIndex := errorI "index"

@[export pantograph_version]
def pantographVersion: String := version

/-- Adds the given paths to Lean package search path -/
@[export pantograph_init_search]
unsafe def initSearch (sp: String): IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot) (sp := System.SearchPath.parse sp)

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

/-- Creates a Core.State object needed to run all monads -/
@[export pantograph_create_core_state]
def createCoreState (imports: Array String): IO Lean.Core.State := do
  let env ← Lean.importModules
    (imports := imports.map (λ str => { module := str.toName, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  return { env := env }

/-- Execute a `CoreM` monad -/
@[export pantograph_exec_core]
def execCore {α} (context: Lean.Core.Context) (state: Lean.Core.State) (coreM: Lean.CoreM α): IO (α × Lean.Core.State) :=
  coreM.toIO context state

@[export pantograph_env_catalog]
def envCatalog: Lean.CoreM Protocol.EnvCatalogResult :=
  Environment.catalog ({}: Protocol.EnvCatalog)

@[export pantograph_env_inspect]
def envInspect (cc: Lean.Core.Context) (cs: Lean.Core.State)
    (name: String) (value: Bool) (dependency: Bool) (options: Protocol.Options): IO (Protocol.CR Protocol.EnvInspectResult) := do
  let coreM: Lean.CoreM _ := Environment.inspect ({
    name, value? := .some value, dependency?:= .some dependency
  }: Protocol.EnvInspect) options
  let (result, _) ← coreM.toIO cc cs
  return result

@[export pantograph_env_add]
def envAdd (cc: Lean.Core.Context) (cs: Lean.Core.State)
  (name: String) (type: String) (value: String) (isTheorem: Bool): IO (Protocol.CR Protocol.EnvAddResult) := do
  let coreM: Lean.CoreM _ := Environment.addDecl { name, type, value, isTheorem }
  let (result, _) ← coreM.toIO cc cs
  return result

@[export pantograph_expr_parse]
def exprParse (s: String): Lean.CoreM (Protocol.CR Lean.Expr) := do
  let env ← Lean.MonadEnv.getEnv
  let syn ← match syntax_from_str env s with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => pure syn
  runTermElabM (do
    match ← syntax_to_expr syn with
    | .error str => return .error $ errorI "elab" str
    | .ok expr => return .ok expr)

@[export pantograph_expr_print]
def exprPrint (expr: Lean.Expr) (options: @&Protocol.Options): Lean.CoreM (Protocol.CR Protocol.ExprEchoResult) := do
  let termElabM: Lean.Elab.TermElabM _ :=
      try
        let type ← Lean.Meta.inferType expr
        return .ok {
            type := (← serialize_expression options type),
            expr := (← serialize_expression options expr)
        }
      catch exception =>
        return .error $ errorI "typing" (← exception.toMessageData.toString)
  runTermElabM termElabM

@[export pantograph_goal_start]
def goalStart (expr: Lean.Expr): Lean.CoreM GoalState :=
  runTermElabM (GoalState.create expr)

end Pantograph
