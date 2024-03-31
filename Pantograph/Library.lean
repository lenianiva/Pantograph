import Pantograph.Environment
import Pantograph.Goal
import Pantograph.Protocol
import Pantograph.Serial
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
    fileMap := { source := "", positions := #[0] },
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

@[export pantograph_env_catalog_m]
def envCatalog: Lean.CoreM Protocol.EnvCatalogResult :=
  Environment.catalog ({}: Protocol.EnvCatalog)

@[export pantograph_mk_options]
def mkOptions
  (printJsonPretty: Bool)
  (printExprPretty: Bool)
  (printExprAST: Bool)
  (noRepeat: Bool)
  (printAuxDecls: Bool)
  (printImplementationDetailHyps: Bool)
  : Protocol.Options := {
    printJsonPretty,
    printExprPretty,
    printExprAST,
    noRepeat,
    printAuxDecls,
    printImplementationDetailHyps,
  }

@[export pantograph_env_inspect_m]
def envInspect (name: String) (value: Bool) (dependency: Bool) (options: @&Protocol.Options):
    Lean.CoreM (Protocol.CR Protocol.EnvInspectResult) :=
  Environment.inspect ({
    name, value? := .some value, dependency?:= .some dependency
  }: Protocol.EnvInspect) options

@[export pantograph_env_add_m]
def envAdd (name: String) (type: String) (value: String) (isTheorem: Bool):
    Lean.CoreM (Protocol.CR Protocol.EnvAddResult) :=
  Environment.addDecl { name, type, value, isTheorem }

def parseElabType (type: String): Lean.Elab.TermElabM (Protocol.CR Lean.Expr) := do
  let env ← Lean.MonadEnv.getEnv
  let syn ← match parseTerm env type with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => pure syn
  match ← elabType syn with
  | .error str => return .error $ errorI "elab" str
  | .ok expr => return .ok expr

/-- This must be a TermElabM since the parsed expr contains extra information -/
def parseElabExpr (expr: String) (expectedType?: Option String := .none): Lean.Elab.TermElabM (Protocol.CR Lean.Expr) := do
  let env ← Lean.MonadEnv.getEnv
  let expectedType? ← match ← expectedType?.mapM parseElabType with
    | .none => pure $ .none
    | .some (.ok t) => pure $ .some t
    | .some (.error e) => return .error e
  let syn ← match parseTerm env expr with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => pure syn
  match ← elabTerm syn expectedType? with
  | .error str => return .error $ errorI "elab" str
  | .ok expr => return .ok expr

@[export pantograph_expr_echo_m]
def exprEcho (expr: String) (expectedType?: Option String := .none) (options: @&Protocol.Options):
    Lean.CoreM (Protocol.CR Protocol.ExprEchoResult) := do
  let termElabM: Lean.Elab.TermElabM _ := do
    let expr ← match ← parseElabExpr expr expectedType? with
      | .error e => return .error e
      | .ok expr => pure expr
    try
      let type ← instantiateAll (← Lean.Meta.inferType expr)
      return .ok {
          type := (← serialize_expression options type),
          expr := (← serialize_expression options expr)
      }
    catch exception =>
      return .error $ errorI "typing" (← exception.toMessageData.toString)
  runTermElabM termElabM

@[export pantograph_goal_start_expr_m]
def goalStartExpr (expr: String): Lean.CoreM (Protocol.CR GoalState) :=
  let termElabM: Lean.Elab.TermElabM _ := do
    let expr ← match ← parseElabType expr with
      | .error e => return .error e
      | .ok expr => pure $ expr
    return .ok $ ← GoalState.create expr
  runTermElabM termElabM

@[export pantograph_goal_tactic_m]
def goalTactic (state: GoalState) (goalId: Nat) (tactic: String): Lean.CoreM TacticResult :=
  runTermElabM <| GoalState.execute state goalId tactic

@[export pantograph_goal_try_assign_m]
def goalTryAssign (state: GoalState) (goalId: Nat) (expr: String): Lean.CoreM TacticResult :=
  runTermElabM <| GoalState.tryAssign state goalId expr

@[export pantograph_goal_continue]
def goalContinue (target: GoalState) (branch: GoalState): Except String GoalState :=
  target.continue branch

@[export pantograph_goal_resume]
def goalResume (target: GoalState) (goals: Array String): Except String GoalState :=
  target.resume (goals.map (λ n => { name := n.toName }) |>.toList)

@[export pantograph_goal_serialize_m]
def goalSerialize (state: GoalState) (options: @&Protocol.Options): Lean.CoreM (Array Protocol.Goal) :=
  runMetaM <| state.serializeGoals (parent := .none) options

@[export pantograph_goal_print_m]
def goalPrint (state: GoalState) (options: @&Protocol.Options): Lean.CoreM Protocol.GoalPrintResult := do
  let metaM := do
    state.restoreMetaM
    return {
      root? := ← state.rootExpr?.mapM (λ expr => do
        serialize_expression options (← instantiateAll expr)),
      parent? := ← state.parentExpr?.mapM (λ expr => do
        serialize_expression options (← instantiateAll expr)),
    }
  runMetaM metaM


end Pantograph
