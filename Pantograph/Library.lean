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

open Lean

namespace Pantograph

def defaultTermElabMContext: Elab.Term.Context := {
    errToSorry := false
  }
def runMetaM { α } (metaM: MetaM α): CoreM α :=
  metaM.run'
def runTermElabM { α } (termElabM: Elab.TermElabM α): CoreM α :=
  termElabM.run' (ctx := defaultTermElabMContext) |>.run'

def errorI (type desc: String): Protocol.InteractionError := { error := type, desc := desc }

/-- Adds the given paths to Lean package search path -/
@[export pantograph_init_search]
unsafe def initSearch (sp: String): IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot) (sp := System.SearchPath.parse sp)

/-- Creates a Core.Context object needed to run all monads -/
@[export pantograph_create_core_context]
def createCoreContext (options: Array String): IO Core.Context := do
  let options? ← options.foldlM setOptionFromString' Options.empty |>.run
  let options ← match options? with
    | .ok options => pure options
    | .error e => throw $ IO.userError s!"Options cannot be parsed: {e}"
  return {
    currNamespace := Name.str .anonymous "Aniva"
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0] },
    options := options
  }

/-- Creates a Core.State object needed to run all monads -/
@[export pantograph_create_core_state]
def createCoreState (imports: Array String): IO Core.State := do
  let env ← Lean.importModules
    (imports := imports.map (λ str => { module := str.toName, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  return { env := env }

@[export pantograph_create_meta_context]
def createMetaContext: IO Lean.Meta.Context := do
  return {}

@[export pantograph_env_catalog_m]
def envCatalog: CoreM Protocol.EnvCatalogResult :=
  Environment.catalog ({}: Protocol.EnvCatalog)

@[export pantograph_env_inspect_m]
def envInspect (name: String) (value: Bool) (dependency: Bool) (options: @&Protocol.Options):
    CoreM (Protocol.CR Protocol.EnvInspectResult) :=
  Environment.inspect ({
    name, value? := .some value, dependency?:= .some dependency
  }: Protocol.EnvInspect) options

@[export pantograph_env_add_m]
def envAdd (name: String) (type: String) (value: String) (isTheorem: Bool):
    CoreM (Protocol.CR Protocol.EnvAddResult) :=
  Environment.addDecl { name, type, value, isTheorem }

def parseElabType (type: String): Elab.TermElabM (Protocol.CR Expr) := do
  let env ← MonadEnv.getEnv
  let syn ← match parseTerm env type with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => pure syn
  match ← elabType syn with
  | .error str => return .error $ errorI "elab" str
  | .ok expr => return .ok (← instantiateMVars expr)

/-- This must be a TermElabM since the parsed expr contains extra information -/
def parseElabExpr (expr: String) (expectedType?: Option String := .none): Elab.TermElabM (Protocol.CR Expr) := do
  let env ← MonadEnv.getEnv
  let expectedType? ← match ← expectedType?.mapM parseElabType with
    | .none => pure $ .none
    | .some (.ok t) => pure $ .some t
    | .some (.error e) => return .error e
  let syn ← match parseTerm env expr with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => pure syn
  match ← elabTerm syn expectedType? with
  | .error str => return .error $ errorI "elab" str
  | .ok expr => return .ok (← instantiateMVars expr)

@[export pantograph_expr_echo_m]
def exprEcho (expr: String) (expectedType?: Option String := .none) (levels: Array String := #[])  (options: @&Protocol.Options := {}):
    CoreM (Protocol.CR Protocol.ExprEchoResult) :=
  runTermElabM $ Elab.Term.withLevelNames (levels.toList.map (·.toName)) do
    let expr ← match ← parseElabExpr expr expectedType? with
      | .error e => return .error e
      | .ok expr => pure expr
    try
      let type ← unfoldAuxLemmas (← Meta.inferType expr)
      return .ok {
          type := (← serializeExpression options type),
          expr := (← serializeExpression options expr)
      }
    catch exception =>
      return .error $ errorI "typing" (← exception.toMessageData.toString)

@[export pantograph_goal_start_expr_m]
def goalStartExpr (expr: String) (levels: Array String): CoreM (Protocol.CR GoalState) :=
  runTermElabM $ Elab.Term.withLevelNames (levels.toList.map (·.toName)) do
    let expr ← match ← parseElabType expr with
      | .error e => return .error e
      | .ok expr => pure $ expr
    return .ok $ ← GoalState.create expr

@[export pantograph_goal_resume]
def goalResume (target: GoalState) (goals: Array String): Except String GoalState :=
  target.resume (goals.map (λ n => { name := n.toName }) |>.toList)

@[export pantograph_goal_continue]
def goalContinue (target: GoalState) (branch: GoalState): Except String GoalState :=
  target.continue branch

@[export pantograph_goal_serialize_m]
def goalSerialize (state: GoalState) (options: @&Protocol.Options): CoreM (Array Protocol.Goal) :=
  runMetaM <| state.serializeGoals (parent := .none) options

@[export pantograph_goal_print_m]
def goalPrint (state: GoalState) (options: @&Protocol.Options): CoreM Protocol.GoalPrintResult :=
  runMetaM do
    state.restoreMetaM
    return {
      root? := ← state.rootExpr?.mapM (λ expr =>
        state.withRootContext do
          serializeExpression options (← instantiateAll expr)),
      parent? := ← state.parentExpr?.mapM (λ expr =>
        state.withParentContext do
          serializeExpression options (← instantiateAll expr)),
    }
@[export pantograph_goal_diag_m]
def goalDiag (state: GoalState) (diagOptions: Protocol.GoalDiag) : CoreM String :=
  runMetaM $ state.diag diagOptions

@[export pantograph_goal_tactic_m]
def goalTactic (state: GoalState) (goalId: Nat) (tactic: String): CoreM TacticResult :=
  runTermElabM <| state.tryTactic goalId tactic
@[export pantograph_goal_assign_m]
def goalAssign (state: GoalState) (goalId: Nat) (expr: String): CoreM TacticResult :=
  runTermElabM <| state.tryAssign goalId expr
@[export pantograph_goal_have_m]
protected def GoalState.tryHave (state: GoalState) (goalId: Nat) (binderName: String) (type: String): CoreM TacticResult := do
  let type ← match (← Compile.parseTermM type) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  runTermElabM do
    state.restoreElabM
    state.execute goalId (Tactic.«have» binderName.toName type)
@[export pantograph_goal_evaluate_m]
protected def GoalState.tryEvaluate (state: GoalState) (goalId: Nat) (binderName: String) (type: String): CoreM TacticResult := do
  let type ← match (← Compile.parseTermM type) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  runTermElabM do
    state.restoreElabM
    state.execute goalId (Tactic.evaluate binderName.toName type)
@[export pantograph_goal_let_m]
def goalLet (state: GoalState) (goalId: Nat) (binderName: String) (type: String): CoreM TacticResult :=
  runTermElabM <| state.tryLet goalId binderName type
@[export pantograph_goal_conv_m]
def goalConv (state: GoalState) (goalId: Nat): CoreM TacticResult :=
  runTermElabM <| state.conv goalId
@[export pantograph_goal_conv_exit_m]
def goalConvExit (state: GoalState): CoreM TacticResult :=
  runTermElabM <| state.convExit
@[export pantograph_goal_calc_m]
def goalCalc (state: GoalState) (goalId: Nat) (pred: String): CoreM TacticResult :=
  runTermElabM <| state.tryCalc goalId pred
@[export pantograph_goal_focus]
def goalFocus (state: GoalState) (goalId: Nat): Option GoalState :=
  state.focus goalId
@[export pantograph_goal_motivated_apply_m]
def goalMotivatedApply (state: GoalState) (goalId: Nat) (recursor: String): CoreM TacticResult :=
  runTermElabM <| state.tryMotivatedApply goalId recursor
@[export pantograph_goal_no_confuse_m]
def goalNoConfuse (state: GoalState) (goalId: Nat) (eq: String): CoreM TacticResult :=
  runTermElabM <| state.tryNoConfuse goalId eq

inductive SyntheticTactic where
  | congruenceArg
  | congruenceFun
  | congruence
/-- Executes a synthetic tactic which has no arguments -/
@[export pantograph_goal_synthetic_tactic_m]
def goalSyntheticTactic (state: GoalState) (goalId: Nat) (case: SyntheticTactic): CoreM TacticResult :=
  runTermElabM do
    state.restoreElabM
    state.execute goalId $ match case with
      | .congruenceArg => Tactic.congruenceArg
      | .congruenceFun => Tactic.congruenceFun
      | .congruence => Tactic.congruence



end Pantograph
