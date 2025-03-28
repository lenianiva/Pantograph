import Std.Data.HashMap
import Pantograph

namespace Pantograph.Repl

open Lean

structure Context where
  coreContext : Core.Context

/-- Stores state of the REPL -/
structure State where
  options : Protocol.Options := {}
  nextId : Nat := 0
  goalStates : Std.HashMap Nat GoalState := Std.HashMap.empty

  env : Environment
  -- Parser state
  scope : Elab.Command.Scope := { header := "" }

/-- Main state monad for executing commands -/
abbrev MainM := ReaderT Context $ StateRefT State IO
def getMainState : MainM State := get
/-- Fallible subroutine return type -/
abbrev CR α := Except Protocol.InteractionError α

instance : MonadEnv MainM where
  getEnv := return (← get).env
  modifyEnv f := modify fun s => { s with env := f s.env  }

def newGoalState (goalState: GoalState) : MainM Nat := do
  let state ← get
  let stateId := state.nextId
  set { state with
    goalStates := state.goalStates.insert stateId goalState,
    nextId := state.nextId + 1
  }
  return stateId

def runCoreM { α } (coreM : CoreM α) : MainM α := do
  let scope := (← get).scope
  let coreCtx : Core.Context := {
    (← read).coreContext with
    currNamespace      := scope.currNamespace
    openDecls          := scope.openDecls
    options            := scope.opts
  }
  let coreState : Core.State := {
    env := (← get).env
  }
  let (result, state') ← coreM.toIO coreCtx coreState
  modifyEnv λ _ => state'.env
  return result

def liftMetaM { α } (metaM : MetaM α): MainM α :=
  runCoreM metaM.run'
def liftTermElabM { α } (termElabM: Elab.TermElabM α) : MainM α :=
  runCoreM $ termElabM.run' (ctx := defaultElabContext) |>.run'

section Frontend

structure CompilationUnit where
  -- Should be the penultimate environment, but this is ok
  env : Environment
  boundary : Nat × Nat
  invocations : List Protocol.InvokedTactic
  sorrys : List Frontend.InfoWithContext
  messages : Array String
  newConstants : List Name

def frontend_process_inner (args: Protocol.FrontendProcess): MainM (CR Protocol.FrontendProcessResult) := do
  let options := (← getMainState).options
  let (fileName, file) ← match args.fileName?, args.file? with
    | .some fileName, .none => do
      let file ← IO.FS.readFile fileName
      pure (fileName, file)
    | .none, .some file =>
      pure ("<anonymous>", file)
    | _, _ => return .error <| errorI "arguments" "Exactly one of {fileName, file} must be supplied"
  let env?: Option Environment ← if args.readHeader then
      pure .none
    else do
      .some <$> getEnv
  let (context, state) ← do Frontend.createContextStateFromFile file fileName env? {}
  let frontendM: Elab.Frontend.FrontendM (List CompilationUnit) :=
    Frontend.mapCompilationSteps λ step => do
    let boundary := (step.src.startPos.byteIdx, step.src.stopPos.byteIdx)
    let invocations: Option (List Protocol.InvokedTactic) ← if args.invocations then
        Frontend.collectTacticsFromCompilationStep step
      else
        pure []
    let sorrys ← if args.sorrys then
        Frontend.collectSorrys step (options := { collectTypeErrors := args.typeErrorsAsGoals })
      else
        pure []
    let messages ← step.messageStrings
    let newConstants ← if args.newConstants then
        Frontend.collectNewDefinedConstants step
      else
        pure []
    return {
      env := step.before,
      boundary,
      invocations,
      sorrys,
      messages,
      newConstants
    }
  let (li, state') ← frontendM.run context |>.run state
  if args.inheritEnv then
    setEnv state'.commandState.env
    if let .some scope := state'.commandState.scopes.head? then
      -- modify the scope
      set { ← getMainState with scope }
  let units ← li.mapM λ step => withEnv step.env do
    let newConstants? := if args.newConstants then
        .some $ step.newConstants.toArray.map λ name => name.toString
      else
        .none
    let (goalStateId?, goals?, goalSrcBoundaries?) ← if step.sorrys.isEmpty then do
        pure (.none, .none, .none)
      else do
        let ({ state, srcBoundaries }, goals) ← liftMetaM do
          let result@{state, .. } ← Frontend.sorrysToGoalState step.sorrys
          let goals ← goalSerialize state options
          pure (result, goals)
        let stateId ← newGoalState state
        let srcBoundaries := srcBoundaries.toArray.map (λ (b, e) => (b.byteIdx, e.byteIdx))
        pure (.some stateId, .some goals, .some srcBoundaries)
    let invocations? := if args.invocations then .some step.invocations else .none
    return {
      boundary := step.boundary,
      messages := step.messages,
      invocations?,
      goalStateId?,
      goals?,
      goalSrcBoundaries?,
      newConstants?,
    }
  return .ok { units }

end Frontend

/-- Main loop command of the REPL -/
def execute (command: Protocol.Command): MainM Json := do
  let run { α β: Type } [FromJson α] [ToJson β] (comm: α → MainM (CR β)): MainM Json :=
    match fromJson? command.payload with
    | .ok args => do
      match (← comm args) with
      | .ok result =>  return toJson result
      | .error ierror => return toJson ierror
    | .error error => return toJson $ errorCommand s!"Unable to parse json: {error}"
  match command.cmd with
  | "reset"         => run reset
  | "stat"          => run stat
  | "expr.echo"     => run expr_echo
  | "env.describe"  => run env_describe
  | "env.module_read" => run env_module_read
  | "env.catalog"   => run env_catalog
  | "env.inspect"   => run env_inspect
  | "env.add"       => run env_add
  | "env.save"      => run env_save
  | "env.load"      => run env_load
  | "options.set"   => run options_set
  | "options.print" => run options_print
  | "goal.start"    => run goal_start
  | "goal.tactic"   => run goal_tactic
  | "goal.continue" => run goal_continue
  | "goal.delete"   => run goal_delete
  | "goal.print"    => run goal_print
  | "goal.save"     => run goal_save
  | "goal.load"     => run goal_load
  | "frontend.process" => run frontend_process
  | cmd =>
    let error: Protocol.InteractionError :=
      errorCommand s!"Unknown command {cmd}"
    return toJson error
  where
  errorCommand := errorI "command"
  errorIndex := errorI "index"
  errorIO := errorI "io"
  -- Command Functions
  reset (_: Protocol.Reset): MainM (CR Protocol.StatResult) := do
    let state ← getMainState
    let nGoals := state.goalStates.size
    set { state with nextId := 0, goalStates := .empty }
    return .ok { nGoals }
  stat (_: Protocol.Stat): MainM (CR Protocol.StatResult) := do
    let state ← getMainState
    let nGoals := state.goalStates.size
    return .ok { nGoals }
  env_describe (args: Protocol.EnvDescribe): MainM (CR Protocol.EnvDescribeResult) := do
    let result ← runCoreM $ Environment.describe args
    return .ok result
  env_module_read (args: Protocol.EnvModuleRead): MainM (CR Protocol.EnvModuleReadResult) := do
    runCoreM $ Environment.moduleRead args
  env_catalog (args: Protocol.EnvCatalog): MainM (CR Protocol.EnvCatalogResult) := do
    let result ← runCoreM $ Environment.catalog args
    return .ok result
  env_inspect (args: Protocol.EnvInspect): MainM (CR Protocol.EnvInspectResult) := do
    let state ← getMainState
    runCoreM $ Environment.inspect args state.options
  env_add (args: Protocol.EnvAdd): MainM (CR Protocol.EnvAddResult) := do
    runCoreM $ Environment.addDecl args
  env_save (args: Protocol.EnvSaveLoad): MainM (CR Protocol.EnvSaveLoadResult) := do
    let env ← MonadEnv.getEnv
    environmentPickle env args.path
    return .ok {}
  env_load (args: Protocol.EnvSaveLoad): MainM (CR Protocol.EnvSaveLoadResult) := do
    let (env, _) ← environmentUnpickle args.path
    setEnv env
    return .ok {}
  expr_echo (args: Protocol.ExprEcho): MainM (CR Protocol.ExprEchoResult) := do
    let state ← getMainState
    runCoreM $ exprEcho args.expr (expectedType? := args.type?) (levels := args.levels.getD #[]) (options := state.options)
  options_set (args: Protocol.OptionsSet): MainM (CR Protocol.OptionsSetResult) := do
    let state ← getMainState
    let options := state.options
    set { state with
      options := {
        -- FIXME: This should be replaced with something more elegant
        printJsonPretty := args.printJsonPretty?.getD options.printJsonPretty,
        printExprPretty := args.printExprPretty?.getD options.printExprPretty,
        printExprAST := args.printExprAST?.getD options.printExprAST,
        printDependentMVars := args.printDependentMVars?.getD options.printDependentMVars,
        noRepeat := args.noRepeat?.getD options.noRepeat,
        printAuxDecls := args.printAuxDecls?.getD options.printAuxDecls,
        printImplementationDetailHyps := args.printImplementationDetailHyps?.getD options.printImplementationDetailHyps
        automaticMode := args.automaticMode?.getD options.automaticMode,
      }
    }
    return .ok {  }
  options_print (_: Protocol.OptionsPrint): MainM (CR Protocol.Options) := do
    return .ok (← getMainState).options
  goal_start (args: Protocol.GoalStart): MainM (CR Protocol.GoalStartResult) := do
    let expr?: Except _ GoalState ← liftTermElabM (match args.expr, args.copyFrom with
      | .some expr, .none => goalStartExpr expr (args.levels.getD #[])
      | .none, .some copyFrom => do
        (match (← getEnv).find? <| copyFrom.toName with
        | .none => return .error <| errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok (← GoalState.create cInfo.type))
      | _, _ =>
        return .error <| errorI "arguments" "Exactly one of {expr, copyFrom} must be supplied")
    match expr? with
    | .error error => return .error error
    | .ok goalState =>
      let stateId ← newGoalState goalState
      return .ok { stateId, root := goalState.root.name.toString }
  goal_tactic (args: Protocol.GoalTactic): MainM (CR Protocol.GoalTacticResult) := do
    let state ← getMainState
    let .some goalState := state.goalStates[args.stateId]? |
      return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let .some goal := goalState.goals.get? args.goalId |
      return .error $ errorIndex s!"Invalid goal index {args.goalId}"
    let nextGoalState?: Except _ TacticResult ← liftTermElabM do
      -- NOTE: Should probably use a macro to handle this...
      match args.tactic?, args.expr?, args.have?, args.let?, args.calc?, args.conv?, args.draft?  with
      | .some tactic, .none, .none, .none, .none, .none, .none => do
        pure <| Except.ok <| ← goalState.tryTactic goal tactic
      | .none, .some expr, .none, .none, .none, .none, .none => do
        pure <| Except.ok <| ← goalState.tryAssign goal expr
      | .none, .none, .some type, .none, .none, .none, .none => do
        let binderName := args.binderName?.getD ""
        pure <| Except.ok <| ← goalState.tryHave goal binderName type
      | .none, .none, .none, .some type, .none, .none, .none => do
        let binderName := args.binderName?.getD ""
        pure <| Except.ok <| ← goalState.tryLet goal binderName type
      | .none, .none, .none, .none, .some pred, .none, .none => do
        pure <| Except.ok <| ← goalState.tryCalc goal pred
      | .none, .none, .none, .none, .none, .some true, .none => do
        pure <| Except.ok <| ← goalState.conv goal
      | .none, .none, .none, .none, .none, .some false, .none => do
        pure <| Except.ok <| ← goalState.convExit
      | .none, .none, .none, .none, .none, .none, .some draft => do
        pure <| Except.ok <| ← goalState.tryDraft goal draft
      | _, _, _, _, _, _, _ =>
        let error := errorI "arguments" "Exactly one of {tactic, expr, have, let, calc, conv, draft} must be supplied"
        pure $ .error error
    match nextGoalState? with
    | .error error => return .error error
    | .ok (.success nextGoalState) => do
      let nextGoalState ← match state.options.automaticMode, args.conv? with
        | true, .none => do
          let .ok result := nextGoalState.resume (nextGoalState.goals ++ goalState.goals) |
            return .error $ errorIO "Resuming known goals"
          pure result
        | true, .some true => pure nextGoalState
        | true, .some false => do
          let .some (_, _, dormantGoals) := goalState.convMVar? |
            return .error $ errorIO "If conv exit succeeded this should not fail"
          let .ok result := nextGoalState.resume (nextGoalState.goals ++ dormantGoals) |
            return .error $ errorIO "Resuming known goals"
          pure result
        | false, _ => pure nextGoalState
      let nextStateId ← newGoalState nextGoalState
      let goals ← runCoreM $ nextGoalState.serializeGoals (parent := .some goalState) (options := state.options) |>.run'
      return .ok {
        nextStateId? := .some nextStateId,
        goals? := .some goals,
      }
    | .ok (.parseError message) =>
      return .ok { parseError? := .some message }
    | .ok (.invalidAction message) =>
      return .error $ errorI "invalid" message
    | .ok (.failure messages) =>
      return .ok { tacticErrors? := .some messages }
  goal_continue (args: Protocol.GoalContinue): MainM (CR Protocol.GoalContinueResult) := do
    let state ← getMainState
    let .some target := state.goalStates[args.target]? |
      return .error $ errorIndex s!"Invalid state index {args.target}"
    let nextState? ← match args.branch?, args.goals? with
      | .some branchId, .none => do
        match state.goalStates[branchId]? with
        | .none => return .error $ errorIndex s!"Invalid state index {branchId}"
        | .some branch => pure $ target.continue branch
      | .none, .some goals =>
        pure $ goalResume target goals
      | _, _ => return .error <| errorI "arguments" "Exactly one of {branch, goals} must be supplied"
    match nextState? with
    | .error error => return .error <| errorI "structure" error
    | .ok nextGoalState =>
      let nextStateId ← newGoalState nextGoalState
      let goals ← liftMetaM $ goalSerialize nextGoalState (options := state.options)
      return .ok {
        nextStateId,
        goals,
      }
  goal_delete (args: Protocol.GoalDelete): MainM (CR Protocol.GoalDeleteResult) := do
    let state ← getMainState
    let goalStates := args.stateIds.foldl (λ map id => map.erase id) state.goalStates
    set { state with goalStates }
    return .ok {}
  goal_print (args: Protocol.GoalPrint): MainM (CR Protocol.GoalPrintResult) := do
    let state ← getMainState
    let .some goalState := state.goalStates[args.stateId]? |
      return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let result ← liftMetaM <| goalPrint
        goalState
        (rootExpr := args.rootExpr?.getD False)
        (parentExpr := args.parentExpr?.getD False)
        (goals := args.goals?.getD False)
        (extraMVars := args.extraMVars?.getD #[])
        (options := state.options)
    return .ok result
  goal_save (args: Protocol.GoalSave): MainM (CR Protocol.GoalSaveResult) := do
    let state ← getMainState
    let .some goalState := state.goalStates[args.id]? |
      return .error $ errorIndex s!"Invalid state index {args.id}"
    goalStatePickle goalState args.path
    return .ok {}
  goal_load (args: Protocol.GoalLoad): MainM (CR Protocol.GoalLoadResult) := do
    let (goalState, _) ← goalStateUnpickle args.path (← MonadEnv.getEnv)
    let id ← newGoalState goalState
    return .ok { id }
  frontend_process (args: Protocol.FrontendProcess): MainM (CR Protocol.FrontendProcessResult) := do
    try
      frontend_process_inner args
    catch e =>
      return .error $ errorI "frontend" e.toString

end Pantograph.Repl
