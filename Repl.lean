import Lean.Data.HashMap
import Pantograph

namespace Pantograph.Repl

structure Context where
  imports: List String

/-- Stores state of the REPL -/
structure State where
  options: Protocol.Options := {}
  nextId: Nat := 0
  goalStates: Lean.HashMap Nat GoalState := Lean.HashMap.empty

/-- Main state monad for executing commands -/
abbrev MainM := ReaderT Context (StateT State Lean.CoreM)

-- HACK: For some reason writing `CommandM α := MainM (Except ... α)` disables
-- certain monadic features in `MainM`
abbrev CR α := Except Protocol.InteractionError α

def runMetaInMainM { α } (metaM: Lean.MetaM α): MainM α :=
  metaM.run'
def runTermElabInMainM { α } (termElabM: Lean.Elab.TermElabM α) : MainM α :=
  termElabM.run' (ctx := Condensed.elabContext) |>.run'

def execute (command: Protocol.Command): MainM Lean.Json := do
  let run { α β: Type } [Lean.FromJson α] [Lean.ToJson β] (comm: α → MainM (CR β)): MainM Lean.Json :=
    match Lean.fromJson? command.payload with
    | .ok args => do
      match (← comm args) with
      | .ok result =>  return Lean.toJson result
      | .error ierror => return Lean.toJson ierror
    | .error error => return Lean.toJson $ errorCommand s!"Unable to parse json: {error}"
  match command.cmd with
  | "reset"         => run reset
  | "stat"          => run stat
  | "expr.echo"     => run expr_echo
  | "env.catalog"   => run env_catalog
  | "env.inspect"   => run env_inspect
  | "env.add"       => run env_add
  | "options.set"   => run options_set
  | "options.print" => run options_print
  | "goal.start"    => run goal_start
  | "goal.tactic"   => run goal_tactic
  | "goal.continue" => run goal_continue
  | "goal.delete"   => run goal_delete
  | "goal.print"    => run goal_print
  | "frontend.process"  => run frontend_process
  | cmd =>
    let error: Protocol.InteractionError :=
      errorCommand s!"Unknown command {cmd}"
    return Lean.toJson error
  where
  errorCommand := errorI "command"
  errorIndex := errorI "index"
  -- Command Functions
  reset (_: Protocol.Reset): MainM (CR Protocol.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    set { state with nextId := 0, goalStates := Lean.HashMap.empty }
    return .ok { nGoals }
  stat (_: Protocol.Stat): MainM (CR Protocol.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    return .ok { nGoals }
  env_catalog (args: Protocol.EnvCatalog): MainM (CR Protocol.EnvCatalogResult) := do
    let result ← Environment.catalog args
    return .ok result
  env_inspect (args: Protocol.EnvInspect): MainM (CR Protocol.EnvInspectResult) := do
    let state ← get
    Environment.inspect args state.options
  env_add (args: Protocol.EnvAdd): MainM (CR Protocol.EnvAddResult) := do
    Environment.addDecl args
  expr_echo (args: Protocol.ExprEcho): MainM (CR Protocol.ExprEchoResult) := do
    let state ← get
    exprEcho args.expr (expectedType? := args.type?) (levels := args.levels.getD #[]) (options := state.options)
  options_set (args: Protocol.OptionsSet): MainM (CR Protocol.OptionsSetResult) := do
    let state ← get
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
    return .ok (← get).options
  goal_start (args: Protocol.GoalStart): MainM (CR Protocol.GoalStartResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let expr?: Except _ GoalState ← runTermElabInMainM (match args.expr, args.copyFrom with
      | .some expr, .none => goalStartExpr expr (args.levels.getD #[])
      | .none, .some copyFrom =>
        (match env.find? <| copyFrom.toName with
        | .none => return .error <| errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok (← GoalState.create cInfo.type))
      | _, _ =>
        return .error <| errorI "arguments" "Exactly one of {expr, copyFrom} must be supplied")
    match expr? with
    | .error error => return .error error
    | .ok goalState =>
      let stateId := state.nextId
      set { state with
        goalStates := state.goalStates.insert stateId goalState,
        nextId := state.nextId + 1
      }
      return .ok { stateId, root := goalState.root.name.toString }
  goal_tactic (args: Protocol.GoalTactic): MainM (CR Protocol.GoalTacticResult) := do
    let state ← get
    let .some goalState := state.goalStates.find? args.stateId |
      return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let .some goal := goalState.goals.get? args.goalId |
      return .error $ errorIndex s!"Invalid goal index {args.goalId}"
    let nextGoalState?: Except _ TacticResult ← runTermElabInMainM do
      match args.tactic?, args.expr?, args.have?, args.calc?, args.conv?  with
      | .some tactic, .none, .none, .none, .none => do
        pure <| Except.ok <| ← goalState.tryTactic goal tactic
      | .none, .some expr, .none, .none, .none => do
        pure <| Except.ok <| ← goalState.tryAssign goal expr
      | .none, .none, .some type, .none, .none => do
        let binderName := args.binderName?.getD ""
        pure <| Except.ok <| ← goalState.tryHave goal binderName type
      | .none, .none, .none, .some pred, .none => do
        pure <| Except.ok <| ← goalState.tryCalc goal pred
      | .none, .none, .none, .none, .some true => do
        pure <| Except.ok <| ← goalState.conv goal
      | .none, .none, .none, .none, .some false => do
        pure <| Except.ok <| ← goalState.convExit
      | _, _, _, _, _ =>
        let error := errorI "arguments" "Exactly one of {tactic, expr, have, calc, conv} must be supplied"
        pure $ Except.error $ error
    match nextGoalState? with
    | .error error => return .error error
    | .ok (.success nextGoalState) => do
      let nextGoalState ← match state.options.automaticMode, args.conv? with
        | true, .none => do
          let .ok result := nextGoalState.resume (nextGoalState.goals ++ goalState.goals) | throwError "Resuming known goals"
          pure result
        | true, .some true => pure nextGoalState
        | true, .some false => do
          let .some (_, _, dormantGoals) := goalState.convMVar? | throwError "If conv exit succeeded this should not fail"
          let .ok result := nextGoalState.resume (nextGoalState.goals ++ dormantGoals) | throwError "Resuming known goals"
          pure result
        | false, _ => pure nextGoalState
      let nextStateId := state.nextId
      set { state with
        goalStates := state.goalStates.insert state.nextId nextGoalState,
        nextId := state.nextId + 1,
      }
      let goals ← nextGoalState.serializeGoals (parent := .some goalState) (options := state.options) |>.run'
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
    let state ← get
    let .some target := state.goalStates.find? args.target | return .error $ errorIndex s!"Invalid state index {args.target}"
    let nextState? ← match args.branch?, args.goals? with
      | .some branchId, .none => do
        match state.goalStates.find? branchId with
        | .none => return .error $ errorIndex s!"Invalid state index {branchId}"
        | .some branch => pure $ target.continue branch
      | .none, .some goals =>
        pure $ goalResume target goals
      | _, _ => return .error <| errorI "arguments" "Exactly one of {branch, goals} must be supplied"
    match nextState? with
    | .error error => return .error <| errorI "structure" error
    | .ok nextGoalState =>
      let nextStateId := state.nextId
      set { state with
        goalStates := state.goalStates.insert nextStateId nextGoalState,
        nextId := state.nextId + 1
      }
      let goals ← goalSerialize nextGoalState (options := state.options)
      return .ok {
        nextStateId,
        goals,
      }
  goal_delete (args: Protocol.GoalDelete): MainM (CR Protocol.GoalDeleteResult) := do
    let state ← get
    let goalStates := args.stateIds.foldl (λ map id => map.erase id) state.goalStates
    set { state with goalStates }
    return .ok {}
  goal_print (args: Protocol.GoalPrint): MainM (CR Protocol.GoalPrintResult) := do
    let state ← get
    let .some goalState := state.goalStates.find? args.stateId | return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let result ← runMetaInMainM <| goalPrint goalState state.options
    return .ok result
  frontend_process (args: Protocol.FrontendProcess): MainM (CR Protocol.FrontendProcessResult) := do
    try
      let (fileName, file) ← match args.fileName?, args.file? with
        | .some fileName, .none => do
          let file ← IO.FS.readFile fileName
          pure (fileName, file)
        | .none, .some file =>
          pure ("<anonymous>", file)
        | _, _ => return .error <| errorI "arguments" "Exactly one of {fileName, file} must be supplied"
      let env?: Option Lean.Environment ← if args.fileName?.isSome then
          pure .none
        else do
          let env ← Lean.MonadEnv.getEnv
          pure <| .some env
      let (context, state) ← do Frontend.createContextStateFromFile file fileName env? {}
      let m := Frontend.mapCompilationSteps λ step => do
        let unitBoundary := (step.src.startPos.byteIdx, step.src.stopPos.byteIdx)
        let tacticInvocations ← if args.invocations then
            Frontend.collectTacticsFromCompilationStep step
          else
            pure []
        return (unitBoundary, tacticInvocations)
      let li ← m.run context |>.run' state
      let units := li.map λ (unit, _) => unit
      let invocations? := if args.invocations then
          .some $ li.bind λ (_, invocations) => invocations
        else
          .none
      return .ok { units, invocations? }
    catch e =>
      return .error $ errorI "frontend" (← e.toMessageData.toString)

end Pantograph.Repl
