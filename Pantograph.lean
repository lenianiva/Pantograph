import Pantograph.Commands
import Pantograph.Serial
import Pantograph.Symbols
import Pantograph.Tactic
import Pantograph.SemihashMap

namespace Pantograph

structure Context where
  imports: List String

/-- Stores state of the REPL -/
structure State where
  options: Commands.Options := {}
  goalStates: SemihashMap GoalState := SemihashMap.empty

-- State monad
abbrev MainM := ReaderT Context (StateT State Lean.Elab.TermElabM)
-- For some reason writing `CommandM α := MainM (Except ... α)` disables certain
-- monadic features in `MainM`
abbrev CR α := Except Commands.InteractionError α

def execute (command: Commands.Command): MainM Lean.Json := do
  let run { α β: Type } [Lean.FromJson α] [Lean.ToJson β] (comm: α → MainM (CR β)): MainM Lean.Json :=
    match Lean.fromJson? command.payload with
    | .ok args => do
      match (← comm args) with
      | .ok result =>  return Lean.toJson result
      | .error ierror => return Lean.toJson ierror
    | .error error => return Lean.toJson $ errorCommand s!"Unable to parse json: {error}"
  match command.cmd with
  | "reset"          => run reset
  | "stat"           => run stat
  | "expr.echo"      => run expr_echo
  | "lib.catalog"    => run lib_catalog
  | "lib.inspect"    => run lib_inspect
  | "options.set"    => run options_set
  | "options.print"  => run options_print
  | "goal.start"     => run goal_start
  | "goal.tactic"    => run goal_tactic
  | "goal.delete"    => run goal_delete
  | cmd =>
    let error: Commands.InteractionError :=
      errorCommand s!"Unknown command {cmd}"
    return Lean.toJson error
  where
  errorI (type desc: String): Commands.InteractionError := { error := type, desc := desc }
  errorCommand := errorI "command"
  errorIndex := errorI "index"
  -- Command Functions
  reset (_: Commands.Reset): MainM (CR Commands.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    set { state with goalStates := SemihashMap.empty }
    return .ok { nGoals }
  stat (_: Commands.Stat): MainM (CR Commands.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    return .ok { nGoals }
  lib_catalog (_: Commands.LibCatalog): MainM (CR Commands.LibCatalogResult) := do
    let env ← Lean.MonadEnv.getEnv
    let names := env.constants.fold (init := #[]) (λ acc name info =>
      match to_filtered_symbol name info with
      | .some x => acc.push x
      | .none => acc)
    return .ok { symbols := names }
  lib_inspect (args: Commands.LibInspect): MainM (CR Commands.LibInspectResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let name := str_to_name args.name
    let info? := env.find? name
    match info? with
    | none => return .error $ errorIndex s!"Symbol not found {args.name}"
    | some info =>
      let module? := env.getModuleIdxFor? name >>=
        (λ idx => env.allImportedModuleNames.get? idx.toNat) |>.map toString
      let value? := match args.value?, info with
        | .some true, _ => info.value?
        | .some false, _ => .none
        | .none, .defnInfo _ => info.value?
        | .none, _ => .none
      return .ok {
        type := ← serialize_expression state.options info.type,
        value? := ← value?.mapM (λ v => serialize_expression state.options v),
        module? := module?
      }
  expr_echo (args: Commands.ExprEcho): MainM (CR Commands.ExprEchoResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    match syntax_from_str env args.expr with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => do
      match (← syntax_to_expr syn) with
      | .error str => return .error $ errorI "elab" str
      | .ok expr => do
        try
          let type ← Lean.Meta.inferType expr
          return .ok {
              type := (← serialize_expression (options := state.options) type),
              expr := (← serialize_expression (options := state.options) expr)
          }
        catch exception =>
          return .error $ errorI "typing" (← exception.toMessageData.toString)
  options_set (args: Commands.OptionsSet): MainM (CR Commands.OptionsSetResult) := do
    let state ← get
    let options := state.options
    set { state with
      options := {
        -- FIXME: This should be replaced with something more elegant
        printJsonPretty := args.printJsonPretty?.getD options.printJsonPretty,
        printExprPretty := args.printExprPretty?.getD options.printExprPretty,
        printExprAST := args.printExprAST?.getD options.printExprAST,
        proofVariableDelta := args.proofVariableDelta?.getD options.proofVariableDelta,
        printAuxDecls := args.printAuxDecls?.getD options.printAuxDecls,
        printImplementationDetailHyps := args.printImplementationDetailHyps?.getD options.printImplementationDetailHyps
      }
    }
    return .ok {  }
  options_print (_: Commands.OptionsPrint): MainM (CR Commands.OptionsPrintResult) := do
    return .ok (← get).options
  goal_start (args: Commands.GoalStart): MainM (CR Commands.GoalStartResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let expr?: Except _ Lean.Expr ← (match args.expr, args.copyFrom with
      | .some expr, .none =>
        (match syntax_from_str env expr with
        | .error str => return .error <| errorI "parsing" str
        | .ok syn => do
          (match (← syntax_to_expr syn) with
          | .error str => return .error <| errorI "elab" str
          | .ok expr => return .ok expr))
      | .none, .some copyFrom =>
        (match env.find? <| str_to_name copyFrom with
        | .none => return .error <| errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok cInfo.type)
      | .none, .none =>
        return .error <| errorI "arguments" "At least one of {expr, copyFrom} must be supplied"
      | _, _ => return .error <| errorI "arguments" "Cannot populate both of {expr, copyFrom}")
    match expr? with
    | .error error => return .error error
    | .ok expr =>
      let goalState ← GoalState.create expr
      let (goalStates, goalId) := state.goalStates.insert goalState
      set { state with goalStates }
      return .ok { goalId }
  goal_tactic (args: Commands.GoalTactic): MainM (CR Commands.GoalTacticResult) := do
    let state ← get
    match state.goalStates.get? args.goalId with
    | .none => return .error $ errorIndex s!"Invalid goal index {args.goalId}"
    | .some goalState =>
      let result ← GoalState.execute goalState args.tactic |>.run state.options
      match result with
      | .success goals =>
        if goals.isEmpty then
          return .ok {}
        else
          -- Append all goals
          let (goalStates, goalIds, sGoals) := Array.foldl (λ acc itr =>
            let (map, indices, serializedGoals) := acc
            let (goalState, sGoal) := itr
            let (map, index) := map.insert goalState
            (map, index :: indices, sGoal :: serializedGoals)
            ) (state.goalStates, [], []) goals
          set { state with goalStates }
          return .ok { goals? := .some sGoals.reverse.toArray, goalIds? := .some goalIds.reverse.toArray }
      | .failure messages =>
        return .ok { tacticErrors? := .some messages }
  goal_delete (args: Commands.GoalDelete): MainM (CR Commands.GoalDeleteResult) := do
    let state ← get
    let goalStates := args.goalIds.foldl (λ map id => map.remove id) state.goalStates
    set { state with goalStates }
    return .ok {}

end Pantograph
