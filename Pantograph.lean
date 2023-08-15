import Pantograph.Commands
import Pantograph.Serial
import Pantograph.Symbols
import Pantograph.Tactic

namespace Pantograph

structure Context where
  imports: List String

/-- Stores state of the REPL -/
structure State where
  options: Commands.Options := {}
  --environments: Array Lean.Environment := #[]
  proofTrees:   Array ProofTree := #[]

-- State monad
abbrev Subroutine := ReaderT Context (StateT State Lean.Elab.TermElabM)

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parse_command (s: String): Except String Commands.Command := do
  let s := s.trim
  match s.get? 0 with
  | .some '{' => -- Parse in Json mode
    Lean.fromJson? (← Lean.Json.parse s)
  | .some _ => -- Parse in line mode
    let offset := s.posOf ' ' |> s.offsetOfPos
    if offset = s.length then
      return { cmd := s.take offset, payload := Lean.Json.null }
    else
      let payload ← s.drop offset |> Lean.Json.parse
      return { cmd := s.take offset, payload := payload }
  | .none => throw "Command is empty"

def execute (command: Commands.Command): Subroutine Lean.Json := do
  match command.cmd with
  | "options.set" =>
    match Lean.fromJson? command.payload with
    | .ok args => options_set args
    | .error x => return errorJson x
  | "options.print" =>
    match Lean.fromJson? command.payload with
    | .ok args => options_print args
    | .error x => return errorJson x
  | "catalog" =>
    match Lean.fromJson? command.payload with
    | .ok args => catalog args
    | .error x => return errorJson x
  | "inspect" =>
    match Lean.fromJson? command.payload with
    | .ok args => inspect args
    | .error x => return errorJson x
  | "clear" => clear
  | "expr.echo" =>
    match Lean.fromJson? command.payload with
    | .ok args => expr_echo args
    | .error x => return errorJson x
  | "proof.start" =>
    match Lean.fromJson? command.payload with
    | .ok args => proof_start args
    | .error x => return errorJson x
  | "proof.tactic" =>
    match Lean.fromJson? command.payload with
    | .ok args => proof_tactic args
    | .error x => return errorJson x
  | "proof.printTree" =>
    match Lean.fromJson? command.payload with
    | .ok args => proof_print_tree args
    | .error x => return errorJson x
  | cmd =>
    let error: Commands.InteractionError :=
      { error := "unknown", desc := s!"Unknown command {cmd}" }
    return Lean.toJson error
  where
  errorI (type desc: String) := Lean.toJson (
    { error := type, desc := desc }: Commands.InteractionError)
  errorJson := errorI "json"
  errorIndex := errorI "index"
  -- Command Functions
  options_set (args: Commands.OptionsSet): Subroutine Lean.Json := do
    let state ← get
    set { state with
      options := {
        printExprPretty := args.printExprPretty?.getD true,
        printExprAST := args.printExprAST?.getD true,
        proofVariableDelta := args.proofVariableDelta?.getD false
      }
    }
    return Lean.toJson ({ }: Commands.OptionsSetResult)
  options_print (_: Commands.OptionsPrint): Subroutine Lean.Json := do
    return Lean.toJson (← get).options
  catalog (_: Commands.Catalog): Subroutine Lean.Json := do
    let env ← Lean.MonadEnv.getEnv
    let names := env.constants.fold (init := #[]) (λ acc name info =>
      match to_filtered_symbol name info with
      | .some x => acc.push x
      | .none => acc)
    return Lean.toJson <| ({ symbols := names }: Commands.CatalogResult)
  inspect (args: Commands.Inspect): Subroutine Lean.Json := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let name := str_to_name args.name
    let info? := env.find? name
    match info? with
    | none => return  errorIndex s!"Symbol not found {args.name}"
    | some info =>
      let module? := env.getModuleIdxFor? name >>=
        (λ idx => env.allImportedModuleNames.get? idx.toNat) |>.map toString
      let value? := match args.value?, info with
        | .some true, _ => info.value?
        | .some false, _ => .none
        | .none, .defnInfo _ => info.value?
        | .none, _ => .none
      return Lean.toJson ({
        type := ← serialize_expression state.options info.type,
        value? := ← value?.mapM (λ v => serialize_expression state.options v),
        module? := module?
      }: Commands.InspectResult)
  clear : Subroutine Lean.Json := do
    let state ← get
    let nTrees := state.proofTrees.size
    set { state with proofTrees := #[] }
    return Lean.toJson ({ nTrees := nTrees }: Commands.ClearResult)
  expr_echo (args: Commands.ExprEcho): Subroutine Lean.Json := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    match syntax_from_str env args.expr with
    | .error str => return errorI "parsing" str
    | .ok syn => do
      match (← syntax_to_expr syn) with
      | .error str => return errorI "elab" str
      | .ok expr => do
        try
          let type ← Lean.Meta.inferType expr
          return Lean.toJson <| ({
              type := (← serialize_expression (options := state.options) type),
              expr := (← serialize_expression (options := state.options) expr)
          }: Commands.ExprEchoResult)
        catch exception =>
          return errorI "typing" (← exception.toMessageData.toString)
  proof_start (args: Commands.ProofStart): Subroutine Lean.Json := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let expr?: Except Lean.Json Lean.Expr ← (match args.expr, args.copyFrom with
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
    | .error error => return error
    | .ok expr =>
      let tree ← ProofTree.create (str_to_name <| args.name.getD "Untitled") expr
      -- Put the new tree in the environment
      let nextTreeId := state.proofTrees.size
      set { state with proofTrees := state.proofTrees.push tree }
      return Lean.toJson ({ treeId := nextTreeId }: Commands.ProofStartResult)
  proof_tactic (args: Commands.ProofTactic): Subroutine Lean.Json := do
    let state ← get
    match state.proofTrees.get? args.treeId with
    | .none => return errorIndex "Invalid tree index {args.treeId}"
    | .some tree =>
      let (result, nextTree) ← ProofTree.execute
        (stateId := args.stateId)
        (goalId := args.goalId.getD 0)
        (tactic := args.tactic) |>.run state.options |>.run tree
      match result with
      | .invalid message => return Lean.toJson <| errorIndex message
      | .success nextId? goals =>
        set { state with proofTrees := state.proofTrees.set! args.treeId nextTree }
        return Lean.toJson (
          { nextId? := nextId?, goals := goals }: Commands.ProofTacticResultSuccess)
      | .failure messages =>
        return Lean.toJson (
          { tacticErrors := messages }: Commands.ProofTacticResultFailure)
  proof_print_tree (args: Commands.ProofPrintTree): Subroutine Lean.Json := do
    let state ← get
    match state.proofTrees.get? args.treeId with
    | .none => return errorIndex "Invalid tree index {args.treeId}"
    | .some tree =>
      return Lean.toJson ({parents := tree.structure_array}: Commands.ProofPrintTreeResult)


end Pantograph
