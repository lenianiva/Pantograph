import Lean.Data.Json
import Lean.Environment

import Pantograph.Commands
import Pantograph.Serial
import Pantograph.Meta
import Pantograph.Symbols

namespace Pantograph


structure Context where

/-- Stores state of the REPL -/
structure State where
  --environments: Array Lean.Environment := #[]
  proofTrees:   Array ProofTree := #[]

-- State monad
abbrev Subroutine := ReaderT Context (StateT State Lean.Elab.TermElabM)

open Commands

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parse_command (s: String): Except String Command := do
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

def execute (command: Command): Subroutine Lean.Json := do
  match command.cmd with
  | "catalog" =>
    match Lean.fromJson? command.payload with
    | .ok args => catalog args
    | .error x => return errorJson x
  | "inspect" =>
    match Lean.fromJson? command.payload with
    | .ok args => inspect args
    | .error x => return errorJson x
  | "clear" => clear
  | "expr.type" =>
    match Lean.fromJson? command.payload with
    | .ok args => expr_type args
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
    let error: InteractionError := { error := "unknown", desc := s!"Unknown command {cmd}" }
      return Lean.toJson error
  where
  errorI (type desc: String) := Lean.toJson ({ error := type, desc := desc }: InteractionError)
  errorJson := errorI "json"
  errorIndex := errorI "index"
  catalog (_: Catalog): Subroutine Lean.Json := do
    let env ← Lean.MonadEnv.getEnv
    let names := env.constants.fold (init := []) (λ es name info =>
      match to_filtered_symbol name info with
      | .some x => x::es
      | .none => es)
    return Lean.toJson <| ({ symbols := names }: CatalogResult)
  inspect (args: Inspect): Subroutine Lean.Json := do
    let env ← Lean.MonadEnv.getEnv
    let name := str_to_name args.name
    let info? := env.find? name
    match info? with
    | none => return  errorIndex s!"Symbol not found {args.name}"
    | some info =>
      let format ← Lean.Meta.ppExpr info.toConstantVal.type
      let module? := env.getModuleIdxFor? name >>=
        (λ idx => env.allImportedModuleNames.get? idx.toNat) |>.map toString
      let boundExpr? ← (match info.toConstantVal.type with
        | .forallE _ _ _ _ => return .some (← type_expr_to_bound info.toConstantVal.type)
        | _ => return Option.none)
      return Lean.toJson ({
        type := toString format,
        boundExpr? := boundExpr?,
        module? := module?
      }: InspectResult)
  clear : Subroutine Lean.Json := do
    let state ← get
    let nTrees := state.proofTrees.size
    set { state with proofTrees := #[] }
    return Lean.toJson ({ nTrees := nTrees }: ClearResult)
  expr_type (args: ExprType): Subroutine Lean.Json := do
    let env ← Lean.MonadEnv.getEnv
    match syntax_from_str env args.expr with
    | .error str => return errorI "parsing" str
    | .ok syn => do
      match (← syntax_to_expr syn) with
      | .error str => return errorI "elab" str
      | .ok expr => do
        try
          let format ← Lean.Meta.ppExpr (← Lean.Meta.inferType expr)
          return Lean.toJson <| ({ type := toString format }: ExprTypeResult)
        catch exception =>
          return errorI "typing" (← exception.toMessageData.toString)
  proof_start (args: ProofStart): Subroutine Lean.Json := do
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
      return Lean.toJson ({ treeId := nextTreeId }: ProofStartResult)
  proof_tactic (args: ProofTactic): Subroutine Lean.Json := do
    let state ← get
    match state.proofTrees.get? args.treeId with
    | .none => return errorIndex "Invalid tree index {args.treeId}"
    | .some tree =>
      let (result, nextTree) ← ProofTree.execute
        (stateId := args.stateId)
        (goalId := args.goalId.getD 0)
        (tactic := args.tactic) |>.run tree
      match result with
      | .invalid message => return Lean.toJson <| errorIndex message
      | .success nextId? goals =>
        set { state with proofTrees := state.proofTrees.set! args.treeId nextTree }
        return Lean.toJson ({ nextId? := nextId?, goals := goals }: ProofTacticResultSuccess)
      | .failure messages =>
        return Lean.toJson ({ tacticErrors := messages }: ProofTacticResultFailure)
  proof_print_tree (args: ProofPrintTree): Subroutine Lean.Json := do
    let state ← get
    match state.proofTrees.get? args.treeId with
    | .none => return errorIndex "Invalid tree index {args.treeId}"
    | .some tree =>
      return Lean.toJson ({parents := tree.structure_array}: ProofPrintTreeResult)


end Pantograph


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
-- This is better than the default version since it handles `.`
def setOptionFromString' (opts : Options) (entry : String) : IO Options := do
  let ps := (entry.splitOn "=").map String.trim
  let [key, val] ← pure ps | throw $ IO.userError "invalid configuration option entry, it must be of the form '<key> = <value>'"
  let key := str_to_name key
  let defValue ← getOptionDefaultValue key
  match defValue with
  | DataValue.ofString _ => pure $ opts.setString key val
  | DataValue.ofBool _   =>
    match val with
    | "true" => pure $ opts.setBool key true
    | "false" => pure $ opts.setBool key false
    | _ => throw $ IO.userError s!"invalid Bool option value '{val}'"
  | DataValue.ofName _   => pure $ opts.setName key val.toName
  | DataValue.ofNat _    =>
    match val.toNat? with
    | none   => throw (IO.userError s!"invalid Nat option value '{val}'")
    | some v => pure $ opts.setNat key v
  | DataValue.ofInt _    =>
    match val.toInt? with
    | none   => throw (IO.userError s!"invalid Int option value '{val}'")
    | some v => pure $ opts.setInt key v
  | DataValue.ofSyntax _ => throw (IO.userError s!"invalid Syntax option value")
end Lean

unsafe def main (args: List String): IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)

  -- Separate imports and options
  let options := args.filterMap (λ s => if s.startsWith "--" then .some <| s.drop 2 else .none)
  let imports:= args.filter (λ s => ¬ (s.startsWith "--"))

  let env ← Lean.importModules
    (imports := imports.map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  let context: Context := {
  }
  let coreContext: Lean.Core.Context := {
    currNamespace := str_to_name "Aniva",
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0], lines := #[1] },
    options := ← options.foldlM Lean.setOptionFromString' Lean.Options.empty
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
