import Lean.Data.Json
import Lean.Environment

import Pantograph.Commands
import Pantograph.Serial
import Pantograph.Meta
import Pantograph.Symbols

namespace Pantograph


structure Context where
  coreContext: Lean.Core.Context

/-- Stores state of the REPL -/
structure State where
  environments: Array Lean.Environment := #[]
  proofTrees:   Array Meta.ProofTree := #[]

-- State monad
abbrev Subroutine := ReaderT Context (StateT State IO)

def nextId (s: State): Nat := s.environments.size

def State.getEnv (state: State) (id: Nat): Except String Lean.Environment :=
  match state.environments.get? id with
  | .some env => return env
  | .none => throw s!"Invalid environment id {id}"


-- Utilities
def option_expect (o: Option α) (error: String): Except String α :=
  match o with
  | .some value => return value
  | .none => throw error


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



unsafe def execute (command: Command): Subroutine Lean.Json := do
  match command.cmd with
  | "create" =>
    match Lean.fromJson? command.payload with
    | .ok args => create args
    | .error x => return errorJson x
  | "catalog" =>
    match Lean.fromJson? command.payload with
    | .ok args => catalog args
    | .error x => return errorJson x
  | "clear" =>
    -- Delete all the environments
    let ret ← clear
    return Lean.toJson ret
  | "inspect" =>
    match Lean.fromJson? command.payload with
    | .ok args => inspect args
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
  errorJson (s: String) := Lean.toJson ({ error := "json", desc := s }: InteractionError)
  errorIndex (s: String) := Lean.toJson ({ error := "index", desc := s }: InteractionError)
  create (args: Create): Subroutine Lean.Json := do
    let state ← get
    let id := nextId state
    let env ← Lean.importModules
      (imports := args.imports.map (λ str => { module := str_to_name str, runtimeOnly := false }))
      (opts := {})
      (trustLevel := 1)
    modify fun s => { environments := s.environments.push env }
    let num_filtered_symbols := env.constants.fold (init := 0) (λ acc name info =>
      acc + if is_symbol_unsafe_or_internal name info then 0 else 1)
    return Lean.toJson ({
      id := id,
      symbols := env.constants.size,
      filtered_symbols := num_filtered_symbols }: CreateResult)
  catalog (args: Catalog): Subroutine Lean.Json := do
    let state ← get
    match state.getEnv args.id with
    | .error error => return Lean.toJson <| errorIndex error
    | .ok env =>
      let names := env.constants.fold (init := []) (λ es name info =>
        match to_filtered_symbol name info with
        | .some x => x::es
        | .none => es)
      return Lean.toJson <| ({ theorems := names }: CatalogResult)
  clear: Subroutine Lean.Json := do
    let state ← get
    let nEnv := state.environments.size
    for env in state.environments do
      env.freeRegions
    set ({ }: State)
    return Lean.toJson ({ nEnv := nEnv }: ClearResult)
  inspect (args: Inspect): Subroutine Lean.Json := do
    let context ← read
    let state ← get
    match state.getEnv args.id with
    | .error error => return Lean.toJson <| errorIndex error
    | .ok env =>
      let info? := env.find? <| str_to_name args.symbol
      match info? with
      | none => return Lean.toJson <| errorIndex s!"Symbol not found {args.symbol}"
      | some info =>
        let format ← Serial.expr_to_str
          (env := env)
          (coreContext := context.coreContext)
          (expr := info.toConstantVal.type)
        return Lean.toJson ({ type := format }: InspectResult)
  proof_start (args: ProofStart): Subroutine Lean.Json := do
    let context ← read
    let state ← get
    let ret?: Except Lean.Json Meta.ProofTree ← ExceptT.run <| (do
      let env ← match state.getEnv args.id with
        | .error error => throw <| Lean.toJson <| errorIndex error
        | .ok env => pure env
      let tree := Meta.createProofTree
        (name := args.name)
        (env := env)
        (coreContext := context.coreContext)
      let expr: Lean.Expr ← match args.expr, args.copyFrom with
        | "", "" =>
          throw <| Lean.toJson ({ error := "arguments", desc := "At least one of {expr, copyFrom} must be supplied" }: InteractionError)
        | expr, "" =>
          let syn ← match Serial.syntax_from_str env expr with
            | .error str => throw <| Lean.toJson ({ error := "parsing", desc := str }: InteractionError)
            | .ok syn => pure syn
          let expr: Lean.Expr ← match (← Meta.ProofM.syntax_to_expr syn |>.run' tree) with
            | .error str => throw <| Lean.toJson ({ error := "elab", desc := str }: InteractionError)
            | .ok expr => pure expr
          pure expr
        | "", copyFrom =>
          match Serial.expr_from_const env (name := str_to_name copyFrom) with
          | .error str =>
            IO.println "Symbol not found"
            throw <| errorIndex str
          | .ok expr => pure expr
        | _, _ => throw <| Lean.toJson ({ error := "arguments", desc := "Cannot populate both of {expr, copyFrom}" }: InteractionError)
      let (_, tree) := ← (Meta.ProofM.start expr |>.run tree)
      return tree
    )
    match ret? with
    | .error error => return error
    | .ok tree =>
      -- Put the new tree in the environment
      let nextId := state.proofTrees.size
      set { state with proofTrees := state.proofTrees.push tree }
      return Lean.toJson ({ treeId := nextId }: ProofStartResult)
  proof_tactic (args: ProofTactic): Subroutine Lean.Json := do
    let state ← get
    match state.proofTrees.get? args.treeId with
    | .none => return Lean.toJson <| errorIndex "Invalid tree index {args.treeId}"
    | .some tree =>
      let (result, nextTree) ← Meta.ProofM.execute args.stateId args.goalId args.tactic |>.run tree
      match result with
      | .invalid message => return Lean.toJson <| errorIndex message
      | .success nextId goals =>
        set { state with proofTrees := state.proofTrees.set! args.treeId nextTree }
        return Lean.toJson ({ nextId := nextId, goals := goals }: ProofTacticResultSuccess)
      | .failure messages =>
        return Lean.toJson ({ errorMessages := messages }: ProofTacticResultFailure)
  proof_print_tree (args: ProofPrintTree): Subroutine Lean.Json := do
    let state ← get
    match state.proofTrees.get? args.treeId with
    | .none => return Lean.toJson <| errorIndex "Invalid tree index {args.treeId}"
    | .some tree =>
      let parents := tree.states.map λ state => match state.parent with
        | .none => ""
        | .some parent => s!"{parent}.{state.parentGoalId}"
      return Lean.toJson ({parents := parents}: ProofPrintTreeResult)


end Pantograph


-- Main IO functions
open Pantograph

unsafe def loop : Subroutine Unit := do
  let command ← (← IO.getStdin).getLine
  match parse_command command with
  | .error _ =>
    -- Halt execution if command is empty
    return ()
  | .ok command =>
    let ret ← execute command
    IO.println <| toString <| ret
  loop

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let context: Context := {
    coreContext := {
      currNamespace := str_to_name "Aniva",
      openDecls := [],     -- No 'open' directives needed
      fileName := "<Pantograph>",
      fileMap := { source := "", positions := #[0], lines := #[1] }
    }
  }
  try
    loop.run context |>.run' {}
  catch ex =>
    IO.println "Uncaught IO exception"
    IO.println ex.toString
