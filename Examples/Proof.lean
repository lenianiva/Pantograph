import Lean
import Pantograph.Meta
import Pantograph.Serial
import Pantograph.Symbols

open Pantograph

/-
Example of using the internal API to execute tactics!
-/

def serialise (result: Meta.TacticResult): String := match result with
  | .invalid message => s!"Invalid: {message}"
  | .success 0 _ => s!"Completed!"
  | .success nextId _ => s!"Success: {nextId}"
  | .failure messages => s!"Failures: {messages}"

def start_proof: IO Meta.ProofTree := do
  let imports := ["Init"]
  let env: Lean.Environment ← Lean.importModules
    (imports := imports.map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  let name := str_to_name "Nat.add_comm"
  let state := Meta.createProofTree
    (name := str_to_name "aa") env
    (coreContext := {
      currNamespace := str_to_name "Aniva",
      openDecls := [],     -- No 'open' directives needed
      fileName := "<Pantograph>",
      fileMap := { source := "", positions := #[0], lines := #[1] }
    })
  let s := "∀ (n m : Nat), n + m = m + n"
  let syn: Lean.Syntax := Serial.syntax_from_str env s |>.toOption |>.get!
  IO.println "Created syntax"
  let expr: Lean.Expr := (← Meta.ProofM.syntax_to_expr syn |>.run' state) |>.toOption |>.get!
  IO.println "Created expr"
  --let expr := env.find? name |>.get! |>.type
  let (_, state) ← Meta.ProofM.start expr |>.run state
  return state

def execute_proof: IO Unit := do
  let state ← start_proof
  IO.println "Proof state started!"
  let tactic := "intro n m"
  let (result, state) ← Meta.ProofM.execute 0 tactic |>.run state
  IO.println s! "Executed {tactic}, Response: [{serialise result}]"
  let tactic := "assumption" -- should fail
  let (result, state) ← Meta.ProofM.execute 1 tactic |>.run state
  IO.println s! "Executed {tactic}, Response: [{serialise result}]"
  let tactic := "rw [Nat.add_comm]"
  let (result, state) ← Meta.ProofM.execute 1 tactic |>.run state
  IO.println s! "Executed {tactic}, Response: [{serialise result}]"

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  execute_proof
