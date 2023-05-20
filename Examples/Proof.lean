import Lean
import Pantograph.Proofs
import Pantograph.Symbols

open Pantograph

/-
Example of using the internal API to execute tactics!
-/

def execute_proof (env: Lean.Environment): IO Unit := do
  let name := strToName "Nat.add_comm"
  let context := createContext name env
  (do
    let state ← start_proof_state
    IO.println "Proof state started!"
    let tactic := "intro n m"
    let (state, response) ← execute_tactic state tactic
    IO.println s! "Executed {tactic}  Errors: {response.errors}  Goals: {response.goals}"
    let tactic := "assumption" -- should fail
    let (_, response) ← execute_tactic state tactic
    IO.println s! "Executed {tactic}  Errors: {response.errors}  Goals: {response.goals}"
    let tactic := "rw [Nat.add_comm]"
    let (state, response) ← execute_tactic state tactic
    IO.println s! "Executed {tactic}  Errors: {response.errors}  Goals: {response.goals}"
  ) |>.run context

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let imports := ["Init"]
  let env: Lean.Environment ← Lean.importModules
    (imports := imports.map (λ str => { module := strToName str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  execute_proof env
