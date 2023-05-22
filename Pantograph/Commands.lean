-- All the command input/output structures are stored here
import Lean.Data.Json

namespace Pantograph.Commands

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

structure InteractionError where
  error: String
  desc: String
  deriving Lean.ToJson


-- Individual command and return types

-- Create a new environment using the given imports
structure Create where
  imports : List String  := []
  deriving Lean.FromJson
structure CreateResult where
  id: Nat
  symbols: Nat
  filtered_symbols: Nat
  deriving Lean.ToJson

-- Print all symbols in environment
structure Catalog where
  id: Nat
  deriving Lean.FromJson
structure CatalogResult where
  theorems: List String
  deriving Lean.ToJson

-- Reset the state of REPL
structure ClearResult where
  nEnv: Nat   -- Number of environments reset
  deriving Lean.ToJson

-- Print the type of a symbol
structure Inspect where
  id: Nat -- Environment id
  symbol: String
  deriving Lean.FromJson
structure InspectResult where
  type: String  := ""
  deriving Lean.ToJson

structure ProofStart where
  id: Nat -- Environment id
  name: String := "Untitled" -- Identifier of the proof
  -- Only one of the fields below may be populated.
  expr: String := "" -- Proof expression
  copyFrom: String := "" -- Theorem name
  deriving Lean.FromJson
structure ProofStartResult where
  error: String := ""
  treeId: Nat := 0 -- Proof tree id
  deriving Lean.ToJson

structure ProofTactic where
  treeId: Nat
  stateId: Nat
  goalId: Nat := 0
  tactic: String
  deriving Lean.FromJson
structure ProofTacticResultSuccess where
  goals: Array String
  nextId: Nat
  deriving Lean.ToJson
structure ProofTacticResultFailure where
  errorMessages: Array String -- Error messages generated by tactic
  deriving Lean.ToJson

structure ProofPrintTree where
  treeId: Nat
  deriving Lean.FromJson
structure ProofPrintTreeResult where
  -- "" if no parents, otherwise "parentId.goalId"
  parents: Array String
  deriving Lean.ToJson

end Pantograph.Commands
