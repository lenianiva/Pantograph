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

structure ProofTrace where
  id: Nat -- Environment id
  deriving Lean.FromJson
structure ProofTraceResult where
  expr: String
  deriving Lean.ToJson

end Pantograph.Commands
