-- All the command input/output structures are stored here
import Lean.Data.Json

namespace Pantograph.Commands

structure Create where
  imports : List String  := []
  deriving Lean.FromJson
structure CreateResult where
  id: Nat
  symbols: Nat
  filtered_symbols: Nat
  deriving Lean.ToJson

structure Catalog where
  id: Nat
  deriving Lean.FromJson
structure CatalogResult where
  theorems: List String
  deriving Lean.ToJson

structure ClearResult where
  n: Nat -- Number of environments reset
  deriving Lean.ToJson

structure Inspect where
  id: Nat -- Environment id
  symbol: String
  deriving Lean.FromJson
structure InspectResult where
  type: String
  deriving Lean.ToJson

structure ProofTrace where
  id: Nat -- Environment id
  deriving Lean.FromJson
structure ProofTraceResult where
  expr: String
  deriving Lean.ToJson

end Pantograph.Commands
