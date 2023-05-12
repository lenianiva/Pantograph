-- All the command input/output structures are stored here
import Lean.Data.Json

namespace Pantograph.Commands

structure Create where
  imports : List String
  deriving Lean.FromJson
structure Catalog where
  id: Nat
  deriving Lean.FromJson

structure CreateResult where
  id: Nat
  symbols: Nat
  filtered_symbols: Nat
  deriving Lean.ToJson
structure CatalogResult where
  theorems: List String
  deriving Lean.ToJson
structure ClearResult where
  n: Nat -- Number of environments reset
  deriving Lean.ToJson

end Pantograph.Commands
