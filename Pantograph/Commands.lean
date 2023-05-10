-- All the command input/output structures are stored here
import Lean.Data.Json

namespace Pantograph.Commands

structure Create where
  imports : List String
  deriving Lean.FromJson
structure Catalog where
  id: Nat
  deriving Lean.FromJson

end Pantograph.Commands
