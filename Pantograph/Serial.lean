import Lean.Environment
import Lean.Replay
import Init.System.IOError
import Std.Data.HashMap

/-!
Input/Output functions

# Pickling and unpickling objects

By abusing `saveModuleData` and `readModuleData` we can pickle and unpickle objects to disk.
-/

open Lean

namespace Pantograph

/--
Save an object to disk.
If you need to write multiple objects from within a single declaration,
you will need to provide a unique `key` for each.
-/
def pickle {α : Type} (path : System.FilePath) (x : α) (key : Name := by exact decl_name%) : IO Unit :=
  saveModuleData path key (unsafe unsafeCast x)

/--
Load an object from disk.
Note: The returned `CompactedRegion` can be used to free the memory behind the value
of type `α`, using `CompactedRegion.free` (which is only safe once all references to the `α` are
released). Ignoring the `CompactedRegion` results in the data being leaked.
Use `withUnpickle` to call `CompactedRegion.free` automatically.

This function is unsafe because the data being loaded may not actually have type `α`, and this
may cause crashes or other bad behavior.
-/
unsafe def unpickle (α : Type) (path : System.FilePath) : IO (α × CompactedRegion) := do
  let (x, region) ← readModuleData path
  pure (unsafeCast x, region)

/-- Load an object from disk and run some continuation on it, freeing memory afterwards. -/
unsafe def withUnpickle [Monad m] [MonadLiftT IO m] {α β : Type}
    (path : System.FilePath) (f : α → m β) : m β := do
  let (x, region) ← unpickle α path
  let r ← f x
  region.free
  pure r

/--
Pickle an `Environment` to disk.

We only store:
* the list of imports
* the new constants from `Environment.constants`
and when unpickling, we build a fresh `Environment` from the imports,
and then add the new constants.
-/
@[export pantograph_env_pickle_m]
def env_pickle (env : Environment) (path : System.FilePath) : IO Unit :=
  Pantograph.pickle path (env.header.imports, env.constants.map₂)

/--
Unpickle an `Environment` from disk.

We construct a fresh `Environment` with the relevant imports,
and then replace the new constants.
-/
@[export pantograph_env_unpickle_m]
def env_unpickle (path : System.FilePath) : IO (Environment × CompactedRegion) := unsafe do
  let ((imports, map₂), region) ← Pantograph.unpickle (Array Import × PHashMap Name ConstantInfo) path
  let env ← importModules imports {} 0
  return (← env.replay (Std.HashMap.ofList map₂.toList), region)

end Pantograph
