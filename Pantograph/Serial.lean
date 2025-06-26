import Pantograph.Goal

import Lean.Environment
import Lean.Replay
import Std.Data.HashMap

open Lean

/-!
Input/Output functions borrowed from REPL

# Pickling and unpickling objects

By abusing `saveModuleData` and `readModuleData` we can pickle and unpickle objects to disk.
-/

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

abbrev ConstArray := Array (Name × ConstantInfo)
abbrev DistilledEnvironment := Array Import × ConstArray

/-- Boil an environment down to minimal components -/
def distillEnvironment (env : Environment) (background? : Option Environment := .none)
  : DistilledEnvironment :=
  let filter : Name → Bool := match background? with
    | .some env => (¬ env.contains ·)
    | .none => λ _ => true
  let constants : ConstArray := env.constants.map₂.foldl (init := #[]) λ acc name info =>
    if filter name then
      acc.push (name, info)
    else
      acc
  (env.header.imports, constants)
/--
Pickle an `Environment` to disk.

We only store:
* the list of imports
* the new constants from `Environment.constants`
and when unpickling, we build a fresh `Environment` from the imports,
and then add the new constants.
-/
@[export pantograph_env_pickle_m]
def environmentPickle (env : Environment) (path : System.FilePath) (background? : Option Environment := .none)
  : IO Unit :=
  pickle path $ distillEnvironment env background?

deriving instance BEq for Import

def resurrectEnvironment
  (distilled : DistilledEnvironment)
  (background? : Option Environment := .none)
  : IO Environment := do
  let (imports, constArray) := distilled
  let env ← match background? with
    | .none => importModules imports {} 0 (loadExts := true)
    | .some env =>
      assert! env.imports == imports
      pure env
  env.replay (Std.HashMap.ofList constArray.toList)
/--
Unpickle an `Environment` from disk.

We construct a fresh `Environment` with the relevant imports,
and then replace the new constants.
-/
@[export pantograph_env_unpickle_m]
def environmentUnpickle (path : System.FilePath) (background? : Option Environment := .none)
  : IO (Environment × CompactedRegion) := unsafe do
  let (distilled, region) ← unpickle (Array Import × ConstArray) path
  return (← resurrectEnvironment distilled background?, region)


open Lean.Core in
structure CompactCoreState where
  -- env             : Environment
  nextMacroScope  : MacroScope     := firstFrontendMacroScope + 1
  ngen            : NameGenerator  := {}
  -- traceState      : TraceState     := {}
  -- cache           : Cache     := {}
  -- messages        : MessageLog     := {}
  -- infoState       : Elab.InfoState := {}

@[export pantograph_goal_state_pickle_m]
def goalStatePickle (goalState : GoalState) (path : System.FilePath) (background? : Option Environment := .none)
  : IO Unit :=
  let {
    savedState := {
      term := {
        meta := {
          core := {
            env, nextMacroScope, ngen, ..
          },
          meta,
        }
        «elab»,
      },
      tactic
    }
    root,
    parentMVars,
    fragments,
  } := goalState
  pickle path (
    distillEnvironment env background?,

    ({ nextMacroScope, ngen } : CompactCoreState),
    meta,
    «elab»,
    tactic,

    root,
    parentMVars,
    fragments,
  )

@[export pantograph_goal_state_unpickle_m]
def goalStateUnpickle (path : System.FilePath) (background? : Option Environment := .none)
    : IO (GoalState × CompactedRegion) := unsafe do
  let ((
    distilledEnv,

    compactCore,
    meta,
    «elab»,
    tactic,

    root,
    parentMVars,
    fragments,
  ), region) ← Pantograph.unpickle (
    DistilledEnvironment ×

    CompactCoreState ×
    Meta.State ×
    Elab.Term.State ×
    Elab.Tactic.State ×

    MVarId ×
    List MVarId ×
    FragmentMap
  ) path
  let env ← resurrectEnvironment distilledEnv background?
  let goalState := {
    savedState := {
      term := {
        meta := {
          core := {
            compactCore with
            passedHeartbeats := 0,
            env,
          },
          meta,
        },
        «elab»,
      },
      tactic,
    },
    root,
    parentMVars,
    fragments,
  }
  return (goalState, region)

end Pantograph
