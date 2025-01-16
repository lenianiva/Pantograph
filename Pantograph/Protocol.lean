/-
All the command input/output structures are stored here

Note that no command other than `InteractionError` may have `error` as one of
its field names to avoid confusion with error messages generated by the REPL.
-/
import Lean.Data.Json
import Lean.Data.Position

namespace Pantograph.Protocol


/-- Main Option structure, placed here to avoid name collision -/
structure Options where
  -- When false, suppress newlines in Json objects. Useful for machine-to-machine interaction.
  -- This should be  false` by default to avoid any surprises with parsing.
  printJsonPretty: Bool    := false
  -- When enabled, pretty print every expression
  printExprPretty: Bool    := true
  -- When enabled, print the raw AST of expressions
  printExprAST: Bool       := false
  printDependentMVars: Bool := false
  -- When enabled, the types and values of persistent variables in a goal
  -- are not shown unless they are new to the proof step. Reduces overhead.
  -- NOTE: that this assumes the type and assignment of variables can never change.
  noRepeat: Bool := false
  -- See `pp.auxDecls`
  printAuxDecls: Bool      := false
  -- See `pp.implementationDetailHyps`
  printImplementationDetailHyps: Bool := false
  -- If this is set to `true`, goals will never go dormant, so you don't have to manage resumption
  automaticMode: Bool := true
  deriving Lean.ToJson

abbrev OptionsT := ReaderT Options

--- Expression Objects ---

structure BoundExpression where
  binders: Array (String × String)
  target: String
  deriving Lean.ToJson
structure Expression where
  -- Pretty printed expression
  pp?: Option String             := .none
  -- AST structure
  sexp?: Option String           := .none
  dependentMVars?: Option (Array String) := .none
  deriving Lean.ToJson

structure Variable where
  /-- The internal name used in raw expressions -/
  name: String := ""
  /-- The name displayed to the user -/
  userName: String
  /-- Does the name contain a dagger -/
  isInaccessible: Bool := false
  type?: Option Expression  := .none
  value?: Option Expression := .none
  deriving Lean.ToJson
structure Goal where
  name: String := ""
  /-- Name of the metavariable -/
  userName?: Option String  := .none
  /-- Is the goal in conversion mode -/
  isConversion: Bool        := false
  /-- target expression type -/
  target: Expression
  /-- Variables -/
  vars: Array Variable      := #[]
  deriving Lean.ToJson



--- Individual Commands and return types ---

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

structure InteractionError where
  error: String
  desc: String
  deriving Lean.ToJson

def errorIndex (desc: String): InteractionError := { error := "index", desc }
def errorExpr (desc: String): InteractionError := { error := "expr", desc }


--- Individual command and return types ---


structure Reset where
  deriving Lean.FromJson
structure Stat where
  deriving Lean.FromJson
structure StatResult where
  -- Number of goals states
  nGoals: Nat
  deriving Lean.ToJson

-- Return the type of an expression
structure ExprEcho where
  expr: String
  type?: Option String
  -- universe levels
  levels: Option (Array String) := .none
  deriving Lean.FromJson
structure ExprEchoResult where
  expr: Expression
  type: Expression
  deriving Lean.ToJson

-- Describe the current state of the environment
structure EnvDescribe where
  deriving Lean.FromJson
structure EnvDescribeResult where
  imports : Array String
  modules : Array String
  deriving Lean.ToJson

-- Describe a module
structure EnvModuleRead where
  module : String
  deriving Lean.FromJson
structure EnvModuleReadResult where
  imports: Array String
  constNames: Array String
  extraConstNames: Array String
  deriving Lean.ToJson

-- Print all symbols in environment
structure EnvCatalog where
  deriving Lean.FromJson
structure EnvCatalogResult where
  symbols: Array String
  deriving Lean.ToJson

-- Print the type of a symbol
structure EnvInspect where
  name: String
  -- Show the value expressions; By default definitions values are shown and
  -- theorem values are hidden.
  value?: Option Bool := .some false
  -- Show the type and value dependencies
  dependency?: Option Bool := .some false
  -- Show source location
  source?: Option Bool := .some false
  deriving Lean.FromJson
-- See `InductiveVal`
structure InductInfo where
  numParams: Nat
  numIndices: Nat
  all: Array String
  ctors: Array String
  isRec:       Bool := false
  isReflexive: Bool := false
  isNested:    Bool := false
  deriving Lean.ToJson
-- See `ConstructorVal`
structure ConstructorInfo where
  induct: String
  cidx: Nat
  numParams: Nat
  numFields: Nat
  deriving Lean.ToJson

/-- See `Lean/Declaration.lean` -/
structure RecursorRule where
  ctor: String
  nFields: Nat
  rhs: Expression
  deriving Lean.ToJson
structure RecursorInfo where
  all: Array String
  numParams: Nat
  numIndices: Nat
  numMotives: Nat
  numMinors: Nat
  rules: Array RecursorRule
  k: Bool
  deriving Lean.ToJson
structure EnvInspectResult where
  type: Expression
  isUnsafe: Bool            := false
  value?: Option Expression := .none
  module?: Option String    := .none
  -- If the name is private, displays the public facing name
  publicName?: Option String := .none
  typeDependency?: Option (Array String) := .none
  valueDependency?: Option (Array String) := .none
  inductInfo?:      Option InductInfo      := .none
  constructorInfo?: Option ConstructorInfo := .none
  recursorInfo?:    Option RecursorInfo    := .none

  -- Location in source
  sourceUri?: Option String := .none
  sourceStart?: Option Lean.Position := .none
  sourceEnd?: Option Lean.Position := .none
  deriving Lean.ToJson

structure EnvAdd where
  name: String
  type: String
  value: String
  isTheorem: Bool
  deriving Lean.FromJson
structure EnvAddResult where
  deriving Lean.ToJson

structure EnvSaveLoad where
  path: System.FilePath
  deriving Lean.FromJson
structure EnvSaveLoadResult where
  deriving Lean.ToJson

/-- Set options; See `Options` struct above for meanings -/
structure OptionsSet where
  printJsonPretty?: Option Bool
  printExprPretty?: Option Bool
  printExprAST?: Option Bool
  printDependentMVars?: Option Bool
  noRepeat?: Option Bool
  printAuxDecls?: Option Bool
  printImplementationDetailHyps?: Option Bool
  automaticMode?: Option Bool
  deriving Lean.FromJson
structure OptionsSetResult where
  deriving Lean.ToJson
structure OptionsPrint where
  deriving Lean.FromJson

structure GoalStart where
  -- Only one of the fields below may be populated.
  expr: Option String     -- Directly parse in an expression
  -- universe levels
  levels: Option (Array String) := .none
  copyFrom: Option String -- Copy the type from a theorem in the environment
  deriving Lean.FromJson
structure GoalStartResult where
  stateId: Nat := 0
  -- Name of the root metavariable
  root: String
  deriving Lean.ToJson
structure GoalTactic where
  -- Identifiers for tree, state, and goal
  stateId: Nat
  goalId: Nat := 0
  -- One of the fields here must be filled
  tactic?: Option String := .none
  expr?: Option String := .none
  have?: Option String := .none
  let?: Option String := .none
  calc?: Option String := .none
  -- true to enter `conv`, `false` to exit. In case of exit the `goalId` is ignored.
  conv?: Option Bool := .none

  -- In case of the `have` tactic, the new free variable name is provided here
  binderName?: Option String := .none

  deriving Lean.FromJson
structure GoalTacticResult where
  -- The next goal state id. Existence of this field shows success
  nextStateId?: Option Nat          := .none
  -- If the array is empty, it shows the goals have been fully resolved.
  goals?: Option (Array Goal)          := .none

  -- Existence of this field shows tactic execution failure
  tacticErrors?: Option (Array String) := .none

  -- Existence of this field shows the tactic parsing has failed
  parseError?: Option String := .none
  deriving Lean.ToJson
structure GoalContinue where
  -- State from which the continuation acquires the context
  target: Nat

  -- One of the following must be supplied
  -- The state which is an ancestor of `target` where goals will be extracted from
  branch?: Option Nat := .none
  -- Or, the particular goals that should be brought back into scope
  goals?: Option (Array String) := .none
  deriving Lean.FromJson
structure GoalContinueResult where
  nextStateId: Nat
  goals: (Array Goal)
  deriving Lean.ToJson

-- Remove goal states
structure GoalDelete where
  -- This is ok being a List because it doesn't show up in the ABI
  stateIds: List Nat
  deriving Lean.FromJson
structure GoalDeleteResult where
  deriving Lean.ToJson

structure GoalPrint where
  stateId: Nat

  -- Print root?
  rootExpr?: Option Bool := .some False
  -- Print the parent expr?
  parentExpr?: Option Bool := .some False
  -- Print goals?
  goals?: Option Bool := .some False
  -- Print values of extra mvars?
  extraMVars?: Option (Array String) := .none
  deriving Lean.FromJson
structure GoalPrintResult where
  -- The root expression
  root?: Option Expression := .none
  -- The filling expression of the parent goal
  parent?: Option Expression := .none
  goals: Array Goal := #[]
  extraMVars: Array Expression := #[]
  deriving Lean.ToJson

-- Diagnostic Options, not available in REPL
structure GoalDiag where
  printContext: Bool := true
  printValue: Bool := true
  printNewMVars: Bool := false
  -- Print all mvars
  printAll: Bool := false
  instantiate: Bool := true
  printSexp: Bool := false

structure GoalSave where
  id: Nat
  path: System.FilePath
  deriving Lean.FromJson
structure GoalSaveResult where
  deriving Lean.ToJson
structure GoalLoad where
  path: System.FilePath
  deriving Lean.FromJson
structure GoalLoadResult where
  id: Nat
  deriving Lean.ToJson


/-- Executes the Lean compiler on a single file -/
structure FrontendProcess where
  -- One of these two must be supplied: Either supply the file name or the content.
  fileName?: Option String := .none
  file?: Option String := .none
  -- collect tactic invocations
  invocations: Bool := false
  -- collect `sorry`s
  sorrys: Bool := false
  -- collect type errors
  typeErrorsAsGoals: Bool := false
  -- list new constants from each compilation step
  newConstants: Bool := false
  deriving Lean.FromJson
structure InvokedTactic where
  goalBefore: String
  goalAfter: String
  tactic: String

  -- List of used constants
  usedConstants: Array String
  deriving Lean.ToJson

structure CompilationUnit where
  -- String boundaries of compilation units
  boundary: (Nat × Nat)
  messages: Array String := #[]
  -- Tactic invocations
  invocations?: Option (List InvokedTactic) := .none
  goalStateId?: Option Nat := .none
  goals?: Option (Array Goal) := .none
  -- Code segments which generated the goals
  goalSrcBoundaries?: Option (Array (Nat × Nat)) := .none

  -- New constants defined in compilation unit
  newConstants?: Option (Array String) := .none
  deriving Lean.ToJson
structure FrontendProcessResult where
  units: List CompilationUnit
  deriving Lean.ToJson

abbrev CR α := Except InteractionError α

end Pantograph.Protocol
