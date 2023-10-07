import LSpec
import Pantograph.Tactic
import Pantograph.Serial

namespace Pantograph.Test.Holes
open Pantograph
open Lean

abbrev TestM := StateRefT LSpec.TestSeq (ReaderT Commands.Options M)

deriving instance DecidableEq, Repr for Commands.Expression
deriving instance DecidableEq, Repr for Commands.Variable
deriving instance DecidableEq, Repr for Commands.Goal

def add_test (test: LSpec.TestSeq): TestM Unit := do
  set $ (← get) ++ test

def start_goal (hole: String): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  let syn? := syntax_from_str env hole
  add_test $ LSpec.check s!"Parsing {hole}" (syn?.isOk)
  match syn? with
  | .error error =>
    IO.println error
    return Option.none
  | .ok syn =>
    let expr? ← syntax_to_expr syn
    add_test $ LSpec.check s!"Elaborating" expr?.isOk
    match expr? with
    | .error error =>
      IO.println error
      return Option.none
    | .ok expr =>
      let goal ← GoalState.create (expr := expr)
      return Option.some goal

def assert_unreachable (message: String): LSpec.TestSeq := LSpec.check message false

def build_goal (nameType: List (String × String)) (target: String): Commands.Goal :=
  {
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      name := x.fst,
      type? := .some { pp? := .some x.snd },
      isInaccessible? := .some false
    })).toArray
  }
-- Like `build_goal` but allow certain variables to be elided.
def build_goal_selective (nameType: List (String × Option String)) (target: String): Commands.Goal :=
  {
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      name := x.fst,
      type? := x.snd.map (λ type => { pp? := type }),
      isInaccessible? := x.snd.map (λ _ => false)
    })).toArray
  }

def construct_sigma: TestM Unit := do
  let goal? ← start_goal "∀ (n m: Nat), n + m = m + n"
  add_test $ LSpec.check "Start goal" goal?.isSome
  if let .some goal := goal? then
    return ()


def proof_runner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
  let termElabM := tests.run LSpec.TestSeq.done |>.run {} -- with default options

  let coreContext: Lean.Core.Context := {
    currNamespace := str_to_name "Aniva",
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0], lines := #[1] }
  }
  let metaM := termElabM.run' (ctx := {
    declName? := some "_pantograph",
    errToSorry := false
  })
  let coreM := metaM.run'
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok (_, a) =>
    return a

def suite: IO LSpec.TestSeq := do
  let env: Lean.Environment ← Lean.importModules
    (imports := #["Init"].map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  let tests := [
    ("Σ'", construct_sigma)
  ]
  let tests ← tests.foldlM (fun acc tests => do
    let (name, tests) := tests
    let tests ← proof_runner env tests
    return acc ++ (LSpec.group name tests)) LSpec.TestSeq.done

  return LSpec.group "Holes" tests

end Pantograph.Test.Holes
