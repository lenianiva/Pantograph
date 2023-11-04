import LSpec
import Pantograph.Goal
import Pantograph.Serial
import Test.Common

namespace Pantograph.Test.Holes
open Pantograph
open Lean

abbrev TestM := StateRefT LSpec.TestSeq (ReaderT Protocol.Options M)

def addTest (test: LSpec.TestSeq): TestM Unit := do
  set $ (← get) ++ test

def startProof (expr: String): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  let syn? := syntax_from_str env expr
  addTest $ LSpec.check s!"Parsing {expr}" (syn?.isOk)
  match syn? with
  | .error error =>
    IO.println error
    return Option.none
  | .ok syn =>
    let expr? ← syntax_to_expr_type syn
    addTest $ LSpec.check s!"Elaborating" expr?.isOk
    match expr? with
    | .error error =>
      IO.println error
      return Option.none
    | .ok expr =>
      let goal ← GoalState.create (expr := expr)
      return Option.some goal

def buildGoal (nameType: List (String × String)) (target: String) (userName?: Option String := .none): Protocol.Goal :=
  {
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
      isInaccessible? := .some false
    })).toArray
  }
def proofRunner (env: Lean.Environment) (tests: TestM Unit): IO LSpec.TestSeq := do
  let termElabM := tests.run LSpec.TestSeq.done |>.run {} -- with default options

  let coreContext: Lean.Core.Context := {
    currNamespace := Name.append .anonymous "Aniva",
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

/-- M-coupled goals -/
def test_m_couple: TestM Unit := do
  let state? ← startProof "(2: Nat) ≤ 5"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.execute (goalId := 0) (tactic := "apply Nat.le_trans") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply Nat.le_trans" ((← state1.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ ?m", .some "?m ≤ 5", .some "Nat"])
  addTest $ LSpec.test "(1 root)" state1.rootExpr?.isNone
  -- Set m to 3
  let state2 ← match ← state1.execute (goalId := 2) (tactic := "exact 3") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "(1b root)" state2.rootExpr?.isNone
  let state1b ← match state2.continue state1 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "exact 3" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ 3", .some "3 ≤ 5"])
  addTest $ LSpec.test "(2 root)" state1b.rootExpr?.isNone
  return ()

def test_proposition_generation: TestM Unit := do
  let state? ← startProof "Σ' p:Prop, p"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.execute (goalId := 0) (tactic := "apply PSigma.mk") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply PSigma.mk" ((← state1.serializeGoals (options := ← read)).map (·.devolatilize) =
    #[
      buildGoal [] "?fst" (userName? := .some "snd"),
      buildGoal [] "Prop" (userName? := .some "fst")
      ])
  if let #[goal1, goal2] := ← state1.serializeGoals (options := { (← read) with printExprAST := true }) then
    addTest $ LSpec.test "(1 reference)" (goal1.target.sexp? = .some s!"(:mv {goal2.name})")
  addTest $ LSpec.test "(1 root)" state1.rootExpr?.isNone

  let state2 ← match ← state1.tryAssign (goalId := 0) (expr := "λ (x: Nat) => _") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check ":= λ (x: Nat), _" ((← state2.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "Nat → Prop", .some "∀ (x : Nat), ?m.29 x"])
  addTest $ LSpec.test "(2 root)" state2.rootExpr?.isNone

  let state3 ← match ← state2.tryAssign (goalId := 1) (expr := "fun x => Eq.refl x") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check ":= Eq.refl" ((← state3.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[])

  addTest $ LSpec.test "(3 root)" state3.rootExpr?.isSome
  return ()

def test_partial_continuation: TestM Unit := do
  let state? ← startProof "(2: Nat) ≤ 5"
  let state0 ← match state? with
    | .some state => pure state
    | .none => do
      addTest $ assertUnreachable "Goal could not parse"
      return ()

  let state1 ← match ← state0.execute (goalId := 0) (tactic := "apply Nat.le_trans") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply Nat.le_trans" ((← state1.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ ?m", .some "?m ≤ 5", .some "Nat"])

  let state2 ← match ← state1.execute (goalId := 2) (tactic := "apply Nat.succ") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check "apply Nat.succ" ((← state2.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "Nat"])

  -- Execute a partial continuation
  let coupled_goals := state1.goals ++ state2.goals
  let state1b ← match state2.resume (goals := coupled_goals) with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "(continue)" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ Nat.succ ?m", .some "Nat.succ ?m ≤ 5", .some "Nat"])
  addTest $ LSpec.test "(2 root)" state1b.rootExpr?.isNone

  -- Continuation should fail if the state does not exist:
  match state0.resume coupled_goals with
  | .error error => addTest $ LSpec.check "(continuation failure message)" (error = "Goals not in scope")
  | .ok _ => addTest $ assertUnreachable "(continuation failure)"
  -- Continuation should fail if some goals have not been solved
  match state2.continue state1 with
  | .error error => addTest $ LSpec.check "(continuation failure message)" (error = "Target state has unresolved goals")
  | .ok _ => addTest $ assertUnreachable "(continuation failure)"
  return ()


def suite: IO LSpec.TestSeq := do
  let env: Lean.Environment ← Lean.importModules
    (imports := #["Init"].map (λ str => { module := str_to_name str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)
  let tests := [
    ("2 < 5", test_m_couple),
    ("Proposition Generation", test_proposition_generation),
    ("Partial Continuation", test_partial_continuation)
  ]
  let tests ← tests.foldlM (fun acc tests => do
    let (name, tests) := tests
    let tests ← proofRunner env tests
    return acc ++ (LSpec.group name tests)) LSpec.TestSeq.done

  return LSpec.group "Holes" tests

end Pantograph.Test.Holes
