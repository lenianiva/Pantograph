import LSpec
import Pantograph.Goal
import Pantograph.Serial
import Test.Common
import Lean

namespace Pantograph.Test.Metavar
open Pantograph
open Lean

abbrev TestM := StateRefT LSpec.TestSeq (ReaderT Protocol.Options M)

def addTest (test: LSpec.TestSeq): TestM Unit := do
  set $ (← get) ++ test

-- Tests that all delay assigned mvars are instantiated
def test_instantiate_mvar: TestM Unit := do
  let env ← Lean.MonadEnv.getEnv
  let value := "@Nat.le_trans 2 2 5 (@of_eq_true (@LE.le Nat instLENat 2 2) (@eq_true (@LE.le Nat instLENat 2 2) (@Nat.le_refl 2))) (@of_eq_true (@LE.le Nat instLENat 2 5) (@eq_true_of_decide (@LE.le Nat instLENat 2 5) (@Nat.decLe 2 5) (@Eq.refl Bool Bool.true)))"
  let syn ← match parseTerm env value with
    | .ok s => pure $ s
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let expr ← match ← elabTerm syn with
    | .ok expr => pure $ expr
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let t ← Lean.Meta.inferType expr
  addTest $ LSpec.check "typing" ((toString (← serialize_expression_ast t)) =
    "((:c LE.le) (:c Nat) (:c instLENat) ((:c OfNat.ofNat) (:mv _uniq.2) (:lit 2) (:mv _uniq.3)) ((:c OfNat.ofNat) (:mv _uniq.14) (:lit 5) (:mv _uniq.15)))")
  return ()



def startProof (expr: String): TestM (Option GoalState) := do
  let env ← Lean.MonadEnv.getEnv
  let syn? := parseTerm env expr
  addTest $ LSpec.check s!"Parsing {expr}" (syn?.isOk)
  match syn? with
  | .error error =>
    IO.println error
    return Option.none
  | .ok syn =>
    let expr? ← elabType syn
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

  let coreContext: Lean.Core.Context ← createCoreContext #[]
  let metaM := termElabM.run' (ctx := defaultTermElabMContext)
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

def test_m_couple_simp: TestM Unit := do
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
  let state2 ← match ← state1.execute (goalId := 2) (tactic := "exact 2") with
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
  addTest $ LSpec.check "exact 2" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ 2", .some "2 ≤ 5"])
  addTest $ LSpec.test "(2 root)" state1b.rootExpr?.isNone
  let state3 ← match ← state1b.execute (goalId := 0) (tactic := "simp") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let state4 ← match state3.continue state1b with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  let state5 ← match ← state4.execute (goalId := 0) (tactic := "simp") with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()

  state5.restoreMetaM
  let root ← match state5.rootExpr? with
    | .some e => pure e
    | .none =>
      addTest $ assertUnreachable "(5 root)"
      return ()
  let rootStr: String := toString (← Lean.Meta.ppExpr root)
  addTest $ LSpec.check "(5 root)" (rootStr = "Nat.le_trans (of_eq_true (Init.Data.Nat.Basic._auxLemma.4 2)) (of_eq_true (eq_true_of_decide (Eq.refl true)))")
  let unfoldedRoot ←  unfoldAuxLemmas root
  addTest $ LSpec.check "(5 root)" ((toString (← Lean.Meta.ppExpr unfoldedRoot)) =
    "Nat.le_trans (of_eq_true (eq_true (Nat.le_refl 2))) (of_eq_true (eq_true_of_decide (Eq.refl true)))")
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
    #[.some "2 ≤ ?m.succ", .some "?m.succ ≤ 5", .some "Nat"])
  addTest $ LSpec.test "(2 root)" state1b.rootExpr?.isNone

  -- Roundtrip
  --let coupled_goals := coupled_goals.map (λ g =>
  --  { name := str_to_name $ name_to_ast g.name (sanitize := false)})
  let coupled_goals := coupled_goals.map (λ g => name_to_ast g.name (sanitize := false))
  let coupled_goals := coupled_goals.map (λ g => { name := g.toName })
  let state1b ← match state2.resume (goals := coupled_goals) with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "(continue)" ((← state1b.serializeGoals (options := ← read)).map (·.target.pp?) =
    #[.some "2 ≤ ?m.succ", .some "?m.succ ≤ 5", .some "Nat"])
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


def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("Instantiate", test_instantiate_mvar),
    ("2 < 5", test_m_couple),
    ("2 < 5", test_m_couple_simp),
    ("Proposition Generation", test_proposition_generation),
    ("Partial Continuation", test_partial_continuation)
  ]
  tests.map (fun (name, test) => (name, proofRunner env test))

end Pantograph.Test.Metavar
