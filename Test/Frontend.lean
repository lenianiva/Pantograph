import LSpec
import Pantograph
import Repl
import Test.Common

open Lean Pantograph
namespace Pantograph.Test.Frontend

def collectSorrysFromSource (source: String) : MetaM (List GoalState) := do
  let filename := "<anonymous>"
  let (context, state) ← do Frontend.createContextStateFromFile source filename (← getEnv) {}
  let m := Frontend.mapCompilationSteps λ step => do
    return (step.before, Frontend.collectSorrys step)
  let li ← m.run context |>.run' state
  let goalStates ← li.filterMapM λ (env, sorrys) => withEnv env do
    if sorrys.isEmpty then
      return .none
    let goalState ← Frontend.sorrysToGoalState sorrys
    return .some goalState
  return goalStates

def test_multiple_sorrys_in_proof : TestT MetaM Unit := do
  let sketch := "
theorem plus_n_Sm_proved_formal_sketch : ∀ n m : Nat, n + (m + 1) = (n + m) + 1 := by
   have h_nat_add_succ: ∀ n m : Nat, n = m := sorry
   sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! "Incorrect number of states"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "∀ (n m : Nat), n = m" },
      vars := #[
      ]
    },
    {
      target := { pp? := "∀ (n m : Nat), n + (m + 1) = n + m + 1" },
      vars := #[{
        userName := "h_nat_add_succ",
        type? := .some { pp? := "∀ (n m : Nat), n = m" },
      }],
    }
  ])

def test_sorry_in_middle: TestT MetaM Unit := do
  let sketch := "
example : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "n + m = m + n" },
      vars := #[{
           userName := "n",
           type? := .some { pp? := "Nat" },
        }, {
           userName := "m",
           type? := .some { pp? := "Nat" },
        }
      ],
    }
  ])

def test_sorry_in_induction : TestT MetaM Unit := do
  let sketch := "
example : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  induction n with
  | zero =>
    have h1 : 0 + m = m := sorry
    sorry
  | succ n ih =>
    have h2 : n + m = m := sorry
    sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "0 + m = m" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }]
    },
    {
      userName? := .some "zero",
      target := { pp? := "0 + m = m + 0" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "h1",
        type? := .some { pp? := "0 + m = m" },
      }]
    },
    {
      target := { pp? := "n + m = m" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "n",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "ih",
        type? := .some { pp? := "n + m = m + n" },
      }]
    },
    {
      userName? := .some "succ",
      target := { pp? := "n + 1 + m = m + (n + 1)" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "n",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "ih",
        type? := .some { pp? := "n + m = m + n" },
      },  {
        userName := "h2",
        type? := .some { pp? := "n + m = m" },
      }]
    }
  ])

def test_sorry_in_coupled: TestT MetaM Unit := do
  let sketch := "
example : ∀ (y: Nat), ∃ (x: Nat), y + 1 = x := by
  intro y
  apply Exists.intro
  case h => sorry
  case w => sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "y + 1 = ?w" },
      vars := #[{
           userName := "y",
           type? := .some { pp? := "Nat" },
        }
      ],
    },
    {
      userName? := .some "w",
      target := { pp? := "Nat" },
      vars := #[{
           userName := "y",
           type? := .some { pp? := "Nat" },
        }
      ],
    }
  ])

def test_environment_capture: TestT MetaM Unit := do
  let sketch := "
def mystery (n: Nat) := n + 1

example (n: Nat) : mystery n + 1 = n + 2 := sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "mystery n + 1 = n + 2" },
      vars := #[{
         userName := "n",
         type? := .some { pp? := "Nat" },
      }],
    }
  ])

def collectInvocationsFromSource (source: String) : MetaM (List (List Protocol.InvokedTactic)) := do
  let filename := "<anonymous>"
  let (context, state) ← do Frontend.createContextStateFromFile source filename (← getEnv) {}
  let m := Frontend.mapCompilationSteps λ step => do
    return (step.before, ← Frontend.collectTacticsFromCompilationStep step)
  let li ← m.run context |>.run' state
  let invocationLists ← li.mapM λ (env, invocations) => withEnv env do
    return invocations
  return invocationLists

def test_invalid_tactic_syntax: TestT MetaM Unit := do
  let sketch := "
  example : 17 * 2 = 34 := by
    have h1 (x y : ℕ) : (6 * x + 3 * y) = 5 * x - y (mod 7)
  "
  let invocationLists ← collectInvocationsFromSource sketch
  let [[i]] := invocationLists |
    panic s!"Incorrect number of invocations"
  addTest $ LSpec.check "invocations"
    (i.tactic = "<failed to pretty print>")

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("multiple_sorrys_in_proof", test_multiple_sorrys_in_proof),
    ("sorry_in_middle", test_sorry_in_middle),
    ("sorry_in_induction", test_sorry_in_induction),
    ("sorry_in_coupled", test_sorry_in_coupled),
    ("environment_capture", test_environment_capture),
    ("invalid_tactic_syntax", test_invalid_tactic_syntax),
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))

end Pantograph.Test.Frontend
