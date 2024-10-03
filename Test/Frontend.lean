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
    return Frontend.collectSorrys step
  let li ← m.run context |>.run' state
  let goalStates ← li.filterMapM λ sorrys => do
    if sorrys.isEmpty then
      return .none
    let goalState ← Frontend.sorrysToGoalState sorrys
    return .some goalState
  return goalStates

def test_multiple_sorries_in_proof : TestT MetaM Unit := do
  let sketch := "
theorem plus_n_Sm_proved_formal_sketch : ∀ n m : Nat, n + (m + 1) = (n + m) + 1 := by
   have h_nat_add_succ: ∀ n m : Nat, n = m := sorry
   sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! "Illegal number of states"
  addTest $ LSpec.check "plus_n_Sm" ((← goalState.serializeGoals (options := {})) = #[
    {
      name := "_uniq.1",
      target := { pp? := "∀ (n m : Nat), n = m" },
      vars := #[
      ]
    },
    {
      name := "_uniq.4",
      target := { pp? := "∀ (n m : Nat), n + (m + 1) = n + m + 1" },
      vars := #[{
        name := "_uniq.3",
        userName := "h_nat_add_succ",
        type? := .some { pp? := "∀ (n m : Nat), n = m" },
      }],
    }
  ])


def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("multiple_sorrys_in_proof", test_multiple_sorries_in_proof),
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))

end Pantograph.Test.Frontend
