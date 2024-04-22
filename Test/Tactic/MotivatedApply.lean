import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.MotivatedApply

def valueAndType (recursor: String): MetaM (Expr × Expr) := do
  let recursor ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := recursor)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => throwError "Failed to parse: {error}"
  runTermElabMInMeta do
    let recursor ← Elab.Term.elabTerm (stx := recursor) .none
    let recursorType ← Meta.inferType recursor
    return (recursor, recursorType)


def test_type_extract (env: Environment): IO LSpec.TestSeq :=
  runMetaMSeq env do
    let mut tests := LSpec.TestSeq.done
    let (recursor, recursorType) ← valueAndType "@Nat.brecOn"
    tests := tests ++ LSpec.check "recursorType" ("{motive : Nat → Sort ?u.1} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t" =
      (← exprToStr recursorType))
    let info ← match Tactic.getRecursorInformation recursorType with
      | .some info => pure info
      | .none => throwError "Failed to extract recursor info"
    tests := tests ++ LSpec.check "iMotive" (info.iMotive = 2)
    let motiveType := info.getMotiveType
    tests := tests ++ LSpec.check "motiveType" ("Nat → Sort ?u.1" =
      (← exprToStr motiveType))
    return tests

def test_execute (env: Environment): IO LSpec.TestSeq :=
  let expr := "λ (n t: Nat) => n + 0 = n"
  runMetaMSeq env do
    let (expr, exprType) ← valueAndType expr
    Meta.lambdaTelescope expr $ λ _ body => do
      let recursor ← match Parser.runParserCategory
        (env := ← MonadEnv.getEnv)
        (catName := `term)
        (input := "@Nat.brecOn")
        (fileName := filename) with
        | .ok syn => pure syn
        | .error error => throwError "Failed to parse: {error}"
      let mut tests := LSpec.TestSeq.done
      -- Apply the tactic
      let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
      let tactic := Tactic.motivatedApply recursor
      let test ← runTermElabMInMeta do
        let newGoals ← runTacticOnMVar tactic target.mvarId!
        pure $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) =
          [
            "Nat → Prop",
            "Nat",
            "∀ (t : Nat), Nat.below t → ?motive t",
            "?motive ?m.69 = (n + 0 = n)",
          ])
      tests := tests ++ test
      return tests

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("type_extract", test_type_extract env),
    ("execute", test_execute env),
  ]

end Pantograph.Test.Tactic.MotivatedApply
