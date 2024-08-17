import LSpec
import Lean
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Tactic.Prograde

def test_eval : TestT Elab.TermElabM Unit := do
  let expr := "forall (p q : Prop) (h: p), And (Or p q) (Or p q)"
  let expr ← parseSentence expr
  Meta.forallTelescope expr $ λ _ body => do
    let e ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := "Or.inl h")
      (fileName := filename) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let target: Expr := mkAnd
      (mkOr (.fvar ⟨uniq 8⟩) (.fvar ⟨uniq 9⟩))
      (mkOr (.fvar ⟨uniq 8⟩) (.fvar ⟨uniq 9⟩))
    let h := .fvar ⟨uniq 8⟩
    addTest $ LSpec.test "goals before" ((← toCondensedGoal goal.mvarId!).devolatilize == {
      context := #[
        cdeclOf `p (.sort 0),
        cdeclOf `q (.sort 0),
        cdeclOf `h h
      ],
      target,
    })
    let tactic := Tactic.evalDefine `h2 e
    let m := .mvar ⟨uniq 13⟩
    let [newGoal] ← runTacticOnMVar tactic goal.mvarId! | panic! "Incorrect goal number"
    addTest $ LSpec.test "goals after" ((← toCondensedGoal newGoal).devolatilize == {
      context := #[
        cdeclOf `p (.sort 0),
        cdeclOf `q (.sort 0),
        cdeclOf `h h,
        {
          userName := `h2,
          type := mkOr h m,
          value? := .some $ mkApp3 (mkConst `Or.inl) h m (.fvar ⟨uniq 10⟩)
        }
      ],
      target,
    })
    addTest $ LSpec.test "assign" ((← getExprMVarAssignment? goal.mvarId!) == .some (.mvar newGoal))

def test_proof_eval : TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro p q h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals).map (·.devolatilize) =
    #[buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p")] "(p ∨ q) ∨ p ∨ q"])

  let expr := "Or.inl (Or.inl h)"
  let state2 ← match ← state1.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state2.serializeGoals).map (·.devolatilize) =
    #[])

  let evalBind := "y"
  let evalExpr := "Or.inl h"
  let state2 ← match ← state1.tryDefine (goalId := 0) (binderName := evalBind) (expr := evalExpr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"eval {evalBind} := {evalExpr}" ((← state2.serializeGoals).map (·.devolatilize) =
    #[{
      target := { pp? := .some  "(p ∨ q) ∨ p ∨ q"},
      vars := #[
        { userName := "p", type? := .some { pp? := .some "Prop" } },
        { userName := "q", type? := .some { pp? := .some "Prop" } },
        { userName := "h", type? := .some { pp? := .some "p" } },
        { userName := "y",
          type? := .some { pp? := .some "p ∨ ?m.25" },
          value? := .some { pp? := .some "Or.inl h" },
        }
      ]
  }])

  let expr := "Or.inl y"
  let state3 ← match ← state2.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state3.serializeGoals).map (·.devolatilize) =
    #[])

  addTest $ LSpec.check "(3 root)" state3.rootExpr?.isSome

def test_proof_have : TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro p q h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals).map (·.devolatilize) =
    #[buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p")] "(p ∨ q) ∨ p ∨ q"])

  let expr := "Or.inl (Or.inl h)"
  let state2 ← match ← state1.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state2.serializeGoals).map (·.devolatilize) =
    #[])

  let haveBind := "y"
  let haveType := "p ∨ q"
  let state2 ← match ← state1.tryHave (goalId := 0) (binderName := haveBind) (type := haveType) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!"have {haveBind}: {haveType}" ((← state2.serializeGoals).map (·.devolatilize) =
    #[
      buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p")] "p ∨ q",
      buildGoal [("p", "Prop"), ("q", "Prop"), ("h", "p"), ("y", "p ∨ q")] "(p ∨ q) ∨ p ∨ q"
    ])

  let expr := "Or.inl h"
  let state3 ← match ← state2.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state3.serializeGoals).map (·.devolatilize) =
    #[])

  let state2b ← match state3.continue state2 with
    | .ok state => pure state
    | .error e => do
      addTest $ assertUnreachable e
      return ()
  let expr := "Or.inl y"
  let state4 ← match ← state2b.tryAssign (goalId := 0) (expr := expr) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check s!":= {expr}" ((← state4.serializeGoals).map (·.devolatilize) =
    #[])

  addTest $ LSpec.check "(4 root)" state4.rootExpr?.isSome

def test_let (specialized: Bool): TestT Elab.TermElabM Unit := do
  let rootExpr ← parseSentence "∀ (p q: Prop), p → ((p ∨ q) ∨ (p ∨ q))"
  let state0 ← GoalState.create rootExpr
  let tactic := "intro a p h"
  let state1 ← match ← state0.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state1.serializeGoals).map (·.devolatilize) =
    #[{
      target := { pp? := .some mainTarget },
      vars := interiorVars,
    }])

  let letType := "Nat"
  let expr := s!"let b: {letType} := _; _"
  let result2 ← match specialized with
    | true => state1.tryLet (goalId := 0) (binderName := "b") (type := letType)
    | false => state1.tryAssign (goalId := 0) (expr := expr)
  let state2 ← match result2 with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  let serializedState2 ← state2.serializeGoals
  let letBindName := if specialized then "b" else "_1"
  addTest $ LSpec.check expr (serializedState2.map (·.devolatilize) =
    #[{
      target := { pp? := .some letType },
      vars := interiorVars,
      userName? := .some letBindName
    },
    {
      target := { pp? := .some mainTarget },
      vars := interiorVars ++ #[{
        userName := "b",
        type? := .some { pp? := .some letType },
        value? := .some { pp? := .some s!"?{letBindName}" },
      }],
      userName? := if specialized then .none else .some "_2",
    }
    ])

  let tactic := "exact 1"
  let state3 ← match ← state2.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.check tactic ((← state3.serializeGoals).map (·.devolatilize) = #[])

  let state3r ← match state3.continue state2 with
    | .error msg => do
      addTest $ assertUnreachable $ msg
      return ()
    | .ok state => pure state
  addTest $ LSpec.check "(continue)" ((← state3r.serializeGoals).map (·.devolatilize) =
    #[
    {
      target := { pp? := .some mainTarget },
      vars := interiorVars ++ #[{
        userName := "b",
        type? := .some { pp? := .some "Nat" },
        value? := .some { pp? := .some "1" },
      }],
      userName? := if specialized then .none else .some "_2",
    }
    ])

  let tactic := "exact h"
  match ← state3r.tryTactic (goalId := 0) (tactic := tactic) with
  | .failure #[message] =>
    addTest $ LSpec.check tactic  (message = s!"type mismatch\n  h\nhas type\n  a : Prop\nbut is expected to have type\n  {mainTarget} : Prop")
  | other => do
    addTest $ assertUnreachable $ other.toString

  let tactic := "exact Or.inl (Or.inl h)"
  let state4 ← match ← state3r.tryTactic (goalId := 0) (tactic := tactic) with
    | .success state => pure state
    | other => do
      addTest $ assertUnreachable $ other.toString
      return ()
  addTest $ LSpec.test "(4 root)" state4.rootExpr?.isSome
  where
    mainTarget := "(a ∨ p) ∨ a ∨ p"
    interiorVars: Array Protocol.Variable := #[
        { userName := "a", type? := .some { pp? := .some "Prop" }, },
        { userName := "p", type? := .some { pp? := .some "Prop" }, },
        { userName := "h", type? := .some { pp? := .some "a" }, }
      ]

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("eval", test_eval),
    ("Proof eval", test_proof_eval),
    ("Proof have", test_proof_have),
    ("let via assign", test_let false),
    ("let via tryLet", test_let true),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))

end Pantograph.Test.Tactic.Prograde
