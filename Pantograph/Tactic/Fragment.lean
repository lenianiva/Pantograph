/- Fragmented tactics are the tactics which can give incremental feedback and
whose integrity as a block is crucial to its operation. e.g. `calc` or `conv`.
Here, a unified system handles all fragments.

Inside a tactic fragment, the parser category may be different. An incomplete
fragmented tactic may not be elaboratable..
-/
import Lean.Meta
import Lean.Elab

open Lean

namespace Pantograph

inductive Fragment where
  | calc (prevRhs? : Option Expr)
  | conv (rhs : MVarId) (dormant : List MVarId)

protected def Fragment.enterCalc : Elab.Tactic.TacticM Fragment := do
  return .calc .none
protected def Fragment.enterConv : Elab.Tactic.TacticM Fragment := do
  let goal ← Elab.Tactic.getMainGoal
  let convGoal ← goal.withContext do
    let (rhs, newGoal) ← Elab.Tactic.Conv.mkConvGoalFor (← Elab.Tactic.getMainTarget)
    Elab.Tactic.replaceMainGoal [newGoal.mvarId!]
    pure rhs.mvarId!
  let otherGoals := (← Elab.Tactic.getGoals).filter (· != goal)
  return .conv convGoal otherGoals

protected def Fragment.exit (fragment : Fragment) (goal: MVarId) : Elab.Tactic.TacticM Unit :=
  match fragment with
  | .calc _prevRhs? => Elab.Tactic.setGoals [goal]
  | .conv rhs otherGoals => do
    -- Close all existing goals with `refl`
    for mvarId in (← Elab.Tactic.getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    Elab.Tactic.pruneSolvedGoals
    unless (← Elab.Tactic.getGoals).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{Elab.goalsToMessageData (← Elab.Tactic.getGoals)}"

    Elab.Tactic.setGoals $ [goal] ++ otherGoals
    let targetNew ← instantiateMVars (.mvar rhs)
    let proof ← instantiateMVars (.mvar goal)

    Elab.Tactic.liftMetaTactic1 (·.replaceTargetEq targetNew proof)

structure TacticFragment where
  -- The goal which the fragment acts on
  goal : MVarId
  fragment : Fragment

protected def Fragment.step (fragment : Fragment) (goal : MVarId) (s : String)
  : Elab.Tactic.TacticM (Option TacticFragment) := goal.withContext do
  match fragment with
  | .calc prevRhs? => do
    let .ok stx := Parser.runParserCategory
      (env := ← getEnv)
      (catName := `term)
      (input := s)
      (fileName := ← getFileName) | throwError s!"Failed to parse calc element {s}"
    let `(term|$pred) := stx
    let decl ← goal.getDecl
    let target ← instantiateMVars decl.type
    let tag := decl.userName

    let mut step ← Elab.Term.elabType <| ← do
      if let some prevRhs := prevRhs? then
        Elab.Term.annotateFirstHoleWithType pred (← Meta.inferType prevRhs)
      else
        pure pred

    let some (_, lhs, rhs) ← Elab.Term.getCalcRelation? step |
      throwErrorAt pred "invalid 'calc' step, relation expected{indentExpr step}"
    if let some prevRhs := prevRhs? then
      unless ← Meta.isDefEqGuarded lhs prevRhs do
        throwErrorAt pred "invalid 'calc' step, left-hand-side is{indentD m!"{lhs} : {← Meta.inferType lhs}"}\nprevious right-hand-side is{indentD m!"{prevRhs} : {← Meta.inferType prevRhs}"}"

    -- Creates a mvar to represent the proof that the calc tactic solves the
    -- current branch
    -- In the Lean `calc` tactic this is gobbled up by
    -- `withCollectingNewGoalsFrom`
    let mut proof ← Meta.mkFreshExprMVarAt (← getLCtx) (← Meta.getLocalInstances) step
      (userName := tag ++ `calc)
    let mvarBranch := proof.mvarId!

    let mut proofType ← Meta.inferType proof
    let mut remainder? := Option.none

    -- The calc tactic either solves the main goal or leaves another relation.
    -- Replace the main goal, and save the new goal if necessary
    unless ← Meta.isDefEq proofType target do
      let rec throwFailed :=
        throwError "'calc' tactic failed, has type{indentExpr proofType}\nbut it is expected to have type{indentExpr target}"
      let some (_, _, rhs) ← Elab.Term.getCalcRelation? proofType | throwFailed
      let some (r, _, rhs') ← Elab.Term.getCalcRelation? target | throwFailed
      let lastStep := mkApp2 r rhs rhs'
      let lastStepGoal ← Meta.mkFreshExprSyntheticOpaqueMVar lastStep tag
      (proof, proofType) ← Elab.Term.mkCalcTrans proof proofType lastStepGoal lastStep
      unless ← Meta.isDefEq proofType target do throwFailed
      remainder? := .some lastStepGoal.mvarId!
    goal.assign proof

    let goals := [ mvarBranch ] ++ remainder?.toList
    Elab.Tactic.setGoals goals
    match remainder? with
    | .some goal => return .some { goal, fragment := .calc (.some rhs) }
    | .none => return .none
  | fragment@(.conv _ _) => do
    let .ok tactic := Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `conv)
      (input := s)
      (fileName := ← getFileName) | throwError "Could not parse `conv tactic {s}"
    Elab.Tactic.evalTactic tactic
    let goal ← Elab.Tactic.getMainGoal
    return .some { goal, fragment }

end Pantograph
