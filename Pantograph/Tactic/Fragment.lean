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
  | conv (rhs : MVarId)
  -- This goal is spawned from a `conv`
  | convSentinel (parent : MVarId)
  deriving BEq
abbrev FragmentMap := Std.HashMap MVarId Fragment
def FragmentMap.empty : FragmentMap := Std.HashMap.emptyWithCapacity 2

protected def Fragment.map (fragment : Fragment) (mapExpr : Expr → CoreM Expr) : CoreM Fragment :=
  let mapMVar (mvarId : MVarId) : CoreM MVarId :=
    return (← mapExpr (.mvar mvarId)) |>.mvarId!
  match fragment with
  | .calc prevRhs? => return .calc (← prevRhs?.mapM mapExpr)
  | .conv rhs => do
    let rhs' ← mapMVar rhs
    return .conv rhs'
  | .convSentinel parent => do
    return .convSentinel (← mapMVar parent)

protected def Fragment.enterCalc : Fragment := .calc .none
protected def Fragment.enterConv : Elab.Tactic.TacticM FragmentMap := do
  let goal ← Elab.Tactic.getMainGoal
  goal.checkNotAssigned `GoalState.conv
  let (rhs, newGoal) ← goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let (rhs, newGoal) ← Elab.Tactic.Conv.mkConvGoalFor target
    pure (rhs.mvarId!, newGoal.mvarId!)
  Elab.Tactic.replaceMainGoal [newGoal]
  return FragmentMap.empty
    |>.insert goal (.conv rhs)
    |>.insert newGoal (.convSentinel goal)

protected def Fragment.exit (fragment : Fragment) (goal : MVarId) (fragments : FragmentMap)
  : Elab.Tactic.TacticM FragmentMap :=
  match fragment with
  | .calc .. => do
    Elab.Tactic.setGoals [goal]
    return fragments.erase goal
  | .conv rhs => do
    let goals := (← Elab.Tactic.getGoals).filter λ descendant =>
      match fragments[descendant]? with
      | .some s => (.convSentinel goal) == s
      | _ => false -- Not a conv goal from this
    -- Close all existing goals with `refl`
    for mvarId in goals do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    Elab.Tactic.pruneSolvedGoals
    unless (← goals.filterM (·.isAssignedOrDelayedAssigned)).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{Elab.goalsToMessageData (goals)}"

    Elab.Tactic.replaceMainGoal [goal]
    let targetNew ← instantiateMVars (.mvar rhs)
    let proof ← instantiateMVars (.mvar goal)

    Elab.Tactic.liftMetaTactic1 (·.replaceTargetEq targetNew proof)
    return fragments.erase goal
  | .convSentinel _ =>
    return fragments.erase goal

protected def Fragment.step (fragment : Fragment) (goal : MVarId) (s : String)
  : Elab.Tactic.TacticM FragmentMap := goal.withContext do
  assert! ¬ (← goal.isAssigned)
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
    | .some goal => return FragmentMap.empty.insert goal $ .calc (.some rhs)
    | .none => return .empty
  | .conv .. => do
    throwError "Direct operation on conversion tactic parent goal is not allowed"
  | fragment@(.convSentinel _) => do
    assert! isLHSGoal? (← goal.getType) |>.isSome
    let tactic ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `conv)
      (input := s)
      (fileName := ← getFileName) with
      | .ok stx => pure $ stx
      | .error error => throwError error
    let oldGoals ← Elab.Tactic.getGoals
    -- Label newly generated goals as conv sentinels
    Elab.Tactic.evalTactic tactic
    let newGoals := (← Elab.Tactic.getUnsolvedGoals).filter λ g => ¬ (oldGoals.contains g)
    return newGoals.foldl (init := FragmentMap.empty) λ acc g =>
      acc.insert g fragment

end Pantograph
