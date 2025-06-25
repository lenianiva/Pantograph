/-
Functions for handling metavariables

All the functions starting with `try` resume their inner monadic state.
-/
import Pantograph.Tactic
import Lean


namespace Pantograph
open Lean

/-- Determine the acting area of a tactic -/
inductive Site where
  | focus (goal : MVarId)
  | prefer (goal : MVarId)
  | unfocus
  deriving BEq, Inhabited

instance : Coe MVarId Site where
  coe := .focus
instance : ToString Site where
  toString
    | .focus { name } => s!"[{name}]"
    | .prefer { name } => s!"[{name},...]"
    | .unfocus => "[*]"

/-- Executes a `TacticM` on a site and return affected goals -/
protected def Site.runTacticM (site : Site)
  { m } [Monad m] [MonadLiftT Elab.Tactic.TacticM m] [MonadControlT Elab.Tactic.TacticM m] [MonadMCtx m] [MonadError m]
  (f : m α) : m (α × List MVarId) :=
  match site with
  | .focus goal => do
    Elab.Tactic.setGoals [goal]
    let a ← f
    return (a, [goal])
  | .prefer goal => do
    let before ← Elab.Tactic.getUnsolvedGoals
    let otherGoals := before.filter (· != goal)
    Elab.Tactic.setGoals (goal :: otherGoals)
    let a ← f
    let after ← Elab.Tactic.getUnsolvedGoals
    let parents := before.filter (¬ after.contains ·)
    return (a, parents)
  | .unfocus => do
    let before ← Elab.Tactic.getUnsolvedGoals
    let a ← f
    let after ← Elab.Tactic.getUnsolvedGoals
    let parents := before.filter (¬ after.contains ·)
    return (a, parents)

/--
Kernel view of the state of a proof
 -/
structure GoalState where
  -- Captured `TacticM` state
  savedState : Elab.Tactic.SavedState

  -- The root goal which is the search target
  root: MVarId

  -- Parent goals assigned to produce this state
  parentMVars : List MVarId := []

  -- Any goal associated with a fragment has a partial tactic which has not
  -- finished executing.
  fragments : FragmentMap := .empty

def throwNoGoals { m α } [Monad m] [MonadError m] : m α := throwError "no goals to be solved"

@[export pantograph_goal_state_create_m]
protected def GoalState.create (expr: Expr): Elab.TermElabM GoalState := do
  -- May be necessary to immediately synthesise all metavariables if we need to leave the elaboration context.
  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070

  --Elab.Term.synthesizeSyntheticMVarsNoPostponing
  --let expr ← instantiateMVars expr
  let root ← Meta.mkFreshExprMVar expr (kind := MetavarKind.synthetic) (userName := .anonymous)
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [root.mvarId!]}
  return {
    root := root.mvarId!,
    savedState,
  }
@[export pantograph_goal_state_create_from_mvars_m]
protected def GoalState.createFromMVars (goals: List MVarId) (root: MVarId): MetaM GoalState := do
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals } |>.run' {}
  return {
    root,
    savedState,
  }
@[always_inline]
protected def GoalState.goals (state: GoalState): List MVarId :=
  state.savedState.tactic.goals
@[always_inline]
protected def GoalState.mainGoal? (state : GoalState) : Option MVarId :=
  state.goals.head?
@[always_inline]
protected def GoalState.actingGoal? (state : GoalState) (site : Site) : Option MVarId := do
  match site with
  | .focus goal | .prefer goal => return goal
  | .unfocus => state.mainGoal?

@[export pantograph_goal_state_goals]
protected def GoalState.goalsArray (state: GoalState): Array MVarId := state.goals.toArray
protected def GoalState.mctx (state: GoalState): MetavarContext :=
  state.savedState.term.meta.meta.mctx
protected def GoalState.env (state: GoalState): Environment :=
  state.savedState.term.meta.core.env

@[export pantograph_goal_state_meta_context_of_goal]
protected def GoalState.metaContextOfGoal (state: GoalState) (mvarId: MVarId): Option Meta.Context := do
  let mvarDecl ← state.mctx.findDecl? mvarId
  return { lctx := mvarDecl.lctx, localInstances := mvarDecl.localInstances }
@[always_inline]
protected def GoalState.metaState (state: GoalState): Meta.State :=
  state.savedState.term.meta.meta
@[always_inline]
protected def GoalState.coreState (state: GoalState): Core.SavedState :=
  state.savedState.term.meta.core

protected def GoalState.withContext' (state: GoalState) (mvarId: MVarId) (m: MetaM α): MetaM α := do
  mvarId.withContext m |>.run' (← read) state.metaState
protected def GoalState.withContext { m } [MonadControlT MetaM m] [Monad m] (state: GoalState) (mvarId: MVarId) : m α → m α :=
  Meta.mapMetaM <| state.withContext' mvarId
/-- Uses context of the first parent -/
protected def GoalState.withParentContext { n } [MonadControlT MetaM n] [Monad n] (state: GoalState): n α → n α :=
  Meta.mapMetaM <| state.withContext' state.parentMVars[0]!
protected def GoalState.withRootContext { n } [MonadControlT MetaM n] [Monad n] (state: GoalState): n α → n α :=
  Meta.mapMetaM <| state.withContext' state.root

private def GoalState.mvars (state: GoalState): SSet MVarId :=
  state.mctx.decls.foldl (init := .empty) fun acc k _ => acc.insert k
-- Restore the name generator and macro scopes of the core state
protected def GoalState.restoreCoreMExtra (state: GoalState): CoreM Unit := do
  let savedCore := state.coreState
  modifyGetThe Core.State (fun st => ((),
    { st with nextMacroScope := savedCore.nextMacroScope, ngen := savedCore.ngen }))
protected def GoalState.restoreMetaM (state: GoalState): MetaM Unit := do
  state.restoreCoreMExtra
  state.savedState.term.meta.restore
protected def GoalState.restoreElabM (state: GoalState): Elab.TermElabM Unit := do
  state.restoreCoreMExtra
  state.savedState.term.restore
private def GoalState.restoreTacticM (state: GoalState) (goal: MVarId): Elab.Tactic.TacticM Unit := do
  state.restoreElabM
  Elab.Tactic.setGoals [goal]

/-- Immediately bring all parent goals back into scope. Used in automatic mode -/
@[export pantograph_goal_state_immediate_resume]
protected def GoalState.immediateResume (state: GoalState) (parent: GoalState): GoalState :=
  -- Prune parents solved goals
  let mctx := state.mctx
  let parentGoals := parent.goals.filter λ goal =>
    let isDuplicate := state.goals.contains goal
    let isSolved := mctx.eAssignment.contains goal || mctx.dAssignment.contains goal
    (¬ isDuplicate) && (¬ isSolved)
  {
    state with
    savedState := {
      state.savedState with
      tactic := { goals := state.goals ++ parentGoals },
    },
  }

/--
Brings into scope a list of goals. User must ensure `goals` are distinct.
-/
@[export pantograph_goal_state_resume]
protected def GoalState.resume (state : GoalState) (goals : List MVarId) : Except String GoalState := do
  if ¬ (goals.all (λ goal => state.mvars.contains goal)) then
    let invalid_goals := goals.filter (λ goal => ¬ state.mvars.contains goal) |>.map (·.name.toString)
    .error s!"Goals {invalid_goals} are not in scope"
  -- Set goals to the goals that have not been assigned yet, similar to the `focus` tactic.
  let unassigned := goals.filter λ goal =>
    let isSolved := state.mctx.eAssignment.contains goal || state.mctx.dAssignment.contains goal
    ¬ isSolved
  return {
    state with
    savedState := {
      term := state.savedState.term,
      tactic := { goals := unassigned },
    },
  }
/--
Brings into scope all goals from `branch`
-/
@[export pantograph_goal_state_continue]
protected def GoalState.continue (target : GoalState) (branch : GoalState) : Except String GoalState :=
  if !target.goals.isEmpty then
    .error s!"Target state has unresolved goals"
  else if target.root != branch.root then
    .error s!"Roots of two continued goal states do not match: {target.root.name} != {branch.root.name}"
  else
    target.resume (goals := branch.goals)

@[export pantograph_goal_state_root_expr]
protected def GoalState.rootExpr? (goalState : GoalState) : Option Expr := do
  if goalState.root.name == .anonymous then
    .none
  let expr ← goalState.mctx.eAssignment.find? goalState.root
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  return expr
@[export pantograph_goal_state_is_solved]
protected def GoalState.isSolved (goalState : GoalState) : Bool :=
  let solvedRoot := match goalState.rootExpr? with
    | .some e => ¬ e.hasExprMVar
    | .none => true
  goalState.goals.isEmpty && solvedRoot
@[export pantograph_goal_state_get_mvar_e_assignment]
protected def GoalState.getMVarEAssignment (goalState: GoalState) (mvarId: MVarId): Option Expr := do
  let expr ← goalState.mctx.eAssignment.find? mvarId
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  return expr
@[export pantograph_goal_state_parent_exprs]
protected def GoalState.parentExprs (state : GoalState) : List Expr :=
  state.parentMVars.map λ goal => state.getMVarEAssignment goal |>.get!
@[always_inline]
protected def GoalState.hasUniqueParent (state : GoalState) : Bool :=
  state.parentMVars.length == 1
@[always_inline]
protected def GoalState.parentExpr! (state : GoalState) : Expr :=
  assert! state.parentMVars.length == 1
  (state.getMVarEAssignment state.parentMVars[0]!).get!

deriving instance BEq for DelayedMetavarAssignment

/-- Given states `dst`, `src`, and `src'`, where `dst` and `src'` are
descendants of `src`, replay the differential `src' - src` in `dst`. Colliding
metavariable and lemma names will be automatically renamed to ensure there is no
collision. This implements branch unification. Unification might be impossible
if conflicting assignments exist. We also assume the monotonicity property: In a
chain of descending goal states, a mvar cannot be unassigned, and once assigned
its assignment cannot change. -/
@[export pantograph_goal_state_replay_m]
protected def GoalState.replay (dst : GoalState) (src src' : GoalState) : CoreM GoalState :=
  withTraceNode `Pantograph.GoalState.replay (fun _ => return m!"replay") do
  let srcNGen := src.coreState.ngen
  let srcNGen' := src'.coreState.ngen
  let dstNGen := dst.coreState.ngen
  assert! srcNGen.namePrefix == srcNGen'.namePrefix
  assert! srcNGen.namePrefix == dstNGen.namePrefix
  assert! src.mctx.depth == src'.mctx.depth
  assert! src.mctx.depth == dst.mctx.depth

  let diffNGenIdx := dst.coreState.ngen.idx - srcNGen.idx

  trace[Pantograph.GoalState.replay] "Merging ngen {srcNGen.idx} -> ({srcNGen'.idx}, {dstNGen.idx})"
  -- True if the name is generated after `src`
  let isNewName : Name → Bool
    | .num pref n =>
      pref == srcNGen.namePrefix ∧ n ≥ srcNGen.idx
    | _ => false
  let mapId : Name → Name
    | id@(.num pref n) =>
      if isNewName id then
        .num pref (n + diffNGenIdx)
      else
        id
    | id => id
  let mapMVar : MVarId → MVarId
    | { name } => ⟨mapId name⟩
  let rec mapLevel : Level → Level
    | .succ x => .succ (mapLevel x)
    | .max l1 l2 => .max (mapLevel l1) (mapLevel l2)
    | .imax l1 l2 => .imax (mapLevel l1) (mapLevel l2)
    | .mvar { name } => .mvar ⟨mapId name⟩
    | l => l
  let mapExpr (e : Expr) : CoreM Expr := Core.transform e λ
    | .sort level => pure $ .done $ .sort (mapLevel level)
    | .mvar { name } => pure $ .done $ .mvar ⟨mapId name⟩
    | _ => pure .continue
  let mapDelayedAssignment (d : DelayedMetavarAssignment) : CoreM DelayedMetavarAssignment := do
    let { mvarIdPending, fvars } := d
    return {
      mvarIdPending := mapMVar mvarIdPending,
      fvars := ← fvars.mapM mapExpr,
    }
  let mapLocalDecl (ldecl : LocalDecl) : CoreM LocalDecl := do
    let ldecl := ldecl.setType (← mapExpr ldecl.type)
    if let .some value := ldecl.value? then
      return ldecl.setValue (← mapExpr value)
    else
      return ldecl

  let { term := savedTerm@{ meta := savedMeta@{ core, meta := meta@{ mctx, .. } }, .. }, .. } := dst.savedState
  trace[Pantograph.GoalState.replay] "Merging mvars {src.mctx.mvarCounter} -> ({src'.mctx.mvarCounter}, {dst.mctx.mvarCounter})"
  let mctx := {
    mctx with
    mvarCounter := mctx.mvarCounter + (src'.mctx.mvarCounter - src.mctx.mvarCounter),
    lDepth := src'.mctx.lDepth.foldl (init := mctx.lDepth) λ acc lmvarId@{ name } depth =>
      if src.mctx.lDepth.contains lmvarId then
        acc
      else
        acc.insert ⟨mapId name⟩ depth
    decls := ← src'.mctx.decls.foldlM (init := mctx.decls) λ acc _mvarId@{ name } decl => do
      if decl.index < src.mctx.mvarCounter then
        return acc
      let mvarId := ⟨mapId name⟩
      let decl := {
        decl with
        lctx := ← decl.lctx.foldlM (init := .empty) λ acc decl => do
          let decl ← mapLocalDecl decl
          return acc.addDecl decl,
        type := ← mapExpr decl.type,
      }
      return acc.insert mvarId decl

    -- Merge mvar assignments
    userNames := src'.mctx.userNames.foldl (init := mctx.userNames) λ acc userName mvarId =>
      if acc.contains userName then
        acc
      else
        acc.insert userName mvarId,
    lAssignment := src'.mctx.lAssignment.foldl (init := mctx.lAssignment) λ acc lmvarId' l =>
      let lmvarId := ⟨mapId lmvarId'.name⟩
      if mctx.lAssignment.contains lmvarId then
        -- Skip the intersecting assignments for now
        acc
      else
        let l := mapLevel l
        acc.insert lmvarId l,
    eAssignment := ← src'.mctx.eAssignment.foldlM (init := mctx.eAssignment) λ acc mvarId' e => do
      let mvarId := ⟨mapId mvarId'.name⟩
      if mctx.eAssignment.contains mvarId then
        -- Skip the intersecting assignments for now
        return acc
      else
        let e ← mapExpr e
        return acc.insert mvarId e,
    dAssignment := ← src'.mctx.dAssignment.foldlM (init := mctx.dAssignment) λ acc mvarId' d => do
      let mvarId := ⟨mapId mvarId'.name⟩
      if mctx.dAssignment.contains mvarId then
        return acc
      else
        let d ← mapDelayedAssignment d
        return acc.insert mvarId d
  }
  let ngen := {
    core.ngen with
    idx := core.ngen.idx + (srcNGen'.idx - srcNGen.idx)
  }
  -- Merge conflicting lmvar and mvar assignments using `isDefEq`

  let savedMeta := {
    savedMeta with
    core := {
      core with
      ngen,
    }
    meta := {
      meta with
      mctx,
    }
  }
  let m : MetaM Meta.SavedState := Meta.withMCtx mctx do
    savedMeta.restore

    for (lmvarId, l') in src'.mctx.lAssignment do
      if isNewName lmvarId.name then
        continue
      let .some l ← getLevelMVarAssignment? lmvarId | continue
      let l' := mapLevel l'
      trace[Pantograph.GoalState.replay] "Merging level assignments on {lmvarId.name}"
      unless ← Meta.isLevelDefEq l l' do
        throwError "Conflicting assignment of level metavariable {lmvarId.name}"
    for (mvarId, e') in src'.mctx.eAssignment do
      if isNewName mvarId.name then
        continue
      if ← mvarId.isDelayedAssigned then
        throwError "Conflicting assignment of expr metavariable (e != d) {mvarId.name}"
      let .some e ← getExprMVarAssignment? mvarId | continue
      let e' ← mapExpr e'
      trace[Pantograph.GoalState.replay] "Merging expr assignments on {mvarId.name}"
      unless ← Meta.isDefEq e e' do
        throwError "Conflicting assignment of expr metavariable (e != e) {mvarId.name}"
    for (mvarId, d') in src'.mctx.dAssignment do
      if isNewName mvarId.name then
        continue
      if ← mvarId.isAssigned then
        throwError "Conflicting assignment of expr metavariable (d != e) {mvarId.name}"
      let .some d ← getDelayedMVarAssignment? mvarId | continue
      trace[Pantograph.GoalState.replay] "Merging expr (delayed) assignments on {mvarId.name}"
      unless d == d' do
        throwError "Conflicting assignment of expr metavariable (d != d) {mvarId.name}"

    Meta.saveState
  let goals :=dst.savedState.tactic.goals ++
    src'.savedState.tactic.goals.map (⟨mapId ·.name⟩)
  let fragments ← src'.fragments.foldM (init := dst.fragments) λ acc mvarId' fragment' => do
    let mvarId := ⟨mapId mvarId'.name⟩
    let fragment ← fragment'.map mapExpr
    if let .some _fragment0 := acc[mvarId]? then
      throwError "Conflicting fragments on {mvarId.name}"
    return acc.insert mvarId fragment
  return {
    dst with
    savedState := {
      tactic := {
        goals
      },
      term := {
        savedTerm with
        meta := ← m.run',
      },
    },
    parentMVars := dst.parentMVars ++ src.parentMVars.map mapMVar,
    fragments,
  }

--- Tactic execution functions ---

/--
These descendants serve as "seed" mvars. If a MVarError's mvar is related to one
of these seed mvars, it means an error has occurred when a tactic was executing
on `src`. `evalTactic`, will not capture these mvars, so we need to manually
find them and save them into the goal list. See the rationales document for the
inspiration of this function.
-/
private def collectAllErroredMVars (src : MVarId) : Elab.TermElabM (List MVarId) := do
  -- Mimics `Elab.Term.logUnassignedUsingErrorInfos`
  let descendants ←  Meta.getMVars (.mvar src)
  --let _ ← Elab.Term.logUnassignedUsingErrorInfos descendants
  let mut alreadyVisited : MVarIdSet := {}
  let mut result : MVarIdSet := {}
  for { mvarId, .. } in (← get).mvarErrorInfos do
    unless alreadyVisited.contains mvarId do
      alreadyVisited := alreadyVisited.insert mvarId
      /- The metavariable `mvarErrorInfo.mvarId` may have been assigned or
         delayed assigned to another metavariable that is unassigned. -/
      let mvarDeps ← Meta.getMVars (.mvar mvarId)
      if mvarDeps.any descendants.contains then do
        result := mvarDeps.foldl (·.insert ·) result
  return result.toList

/-- Merger of two unique lists -/
private def mergeMVarLists (li1 li2 : List MVarId) : List MVarId :=
  let li2' := li2.filter (¬ li1.contains ·)
  li1 ++ li2'

/--
Set `guardMVarErrors` to true to capture mvar errors. Lean will not
automatically collect mvars from text tactics (vide
`test_tactic_failure_synthesize_placeholder`)
-/
protected def GoalState.step' { α } (state : GoalState) (site : Site) (tacticM : Elab.Tactic.TacticM α) (guardMVarErrors : Bool := false)
  : Elab.TermElabM (α × GoalState) := do
  let ((a, parentMVars), { goals }) ← site.runTacticM tacticM
    |>.run { elaborator := .anonymous }
    |>.run state.savedState.tactic
  let nextElabState ← MonadBacktrack.saveState
  --Elab.Term.synthesizeSyntheticMVarsNoPostponing

  let goals ← if guardMVarErrors then
      parentMVars.foldlM (init := goals) λ goals parent => do
        let errors ← collectAllErroredMVars parent
        return mergeMVarLists goals errors
    else
      pure goals
  let state' := {
    state with
    savedState := { term := nextElabState, tactic := { goals }, },
    parentMVars,
  }
  return (a, state')
protected def GoalState.step (state : GoalState) (site : Site) (tacticM : Elab.Tactic.TacticM Unit) (guardMVarErrors : Bool := false)
  : Elab.TermElabM GoalState :=
  Prod.snd <$> GoalState.step' state site tacticM guardMVarErrors

/-- Response for executing a tactic -/
inductive TacticResult where
  -- Goes to next state
  | success (state : GoalState) (messages : Array String)
  -- Tactic failed with messages
  | failure (messages : Array String)
  -- Could not parse tactic
  | parseError (message : String)
  -- The given action cannot be executed in the state
  | invalidAction (message : String)

private def dumpMessageLog (prevMessageLength : Nat := 0) : CoreM (Bool × Array String) := do
  let newMessages := (← Core.getMessageLog).toList.drop prevMessageLength
  let hasErrors := newMessages.any (·.severity == .error)
  let newMessages ← newMessages.mapM λ m => m.toString
  Core.resetMessageLog
  return (hasErrors, newMessages.toArray)

def withCapturingError (elabM : Elab.Term.TermElabM GoalState) : Elab.TermElabM TacticResult := do
  assert! (← Core.getMessageLog).toList.isEmpty
  try
    let state ← elabM

    -- Check if error messages have been generated in the core.
    let (hasError, newMessages) ← dumpMessageLog
    if hasError then
      return .failure newMessages
    else
      return .success state newMessages
  catch exception =>
    match exception with
    | .internal _ =>
      let (_, messages) ← dumpMessageLog
      return .failure messages
    | _ => return .failure #[← exception.toMessageData.toString]

/-- Executes a `TacticM` monad on this `GoalState`, collecting the errors as necessary -/
protected def GoalState.tryTacticM
    (state: GoalState) (site : Site)
    (tacticM: Elab.Tactic.TacticM Unit)
    (guardMVarErrors : Bool := false)
    : Elab.TermElabM TacticResult :=
  withCapturingError do
    state.step site tacticM guardMVarErrors

/-- Execute a string tactic on given state. Restores TermElabM -/
@[export pantograph_goal_state_try_tactic_m]
protected def GoalState.tryTactic (state: GoalState) (site : Site) (tactic: String):
    Elab.TermElabM TacticResult := do
  state.restoreElabM
  let .some goal := state.actingGoal? site | throwNoGoals
  if let .some fragment := state.fragments[goal]? then
    return ← withCapturingError do
      let (moreFragments, state') ← state.step' site (fragment.step goal tactic)
      let fragments := moreFragments.fold (init := state.fragments.erase goal) λ acc mvarId f =>
        acc.insert mvarId f
      return { state' with fragments }
  -- Normal tactic without fragment
  let tactic ← match Parser.runParserCategory
    (env := ← getEnv)
    (catName := `tactic)
    (input := tactic)
    (fileName := ← getFileName) with
    | .ok stx => pure $ stx
    | .error error => return .parseError error
  let tacticM := Elab.Tactic.evalTactic tactic
  withCapturingError do
    state.step site tacticM (guardMVarErrors := true)

-- Specialized Tactics

protected def GoalState.tryAssign (state : GoalState) (site : Site) (expr : String)
    : Elab.TermElabM TacticResult := do
  state.restoreElabM
  let expr ← match Parser.runParserCategory
    (env := ← getEnv)
    (catName := `term)
    (input := expr)
    (fileName := ← getFileName) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.tryTacticM site $ Tactic.evalAssign expr

protected def GoalState.tryLet (state : GoalState) (site : Site) (binderName : String) (type : String)
    : Elab.TermElabM TacticResult := do
  state.restoreElabM
  let type ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := type)
    (fileName := ← getFileName) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.tryTacticM site $ Tactic.evalLet binderName.toName type

/-- Enter conv tactic mode -/
@[export pantograph_goal_state_conv_enter_m]
protected def GoalState.conv (state : GoalState) (site : Site) :
      Elab.TermElabM TacticResult := do
  let .some goal := state.actingGoal? site | throwNoGoals
  if let .some (.conv ..) := state.fragments[goal]? then
    return .invalidAction "Already in conv state"
  withCapturingError do
    let (fragments, state') ← state.step' site Fragment.enterConv
    return {
      state' with
      fragments := fragments.fold (init := state'.fragments) λ acc goal fragment =>
        acc.insert goal fragment
    }

/-- Exit from `conv` mode, and conclude all conversion tactic sentinels
descended from `goal`. -/
@[export pantograph_goal_state_conv_exit_m]
protected def GoalState.convExit (state : GoalState) (goal : MVarId):
      Elab.TermElabM TacticResult := do
  let .some fragment@(.conv ..) := state.fragments[goal]? |
    return .invalidAction "Not in conv state"
  withCapturingError do
    let (fragments, state') ← state.step' goal (fragment.exit goal state.fragments)
    return {
      state' with
      fragments,
    }

protected def GoalState.calcPrevRhsOf? (state : GoalState) (goal : MVarId) : Option Expr := do
  let .some (.calc prevRhs?) := state.fragments[goal]? | .none
  prevRhs?

@[export pantograph_goal_state_try_calc_m]
protected def GoalState.tryCalc (state : GoalState) (site : Site) (pred : String)
  : Elab.TermElabM TacticResult := do
  let .some goal := state.actingGoal? site | throwNoGoals
  let prevRhs? := state.calcPrevRhsOf? goal
  withCapturingError do
    let (moreFragments, state') ← state.step' goal do
      let fragment := Fragment.calc prevRhs?
      fragment.step goal pred
    let fragments := moreFragments.fold (init := state.fragments.erase goal) λ acc mvarId f =>
      acc.insert mvarId f
    return {
      state' with
      fragments,
    }

initialize
  registerTraceClass `Pantograph.GoalState.replay

end Pantograph
