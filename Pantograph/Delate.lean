/-
This file handles "Delation": The conversion of Kernel view into Search view.
-/
import Lean
import Std.Data.HashMap
import Pantograph.Goal
import Pantograph.Protocol

open Lean

-- Symbol processing functions --

namespace Pantograph

structure ProjectionApplication where
  projector: Name
  numParams: Nat
  inner: Expr

@[export pantograph_expr_proj_to_app]
def exprProjToApp (env: Environment) (e: Expr): ProjectionApplication :=
  let (typeName, idx, inner) := match e with
    | .proj typeName idx inner => (typeName, idx, inner)
    | _ => panic! "Argument must be proj"
  let ctor := getStructureCtor env typeName
  let fieldName := getStructureFields env typeName |>.get! idx
  let projector := getProjFnForField? env typeName fieldName |>.get!
  {
    projector,
    numParams := ctor.numParams,
    inner,
  }

def _root_.Lean.Name.isAuxLemma (n : Lean.Name) : Bool := n matches .num (.str _ "_auxLemma") _

/-- Unfold all lemmas created by `Lean.Meta.mkAuxLemma`. These end in `_auxLemma.nn` where `nn` is a number. -/
@[export pantograph_unfold_aux_lemmas]
def unfoldAuxLemmas (e : Expr) : CoreM Expr := do
  Lean.Meta.deltaExpand e Lean.Name.isAuxLemma

/--
Force the instantiation of delayed metavariables even if they cannot be fully
instantiated. This is used during resumption to provide diagnostic data about
the current goal.

Since Lean 4 does not have an `Expr` constructor corresponding to delayed
metavariables, any delayed metavariables must be recursively handled by this
function to ensure that nested delayed metavariables can be properly processed.
The caveat is this recursive call will lead to infinite recursion if a loop
between metavariable assignment exists.

This function ensures any metavariable in the result is either
1. Delayed assigned with its pending mvar not assigned in any form
2. Not assigned (delay or not)
 -/
partial def instantiateDelayedMVars (eOrig: Expr) : MetaM Expr := do
  --let padding := String.join $ List.replicate level "│ "
  --IO.println s!"{padding}Starting {toString eOrig}"
  let mut result ← Meta.transform (← instantiateMVars eOrig)
    (pre := fun e => e.withApp fun f args => do
      let .mvar mvarId := f | return .continue
      --IO.println s!"{padding}├V {e}"
      let mvarDecl ← mvarId.getDecl

      -- This is critical to maintaining the interdependency of metavariables.
      -- Without setting `.syntheticOpaque`, Lean's metavariable elimination
      -- system will not make the necessary delayed assigned mvars in case of
      -- nested mvars.
      mvarId.setKind .syntheticOpaque

      mvarId.withContext do
        let lctx ← MonadLCtx.getLCtx
        if mvarDecl.lctx.any (λ decl => !lctx.contains decl.fvarId) then
          let violations := mvarDecl.lctx.decls.foldl (λ acc decl? => match decl? with
            | .some decl => if lctx.contains decl.fvarId then acc else acc ++ [decl.fvarId.name]
            | .none => acc) []
          panic! s!"In the context of {mvarId.name}, there are local context variable violations: {violations}"

        if let .some assign ← getExprMVarAssignment? mvarId then
          --IO.println s!"{padding}├A ?{mvarId.name}"
          assert! !(← mvarId.isDelayedAssigned)
          return .visit (mkAppN assign args)
        else if let some { fvars, mvarIdPending } ← getDelayedMVarAssignment? mvarId then
          --let substTableStr := String.intercalate ", " $ Array.zipWith fvars args (λ fvar assign => s!"{fvar.fvarId!.name} := {assign}") |>.toList
          --IO.println s!"{padding}├MD ?{mvarId.name} := ?{mvarIdPending.name} [{substTableStr}]"

          if args.size < fvars.size then
            throwError "Not enough arguments to instantiate a delay assigned mvar. This is due to bad implementations of a tactic: {args.size} < {fvars.size}. Expr: {toString e}; Origin: {toString eOrig}"
          --if !args.isEmpty then
            --IO.println s!"{padding}├── Arguments Begin"
          let args ← args.mapM self
          --if !args.isEmpty then
            --IO.println s!"{padding}├── Arguments End"
          if !(← mvarIdPending.isAssignedOrDelayedAssigned) then
            --IO.println s!"{padding}├T1"
            let result := mkAppN f args
            return .done result

          let pending ← mvarIdPending.withContext do
            let inner ← instantiateDelayedMVars (.mvar mvarIdPending) --(level := level + 1)
            --IO.println s!"{padding}├Pre: {inner}"
            pure <| (← inner.abstractM fvars).instantiateRev args

          -- Tail arguments
          let result := mkAppRange pending fvars.size args.size args
          --IO.println s!"{padding}├MD {result}"
          return .done result
        else
          assert! !(← mvarId.isAssigned)
          assert! !(← mvarId.isDelayedAssigned)
          --if !args.isEmpty then
          --  IO.println s!"{padding}├── Arguments Begin"
          let args ← args.mapM self
          --if !args.isEmpty then
          --  IO.println s!"{padding}├── Arguments End"

          --IO.println s!"{padding}├M ?{mvarId.name}"
          return .done (mkAppN f args))
  --IO.println s!"{padding}└Result {result}"
  return result
  where
  self e := instantiateDelayedMVars e --(level := level + 1)

/--
Convert an expression to an equiavlent form with
1. No nested delayed assigned mvars
2. No aux lemmas
3. No assigned mvars
 -/
@[export pantograph_instantiate_all_m]
def instantiateAll (e: Expr): MetaM Expr := do
  let e ← instantiateDelayedMVars e
  let e ← unfoldAuxLemmas e
  return e

structure DelayedMVarInvocation where
  mvarIdPending: MVarId
  args: Array (FVarId × (Option Expr))
  -- Extra arguments applied to the result of this substitution
  tail: Array Expr

-- The pending mvar of any delayed assigned mvar must not be assigned in any way.
@[export pantograph_to_delayed_mvar_invocation_m]
def toDelayedMVarInvocation (e: Expr): MetaM (Option DelayedMVarInvocation) := do
  let .mvar mvarId := e.getAppFn | return .none
  let .some decl ← getDelayedMVarAssignment? mvarId | return .none
  let mvarIdPending := decl.mvarIdPending
  let mvarDecl ← mvarIdPending.getDecl
  -- Print the function application e. See Lean's `withOverApp`
  let args := e.getAppArgs

  assert! args.size ≥ decl.fvars.size
  assert! !(← mvarIdPending.isAssigned)
  assert! !(← mvarIdPending.isDelayedAssigned)
  let fvarArgMap: Std.HashMap FVarId Expr := Std.HashMap.ofList $ (decl.fvars.map (·.fvarId!) |>.zip args).toList
  let subst ← mvarDecl.lctx.foldlM (init := []) λ acc localDecl => do
    let fvarId := localDecl.fvarId
    let a := fvarArgMap[fvarId]?
    return acc ++ [(fvarId, a)]

  assert! decl.fvars.all (λ fvar => mvarDecl.lctx.findFVar? fvar |>.isSome)

  return .some {
    mvarIdPending,
    args := subst.toArray,
    tail := args.toList.drop decl.fvars.size |>.toArray,
  }

-- Condensed representation

namespace Condensed

-- Mirrors Lean's LocalDecl
structure LocalDecl where
  -- Default value is for testing
  fvarId: FVarId := { name := .anonymous }
  userName: Name

  -- Normalized expression
  type : Expr
  value? : Option Expr := .none

structure Goal where
  mvarId: MVarId := { name := .anonymous }
  userName: Name := .anonymous
  context: Array LocalDecl
  target: Expr

@[export pantograph_goal_is_lhs]
def isLHS (g: Goal) : Bool := isLHSGoal? g.target |>.isSome

end Condensed

-- Get the list of visible (by default) free variables from a goal
@[export pantograph_visible_fvars_of_mvar]
protected def visibleFVarsOfMVar (mctx: MetavarContext) (mvarId: MVarId): Option (Array FVarId) := do
  let mvarDecl ← mctx.findDecl? mvarId
  let lctx := mvarDecl.lctx
  return lctx.decls.foldl (init := #[]) fun r decl? => match decl? with
    | some decl => if decl.isAuxDecl ∨ decl.isImplementationDetail then r else r.push decl.fvarId
    | none      => r

@[export pantograph_to_condensed_goal_m]
def toCondensedGoal (mvarId: MVarId): MetaM Condensed.Goal := do
  let ppAuxDecls     := Meta.pp.auxDecls.get (← getOptions)
  let ppImplDetailHyps := Meta.pp.implementationDetailHyps.get (← getOptions)
  let mvarDecl ← mvarId.getDecl
  let lctx     := mvarDecl.lctx
  let lctx     := lctx.sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx mvarDecl.localInstances do
    let ppVar (localDecl : LocalDecl) : MetaM Condensed.LocalDecl := do
      match localDecl with
      | .cdecl _ fvarId userName type _ _ =>
        let type ← instantiate type
        return { fvarId, userName, type }
      | .ldecl _ fvarId userName type value _ _ => do
        let userName := userName.simpMacroScopes
        let type ← instantiate type
        let value ← instantiate value
        return { fvarId, userName, type, value? := .some value }
    let vars ← lctx.foldlM (init := []) fun acc (localDecl : LocalDecl) => do
      let skip := !ppAuxDecls && localDecl.isAuxDecl ||
        !ppImplDetailHyps && localDecl.isImplementationDetail
      if skip then
        return acc
      else
        let var ← ppVar localDecl
        return var::acc
    return {
        mvarId,
        userName := mvarDecl.userName,
        context := vars.reverse.toArray,
        target := ← instantiate mvarDecl.type
    }
  where
  instantiate := instantiateAll

@[export pantograph_goal_state_to_condensed_m]
protected def GoalState.toCondensed (state: GoalState):
    CoreM (Array Condensed.Goal):= do
  let metaM := do
    let goals := state.goals.toArray
    goals.mapM fun goal => do
      match state.mctx.findDecl? goal with
      | .some _ =>
        let serializedGoal ← toCondensedGoal goal
        pure serializedGoal
      | .none => throwError s!"Metavariable does not exist in context {goal.name}"
  metaM.run' (s := state.savedState.term.meta.meta)

def typeExprToBound (expr: Expr): MetaM Protocol.BoundExpression := do
  Meta.forallTelescope expr fun arr body => do
    let binders ← arr.mapM fun fvar => do
      return (toString (← fvar.fvarId!.getUserName), toString (← Meta.ppExpr (← fvar.fvarId!.getType)))
    return { binders, target := toString (← Meta.ppExpr body) }

def serializeName (name: Name) (sanitize: Bool := true): String :=
  let internal := name.isInaccessibleUserName || name.hasMacroScopes
  if sanitize && internal then "_"
  else toString name |> addQuotes
  where
  addQuotes (n: String) :=
    let quote := "\""
    if n.contains Lean.idBeginEscape then s!"{quote}{n}{quote}" else n

/-- serialize a sort level. Expression is optimized to be compact e.g. `(+ u 2)` -/
partial def serializeSortLevel (level: Level) (sanitize: Bool): String :=
  let k := level.getOffset
  let u := level.getLevelOffset
  let u_str := match u with
    | .zero => "0"
    | .succ _ => panic! "getLevelOffset should not return .succ"
    | .max v w =>
      let v := serializeSortLevel v sanitize
      let w := serializeSortLevel w sanitize
      s!"(:max {v} {w})"
    | .imax v w =>
      let v := serializeSortLevel v sanitize
      let w := serializeSortLevel w sanitize
      s!"(:imax {v} {w})"
    | .param name =>
      let name := serializeName name sanitize
      s!"{name}"
    | .mvar id =>
      let name := serializeName id.name sanitize
      s!"(:mv {name})"
  match k, u with
  | 0, _ => u_str
  | _, .zero => s!"{k}"
  | _, _ => s!"(+ {u_str} {k})"


/--
 Completely serializes an expression tree. Json not used due to compactness

A `_` symbol in the AST indicates automatic deductions not present in the original expression.
-/
partial def serializeExpressionSexp (expr: Expr) (sanitize: Bool := true): MetaM String := do
  self expr
  where
  delayedMVarToSexp (e: Expr): MetaM (Option String) := do
    let .some invocation ← toDelayedMVarInvocation e | return .none
    let callee ← self $ .mvar invocation.mvarIdPending
    let sites ← invocation.args.mapM (λ (fvarId, arg) => do
        let arg := match arg with
          | .some arg => arg
          | .none => .fvar fvarId
        self arg
      )
    let tailArgs ← invocation.tail.mapM self

    let sites := " ".intercalate sites.toList
    let result := if tailArgs.isEmpty then
        s!"(:subst {callee} {sites})"
      else
        let tailArgs := " ".intercalate tailArgs.toList
        s!"((:subst {callee} {sites}) {tailArgs})"
    return .some result

  self (e: Expr): MetaM String := do
    if let .some result ← delayedMVarToSexp e then
      return result
    match e with
    | .bvar deBruijnIndex =>
      -- This is very common so the index alone is shown. Literals are handled below.
      -- The raw de Bruijn index should never appear in an unbound setting. In
      -- Lean these are handled using a `#` prefix.
      pure s!"{deBruijnIndex}"
    | .fvar fvarId =>
      let name := ofName fvarId.name
      pure s!"(:fv {name})"
    | .mvar mvarId => do
        let pref := if ← mvarId.isDelayedAssigned then "mvd" else "mv"
        let name := ofName mvarId.name
        pure s!"(:{pref} {name})"
    | .sort level =>
      let level := serializeSortLevel level sanitize
      pure s!"(:sort {level})"
    | .const declName _ =>
      -- The universe level of the const expression is elided since it should be
      -- inferrable from surrounding expression
      pure s!"(:c {declName})"
    | .app _ _ => do
      let fn' ← self e.getAppFn
      let args := (← e.getAppArgs.mapM self) |>.toList
      let args := " ".intercalate args
      pure s!"({fn'} {args})"
    | .lam binderName binderType body binderInfo => do
      let binderName' := binderName.eraseMacroScopes
      let binderType' ← self binderType
      let body' ← self body
      let binderInfo' := binderInfoSexp binderInfo
      pure s!"(:lambda {binderName'} {binderType'} {body'}{binderInfo'})"
    | .forallE binderName binderType body binderInfo => do
      let binderName' := binderName.eraseMacroScopes
      let binderType' ← self binderType
      let body' ← self body
      let binderInfo' := binderInfoSexp binderInfo
      pure s!"(:forall {binderName'} {binderType'} {body'}{binderInfo'})"
    | .letE name type value body _ => do
      -- Dependent boolean flag diacarded
      let name' := name.eraseMacroScopes
      let type' ← self type
      let value' ← self value
      let body' ← self body
      pure s!"(:let {name'} {type'} {value'} {body'})"
    | .lit v =>
      -- To not burden the downstream parser who needs to handle this, the literal
      -- is wrapped in a :lit sexp.
      let v' := match v with
        | .natVal val => toString val
        | .strVal val => s!"\"{val}\""
      pure s!"(:lit {v'})"
    | .mdata _ inner =>
      -- NOTE: Equivalent to expr itself, but mdata influences the prettyprinter
      -- It may become necessary to incorporate the metadata.
      self inner
    | .proj _ _ _ => do
      let env ← getEnv
      let projApp := exprProjToApp env e
      let autos := String.intercalate " " (List.replicate projApp.numParams "_")
      let inner ← self projApp.inner
      pure s!"((:c {projApp.projector}) {autos} {inner})"
  -- Elides all unhygenic names
  binderInfoSexp : Lean.BinderInfo → String
    | .default => ""
    | .implicit => " :implicit"
    | .strictImplicit => " :strictImplicit"
    | .instImplicit => " :instImplicit"
  ofName (name: Name) := serializeName name sanitize

def serializeExpression (options: @&Protocol.Options) (e: Expr): MetaM Protocol.Expression := do
  let pp?: Option String ← match options.printExprPretty with
    | true => pure $ .some $ toString $ ← Meta.ppExpr e
    | false => pure $ .none
  let sexp?: Option String ← match options.printExprAST with
    | true => pure $ .some $ ← serializeExpressionSexp e
    | false => pure $ .none
  let dependentMVars? ← match options.printDependentMVars with
    | true => pure $ .some $ (← Meta.getMVars e).map (λ mvarId => mvarId.name.toString)
    | false => pure $ .none
  return {
    pp?,
    sexp?
    dependentMVars?,
  }


/-- Adapted from ppGoal -/
def serializeGoal (options: @&Protocol.Options) (goal: MVarId) (mvarDecl: MetavarDecl) (parentDecl?: Option MetavarDecl := .none)
      : MetaM Protocol.Goal := do
  -- Options for printing; See Meta.ppGoal for details
  let showLetValues  := true
  let ppAuxDecls     := options.printAuxDecls
  let ppImplDetailHyps := options.printImplementationDetailHyps
  let lctx           := mvarDecl.lctx
  let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx mvarDecl.localInstances do
    let ppVarNameOnly (localDecl: LocalDecl): MetaM Protocol.Variable := do
      match localDecl with
      | .cdecl _ fvarId userName _ _ _ =>
        return {
          name := ofName fvarId.name,
          userName:= ofName userName.simpMacroScopes,
          isInaccessible := userName.isInaccessibleUserName
        }
      | .ldecl _ fvarId userName _ _ _ _ => do
        return {
          name := ofName fvarId.name,
          userName := toString userName.simpMacroScopes,
          isInaccessible := userName.isInaccessibleUserName
        }
    let ppVar (localDecl : LocalDecl) : MetaM Protocol.Variable := do
      match localDecl with
      | .cdecl _ fvarId userName type _ _ =>
        let userName := userName.simpMacroScopes
        let type ← instantiate type
        return {
          name := ofName fvarId.name,
          userName:= ofName userName,
          isInaccessible := userName.isInaccessibleUserName
          type? := .some (← serializeExpression options type)
        }
      | .ldecl _ fvarId userName type val _ _ => do
        let userName := userName.simpMacroScopes
        let type ← instantiate type
        let value? ← if showLetValues then
          let val ← instantiate val
          pure $ .some (← serializeExpression options val)
        else
          pure $ .none
        return {
          name := ofName fvarId.name,
          userName:= ofName userName,
          isInaccessible := userName.isInaccessibleUserName
          type? := .some (← serializeExpression options type)
          value? := value?
        }
    let vars ← lctx.foldlM (init := []) fun acc (localDecl : LocalDecl) => do
      let skip := !ppAuxDecls && localDecl.isAuxDecl ||
        !ppImplDetailHyps && localDecl.isImplementationDetail
      if skip then
        return acc
      else
        let nameOnly := options.noRepeat && (parentDecl?.map
          (λ decl => decl.lctx.find? localDecl.fvarId |>.isSome) |>.getD false)
        let var ← match nameOnly with
          | true => ppVarNameOnly localDecl
          | false => ppVar localDecl
        return var::acc
    return {
      name := ofName goal.name,
      userName? := if mvarDecl.userName == .anonymous then .none else .some (ofName mvarDecl.userName),
      isConversion := isLHSGoal? mvarDecl.type |>.isSome,
      target := (← serializeExpression options (← instantiate mvarDecl.type)),
      vars := vars.reverse.toArray
    }
  where
  instantiate := instantiateAll
  ofName (n: Name) := serializeName n (sanitize := false)

protected def GoalState.serializeGoals
      (state: GoalState)
      (parent: Option GoalState := .none)
      (options: @&Protocol.Options := {}):
    MetaM (Array Protocol.Goal):= do
  state.restoreMetaM
  let goals := state.goals.toArray
  let parentDecl? := parent.bind (λ parentState => parentState.mctx.findDecl? state.parentMVar?.get!)
  goals.mapM fun goal => do
    match state.mctx.findDecl? goal with
    | .some mvarDecl =>
      let serializedGoal ← serializeGoal options goal mvarDecl (parentDecl? := parentDecl?)
      pure serializedGoal
    | .none => throwError s!"Metavariable does not exist in context {goal.name}"

/-- Print the metavariables in a readable format -/
@[export pantograph_goal_state_diag_m]
protected def GoalState.diag (goalState: GoalState) (parent?: Option GoalState := .none) (options: Protocol.GoalDiag := {}): CoreM String := do
  let metaM: MetaM String := do
    goalState.restoreMetaM
    let savedState := goalState.savedState
    let goals := savedState.tactic.goals
    let mctx ← getMCtx
    let root := goalState.root
    -- Print the root
    let result: String ← match mctx.decls.find? root with
      | .some decl => printMVar ">" root decl
      | .none => pure s!">{root.name}: ??"
    let resultGoals ← goals.filter (· != root) |>.mapM (fun mvarId =>
      match mctx.decls.find? mvarId with
      | .some decl => printMVar "⊢" mvarId decl
      | .none => pure s!"⊢{mvarId.name}: ??"
    )
    let goals := goals.toSSet
    let resultOthers ← mctx.decls.toList.filter (λ (mvarId, _) =>
        !(goals.contains mvarId || mvarId == root) && options.printAll)
        |>.mapM (fun (mvarId, decl) => do
          let pref := if parentHasMVar mvarId then " " else "~"
          printMVar pref mvarId decl
        )
    pure $ result ++ "\n" ++ (resultGoals.map (· ++ "\n") |> String.join) ++ (resultOthers.map (· ++ "\n") |> String.join)
  metaM.run' {}
  where
    printMVar (pref: String) (mvarId: MVarId) (decl: MetavarDecl): MetaM String := mvarId.withContext do
      let resultFVars: List String ←
        if options.printContext then
          decl.lctx.fvarIdToDecl.toList.mapM (λ (fvarId, decl) =>
            do pure $ (← printFVar fvarId decl) ++ "\n")
        else
          pure []
      let type ← if options.instantiate
        then instantiateAll decl.type
        else pure $ decl.type
      let type_sexp ← if options.printSexp then
          let sexp ← serializeExpressionSexp type (sanitize := false)
          pure <| " " ++ sexp
        else
          pure ""
      let resultMain: String := s!"{pref}{mvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type}{type_sexp}"
      let resultValue: String ←
        if options.printValue then
          if let .some value ← getExprMVarAssignment? mvarId then
            let value ← if options.instantiate
              then instantiateAll value
              else pure $ value
            pure s!"\n := {← Meta.ppExpr value}"
          else if let .some { mvarIdPending, .. } ← getDelayedMVarAssignment? mvarId then
            pure s!"\n ::= {mvarIdPending.name}"
          else
            pure ""
        else
          pure ""
      pure $ (String.join resultFVars) ++ resultMain ++ resultValue
    printFVar (fvarId: FVarId) (decl: LocalDecl): MetaM String := do
      pure s!" | {fvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type}"
    userNameToString : Name → String
      | .anonymous => ""
      | other => s!"[{other}]"
    parentHasMVar (mvarId: MVarId): Bool := parent?.map (λ state => state.mctx.decls.contains mvarId) |>.getD true

end Pantograph
