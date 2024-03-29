/-
All serialisation functions
-/
import Lean

import Pantograph.Protocol
import Pantograph.Goal

open Lean

-- Symbol processing functions --

def Lean.Name.isAuxLemma (n : Lean.Name) : Bool := n matches .num (.str _ "_auxLemma") _

namespace Pantograph

/-- Unfold all lemmas created by `Lean.Meta.mkAuxLemma`. These end in `_auxLemma.nn` where `nn` is a number. -/
def unfoldAuxLemmas (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.deltaExpand e Lean.Name.isAuxLemma

--- Input Functions ---

/-- Read syntax object from string -/
def syntax_from_str (env: Environment) (s: String): Except String Syntax :=
  Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")


/-- Parse a syntax object. May generate additional metavariables! -/
def syntax_to_expr_type (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabType syn
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)
def syntax_to_expr (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabTerm (stx := syn) (expectedType? := .none)
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)


--- Output Functions ---

def type_expr_to_bound (expr: Expr): MetaM Protocol.BoundExpression := do
  Meta.forallTelescope expr fun arr body => do
    let binders ← arr.mapM fun fvar => do
      return (toString (← fvar.fvarId!.getUserName), toString (← Meta.ppExpr (← fvar.fvarId!.getType)))
    return { binders, target := toString (← Meta.ppExpr body) }

def name_to_ast (name: Name) (sanitize: Bool := true): String :=
  let internal := name.isInaccessibleUserName || name.hasMacroScopes
  if sanitize && internal then "_"
  else toString name |> enclose_if_escaped
  where
  enclose_if_escaped (n: String) :=
    let quote := "\""
    if n.contains Lean.idBeginEscape then s!"{quote}{n}{quote}" else n

/-- serialize a sort level. Expression is optimized to be compact e.g. `(+ u 2)` -/
partial def serialize_sort_level_ast (level: Level) (sanitize: Bool): String :=
  let k := level.getOffset
  let u := level.getLevelOffset
  let u_str := match u with
    | .zero => "0"
    | .succ _ => panic! "getLevelOffset should not return .succ"
    | .max v w =>
      let v := serialize_sort_level_ast v sanitize
      let w := serialize_sort_level_ast w sanitize
      s!"(:max {v} {w})"
    | .imax v w =>
      let v := serialize_sort_level_ast v sanitize
      let w := serialize_sort_level_ast w sanitize
      s!"(:imax {v} {w})"
    | .param name =>
      let name := name_to_ast name sanitize
      s!"{name}"
    | .mvar id =>
      let name := name_to_ast id.name sanitize
      s!"(:mv {name})"
  match k, u with
  | 0, _ => u_str
  | _, .zero => s!"{k}"
  | _, _ => s!"(+ {u_str} {k})"

/--
 Completely serializes an expression tree. Json not used due to compactness
-/
partial def serialize_expression_ast (expr: Expr) (sanitize: Bool := true): MetaM String := do
  self expr
  where
  self (e: Expr): MetaM String :=
    match e with
    | .bvar deBruijnIndex =>
      -- This is very common so the index alone is shown. Literals are handled below.
      -- The raw de Bruijn index should never appear in an unbound setting. In
      -- Lean these are handled using a `#` prefix.
      pure s!"{deBruijnIndex}"
    | .fvar fvarId =>
      let name := of_name fvarId.name
      pure s!"(:fv {name})"
    | .mvar mvarId =>
      let name := of_name mvarId.name
      pure s!"(:mv {name})"
    | .sort level =>
      let level := serialize_sort_level_ast level sanitize
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
      let binderName' := of_name binderName
      let binderType' ← self binderType
      let body' ← self body
      let binderInfo' := binder_info_to_ast binderInfo
      pure s!"(:lambda {binderName'} {binderType'} {body'}{binderInfo'})"
    | .forallE binderName binderType body binderInfo => do
      let binderName' := of_name binderName
      let binderType' ← self binderType
      let body' ← self body
      let binderInfo' := binder_info_to_ast binderInfo
      pure s!"(:forall {binderName'} {binderType'} {body'}{binderInfo'})"
    | .letE name type value body _ => do
      -- Dependent boolean flag diacarded
      let name' := name_to_ast name
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
    | .proj typeName idx inner => do
      let env ← getEnv
      let fieldName := getStructureFields env typeName |>.get! idx
      let projectorName := getProjFnForField? env typeName fieldName |>.get!
      let e := Expr.app (.const  projectorName []) inner
      self e
  -- Elides all unhygenic names
  binder_info_to_ast : Lean.BinderInfo → String
    | .default => ""
    | .implicit => " :implicit"
    | .strictImplicit => " :strictImplicit"
    | .instImplicit => " :instImplicit"
  of_name (name: Name) := name_to_ast name sanitize

def serialize_expression (options: @&Protocol.Options) (e: Expr): MetaM Protocol.Expression := do
  let pp := toString (← Meta.ppExpr e)
  let pp?: Option String := match options.printExprPretty with
    | true => .some pp
    | false => .none
  let sexp: String ← serialize_expression_ast e
  let sexp?: Option String := match options.printExprAST with
    | true => .some sexp
    | false => .none
  return {
    pp?,
    sexp?
  }

/-- Adapted from ppGoal -/
def serialize_goal (options: @&Protocol.Options) (goal: MVarId) (mvarDecl: MetavarDecl) (parentDecl?: Option MetavarDecl)
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
        let userName := userName.simpMacroScopes
        return {
          name := of_name fvarId.name,
          userName:= of_name userName.simpMacroScopes,
        }
      | .ldecl _ fvarId userName _ _ _ _ => do
        return {
          name := of_name fvarId.name,
          userName := toString userName.simpMacroScopes,
        }
    let ppVar (localDecl : LocalDecl) : MetaM Protocol.Variable := do
      match localDecl with
      | .cdecl _ fvarId userName type _ _ =>
        let userName := userName.simpMacroScopes
        let type ← instantiateMVars type
        return {
          name := of_name fvarId.name,
          userName:= of_name userName,
          isInaccessible? := .some userName.isInaccessibleUserName
          type? := .some (← serialize_expression options type)
        }
      | .ldecl _ fvarId userName type val _ _ => do
        let userName := userName.simpMacroScopes
        let type ← instantiateMVars type
        let value? ← if showLetValues then
          let val ← instantiateMVars val
          pure $ .some (← serialize_expression options val)
        else
          pure $ .none
        return {
          name := of_name fvarId.name,
          userName:= of_name userName,
          isInaccessible? := .some userName.isInaccessibleUserName
          type? := .some (← serialize_expression options type)
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
      name := of_name goal.name,
      userName? := if mvarDecl.userName == .anonymous then .none else .some (of_name mvarDecl.userName),
      isConversion := isLHSGoal? mvarDecl.type |>.isSome,
      target := (← serialize_expression options (← instantiateMVars mvarDecl.type)),
      vars := vars.reverse.toArray
    }
  where
  of_name (n: Name) := name_to_ast n (sanitize := false)

protected def GoalState.serializeGoals
      (state: GoalState)
      (parent: Option GoalState := .none)
      (options: @&Protocol.Options := {}):
    MetaM (Array Protocol.Goal):= do
  state.restoreMetaM
  let goals := state.goals.toArray
  let parentDecl? := parent.bind (λ parentState =>
    let parentGoal := parentState.goals.get! state.parentGoalId
    parentState.mctx.findDecl? parentGoal)
  goals.mapM fun goal => do
    match state.mctx.findDecl? goal with
    | .some mvarDecl =>
      let serializedGoal ← serialize_goal options goal mvarDecl (parentDecl? := parentDecl?)
      pure serializedGoal
    | .none => throwError s!"Metavariable does not exist in context {goal.name}"

/-- Print the metavariables in a readable format -/
protected def GoalState.print (goalState: GoalState) (options: Protocol.GoalDiag := {}): MetaM Unit := do
  goalState.restoreMetaM
  let savedState := goalState.savedState
  let goals := savedState.tactic.goals
  let mctx ← getMCtx
  let root := goalState.root
  -- Print the root
  match mctx.decls.find? root with
  | .some decl => printMVar ">" root decl
  | .none => IO.println s!">{root.name}: ??"
  goals.forM (fun mvarId => do
    if mvarId != root then
      match mctx.decls.find? mvarId with
      | .some decl => printMVar "⊢" mvarId decl
      | .none => IO.println s!"⊢{mvarId.name}: ??"
  )
  let goals := goals.toSSet
  mctx.decls.forM (fun mvarId decl => do
    if goals.contains mvarId || mvarId == root then
      pure ()
    -- Print the remainig ones that users don't see in Lean
    else if options.printAll then
      let pref := if goalState.newMVars.contains mvarId then "~" else " "
      printMVar pref mvarId decl
    else
      pure ()
      --IO.println s!" {mvarId.name}{userNameToString decl.userName}"
  )
  where
    printMVar (pref: String) (mvarId: MVarId) (decl: MetavarDecl): MetaM Unit := do
      if options.printContext then
        decl.lctx.fvarIdToDecl.forM printFVar
      let type ← if options.instantiate
        then instantiateMVars decl.type
        else pure $ decl.type
      let type_sexp ← serialize_expression_ast type (sanitize := false)
      IO.println s!"{pref}{mvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type} {type_sexp}"
      if options.printValue then
        if let Option.some value := (← getMCtx).eAssignment.find? mvarId then
          let value ← if options.instantiate
            then instantiateMVars value
            else pure $ value
          IO.println s!" := {← Meta.ppExpr value}"
    printFVar (fvarId: FVarId) (decl: LocalDecl): MetaM Unit := do
      IO.println s!" | {fvarId.name}{userNameToString decl.userName}: {← Meta.ppExpr decl.type}"
    userNameToString : Name → String
      | .anonymous => ""
      | other => s!"[{other}]"

end Pantograph
