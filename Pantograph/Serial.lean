/-
All serialisation functions;
This replicates the behaviour of `Scope`s in `Lean/Elab/Command.lean` without
using `Scope`s.
-/
import Lean
import Pantograph.Condensed
import Pantograph.Expr
import Pantograph.Goal
import Pantograph.Protocol

open Lean

-- Symbol processing functions --

namespace Pantograph


--- Input Functions ---

/-- Read syntax object from string -/
def parseTerm (env: Environment) (s: String): Except String Syntax :=
  Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")

/-- Parse a syntax object. May generate additional metavariables! -/
def elabType (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabType syn
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)
def elabTerm (syn: Syntax) (expectedType? : Option Expr := .none): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabTerm (stx := syn) expectedType?
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)


--- Output Functions ---

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
      let binderName' := ofName binderName
      let binderType' ← self binderType
      let body' ← self body
      let binderInfo' := binderInfoSexp binderInfo
      pure s!"(:lambda {binderName'} {binderType'} {body'}{binderInfo'})"
    | .forallE binderName binderType body binderInfo => do
      let binderName' := ofName binderName
      let binderType' ← self binderType
      let body' ← self body
      let binderInfo' := binderInfoSexp binderInfo
      pure s!"(:forall {binderName'} {binderType'} {body'}{binderInfo'})"
    | .letE name type value body _ => do
      -- Dependent boolean flag diacarded
      let name' := serializeName name
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
      let ctor := getStructureCtor env typeName
      let fieldName := getStructureFields env typeName |>.get! idx
      let projectorName := getProjFnForField? env typeName fieldName |>.get!

      let autos := String.intercalate " " (List.replicate ctor.numParams "_")
      let inner ← self inner
      pure s!"((:c {projectorName}) {autos} {inner})"
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
def serializeGoal (options: @&Protocol.Options) (goal: MVarId) (mvarDecl: MetavarDecl) (parentDecl?: Option MetavarDecl)
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
        }
      | .ldecl _ fvarId userName _ _ _ _ => do
        return {
          name := ofName fvarId.name,
          userName := toString userName.simpMacroScopes,
        }
    let ppVar (localDecl : LocalDecl) : MetaM Protocol.Variable := do
      match localDecl with
      | .cdecl _ fvarId userName type _ _ =>
        let userName := userName.simpMacroScopes
        let type ← instantiate type
        return {
          name := ofName fvarId.name,
          userName:= ofName userName,
          isInaccessible? := .some userName.isInaccessibleUserName
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
          isInaccessible? := .some userName.isInaccessibleUserName
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
protected def GoalState.diag (goalState: GoalState) (options: Protocol.GoalDiag := {}): MetaM String := do
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
        let pref := if goalState.newMVars.contains mvarId then "~" else " "
        printMVar pref mvarId decl
      )
  pure $ result ++ "\n" ++ (resultGoals.map (· ++ "\n") |> String.join) ++ (resultOthers.map (· ++ "\n") |> String.join)
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

end Pantograph
