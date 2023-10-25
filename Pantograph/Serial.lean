/-
All serialisation functions
-/
import Lean

import Pantograph.Protocol

namespace Pantograph
open Lean

--- Input Functions ---


/-- Read a theorem from the environment -/
def expr_from_const (env: Environment) (name: Name): Except String Lean.Expr :=
  match env.find? name with
  | none       => throw s!"Symbol not found: {name}"
  | some cInfo => return cInfo.type
/-- Read syntax object from string -/
def syntax_from_str (env: Environment) (s: String): Except String Syntax :=
  Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")


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

private def name_to_ast (name: Lean.Name) (sanitize: Bool := true): String := match name with
  | .anonymous => ":anon"
  | .num n i => match sanitize with
    | false => s!"{toString n} {i}"
    | true => ":anon"
  | n@(.str _ _) => toString n

private def level_depth: Level → Nat
  | .zero => 0
  | .succ l => 1 + (level_depth l)
  | .max u v | .imax u v => 1 + max (level_depth u) (level_depth v)
  | .param _ | .mvar _ => 0

theorem level_depth_max_imax (u v: Level): (level_depth (Level.max u v) = level_depth (Level.imax u v)) := by
  constructor
theorem level_max_depth_decrease (u v: Level): (level_depth u < level_depth (Level.max u v)) := by
  have h1: level_depth (Level.max u v) = 1 + Nat.max (level_depth u) (level_depth v) := by constructor
  rewrite [h1]
  simp_arith
  conv =>
    rhs
    apply Nat.max_def
  sorry
theorem level_offset_decrease (u v: Level): (level_depth u ≤ level_depth (Level.max u v).getLevelOffset) := sorry

/-- serialize a sort level. Expression is optimized to be compact e.g. `(+ u 2)` -/
def serialize_sort_level_ast (level: Level): String :=
  let k := level.getOffset
  let u := level.getLevelOffset
  let u_str := match u with
    | .zero => "0"
    | .succ _ => panic! "getLevelOffset should not return .succ"
    | .max v w =>
      let v := serialize_sort_level_ast v
      let w := serialize_sort_level_ast w
      s!"(:max {v} {w})"
    | .imax v w =>
      let v := serialize_sort_level_ast v
      let w := serialize_sort_level_ast w
      s!"(:imax {v} {w})"
    | .param name =>
      let name := name_to_ast name
      s!"{name}"
    | .mvar id =>
      let name := name_to_ast id.name
      s!"(:mv {name})"
  match k, u with
  | 0, _ => u_str
  | _, .zero => s!"{k}"
  | _, _ => s!"(+ {u_str} {k})"
  termination_by serialize_sort_level_ast level => level_depth level
  decreasing_by
  . sorry

/--
 Completely serializes an expression tree. Json not used due to compactness
-/
def serialize_expression_ast (expr: Expr) (sanitize: Bool := true): MetaM String := do
  return self expr
  where
  self (e: Expr): String :=
    match e with
    | .bvar deBruijnIndex =>
      -- This is very common so the index alone is shown. Literals are handled below.
      -- The raw de Bruijn index should never appear in an unbound setting. In
      -- Lean these are handled using a `#` prefix.
      s!"{deBruijnIndex}"
    | .fvar fvarId =>
      let name := of_name fvarId.name
      s!"(:fv {name})"
    | .mvar mvarId =>
      let name := of_name mvarId.name
      s!"(:mv {name})"
    | .sort level =>
      let level := serialize_sort_level_ast level
      s!"(:sort {level})"
    | .const declName _ =>
      -- The universe level of the const expression is elided since it should be
      -- inferrable from surrounding expression
      s!"(:c {declName})"
    | .app fn arg =>
      let fn' := self fn
      let arg' := self arg
      s!"({fn'} {arg'})"
    | .lam binderName binderType body binderInfo =>
      let binderName' := of_name binderName
      let binderType' := self binderType
      let body' := self body
      let binderInfo' := binder_info_to_ast binderInfo
      s!"(:lambda {binderName'} {binderType'} {body'}{binderInfo'})"
    | .forallE binderName binderType body binderInfo =>
      let binderName' := of_name binderName
      let binderType' := self binderType
      let body' := self body
      let binderInfo' := binder_info_to_ast binderInfo
      s!"(:forall {binderName'} {binderType'} {body'}{binderInfo'})"
    | .letE name type value body _ =>
      -- Dependent boolean flag diacarded
      let name' := name_to_ast name
      let type' := self type
      let value' := self value
      let body' := self body
      s!"(:let {name'} {type'} {value'} {body'})"
    | .lit v =>
      -- To not burden the downstream parser who needs to handle this, the literal
      -- is wrapped in a :lit sexp.
      let v' := match v with
        | .natVal val => toString val
        | .strVal val => s!"\"{val}\""
      s!"(:lit {v'})"
    | .mdata _ inner =>
      -- NOTE: Equivalent to expr itself, but mdata influences the prettyprinter
      -- It may become necessary to incorporate the metadata.
      self inner
    | .proj typeName idx struct =>
      let struct' := self struct
      s!"(:proj {typeName} {idx} {struct'})"
  -- Elides all unhygenic names
  binder_info_to_ast : Lean.BinderInfo → String
    | .default => ""
    | .implicit => " :implicit"
    | .strictImplicit => " :strictImplicit"
    | .instImplicit => " :instImplicit"
  of_name (name: Name) := name_to_ast name sanitize

def serialize_expression (options: Protocol.Options) (e: Expr): MetaM Protocol.Expression := do
  let pp := toString (← Meta.ppExpr e)
  let pp?: Option String := match options.printExprPretty with
      | true => .some pp
      | false => .none
  let sexp: String := (← serialize_expression_ast e)
  let sexp?: Option String := match options.printExprAST with
      | true => .some sexp
      | false => .none
  return {
    pp?,
    sexp?
  }

/-- Adapted from ppGoal -/
def serialize_goal (options: Protocol.Options) (mvarDecl: MetavarDecl) (parentDecl?: Option MetavarDecl)
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
      | .cdecl _ _ varName _ _ _ =>
        let varName := varName.simpMacroScopes
        return {
          name := toString varName,
        }
      | .ldecl _ _ varName _ _ _ _ => do
        return {
          name := toString varName,
        }
    let ppVar (localDecl : LocalDecl) : MetaM Protocol.Variable := do
      match localDecl with
      | .cdecl _ _ varName type _ _ =>
        let varName := varName.simpMacroScopes
        let type ← instantiateMVars type
        return {
          name := toString varName,
          isInaccessible? := .some varName.isInaccessibleUserName
          type? := .some (← serialize_expression options type)
        }
      | .ldecl _ _ varName type val _ _ => do
        let varName := varName.simpMacroScopes
        let type ← instantiateMVars type
        let value? ← if showLetValues then
          let val ← instantiateMVars val
          pure $ .some (← serialize_expression options val)
        else
          pure $ .none
        return {
          name := toString varName,
          isInaccessible? := .some varName.isInaccessibleUserName
          type? := .some (← serialize_expression options type)
          value? := value?
        }
    let vars ← lctx.foldlM (init := []) fun acc (localDecl : LocalDecl) => do
      let skip := !ppAuxDecls && localDecl.isAuxDecl ||
        !ppImplDetailHyps && localDecl.isImplementationDetail
      if skip then
        return acc
      else
        let nameOnly := options.proofVariableDelta && (parentDecl?.map
          (λ decl => decl.lctx.find? localDecl.fvarId |>.isSome) |>.getD false)
        let var ← match nameOnly with
          | true => ppVarNameOnly localDecl
          | false => ppVar localDecl
        return var::acc
    return {
      caseName? := match mvarDecl.userName with
        | Name.anonymous => .none
        | name => .some <| toString name,
      isConversion := isLHSGoal? mvarDecl.type |>.isSome,
      target := (← serialize_expression options (← instantiateMVars mvarDecl.type)),
      vars := vars.reverse.toArray
    }



end Pantograph
