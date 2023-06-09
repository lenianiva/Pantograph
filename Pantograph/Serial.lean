/-
All serialisation functions
-/
import Lean

namespace Pantograph
open Lean


/-- Read a theorem from the environment -/
def expr_from_const (env: Environment) (name: Name): Except String Lean.Expr :=
  match env.find? name with
  | none       => throw s!"Symbol not found: {name}"
  | some cInfo => return cInfo.type
def syntax_from_str (env: Environment) (s: String): Except String Syntax :=
  Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")


def syntax_to_expr_type (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabType syn
    -- Immediately synthesise all metavariables if we need to leave the elaboration context.
    -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070
    --Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)
def syntax_to_expr (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabTerm (stx := syn) (expectedType? := .none)
    -- Immediately synthesise all metavariables if we need to leave the elaboration context.
    -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070
    --Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)

structure BoundExpression where
  binders: Array (String × String)
  target: String
  deriving ToJson
def type_expr_to_bound (expr: Expr): MetaM BoundExpression := do
  Meta.forallTelescope expr fun arr body => do
    let binders ← arr.mapM fun fvar => do
      return (toString (← fvar.fvarId!.getUserName), toString (← Meta.ppExpr (← fvar.fvarId!.getType)))
    return { binders, target := toString (← Meta.ppExpr body) }


structure Variable where
  name: String
  /-- Does the name contain a dagger -/
  isInaccessible: Bool      := false
  type: String
  value?: Option String     := .none
  deriving ToJson
structure Goal where
  /-- String case id -/
  caseName?: Option String  := .none
  /-- Is the goal in conversion mode -/
  isConversion: Bool        := false
  /-- target expression type -/
  target: String
  /-- Variables -/
  vars: Array Variable      := #[]
  deriving ToJson

/-- Adapted from ppGoal -/
def serialize_goal (mvarDecl: MetavarDecl) : MetaM Goal := do
  -- Options for printing; See Meta.ppGoal for details
  let showLetValues  := True
  let ppAuxDecls     := false
  let ppImplDetailHyps := false
  let lctx           := mvarDecl.lctx
  let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx mvarDecl.localInstances do
    let rec ppVars (localDecl : LocalDecl) : MetaM Variable := do
      match localDecl with
      | .cdecl _ _ varName type _ _ =>
        let varName := varName.simpMacroScopes
        let type ← instantiateMVars type
        return {
          name := toString varName,
          isInaccessible := varName.isInaccessibleUserName,
          type := toString <| ← Meta.ppExpr type
        }
      | .ldecl _ _ varName type val _ _ => do
        let varName := varName.simpMacroScopes
        let type ← instantiateMVars type
        let value? ← if showLetValues then
          let val ← instantiateMVars val
          pure $ .some <| toString <| (← Meta.ppExpr val)
        else
          pure $ .none
        return {
          name := toString varName,
          isInaccessible := varName.isInaccessibleUserName,
          type := toString <| ← Meta.ppExpr type
          value? := value?
        }
    let vars ← lctx.foldlM (init := []) fun acc (localDecl : LocalDecl) => do
       let skip := !ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail
       if skip then
         return acc
       else
         let var ← ppVars localDecl
         return var::acc
    return {
      caseName? := match mvarDecl.userName with
        | Name.anonymous => .none
        | name => .some <| toString name,
      isConversion := "| " == (Meta.getGoalPrefix mvarDecl)
      target := toString <| (← Meta.ppExpr (← instantiateMVars mvarDecl.type)),
      vars := vars.reverse.toArray
    }

end Pantograph
