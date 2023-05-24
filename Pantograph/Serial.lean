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


def syntax_to_expr (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabType syn
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


end Pantograph
