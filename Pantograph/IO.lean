import Lean

/-
Expression IO
-/


namespace Pantograph.IO


def exprToStr (env: Lean.Environment) (e: Lean.Expr): String :=
  let format := Lean.Meta.ppExpr e
  "stub"


end Pantograph.IO
