import Lean

/-
Expression IO
-/


namespace Pantograph.IO


def exprToStr (env: Lean.Environment) (coreContext: Lean.Core.Context) (expr: Lean.Expr): IO String := do
  let metaM := Lean.Meta.ppExpr expr
  let coreM : Lean.CoreM Lean.Format := metaM.run'
  let coreState : Lean.Core.State := { env := env }
  let (format, _) ← coreM.toIO coreContext coreState
  return format.pretty


end Pantograph.IO
