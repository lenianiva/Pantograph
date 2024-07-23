/- structures for FFI based interface -/
import Lean

open Lean

namespace Pantograph.Condensed

/-
These two functions are for user defiend names. For internal names such as
`_uniq`, it is favourable to use `lean_name_hash_exported` and `lean_name_eq` to
construct hash maps for Lean names.
-/
@[export pantograph_str_to_name]
def strToName (s: String) : Name := s.toName
@[export pantograph_name_to_str]
def nameToStr (s: Name) : String := s.toString
@[export pantograph_name_is_inaccessible]
def isInaccessible (n: Name) : Bool := n.isInaccessibleUserName

@[export pantograph_mk_app_m]
def mkAppM (constName : Name) (xs : Array Expr) : MetaM Expr := Meta.mkAppM constName xs

@[export pantograph_pp_expr_m]
def ppExpr (e: Expr): MetaM String := toString <$> Meta.ppExpr e


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


-- Functions for creating contexts and states
@[export pantograph_meta_context]
def metaContext: Meta.Context := {}
@[export pantograph_meta_state]
def metaState: Meta.State := {}
@[export pantograph_elab_context]
def elabContext: Meta.Context := {}
@[export pantograph_elab_state]
def elabState (levelNames: Array Name): Elab.Term.State := {
    levelNames := levelNames.toList,
  }



end Pantograph.Condensed
