/- structures for FFI based interface -/
import Lean
import Pantograph.Goal
import Pantograph.Expr

open Lean

namespace Pantograph
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

-- Functions for creating contexts and states
@[export pantograph_elab_context]
def elabContext: Elab.Term.Context := {
    errToSorry := false
  }

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

end Pantograph
