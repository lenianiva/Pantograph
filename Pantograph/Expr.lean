import Lean

open Lean

namespace Pantograph

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

      let lctx ← MonadLCtx.getLCtx
      if mvarDecl.lctx.any (λ decl => !lctx.contains decl.fvarId) then
        let violations := mvarDecl.lctx.decls.foldl (λ acc decl? => match decl? with
          | .some decl => if lctx.contains decl.fvarId then acc else acc ++ [decl.fvarId.name]
          | .none => acc) []
        panic! s!"Local context variable violation: {violations}"

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
  let fvarArgMap: HashMap FVarId Expr := HashMap.ofList $ (decl.fvars.map (·.fvarId!) |>.zip args).toList
  let subst ← mvarDecl.lctx.foldlM (init := []) λ acc localDecl => do
    let fvarId := localDecl.fvarId
    let a := fvarArgMap.find? fvarId
    return acc ++ [(fvarId, a)]

  assert! decl.fvars.all (λ fvar => mvarDecl.lctx.findFVar? fvar |>.isSome)

  return .some {
    mvarIdPending,
    args := subst.toArray,
    tail := args.toList.drop decl.fvars.size |>.toArray,
  }

end Pantograph
