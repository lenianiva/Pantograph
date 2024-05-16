import Lean

open Lean

namespace Pantograph

def _root_.Lean.Name.isAuxLemma (n : Lean.Name) : Bool := n matches .num (.str _ "_auxLemma") _

/-- Unfold all lemmas created by `Lean.Meta.mkAuxLemma`. These end in `_auxLemma.nn` where `nn` is a number. -/
def unfoldAuxLemmas (e : Expr) : CoreM Expr := do
  Lean.Meta.deltaExpand e Lean.Name.isAuxLemma

/--
Force the instantiation of delayed metavariables even if they cannot be fully
instantiated. This is used during resumption.

Since Lean 4 does not have an `Expr` constructor corresponding to delayed
metavariables, any delayed metavariables must be recursively handled by this
function to ensure that nested delayed metavariables can be properly processed.
The caveat is this recursive call will lead to infinite recursion if a loop
between metavariable assignment exists.

This function ensures any metavariable in the result is either
1. Delayed assigned with its pending mvar not assigned in any form
2. Not assigned (delay or not)
 -/
partial def instantiateDelayedMVars (eOrig: Expr): MetaM Expr := do
  --let padding := String.join $ List.replicate level "  "
  --IO.println s!"{padding}Starting {toString eOrig}"
  let result ← Meta.transform (← instantiateMVars eOrig)
    (pre := fun e => e.withApp fun f args => do
      --IO.println s!"{padding} V {toString e}"
      if let .mvar mvarId := f then
        if ← mvarId.isAssigned then
          --IO.println s!"{padding} A ?{mvarId.name}"
          return .continue <| .some (← self e)
        if let some { fvars, mvarIdPending } ← getDelayedMVarAssignment? mvarId then
          -- No progress can be made on this
          if !(← mvarIdPending.isAssigned) then
            --IO.println s!"{padding} D/T1: {toString e}"
            let args ← args.mapM self
            let result := mkAppN f args
            return .done result

          --IO.println s!"{padding} D ?{mvarId.name} := [{fvars.size}] ?{mvarIdPending.name}"
          -- This asstion fails when a tactic or elaboration function is
          -- implemented incorrectly. See `instantiateExprMVars`
          if args.size < fvars.size then
            --IO.println s!"{padding} Illegal callsite: {args.size} < {fvars.size}"
            throwError "Not enough arguments to instantiate a delay assigned mvar. This is due to bad implementations of a tactic: {args.size} < {fvars.size}. Expr: {toString e}; Origin: {toString eOrig}"
          assert! !(← mvarIdPending.isDelayedAssigned)
          let pending ← self (.mvar mvarIdPending)
          if pending == .mvar mvarIdPending then
            -- No progress could be made on this case
            --IO.println s!"{padding}D/N {toString e}"
            assert! !(← mvarIdPending.isAssigned)
            assert! !(← mvarIdPending.isDelayedAssigned)
          --else if pending.isMVar then
          --  assert! !(← pending.mvarId!.isAssigned)
          --  assert! !(← pending.mvarId!.isDelayedAssigned)
          --  -- Progress made, but this is now another delayed assigned mvar
          --  let nextMVarId ← mkFreshMVarId
          --  assignDelayedMVar nextMVarId fvars pending.mvarId!
          --  let args ← args.mapM self
          --  let result := mkAppN (.mvar nextMVarId) args
          --  return .done result
          else
            -- Progress has been made on this mvar
            let pending := pending.abstract fvars
            let args ← args.mapM self
            -- Craete the function call structure
            let subst := pending.instantiateRevRange 0 fvars.size args
            let result := mkAppRange subst fvars.size args.size args
            --IO.println s!"{padding}D/T2 {toString result}"
            return .done result
      return .continue)
  --IO.println s!"{padding}Result {toString result}"
  return result
  where
  self e := instantiateDelayedMVars e

/--
Convert an expression to an equiavlent form with
1. No nested delayed assigned mvars
2. No aux lemmas
3. No assigned mvars
 -/
@[export pantograph_instantiate_all_meta_m]
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
@[export pantograph_to_delayed_mvar_invocation_meta_m]
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
