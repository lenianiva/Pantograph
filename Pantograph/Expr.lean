import Lean

open Lean

namespace Pantograph

def _root_.Lean.Name.isAuxLemma (n : Lean.Name) : Bool := n matches .num (.str _ "_auxLemma") _

/-- Unfold all lemmas created by `Lean.Meta.mkAuxLemma`. These end in `_auxLemma.nn` where `nn` is a number. -/
def unfoldAuxLemmas (e : Expr) : CoreM Expr := do
  Lean.Meta.deltaExpand e Lean.Name.isAuxLemma

def instantiatePartialDelayedMVars (e: Expr): MetaM Expr := do
  Meta.transform e
    (pre := fun e => e.withApp fun f args => do
      if let .mvar mvarId := f then
        if let some decl ← getDelayedMVarAssignment? mvarId then
          if args.size ≥ decl.fvars.size then
            let pending ← instantiateMVars (.mvar decl.mvarIdPending)
            if !pending.isMVar then
              return .visit <| (← Meta.mkLambdaFVars decl.fvars pending).beta args
      return .continue)

@[export pantograph_instantiate_all_meta_m]
def instantiateAll (e: Expr): MetaM Expr := do
  let e ← instantiateMVars e
  let e ← unfoldAuxLemmas e
  --let e ← instantiatePartialDelayedMVars e
  return e

structure DelayedMVarInvocation where
  mvarIdPending: MVarId
  args: Array (FVarId × (Option Expr))
  tail: Array Expr

@[export pantograph_to_delayed_mvar_invocation_meta_m]
def toDelayedMVarInvocation (e: Expr): MetaM (Option DelayedMVarInvocation) := do
  let .mvar mvarId := e.getAppFn | return .none
  let .some decl ← getDelayedMVarAssignment? mvarId | return .none
  let mvarIdPending := decl.mvarIdPending
  let mvarDecl ← mvarIdPending.getDecl
  -- Print the function application e. See Lean's `withOverApp`
  let args := e.getAppArgs

  assert! args.size >= decl.fvars.size
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
