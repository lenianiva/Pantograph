import Lean.Meta

open Lean

namespace Pantograph.Frontend

namespace MetaTranslate

structure Context where
  sourceMCtx : MetavarContext := {}
  sourceLCtx : LocalContext := {}

abbrev FVarMap := HashMap FVarId FVarId

structure State where
  -- Stores mapping from old to new mvar/fvars
  mvarMap: HashMap MVarId MVarId := {}
  fvarMap: HashMap FVarId FVarId := {}

/-
Monadic state for translating a frozen meta state. The underlying `MetaM`
operates in the "target" context and state.
-/
abbrev MetaTranslateM := ReaderT Context StateRefT State MetaM

def getSourceLCtx : MetaTranslateM LocalContext := do pure (← read).sourceLCtx
def getSourceMCtx : MetaTranslateM MetavarContext := do pure (← read).sourceMCtx
def addTranslatedFVar (src dst: FVarId) : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with fvarMap := state.fvarMap.insert src dst })
def addTranslatedMVar (src dst: MVarId) : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with mvarMap := state.mvarMap.insert src dst })

def saveFVarMap : MetaTranslateM FVarMap := do
  return (← get).fvarMap
def restoreFVarMap (map: FVarMap) : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with fvarMap := map })
def resetFVarMap : MetaTranslateM Unit := do
  modifyGet λ state => ((), { state with fvarMap := {} })

mutual
private partial def translateExpr (srcExpr: Expr) : MetaTranslateM Expr := do
  let sourceMCtx ← getSourceMCtx
  let (srcExpr, _) := instantiateMVarsCore (mctx := sourceMCtx) srcExpr
  --IO.println s!"Transform src: {srcExpr}"
  let result ← Core.transform srcExpr λ e => do
    let state ← get
    match e with
    | .fvar fvarId =>
      let .some fvarId' := state.fvarMap.find? fvarId | panic! s!"FVar id not registered: {fvarId.name}"
      assert! (← getLCtx).contains fvarId'
      return .done $ .fvar fvarId'
    | .mvar mvarId => do
      assert! !(sourceMCtx.dAssignment.contains mvarId)
      assert! !(sourceMCtx.eAssignment.contains mvarId)
      match state.mvarMap.find? mvarId with
      | .some mvarId' => do
        return .done $ .mvar mvarId'
      | .none => do
        -- Entering another LCtx, must save the current one
        let fvarMap ← saveFVarMap
        let mvarId' ← translateMVarId mvarId
        restoreFVarMap fvarMap
        return .done $ .mvar mvarId'
    | _ => return .continue
  Meta.check result
  return result

partial def translateLocalInstance (srcInstance: LocalInstance) : MetaTranslateM LocalInstance := do
  return {
    className := srcInstance.className,
    fvar := ← translateExpr srcInstance.fvar
  }
partial def translateLocalDecl (srcLocalDecl: LocalDecl) : MetaTranslateM LocalDecl := do
  let fvarId ← mkFreshFVarId
  addTranslatedFVar srcLocalDecl.fvarId fvarId
  match srcLocalDecl with
  | .cdecl index _ userName type bi kind => do
    --IO.println s!"[CD] {userName} {toString type}"
    return .cdecl index fvarId userName (← translateExpr type) bi kind
  | .ldecl index _ userName type value nonDep kind => do
    --IO.println s!"[LD] {toString type} := {toString value}"
    return .ldecl index fvarId userName (← translateExpr type) (← translateExpr value) nonDep kind

partial def translateLCtx : MetaTranslateM LocalContext := do
  resetFVarMap
  (← getSourceLCtx).foldlM (λ lctx srcLocalDecl => do
    let localDecl ← Meta.withLCtx lctx #[] do translateLocalDecl srcLocalDecl
    pure $ lctx.addDecl localDecl
  ) (← MonadLCtx.getLCtx)

partial def translateMVarId (srcMVarId: MVarId) : MetaTranslateM MVarId := do
  if let .some mvarId' := (← get).mvarMap.find? srcMVarId then
    return mvarId'
  let srcDecl := (← getSourceMCtx).findDecl? srcMVarId |>.get!
  let mvar ← withTheReader Context (λ ctx => { ctx with sourceLCtx := srcDecl.lctx }) do
    let lctx' ← translateLCtx
    let localInstances' ← srcDecl.localInstances.mapM translateLocalInstance
    Meta.withLCtx lctx' localInstances' do
      let target' ← translateExpr srcDecl.type
      Meta.mkFreshExprMVar target' srcDecl.kind srcDecl.userName
  addTranslatedMVar srcMVarId mvar.mvarId!
  return mvar.mvarId!
end

def translateMVarFromTermInfo (termInfo : Elab.TermInfo) (context? : Option Elab.ContextInfo)
    : MetaTranslateM MVarId := do
  withTheReader Context (λ ctx => { ctx with
    sourceMCtx := context?.map (·.mctx) |>.getD {},
    sourceLCtx := termInfo.lctx,
  }) do
    let type := termInfo.expectedType?.get!
    let lctx' ← translateLCtx
    let mvar ← Meta.withLCtx lctx' #[] do
      let type' ← translateExpr type
      Meta.mkFreshExprSyntheticOpaqueMVar type'
    return mvar.mvarId!


def translateMVarFromTacticInfoBefore (tacticInfo : Elab.TacticInfo) (_context? : Option Elab.ContextInfo)
    : MetaTranslateM (List MVarId) := do
  withTheReader Context (λ ctx => { ctx with sourceMCtx := tacticInfo.mctxBefore }) do
    tacticInfo.goalsBefore.mapM translateMVarId


end MetaTranslate

export MetaTranslate (MetaTranslateM)

end Pantograph.Frontend
