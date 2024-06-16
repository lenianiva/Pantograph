import Pantograph.Protocol
import Pantograph.Serial
import Lean

open Lean
open Pantograph

namespace Pantograph.Environment

def isNameInternal (n: Lean.Name): Bool :=
  -- Returns true if the name is an implementation detail which should not be shown to the user.
  isLeanSymbol n ∨ (Lean.privateToUserName? n |>.map isLeanSymbol |>.getD false) ∨ n.isAuxLemma ∨ n.hasMacroScopes
  where
  isLeanSymbol (name: Lean.Name): Bool := match name.getRoot with
    | .str _ name => name == "Lean"
    | _ => true

def toCompactSymbolName (n: Lean.Name) (info: Lean.ConstantInfo): String :=
  let pref := match info with
  | .axiomInfo  _ => "a"
  | .defnInfo   _ => "d"
  | .thmInfo    _ => "t"
  | .opaqueInfo _ => "o"
  | .quotInfo   _ => "q"
  | .inductInfo _ => "i"
  | .ctorInfo   _ => "c"
  | .recInfo    _ => "r"
  s!"{pref}{toString n}"

def toFilteredSymbol (n: Lean.Name) (info: Lean.ConstantInfo): Option String :=
  if isNameInternal n || info.isUnsafe
  then Option.none
  else Option.some <| toCompactSymbolName n info
def catalog (_: Protocol.EnvCatalog): CoreM Protocol.EnvCatalogResult := do
  let env ← Lean.MonadEnv.getEnv
  let names := env.constants.fold (init := #[]) (λ acc name info =>
    match toFilteredSymbol name info with
    | .some x => acc.push x
    | .none => acc)
  return { symbols := names }
def inspect (args: Protocol.EnvInspect) (options: @&Protocol.Options): CoreM (Protocol.CR Protocol.EnvInspectResult) := do
  let env ← Lean.MonadEnv.getEnv
  let name :=  args.name.toName
  let info? := env.find? name
  let info ← match info? with
    | none => return .error $ Protocol.errorIndex s!"Symbol not found {args.name}"
    | some info => pure info
  let module? := env.getModuleIdxFor? name >>=
    (λ idx => env.allImportedModuleNames.get? idx.toNat) |>.map toString
  let value? := match args.value?, info with
    | .some true, _ => info.value?
    | .some false, _ => .none
    | .none, .defnInfo _ => info.value?
    | .none, _ => .none
  let type ← unfoldAuxLemmas info.type
  let value? ← value?.mapM (λ v => unfoldAuxLemmas v)
  -- Information common to all symbols
  let core := {
    type := ← (serializeExpression options type).run',
    isUnsafe := info.isUnsafe,
    value? := ← value?.mapM (λ v => serializeExpression options v |>.run'),
    publicName? := Lean.privateToUserName? name |>.map (·.toString),
    -- BUG: Warning: getUsedConstants here will not include projections. This is a known bug.
    typeDependency? := if args.dependency?.getD false
      then .some <| type.getUsedConstants.map (λ n => serializeName n)
      else .none,
    valueDependency? := if args.dependency?.getD false
      then value?.map (λ e =>
        e.getUsedConstants.filter (!isNameInternal ·) |>.map (λ n => serializeName n) )
      else .none,
    module? := module?
  }
  let result ← match info with
    | .inductInfo induct => pure { core with inductInfo? := .some {
          numParams := induct.numParams,
          numIndices := induct.numIndices,
          all := induct.all.toArray.map (·.toString),
          ctors := induct.ctors.toArray.map (·.toString),
          isRec := induct.isRec,
          isReflexive := induct.isReflexive,
          isNested := induct.isNested,
      } }
    | .ctorInfo ctor => pure { core with constructorInfo? := .some {
          induct := ctor.induct.toString,
          cidx := ctor.cidx,
          numParams := ctor.numParams,
          numFields := ctor.numFields,
      } }
    | .recInfo r => pure { core with recursorInfo? := .some {
          all := r.all.toArray.map (·.toString),
          numParams := r.numParams,
          numIndices := r.numIndices,
          numMotives := r.numMotives,
          numMinors := r.numMinors,
          rules := ← r.rules.toArray.mapM (λ rule => do
              pure {
                ctor := rule.ctor.toString,
                nFields := rule.nfields,
                rhs := ← (serializeExpression options rule.rhs).run',
              })
          k := r.k,
      } }
    | _ => pure core
  return .ok result
def addDecl (args: Protocol.EnvAdd): CoreM (Protocol.CR Protocol.EnvAddResult) := do
  let env ← Lean.MonadEnv.getEnv
  let tvM: Elab.TermElabM (Except String (Expr × Expr)) := do
    let type ← match parseTerm env args.type with
      | .ok syn => do
        match ← elabTerm syn with
        | .error e => return .error e
        | .ok expr => pure expr
      | .error e => return .error e
    let value ← match parseTerm env args.value with
      | .ok syn => do
        try
          let expr ← Elab.Term.elabTerm (stx := syn) (expectedType? := .some type)
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let expr ← instantiateMVars expr
          pure $ expr
        catch ex => return .error (← ex.toMessageData.toString)
      | .error e => return .error e
    pure $ .ok (type, value)
  let (type, value) ← match ← tvM.run' (ctx := {}) |>.run' with
    | .ok t => pure t
    | .error e => return .error $ Protocol.errorExpr e
  let constant := Lean.Declaration.defnDecl <| Lean.mkDefinitionValEx
    (name := args.name.toName)
    (levelParams := [])
    (type := type)
    (value := value)
    (hints := Lean.mkReducibilityHintsRegularEx 1)
    (safety := Lean.DefinitionSafety.safe)
    (all := [])
  let env' ← match env.addDecl constant with
    | .error e => do
      let options ← Lean.MonadOptions.getOptions
      let desc ← (e.toMessageData options).toString
      return .error $ { error := "kernel", desc }
    | .ok env' => pure env'
  Lean.MonadEnv.modifyEnv (λ _ => env')
  return .ok {}

end Pantograph.Environment
