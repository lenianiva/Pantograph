import Pantograph.Delate
import Pantograph.Elab
import Pantograph.Protocol
import Pantograph.Serial
import Lean.Environment
import Lean.Replay

open Lean
open Pantograph

namespace Pantograph.Environment

@[export pantograph_is_name_internal]
def isNameInternal (n: Name): Bool :=
  -- Returns true if the name is an implementation detail which should not be shown to the user.
  n.isAuxLemma ∨ n.hasMacroScopes

/-- Catalog all the non-internal and safe names -/
@[export pantograph_environment_catalog]
def env_catalog (env: Environment): Array Name := env.constants.fold (init := #[]) (λ acc name _ =>
  match isNameInternal name with
  | false => acc.push name
  | true => acc)

@[export pantograph_environment_module_of_name]
def module_of_name (env: Environment) (name: Name): Option Name := do
  let moduleId ← env.getModuleIdxFor? name
  if h : moduleId.toNat < env.allImportedModuleNames.size then
    return env.allImportedModuleNames.get moduleId.toNat h
  else
    .none

def toCompactSymbolName (n: Name) (info: ConstantInfo): String :=
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
def describe (_: Protocol.EnvDescribe): CoreM Protocol.EnvDescribeResult := do
  let env ← Lean.MonadEnv.getEnv
  return {
    imports := env.header.imports.map toString,
    modules := env.header.moduleNames.map (·.toString),
  }
def moduleRead (args: Protocol.EnvModuleRead): CoreM Protocol.EnvModuleReadResult := do
  let env ← Lean.MonadEnv.getEnv
  let .some i := env.header.moduleNames.findIdx? (· == args.module.toName) |
    throwError s!"Module not found {args.module}"
  let data := env.header.moduleData[i]!
  return {
    imports := data.imports.map toString,
    constNames := data.constNames.map (·.toString),
    extraConstNames := data.extraConstNames.map (·.toString),
  }
def catalog (_: Protocol.EnvCatalog): CoreM Protocol.EnvCatalogResult := do
  let env ← Lean.MonadEnv.getEnv
  let names := env.constants.fold (init := #[]) (λ acc name info =>
    match toFilteredSymbol name info with
    | .some x => acc.push x
    | .none => acc)
  return { symbols := names }
def inspect (args: Protocol.EnvInspect) (options: @&Protocol.Options): Protocol.FallibleT CoreM Protocol.EnvInspectResult := do
  let env ← Lean.MonadEnv.getEnv
  let name :=  args.name.toName
  let info? := env.find? name
  let .some info := info? | Protocol.throw $ Protocol.errorIndex s!"Symbol not found {args.name}"
  let module? := env.getModuleIdxFor? name >>=
    (λ idx => env.allImportedModuleNames.get? idx.toNat)
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
    typeDependency? := if args.dependency?.getD false
      then .some <| type.getUsedConstants.map (λ n => serializeName n)
      else .none,
    valueDependency? := if args.dependency?.getD false
      then value?.map (λ e =>
        e.getUsedConstants.filter (!isNameInternal ·) |>.map (λ n => serializeName n) )
      else .none,
    module? := module?.map (·.toString)
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
  let result ← if args.source?.getD false then
      let srcSearchPath ← initSrcSearchPath
      let sourceUri? ← module?.bindM (Server.documentUriFromModule srcSearchPath ·)
      let declRange? ← findDeclarationRanges? name
      let sourceStart? := declRange?.map (·.range.pos)
      let sourceEnd? := declRange?.map (·.range.endPos)
      .pure {
        result with
        sourceUri?,
        sourceStart?,
        sourceEnd?,
      }
    else
      .pure result
  return result
@[export pantograph_env_add_m]
def addDecl (name: String) (levels: Array String := #[]) (type: String) (value: String) (isTheorem: Bool)
    : Protocol.FallibleT CoreM Protocol.EnvAddResult := do
  let env ← Lean.MonadEnv.getEnv
  let levelParams := levels.toList.map (·.toName)
  let tvM: Elab.TermElabM (Except String (Expr × Expr)) :=
    Elab.Term.withLevelNames levelParams do do
    let type ← match parseTerm env type with
      | .ok syn => do
        match ← elabTerm syn with
        | .error e => return .error e
        | .ok expr => pure expr
      | .error e => return .error e
    let value ← match parseTerm env value with
      | .ok syn => do
        try
          let expr ← Elab.Term.elabTerm (stx := syn) (expectedType? := .some type)
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let expr ← instantiateMVars expr
          pure $ expr
        catch ex => return .error (← ex.toMessageData.toString)
      | .error e => return .error e
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    pure $ .ok (← instantiateMVars type, ← instantiateMVars value)
  let (type, value) ← match ← tvM.run' (ctx := {}) |>.run' with
    | .ok t => pure t
    | .error e => Protocol.throw $ Protocol.errorExpr e
  let decl := if isTheorem then
    Lean.Declaration.thmDecl <| Lean.mkTheoremValEx
      (name := name.toName)
      (levelParams := levelParams)
      (type := type )
      (value := value)
      (all := [])
  else
    Lean.Declaration.defnDecl <| Lean.mkDefinitionValEx
      (name := name.toName)
      (levelParams := levelParams)
      (type := type)
      (value := value)
      (hints := Lean.mkReducibilityHintsRegularEx 1)
      (safety := Lean.DefinitionSafety.safe)
      (all := [])
  Lean.addDecl decl
  return {}

end Pantograph.Environment
