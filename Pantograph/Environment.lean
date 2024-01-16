import Pantograph.Protocol
import Pantograph.Serial
import Lean

open Lean
open Pantograph

namespace Pantograph.Environment

abbrev CR α := Except Protocol.InteractionError α

def is_symbol_unsafe_or_internal (n: Lean.Name) (info: Lean.ConstantInfo): Bool :=
  isLeanSymbol n ∨ (Lean.privateToUserName? n |>.map isLeanSymbol |>.getD false) ∨ info.isUnsafe
  where
  isLeanSymbol (name: Lean.Name): Bool := match name.getRoot with
    | .str _ name => name == "Lean"
    | _ => true

def to_compact_symbol_name (n: Lean.Name) (info: Lean.ConstantInfo): String :=
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

def to_filtered_symbol (n: Lean.Name) (info: Lean.ConstantInfo): Option String :=
  if is_symbol_unsafe_or_internal n info
  then Option.none
  else Option.some <| to_compact_symbol_name n info
def catalog (_: Protocol.EnvCatalog): CoreM (CR Protocol.EnvCatalogResult) := do
  let env ← Lean.MonadEnv.getEnv
  let names := env.constants.fold (init := #[]) (λ acc name info =>
    match to_filtered_symbol name info with
    | .some x => acc.push x
    | .none => acc)
  return .ok { symbols := names }
def inspect (args: Protocol.EnvInspect) (options: Protocol.Options): CoreM (CR Protocol.EnvInspectResult) := do
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
  -- Information common to all symbols
  let core := {
    type := ← (serialize_expression options info.type).run',
    value? := ← value?.mapM (λ v => serialize_expression options v |>.run'),
    publicName? := Lean.privateToUserName? name |>.map (·.toString),
    -- BUG: Warning: getUsedConstants here will not include projections. This is a known bug.
    typeDependency? := if args.dependency?.getD false then .some <| info.type.getUsedConstants.map (λ n => name_to_ast n) else .none,
    valueDependency? := if args.dependency?.getD false then info.value?.map (·.getUsedConstants.map (λ n => name_to_ast n)) else .none,
    module? := module?
  }
  let result := match info with
    | .inductInfo induct => { core with inductInfo? := .some {
          numParams := induct.numParams,
          numIndices := induct.numIndices,
          all := induct.all.map (·.toString),
          ctors := induct.ctors.map (·.toString),
          isRec := induct.isRec,
          isUnsafe := induct.isUnsafe,
          isReflexive := induct.isReflexive,
          isNested := induct.isNested,
      } }
    | _ => core
  return .ok result
def addDecl (args: Protocol.EnvAdd): CoreM (CR Protocol.EnvAddResult) := do
  let env ← Lean.MonadEnv.getEnv
  let tvM: Elab.TermElabM (Except String (Expr × Expr)) := do
    let type ← match syntax_from_str env args.type with
      | .ok syn => do
        match ← syntax_to_expr syn with
        | .error e => return .error e
        | .ok expr => pure expr
      | .error e => return .error e
    let value ← match syntax_from_str env args.value with
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
