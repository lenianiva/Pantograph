/-
 - Manages the visibility status of symbols
 -/
import Lean.Declaration

namespace Pantograph

def str_to_name (s: String): Lean.Name :=
  (s.splitOn ".").foldl Lean.Name.str Lean.Name.anonymous

def is_symbol_unsafe_or_internal (n: Lean.Name) (info: Lean.ConstantInfo): Bool :=
  let nameDeduce: Bool := match n.getRoot with
  | .str _ name => name.startsWith "_" ∨ name == "Lean"
  | _ => true
  let stemDeduce: Bool := match n with
  | .anonymous => true
  | .str _ name => name.startsWith "_"
  | .num _ _ => true
  nameDeduce ∨ stemDeduce ∨ info.isUnsafe

def to_compact_symbol_name (n: Lean.Name) (info: Lean.ConstantInfo): String :=
  let pref := match info with
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "defn"
  | .thmInfo    _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo   _ => "ctor"
  | .recInfo    _ => "rec"
  s!"{pref}|{toString n}"

def to_filtered_symbol (n: Lean.Name) (info: Lean.ConstantInfo): Option String :=
  if is_symbol_unsafe_or_internal n info
  then Option.none
  else Option.some <| to_compact_symbol_name n info

end Pantograph
