import Lean.Declaration

namespace Pantograph

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

end Pantograph
