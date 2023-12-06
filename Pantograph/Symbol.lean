import Lean

namespace Pantograph

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

end Pantograph
