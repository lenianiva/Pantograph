/-
 - Manages the visibility status of symbols
 -/
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

end Pantograph
