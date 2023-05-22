import LSpec
import Pantograph.Symbols

open Pantograph

def main := do
  LSpec.lspecIO $
    LSpec.test "Symbol parsing" (Lean.Name.str (.str (.str .anonymous "Lean") "Meta") "run" = Pantograph.str_to_name "Lean.Meta.run")
