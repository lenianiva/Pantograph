import LSpec
import Pantograph.Symbols

namespace Pantograph.Test

def test_serial: IO LSpec.TestSeq := do
  return LSpec.group "Serialisation" $
    LSpec.test "Symbol parsing" (Lean.Name.str (.str (.str .anonymous "Lean") "Meta") "run" = Pantograph.str_to_name "Lean.Meta.run")

end Pantograph.Test
