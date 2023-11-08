import Pantograph.Protocol
import Pantograph.Goal
import LSpec

namespace Pantograph

namespace Protocol
/-- Set internal names to "" -/
def Goal.devolatilize (goal: Goal): Goal :=
  {
    goal with
    name := "",
    vars := goal.vars.map removeInternalAux,
  }
  where removeInternalAux (v: Variable): Variable :=
    {
      v with
      name := ""
    }
deriving instance DecidableEq, Repr for Expression
deriving instance DecidableEq, Repr for Variable
deriving instance DecidableEq, Repr for Goal
end Protocol

def TacticResult.toString : TacticResult → String
  | .success state => s!".success ({state.goals.length} goals)"
  | .failure messages =>
    let messages := "\n".intercalate messages.toList
    s!".failure {messages}"
  | .parseError error => s!".parseError {error}"
  | .indexError index => s!".indexError {index}"

def assertUnreachable (message: String): LSpec.TestSeq := LSpec.check message false

end Pantograph
