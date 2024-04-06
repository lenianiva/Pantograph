import Pantograph.Goal
import Pantograph.Library
import Pantograph.Protocol
import Lean
import LSpec

open Lean

namespace Pantograph

-- Auxiliary functions
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
deriving instance DecidableEq, Repr for ExprEchoResult
deriving instance DecidableEq, Repr for InteractionError
deriving instance DecidableEq, Repr for Option
end Protocol

def TacticResult.toString : TacticResult → String
  | .success state => s!".success ({state.goals.length} goals)"
  | .failure messages =>
    let messages := "\n".intercalate messages.toList
    s!".failure {messages}"
  | .parseError error => s!".parseError {error}"
  | .indexError index => s!".indexError {index}"

namespace Test

def expectationFailure (desc: String) (error: String): LSpec.TestSeq := LSpec.test desc (LSpec.ExpectationFailure "ok _" error)
def assertUnreachable (message: String): LSpec.TestSeq := LSpec.check message false

def runCoreMSeq (env: Environment) (coreM: CoreM LSpec.TestSeq) (options: Array String := #[]): IO LSpec.TestSeq := do
  let coreContext: Core.Context ← createCoreContext options
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok a            => return a
def runMetaMSeq (env: Environment) (metaM: MetaM LSpec.TestSeq): IO LSpec.TestSeq :=
  runCoreMSeq env metaM.run'
def runTermElabMInMeta { α } (termElabM: Lean.Elab.TermElabM α): Lean.MetaM α :=
  termElabM.run' (ctx := {
    declName? := .none,
    errToSorry := false,
  })

def defaultTermElabMContext: Lean.Elab.Term.Context := {
    declName? := some "_pantograph".toName,
    errToSorry := false
  }
end Test

end Pantograph
