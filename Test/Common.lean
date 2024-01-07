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

open Lean

def runCoreMSeq (env: Environment) (coreM: CoreM LSpec.TestSeq): IO LSpec.TestSeq := do
  let coreContext: Core.Context := {
    currNamespace := Name.str .anonymous "Aniva"
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph/Test>",
    fileMap := { source := "", positions := #[0], lines := #[1] }
  }
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

end Pantograph
