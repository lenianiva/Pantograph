import Pantograph.Goal
import Pantograph.Library
import Pantograph.Protocol
import Pantograph.Condensed
import Lean
import LSpec

open Lean

namespace Pantograph

deriving instance Repr for Expr
-- Use strict equality check for expressions
instance : BEq Expr := ⟨Expr.equal⟩

def uniq (n: Nat): Name := .num (.str .anonymous "_uniq") n

-- Auxiliary functions
namespace Protocol
def Goal.devolatilizeVars (goal: Goal): Goal :=
  {
    goal with
    vars := goal.vars.map removeInternalAux,

  }
  where removeInternalAux (v: Variable): Variable :=
    {
      v with
      name := ""
    }
/-- Set internal names to "" -/
def Goal.devolatilize (goal: Goal): Goal :=
  {
    goal.devolatilizeVars with
    name := "",
  }

deriving instance DecidableEq, Repr for Name
deriving instance DecidableEq, Repr for Expression
deriving instance DecidableEq, Repr for Variable
deriving instance DecidableEq, Repr for Goal
deriving instance DecidableEq, Repr for ExprEchoResult
deriving instance DecidableEq, Repr for InteractionError
deriving instance DecidableEq, Repr for Option
end Protocol

namespace Condensed

deriving instance BEq, Repr for LocalDecl
deriving instance BEq, Repr for Goal

protected def LocalDecl.devolatilize (decl: LocalDecl): LocalDecl :=
  {
    decl with fvarId := { name := .anonymous }
  }
protected def Goal.devolatilize (goal: Goal): Goal :=
  {
    goal with
    mvarId := { name := .anonymous },
    context := goal.context.map LocalDecl.devolatilize
  }

end Condensed

def TacticResult.toString : TacticResult → String
  | .success state => s!".success ({state.goals.length} goals)"
  | .failure messages =>
    let messages := "\n".intercalate messages.toList
    s!".failure {messages}"
  | .parseError error => s!".parseError {error}"
  | .indexError index => s!".indexError {index}"
  | .invalidAction error => s!".invalidAction {error}"

namespace Test

def expectationFailure (desc: String) (error: String): LSpec.TestSeq := LSpec.test desc (LSpec.ExpectationFailure "ok _" error)
def assertUnreachable (message: String): LSpec.TestSeq := LSpec.check message false

def parseFailure (error: String) := expectationFailure "parse" error
def elabFailure (error: String) := expectationFailure "elab" error

def runCoreMSeq (env: Environment) (coreM: CoreM LSpec.TestSeq) (options: Array String := #[]): IO LSpec.TestSeq := do
  let coreContext: Core.Context ← createCoreContext options
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok a            => return a
def runMetaMSeq (env: Environment) (metaM: MetaM LSpec.TestSeq): IO LSpec.TestSeq :=
  runCoreMSeq env metaM.run'
def runTermElabMInMeta { α } (termElabM: Lean.Elab.TermElabM α): Lean.MetaM α :=
  termElabM.run' (ctx := Condensed.elabContext)
def runTermElabMSeq (env: Environment) (termElabM: Elab.TermElabM LSpec.TestSeq): IO LSpec.TestSeq :=
  runMetaMSeq env $ termElabM.run' (ctx := Condensed.elabContext)

def exprToStr (e: Expr): Lean.MetaM String := toString <$> Meta.ppExpr e

def parseSentence (s: String): Elab.TermElabM Expr := do
  let recursor ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := s)
    (fileName := filename) with
    | .ok syn => pure syn
    | .error error => throwError "Failed to parse: {error}"
  Elab.Term.elabTerm (stx := recursor) .none

def runTacticOnMVar (tacticM: Elab.Tactic.TacticM Unit) (goal: MVarId): Elab.TermElabM (List MVarId) := do
    let (_, newGoals) ← tacticM { elaborator := .anonymous } |>.run { goals := [goal] }
    return newGoals.goals
def mvarUserNameAndType (mvarId: MVarId): MetaM (Name × String) := do
  let name := (← mvarId.getDecl).userName
  let t ← exprToStr (← mvarId.getType)
  return (name, t)


-- Monadic testing

abbrev TestT := StateT LSpec.TestSeq

def addTest [Monad m] (test: LSpec.TestSeq): TestT m Unit := do
  set $ (← get) ++ test

def runTest [Monad m] (t: TestT m Unit): m LSpec.TestSeq :=
  Prod.snd <$> t.run LSpec.TestSeq.done

def runTestTermElabM (env: Environment) (t: TestT Elab.TermElabM Unit):
  IO LSpec.TestSeq :=
  runTermElabMSeq env $ runTest t

def cdeclOf (userName: Name) (type: Expr): Condensed.LocalDecl :=
  { userName, type }

def buildGoal (nameType: List (String × String)) (target: String) (userName?: Option String := .none):
    Protocol.Goal :=
  {
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
    })).toArray
  }

end Test

end Pantograph
