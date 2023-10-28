/- Integration test for the REPL
 -/
import LSpec
import Pantograph
namespace Pantograph.Test.Integration
open Pantograph

def subroutine_named_step (name cmd: String) (payload: List (String × Lean.Json))
    (expected: Lean.Json): MainM LSpec.TestSeq := do
  let result ← execute { cmd := cmd, payload := Lean.Json.mkObj payload }
  return LSpec.test name (toString result = toString expected)
def subroutine_step (cmd: String) (payload: List (String × Lean.Json))
    (expected: Lean.Json): MainM LSpec.TestSeq := subroutine_named_step cmd cmd payload expected

def subroutine_runner (steps: List (MainM LSpec.TestSeq)): IO LSpec.TestSeq := do
  -- Setup the environment for execution
  let env ← Lean.importModules
    (imports := #[{module := Lean.Name.str .anonymous "Init", runtimeOnly := false }])
    (opts := {})
    (trustLevel := 1)
  let context: Context := {
    imports := ["Init"]
  }
  let coreContext: Lean.Core.Context := {
    currNamespace := Lean.Name.str .anonymous "Aniva"
    openDecls := [],
    fileName := "<Test>",
    fileMap := { source := "", positions := #[0], lines := #[1] },
    options := Lean.Options.empty
  }
  let commands: MainM LSpec.TestSeq :=
    steps.foldlM (λ suite step => do
      let result ← step
      return suite ++ result) LSpec.TestSeq.done
  try
    let termElabM := commands.run context |>.run' {}
    let metaM := termElabM.run' (ctx := {
      declName? := some "_pantograph",
      errToSorry := false
    })
    let coreM := metaM.run'
    return Prod.fst $ (← coreM.toIO coreContext { env := env })
  catch ex =>
    return LSpec.check s!"Uncaught IO exception: {ex.toString}" false

def test_option_modify : IO LSpec.TestSeq :=
  let pp? := Option.some "∀ (n : Nat), n + 1 = Nat.succ n"
  let sexp? := Option.some "(:forall n (:c Nat) ((((:c Eq) (:c Nat)) (((((((:c HAdd.hAdd) (:c Nat)) (:c Nat)) (:c Nat)) (((:c instHAdd) (:c Nat)) (:c instAddNat))) 0) ((((:c OfNat.ofNat) (:c Nat)) (:lit 1)) ((:c instOfNatNat) (:lit 1))))) ((:c Nat.succ) 0)))"
  let module? := Option.some "Init.Data.Nat.Basic"
  let options: Protocol.Options := {}
  subroutine_runner [
    subroutine_step "lib.inspect"
      [("name", .str "Nat.add_one")]
     (Lean.toJson ({
       type := { pp? }, module? }:
      Protocol.LibInspectResult)),
    subroutine_step "options.set"
      [("printExprAST", .bool true)]
     (Lean.toJson ({ }:
      Protocol.OptionsSetResult)),
    subroutine_step "lib.inspect"
      [("name", .str "Nat.add_one")]
     (Lean.toJson ({
       type := { pp?, sexp? }, module? }:
      Protocol.LibInspectResult)),
    subroutine_step "options.print"
      []
     (Lean.toJson ({ options with printExprAST := true }:
      Protocol.OptionsPrintResult))
  ]
def test_malformed_command : IO LSpec.TestSeq :=
  let invalid := "invalid"
  subroutine_runner [
    subroutine_named_step "Invalid command" invalid
      [("name", .str "Nat.add_one")]
     (Lean.toJson ({
       error := "command", desc := s!"Unknown command {invalid}"}:
      Protocol.InteractionError)),
    subroutine_named_step "JSON Deserialization" "expr.echo"
      [(invalid, .str "Random garbage data")]
     (Lean.toJson ({
       error := "command", desc := s!"Unable to parse json: Pantograph.Protocol.ExprEcho.expr: String expected"}:
      Protocol.InteractionError))
  ]
def test_tactic : IO LSpec.TestSeq :=
  let goal: Protocol.Goal := {
    target := { pp? := .some "∀ (q : Prop), x ∨ q → q ∨ x" },
    vars := #[{ name := "_uniq 9", userName := "x", isInaccessible? := .some false, type? := .some { pp? := .some "Prop" }}],
  }
  subroutine_runner [
    subroutine_step "goal.start"
      [("expr", .str "∀ (p q: Prop), p ∨ q → q ∨ p")]
     (Lean.toJson ({stateId := 0}:
      Protocol.GoalStartResult)),
    subroutine_step "goal.tactic"
      [("stateId", .num 0), ("goalId", .num 0), ("tactic", .str "intro x")]
     (Lean.toJson ({
       nextStateId? := .some 1,
       goals? := #[goal],
     }:
      Protocol.GoalTacticResult))
  ]

def suite: IO LSpec.TestSeq := do

  return LSpec.group "Integration" $
    (LSpec.group "Option modify" (← test_option_modify)) ++
    (LSpec.group "Malformed command" (← test_malformed_command)) ++
    (LSpec.group "Tactic" (← test_tactic))


end Pantograph.Test.Integration
