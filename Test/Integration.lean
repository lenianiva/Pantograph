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
  let coreContext: Lean.Core.Context ← createCoreContext #[]
  let commands: MainM LSpec.TestSeq :=
    steps.foldlM (λ suite step => do
      let result ← step
      return suite ++ result) LSpec.TestSeq.done
  try
    let coreM := commands.run context |>.run' {}
    return Prod.fst $ (← coreM.toIO coreContext { env := env })
  catch ex =>
    return LSpec.check s!"Uncaught IO exception: {ex.toString}" false

def test_elab : IO LSpec.TestSeq :=
  subroutine_runner [
    subroutine_step "expr.echo"
      [("expr", .str "λ {α : Sort (u + 1)} => List α")]
     (Lean.toJson ({
       type := { pp? := .some "{α : Type u} → Type u" },
       expr := { pp? := .some "fun {α} => List α" }
     }: Protocol.ExprEchoResult)),
  ]

def test_option_modify : IO LSpec.TestSeq :=
  let pp? := Option.some "∀ (n : Nat), n + 1 = n.succ"
  let sexp? := Option.some "(:forall n (:c Nat) ((:c Eq) (:c Nat) ((:c HAdd.hAdd) (:c Nat) (:c Nat) (:c Nat) ((:c instHAdd) (:c Nat) (:c instAddNat)) 0 ((:c OfNat.ofNat) (:c Nat) (:lit 1) ((:c instOfNatNat) (:lit 1)))) ((:c Nat.succ) 0)))"
  let module? := Option.some "Init.Data.Nat.Basic"
  let options: Protocol.Options := {}
  subroutine_runner [
    subroutine_step "env.inspect"
      [("name", .str "Nat.add_one")]
     (Lean.toJson ({
       type := { pp? }, module? }:
      Protocol.EnvInspectResult)),
    subroutine_step "options.set"
      [("printExprAST", .bool true)]
     (Lean.toJson ({ }:
      Protocol.OptionsSetResult)),
    subroutine_step "env.inspect"
      [("name", .str "Nat.add_one")]
     (Lean.toJson ({
       type := { pp?, sexp? }, module? }:
      Protocol.EnvInspectResult)),
    subroutine_step "options.print"
      []
     (Lean.toJson ({ options with printExprAST := true }:
      Protocol.Options))
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
  let goal1: Protocol.Goal := {
    name := "_uniq.11",
    target := { pp? := .some "∀ (q : Prop), x ∨ q → q ∨ x" },
    vars := #[{ name := "_uniq.10", userName := "x", isInaccessible? := .some false, type? := .some { pp? := .some "Prop" }}],
  }
  let goal2: Protocol.Goal := {
    name := "_uniq.14",
    target := { pp? := .some "x ∨ y → y ∨ x" },
    vars := #[
      { name := "_uniq.10", userName := "x", isInaccessible? := .some false, type? := .some { pp? := .some "Prop" }},
      { name := "_uniq.13", userName := "y", isInaccessible? := .some false, type? := .some { pp? := .some "Prop" }}
    ],
  }
  subroutine_runner [
    subroutine_step "goal.start"
      [("expr", .str "∀ (p q: Prop), p ∨ q → q ∨ p")]
     (Lean.toJson ({stateId := 0, root := "_uniq.9"}:
      Protocol.GoalStartResult)),
    subroutine_step "goal.tactic"
      [("stateId", .num 0), ("goalId", .num 0), ("tactic", .str "intro x")]
     (Lean.toJson ({
       nextStateId? := .some 1,
       goals? := #[goal1],
     }:
      Protocol.GoalTacticResult)),
    subroutine_step "goal.print"
      [("stateId", .num 1)]
     (Lean.toJson ({
       parent? := .some { pp? := .some "fun x => ?m.12 x" },
     }:
      Protocol.GoalPrintResult)),
    subroutine_step "goal.tactic"
      [("stateId", .num 1), ("goalId", .num 0), ("tactic", .str "intro y")]
     (Lean.toJson ({
       nextStateId? := .some 2,
       goals? := #[goal2],
     }:
      Protocol.GoalTacticResult))
  ]

def test_env_add_inspect : IO LSpec.TestSeq :=
  let name1 := "Pantograph.mystery"
  let name2 := "Pantograph.mystery2"
  subroutine_runner [
    subroutine_step "env.add"
      [
        ("name", .str name1),
        ("type", .str "Prop → Prop → Prop"),
        ("value", .str "λ (a b: Prop) => Or a b"),
        ("isTheorem", .bool false)
      ]
     (Lean.toJson ({}: Protocol.EnvAddResult)),
    subroutine_step "env.inspect"
      [("name", .str name1)]
     (Lean.toJson ({
       value? := .some { pp? := .some "fun a b => a ∨ b" },
       type := { pp? := .some "Prop → Prop → Prop" },
     }:
      Protocol.EnvInspectResult)),
    subroutine_step "env.add"
      [
        ("name", .str name2),
        ("type", .str "Nat → Int"),
        ("value", .str "λ (a: Nat) => a + 1"),
        ("isTheorem", .bool false)
      ]
     (Lean.toJson ({}: Protocol.EnvAddResult)),
    subroutine_step "env.inspect"
      [("name", .str name2)]
     (Lean.toJson ({
       value? := .some { pp? := .some "fun a => ↑a + 1" },
       type := { pp? := .some "Nat → Int" },
     }:
      Protocol.EnvInspectResult))
  ]

def suite: List (String × IO LSpec.TestSeq) :=
  [
    ("Elab", test_elab),
    ("Option modify", test_option_modify),
    ("Malformed command", test_malformed_command),
    ("Tactic", test_tactic),
    ("env.add env.inspect", test_env_add_inspect),
  ]


end Pantograph.Test.Integration
