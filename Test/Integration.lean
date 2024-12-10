/- Integration test for the REPL
 -/
import LSpec
import Pantograph
import Repl
import Test.Common

namespace Pantograph.Test.Integration
open Pantograph.Repl

def step { α } [Lean.ToJson α] (cmd: String) (payload: List (String × Lean.Json))
    (expected: α) (name? : Option String := .none): MainM LSpec.TestSeq := do
  let payload := Lean.Json.mkObj payload
  let name := name?.getD s!"{cmd} {payload.compress}"
  let result ← Repl.execute { cmd, payload }
  return LSpec.test name (toString result = toString (Lean.toJson expected))

abbrev Test := List (MainM LSpec.TestSeq)

def test_elab : Test :=
  [
    step "expr.echo"
      [("expr", .str "λ {α : Sort (u + 1)} => List α"), ("levels", .arr #["u"])]
     (Lean.toJson ({
       type := { pp? := .some "{α : Type u} → Type u" },
       expr := { pp? := .some "fun {α} => List α" }
     }: Protocol.ExprEchoResult)),
  ]

def test_option_modify : Test :=
  let pp? := Option.some "∀ (n : Nat), n + 1 = n.succ"
  let sexp? := Option.some "(:forall n (:c Nat) ((:c Eq) (:c Nat) ((:c HAdd.hAdd) (:c Nat) (:c Nat) (:c Nat) ((:c instHAdd) (:c Nat) (:c instAddNat)) 0 ((:c OfNat.ofNat) (:c Nat) (:lit 1) ((:c instOfNatNat) (:lit 1)))) ((:c Nat.succ) 0)))"
  let module? := Option.some "Init.Data.Nat.Basic"
  let options: Protocol.Options := {}
  [
    step "env.inspect" [("name", .str "Nat.add_one")]
     ({ type := { pp? }, module? }: Protocol.EnvInspectResult),
    step "options.set" [("printExprAST", .bool true)]
     ({ }: Protocol.OptionsSetResult),
    step "env.inspect" [("name", .str "Nat.add_one")]
     ({ type := { pp?, sexp? }, module? }: Protocol.EnvInspectResult),
    step "options.print" []
     ({ options with printExprAST := true }: Protocol.Options),
  ]
def test_malformed_command : Test :=
  let invalid := "invalid"
  [
    step invalid [("name", .str "Nat.add_one")]
     ({ error := "command", desc := s!"Unknown command {invalid}" }: Protocol.InteractionError)
     (name? := .some "Invalid Command"),
    step "expr.echo" [(invalid, .str "Random garbage data")]
     ({ error := "command", desc := s!"Unable to parse json: Pantograph.Protocol.ExprEcho.expr: String expected" }:
      Protocol.InteractionError)
    (name? := .some "JSON Deserialization")
  ]
def test_tactic : Test :=
  let goal1: Protocol.Goal := {
    name := "_uniq.11",
    target := { pp? := .some "∀ (q : Prop), x ∨ q → q ∨ x" },
    vars := #[{ name := "_uniq.10", userName := "x", type? := .some { pp? := .some "Prop" }}],
  }
  let goal2: Protocol.Goal := {
    name := "_uniq.17",
    target := { pp? := .some "x ∨ y → y ∨ x" },
    vars := #[
      { name := "_uniq.10", userName := "x", type? := .some { pp? := .some "Prop" }},
      { name := "_uniq.16", userName := "y", type? := .some { pp? := .some "Prop" }}
    ],
  }
  [
    step "goal.start" [("expr", .str "∀ (p q: Prop), p ∨ q → q ∨ p")]
     ({ stateId := 0, root := "_uniq.9" }: Protocol.GoalStartResult),
    step "goal.tactic" [("stateId", .num 0), ("goalId", .num 0), ("tactic", .str "intro x")]
     ({ nextStateId? := .some 1, goals? := #[goal1], }: Protocol.GoalTacticResult),
    step "goal.print" [("stateId", .num 1)]
     ({ parent? := .some { pp? := .some "fun x => ?m.12 x" }, }: Protocol.GoalPrintResult),
    step "goal.tactic" [("stateId", .num 1), ("goalId", .num 0), ("tactic", .str "intro y")]
     ({ nextStateId? := .some 2, goals? := #[goal2], }: Protocol.GoalTacticResult),
  ]
def test_automatic_mode (automatic: Bool): Test :=
  let varsPQ := #[
    { name := "_uniq.10", userName := "p", type? := .some { pp? := .some "Prop" }},
    { name := "_uniq.13", userName := "q", type? := .some { pp? := .some "Prop" }}
  ]
  let goal1: Protocol.Goal := {
    name := "_uniq.17",
    target := { pp? := .some "q ∨ p" },
    vars := varsPQ ++ #[
      { name := "_uniq.16", userName := "h", type? := .some { pp? := .some "p ∨ q" }}
    ],
  }
  let goal2l: Protocol.Goal := {
    name := "_uniq.59",
    userName? := .some "inl",
    target := { pp? := .some "q ∨ p" },
    vars := varsPQ ++ #[
      { name := "_uniq.47", userName := "h✝", type? := .some { pp? := .some "p" }, isInaccessible := true}
    ],
  }
  let goal2r: Protocol.Goal := {
    name := "_uniq.72",
    userName? := .some "inr",
    target := { pp? := .some "q ∨ p" },
    vars := varsPQ ++ #[
      { name := "_uniq.60", userName := "h✝", type? := .some { pp? := .some "q" }, isInaccessible := true}
    ],
  }
  let goal3l: Protocol.Goal := {
    name := "_uniq.78",
    userName? := .some "inl.h",
    target := { pp? := .some "p" },
    vars := varsPQ ++ #[
      { name := "_uniq.47", userName := "h✝", type? := .some { pp? := .some "p" }, isInaccessible := true}
    ],
  }
  [
    step "options.set" [("automaticMode", .bool automatic)]
     ({}: Protocol.OptionsSetResult),
    step "goal.start" [("expr", .str "∀ (p q: Prop), p ∨ q → q ∨ p")]
     ({ stateId := 0, root := "_uniq.9" }: Protocol.GoalStartResult),
    step "goal.tactic" [("stateId", .num 0), ("goalId", .num 0), ("tactic", .str "intro p q h")]
     ({ nextStateId? := .some 1, goals? := #[goal1], }: Protocol.GoalTacticResult),
    step "goal.tactic" [("stateId", .num 1), ("goalId", .num 0), ("tactic", .str "cases h")]
     ({ nextStateId? := .some 2, goals? := #[goal2l, goal2r], }: Protocol.GoalTacticResult),
    let goals? := if automatic then #[goal3l, goal2r] else #[goal3l]
    step "goal.tactic" [("stateId", .num 2), ("goalId", .num 0), ("tactic", .str "apply Or.inr")]
     ({ nextStateId? := .some 3, goals?, }: Protocol.GoalTacticResult),
  ]

def test_env_add_inspect : Test :=
  let name1 := "Pantograph.mystery"
  let name2 := "Pantograph.mystery2"
  [
    step "env.add"
      [
        ("name", .str name1),
        ("type", .str "Prop → Prop → Prop"),
        ("value", .str "λ (a b: Prop) => Or a b"),
        ("isTheorem", .bool false)
      ]
     ({}: Protocol.EnvAddResult),
    step "env.inspect" [("name", .str name1)]
     ({
       value? := .some { pp? := .some "fun a b => a ∨ b" },
       type := { pp? := .some "Prop → Prop → Prop" },
     }:
      Protocol.EnvInspectResult),
    step "env.add"
      [
        ("name", .str name2),
        ("type", .str "Nat → Int"),
        ("value", .str "λ (a: Nat) => a + 1"),
        ("isTheorem", .bool false)
      ]
     ({}: Protocol.EnvAddResult),
    step "env.inspect" [("name", .str name2)]
     ({
       value? := .some { pp? := .some "fun a => ↑a + 1" },
       type := { pp? := .some "Nat → Int" },
     }:
      Protocol.EnvInspectResult)
  ]

example : ∀ (p: Prop), p → p := by
  intro p h
  exact h

def test_frontend_process : Test :=
  [
    let file := "example : ∀ (p q: Prop), p → p ∨ q := by\n  intro p q h\n  exact Or.inl h"
    let goal1 := "p q : Prop\nh : p\n⊢ p ∨ q"
    step "frontend.process"
      [
        ("file", .str file),
        ("invocations", .bool true),
        ("sorrys", .bool false),
      ]
     ({
       units := [{
         boundary := (0, file.utf8ByteSize),
         invocations? := .some [
           {
             goalBefore := "⊢ ∀ (p q : Prop), p → p ∨ q",
             goalAfter := goal1,
             tactic := "intro p q h",
             usedConstants := #[],
           },
           {
             goalBefore := goal1 ,
             goalAfter := "",
             tactic := "exact Or.inl h",
             usedConstants := #["Or.inl"],
           },
         ]
       }],
    }: Protocol.FrontendProcessResult),
  ]

example : 1 + 2 = 3 := rfl
example (p: Prop): p → p := by simp

def test_frontend_process_sorry : Test :=
  let solved := "example : 1 + 2 = 3 := rfl\n"
  let withSorry := "example (p: Prop): p → p := sorry"
  [
    let file := s!"{solved}{withSorry}"
    let goal1: Protocol.Goal := {
      name := "_uniq.6",
      target := { pp? := .some "p → p" },
      vars := #[{ name := "_uniq.4", userName := "p", type? := .some { pp? := .some "Prop" }}],
    }
    step "frontend.process"
      [
        ("file", .str file),
        ("invocations", .bool false),
        ("sorrys", .bool true),
      ]
     ({
       units := [{
         boundary := (0, solved.utf8ByteSize),
       }, {
         boundary := (solved.utf8ByteSize, solved.utf8ByteSize + withSorry.utf8ByteSize),
         goalStateId? := .some 0,
         goals := #[goal1],
         goalSrcBoundaries := #[(57, 62)],
         messages := #["<anonymous>:2:0: warning: declaration uses 'sorry'\n"],
       }],
    }: Protocol.FrontendProcessResult),
  ]


def runTest (env: Lean.Environment) (steps: Test): IO LSpec.TestSeq := do
  -- Setup the environment for execution
  let context: Context := {
    imports := ["Init"]
  }
  let commands: MainM LSpec.TestSeq :=
    steps.foldlM (λ suite step => do
      let result ← step
      return suite ++ result) LSpec.TestSeq.done
  runCoreMSeq env <| commands.run context |>.run' {}


def suite (env : Lean.Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("expr.echo", test_elab),
    ("options.set options.print", test_option_modify),
    ("Malformed command", test_malformed_command),
    ("Tactic", test_tactic),
    ("Manual Mode", test_automatic_mode false),
    ("Automatic Mode", test_automatic_mode true),
    ("env.add env.inspect", test_env_add_inspect),
    ("frontend.process invocation", test_frontend_process),
    ("frontend.process sorry", test_frontend_process_sorry),
  ]
  tests.map (fun (name, test) => (name, runTest env test))


end Pantograph.Test.Integration
