/- Integration test for the REPL
 -/
import LSpec
import Pantograph
import Repl
import Test.Common

namespace Pantograph.Test.Integration
open Pantograph.Repl

deriving instance Lean.ToJson for Protocol.EnvInspect
deriving instance Lean.ToJson for Protocol.EnvAdd
deriving instance Lean.ToJson for Protocol.ExprEcho
deriving instance Lean.ToJson for Protocol.OptionsSet
deriving instance Lean.ToJson for Protocol.OptionsPrint
deriving instance Lean.ToJson for Protocol.GoalStart
deriving instance Lean.ToJson for Protocol.GoalPrint
deriving instance Lean.ToJson for Protocol.GoalTactic
deriving instance Lean.ToJson for Protocol.FrontendProcess

def step { α β } [Lean.ToJson α] [Lean.ToJson β] (cmd: String) (payload: α)
    (expected: β) (name? : Option String := .none): MainM LSpec.TestSeq := do
  let payload := Lean.toJson payload
  let name := name?.getD s!"{cmd} {payload.compress}"
  let result ← Repl.execute { cmd, payload }
  return LSpec.test name (result.pretty = (Lean.toJson expected).pretty)

abbrev Test := List (MainM LSpec.TestSeq)

def test_expr_echo : Test :=
  [
    step "expr.echo"
     ({ expr := "λ {α : Sort (u + 1)} => List α", levels? := .some #["u"]}: Protocol.ExprEcho)
     ({
       type := { pp? := .some "{α : Type u} → Type u" },
       expr := { pp? := .some "fun {α} => List α" }
     }: Protocol.ExprEchoResult),
  ]

def test_option_modify : Test :=
  let pp? := Option.some "∀ (n : Nat), n + 1 = n.succ"
  let sexp? := Option.some "(:forall n (:c Nat) ((:c Eq) (:c Nat) ((:c HAdd.hAdd) (:c Nat) (:c Nat) (:c Nat) ((:c instHAdd) (:c Nat) (:c instAddNat)) 0 ((:c OfNat.ofNat) (:c Nat) (:lit 1) ((:c instOfNatNat) (:lit 1)))) ((:c Nat.succ) 0)))"
  let module? := Option.some "Init.Data.Nat.Basic"
  let options: Protocol.Options := {}
  [
    step "env.inspect" ({ name := "Nat.add_one" } : Protocol.EnvInspect)
     ({ type := { pp? }, module? }: Protocol.EnvInspectResult),
    step "options.set" ({ printExprAST? := .some true } : Protocol.OptionsSet)
     ({ }: Protocol.OptionsSetResult),
    step "env.inspect" ({ name := "Nat.add_one" } : Protocol.EnvInspect)
     ({ type := { pp?, sexp? }, module? }: Protocol.EnvInspectResult),
    step "options.print" ({} : Protocol.OptionsPrint)
     ({ options with printExprAST := true }: Protocol.Options),
  ]
def test_malformed_command : Test :=
  let invalid := "invalid"
  [
    step invalid ({ name := "Nat.add_one" }: Protocol.EnvInspect)
     ({ error := "command", desc := s!"Unknown command {invalid}" }: Protocol.InteractionError)
     (name? := .some "Invalid Command"),
    step "expr.echo" (Lean.Json.mkObj [(invalid, .str "Random garbage data")])
     ({ error := "command", desc := s!"Unable to parse json: Pantograph.Protocol.ExprEcho.expr: String expected" }:
      Protocol.InteractionError)
    (name? := .some "JSON Deserialization")
  ]
def test_tactic : Test :=
  let varX := { name := "_uniq.10", userName := "x", type? := .some { pp? := .some "Prop" }}
  let goal1: Protocol.Goal := {
    name := "_uniq.11",
    target := { pp? := .some "∀ (q : Prop), x ∨ q → q ∨ x" },
    vars := #[varX],
  }
  let goal2: Protocol.Goal := {
    name := "_uniq.14",
    target := { pp? := .some "x ∨ y → y ∨ x" },
    vars := #[
      varX,
      { name := "_uniq.13", userName := "y", type? := .some { pp? := .some "Prop" }}
    ],
  }
  [
    step "goal.start" ({ expr := "∀ (p q: Prop), p ∨ q → q ∨ p" }: Protocol.GoalStart)
     ({ stateId := 0, root := "_uniq.9" }: Protocol.GoalStartResult),
    step "goal.tactic" ({ stateId := 0, tactic? := .some "intro x" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 1, goals? := #[goal1], }: Protocol.GoalTacticResult),
    step "goal.print" ({ stateId := 1, parentExpr? := .some true, rootExpr? := .some true }: Protocol.GoalPrint)
     ({ parent? := .some { pp? := .some "fun x => ?m.11" }, }: Protocol.GoalPrintResult),
    step "goal.tactic" ({ stateId := 1, tactic? := .some "intro y" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 2, goals? := #[goal2], }: Protocol.GoalTacticResult),
    step "goal.tactic" ({ stateId := 1, tactic? := .some "apply Nat.le_of_succ_le" }: Protocol.GoalTactic)
     ({ tacticErrors? := .some #["tactic 'apply' failed, failed to unify\n  ∀ {m : Nat}, Nat.succ ?n ≤ m → ?n ≤ m\nwith\n  ∀ (q : Prop), x ∨ q → q ∨ x\nx : Prop\n⊢ ∀ (q : Prop), x ∨ q → q ∨ x"] }:
      Protocol.GoalTacticResult)
  ]
example : (1 : Nat) + (2 * 3) = 1 + (4 - 3) + (6 - 4) + 3 := by
  simp
def test_tactic_timeout : Test :=
  [
    step "goal.start" ({ expr := "(1 : Nat) + (2 * 3) = 1 + (4 - 3) + (6 - 4) + 3" }: Protocol.GoalStart)
     ({ stateId := 0, root := "_uniq.319" }: Protocol.GoalStartResult),
    -- timeout of 10 milliseconds
    step "options.set" ({ timeout? := .some 10 } : Protocol.OptionsSet)
     ({ }: Protocol.OptionsSetResult),
    step "goal.tactic" ({ stateId := 0, expr? := .some "by\nsleep 1000; simp" }: Protocol.GoalTactic)
     ({ error := "internal", desc := "interrupt" }: Protocol.InteractionError),
    -- ensure graceful recovery
    step "options.set" ({ timeout? := .some 0 } : Protocol.OptionsSet)
     ({ }: Protocol.OptionsSetResult),
    step "goal.tactic" ({ stateId := 0, tactic? := .some "simp" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 1, goals? := .some #[], }: Protocol.GoalTacticResult),
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
    name := "_uniq.61",
    userName? := .some "inl",
    target := { pp? := .some "q ∨ p" },
    vars := varsPQ ++ #[
      { name := "_uniq.49", userName := "h✝", type? := .some { pp? := .some "p" }, isInaccessible := true}
    ],
  }
  let goal2r: Protocol.Goal := {
    name := "_uniq.74",
    userName? := .some "inr",
    target := { pp? := .some "q ∨ p" },
    vars := varsPQ ++ #[
      { name := "_uniq.62", userName := "h✝", type? := .some { pp? := .some "q" }, isInaccessible := true}
    ],
  }
  let goal3l: Protocol.Goal := {
    name := "_uniq.80",
    userName? := .some "inl.h",
    target := { pp? := .some "p" },
    vars := varsPQ ++ #[
      { name := "_uniq.49", userName := "h✝", type? := .some { pp? := .some "p" }, isInaccessible := true}
    ],
  }
  [
    step "options.set" ({automaticMode? := .some automatic}: Protocol.OptionsSet)
     ({}: Protocol.OptionsSetResult),
    step "goal.start" ({ expr := "∀ (p q: Prop), p ∨ q → q ∨ p"} : Protocol.GoalStart)
     ({ stateId := 0, root := "_uniq.9" }: Protocol.GoalStartResult),
    step "goal.tactic" ({ stateId := 0, tactic? := .some "intro p q h" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 1, goals? := #[goal1], }: Protocol.GoalTacticResult),
    step "goal.tactic" ({ stateId := 1, tactic? := .some "cases h" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 2, goals? := #[goal2l, goal2r], }: Protocol.GoalTacticResult),
    let goals? := if automatic then #[goal3l, goal2r] else #[goal3l]
    step "goal.tactic" ({ stateId := 2, tactic? := .some "apply Or.inr" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 3, goals?, }: Protocol.GoalTacticResult),
  ]

def test_env_add_inspect : Test :=
  let name1 := "Pantograph.mystery"
  let name2 := "Pantograph.mystery2"
  let name3 := "Pantograph.mystery3"
  [
    step "env.add"
      ({
        name := name1,
        value := "λ (a b: Prop) => Or a b",
        isTheorem := false
      }: Protocol.EnvAdd)
     ({}: Protocol.EnvAddResult),
    step "env.inspect" ({name := name1, value? := .some true} : Protocol.EnvInspect)
     ({
       value? := .some { pp? := .some "fun a b => a ∨ b" },
       type := { pp? := .some "Prop → Prop → Prop" },
     }:
      Protocol.EnvInspectResult),
    step "env.add"
      ({
        name := name2,
        type? := "Nat → Int",
        value := "λ (a: Nat) => a + 1",
        isTheorem := false
      }: Protocol.EnvAdd)
     ({}: Protocol.EnvAddResult),
    step "env.inspect" ({name := name2, value? := .some true} : Protocol.EnvInspect)
     ({
       value? := .some { pp? := .some "fun a => ↑a + 1" },
       type := { pp? := .some "Nat → Int" },
     }:
      Protocol.EnvInspectResult),
    step "env.add"
      ({
        name := name3,
        levels? := .some #["u"]
        type? := "(α : Type u) → α → (α × α)",
        value := "λ (α : Type u) (x : α) => (x, x)",
        isTheorem := false
      }: Protocol.EnvAdd)
     ({}: Protocol.EnvAddResult),
    step "env.inspect" ({name := name3} : Protocol.EnvInspect)
     ({
       type := { pp? := .some "(α : Type u) → α → α × α" },
     }:
      Protocol.EnvInspectResult),
  ]

example : ∀ (p: Prop), p → p := by
  intro p h
  exact h

def test_frontend_process : Test :=
  let file := "example : ∀ (p q: Prop), p → p ∨ q := by\n  intro p q h\n  exact Or.inl h"
  let goal1 := "p q : Prop\nh : p\n⊢ p ∨ q"
  [
    step "frontend.process"
      ({
        file? := .some file,
        invocations := true,
      }: Protocol.FrontendProcess)
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
      ({
        file? := .some file,
        sorrys := true,
      }: Protocol.FrontendProcess)
     ({
       units := [{
         boundary := (0, solved.utf8ByteSize),
       }, {
         boundary := (solved.utf8ByteSize, solved.utf8ByteSize + withSorry.utf8ByteSize),
         goalStateId? := .some 0,
         goals? := .some #[goal1],
         goalSrcBoundaries? := .some #[(57, 62)],
         messages := #["<anonymous>:2:0: warning: declaration uses 'sorry'\n"],
       }],
     }: Protocol.FrontendProcessResult),
  ]

def test_import_open : Test :=
  let header := "import Init\nopen Nat\nuniverse u"
  let goal1: Protocol.Goal := {
    name := "_uniq.67",
    target := { pp? := .some "n + 1 = n.succ" },
    vars := #[{ name := "_uniq.66", userName := "n", type? := .some { pp? := .some "Nat" }}],
  }
  [
    step "frontend.process"
      ({
        file? := .some header,
        readHeader := true,
        inheritEnv := true,
      }: Protocol.FrontendProcess)
     ({
       units := [
         { boundary := (12, 21) },
         { boundary := (21, header.utf8ByteSize) },
       ],
     }: Protocol.FrontendProcessResult),
    step "goal.start" ({ expr := "∀ (n : Nat), n + 1 = Nat.succ n"} : Protocol.GoalStart)
     ({ stateId := 0, root := "_uniq.65" }: Protocol.GoalStartResult),
    step "goal.tactic" ({ stateId := 0, tactic? := .some "intro n" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 1, goals? := #[goal1], }: Protocol.GoalTacticResult),
    step "goal.tactic" ({ stateId := 1, tactic? := .some "apply add_one" }: Protocol.GoalTactic)
     ({ nextStateId? := .some 2, goals? := .some #[], }: Protocol.GoalTacticResult),
    step "goal.start" ({ expr := "∀ (x : Sort u), Sort (u + 1)"} : Protocol.GoalStart)
     ({ stateId := 0, root := "_uniq.65" }: Protocol.GoalStartResult),
  ]

def runTest (env: Lean.Environment) (steps: Test): IO LSpec.TestSeq := do
  -- Setup the environment for execution
  let coreContext ← createCoreContext #[]
  let mainM : MainM LSpec.TestSeq :=
    steps.foldlM (λ suite step => do return suite ++ (← step)) LSpec.TestSeq.done
  mainM.run { coreContext } |>.run' { env }

def suite (env : Lean.Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("expr.echo", test_expr_echo),
    ("options.set options.print", test_option_modify),
    ("Malformed command", test_malformed_command),
    ("Tactic", test_tactic),
    ("Tactic Timeout", test_tactic_timeout),
    ("Manual Mode", test_automatic_mode false),
    ("Automatic Mode", test_automatic_mode true),
    ("env.add env.inspect", test_env_add_inspect),
    ("frontend.process invocation", test_frontend_process),
    ("frontend.process sorry", test_frontend_process_sorry),
    ("frontend.process import", test_import_open),
  ]
  tests.map (fun (name, test) => (name, runTest env test))


end Pantograph.Test.Integration
