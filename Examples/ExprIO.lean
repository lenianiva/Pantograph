import Lean

def strToName (s: String): Lean.Name :=
  (s.splitOn ".").foldl Lean.Name.str Lean.Name.anonymous

unsafe def main (args: List String): IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let imports := ["Init"]
  let env: Lean.Environment ← Lean.importModules
    (imports := imports.map (λ str => { module := strToName str, runtimeOnly := false }))
    (opts := {})
    (trustLevel := 1)

  let expr := args.head?.getD "a + b"

  match Lean.Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := expr)
    (fileName := "<stdin>") with
  | Except.error error => IO.println s!"{error}"
  | Except.ok (syn: Lean.Syntax) =>
    let reprint := Lean.Syntax.reprint syn |>.get!
    IO.println reprint
