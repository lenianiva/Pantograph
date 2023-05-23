import Lean

/-
Expression IO
-/


namespace Pantograph.Serial


/-- Read a theorem from the environment -/
def expr_from_const (env: Lean.Environment) (name: Lean.Name): Except String Lean.Expr :=
  match env.find? name with
  | none       => throw s!"Symbol not found: {name}"
  | some cInfo => return cInfo.type
def syntax_from_str (env: Lean.Environment) (s: String): Except String Lean.Syntax :=
  Lean.Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")

end Pantograph.Serial
