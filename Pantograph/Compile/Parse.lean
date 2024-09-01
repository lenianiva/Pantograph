import Lean

open Lean

namespace Pantograph.Compile

def parseTermM [Monad m] [MonadEnv m] (s: String): m (Except String Syntax) := do
  return Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")

end Pantograph.Compile
