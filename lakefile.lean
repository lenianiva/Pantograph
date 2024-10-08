import Lake
open Lake DSL

package pantograph

lean_lib Pantograph {
  roots := #[`Pantograph]
  defaultFacets := #[LeanLib.sharedFacet]
}

lean_lib Repl {
}
@[default_target]
lean_exe repl {
  root := `Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}

require LSpec from git
  "https://github.com/lenianiva/LSpec.git" @ "c492cecd0bc473e2f9c8b94d545d02cc0056034f"
lean_lib Test {
}
@[test_driver]
lean_exe test {
  root := `Test.Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}
