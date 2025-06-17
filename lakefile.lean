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
  "https://github.com/argumentcomputer/LSpec.git" @ "8a51034d049c6a229d88dd62f490778a377eec06"
lean_lib Test {
}
@[test_driver]
lean_exe test {
  root := `Test.Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}
