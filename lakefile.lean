import Lake
open Lake DSL

package pantograph

lean_lib Pantograph {
  defaultFacets := #[LeanLib.sharedFacet]
}

@[default_target]
lean_exe pantograph {
  root := `Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}

require LSpec from git
  "https://github.com/lurk-lab/LSpec.git" @ "3388be5a1d1390594a74ec469fd54a5d84ff6114"
lean_lib Test {
}
@[test_driver]
lean_exe test {
  root := `Test.Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}
