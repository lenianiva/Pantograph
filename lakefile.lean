import Lake
open Lake DSL

package pantograph

lean_lib Pantograph {
}

@[default_target]
lean_exe pantograph {
  root := `Main
  -- Somehow solves the native symbol not found problem
  supportInterpreter := true
}

require LSpec from git
  "https://github.com/lurk-lab/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"
lean_lib Test {
}
lean_exe test {
  root := `Test.Main
  -- Somehow solves the native symbol not found problem
  supportInterpreter := true
}
