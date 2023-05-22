import Lake
open Lake DSL

package pantograph

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @  "8e5a00a8afc8913c0584cb85f37951995275fd87"

lean_lib Pantograph {
  -- add library configuration options here
}

@[default_target]
lean_exe pantograph {
  root := `Main
  -- Somehow solves the native symbol not found problem
  supportInterpreter := true
}

require LSpec from git
  "https://github.com/lurk-lab/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"
lean_exe test {
  root := `Test.Main
  -- Somehow solves the native symbol not found problem
  supportInterpreter := true

}

lean_exe examples_proof {
  root := `Examples.Proof
  -- Somehow solves the native symbol not found problem
  supportInterpreter := true
}
