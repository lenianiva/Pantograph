import Lake
open Lake DSL


package pantograph {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @  "8e5a00a8afc8913c0584cb85f37951995275fd87"

lean_lib Pantograph {
  -- add library configuration options here
}

@[default_target]
lean_exe pantograph {
  root := `Main
  supportInterpreter := true
}
