

def main (args : List String) : IO Unit := do
  let command :: args := args | IO.eprintln "Must supply a command"
  IO.println s!"{command}"
