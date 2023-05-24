# Pantograph

An interaction system for Lean 4.

## Installation

Install `elan` and `lean4`. Then, execute
``` sh
lake build
```
In order to use `mathlib`, its binary must also be built

``` sh
lake build Qq
lake build aesop
lake build std
lake build mathlib
```

## Usage

The binary must be run inside a `lake env` environment. i.e. `lake env
build/bin/pantograph OPTIONS|MODULES`. The REPL loop accepts commands as
single-line JSON inputs and outputs either an `Error:` (indicating malformed
command) or a json return value indicating the result of a command execution.
The command can be passed in one of two formats
```
command { ... }
{ "cmd": command, "payload": ... }
```
The list of available commands can be found in `Pantograph/Commands.lean`. An
empty command aborts the REPL.

The `Pantograph` executable must be run with a list of modules to import. It can
also accept options of the form `--key=value` e.g. `--pp.raw=true`.

Example: (~5k symbols)
```
$ lake env build/bin/Pantograph "Init"
catalog
inspect {"name": "Nat.le_add_left"}
```
Example with `mathlib` (~90k symbols)
```
$ lake env build/bin/Pantograph "Mathlib.Analysis.Seminorm"
catalog
```
Example proving a theorem: (alternatively use `proof.start {"copyFrom": "Nat.add_comm"}`) to prime the proof
```
$ lake env build/bin/Pantograph "Init"
proof.start {"expr": "∀ (n m : Nat), n + m = m + n"}
proof.tactic {"treeId": 0, "stateId": 0, "goalId": 0, "tactic": "intro n m"}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "assumption"}
proof.printTree {"treeId": 0}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "rw [Nat.add_comm]"}
proof.printTree {"treeId": 0}
```
where the application of `assumption` should lead to a failure.

## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```

## Testing

The tests are based on `LSpec`. To run tests,
``` sh
test/all.sh
```

