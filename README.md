# Pantograph

An interaction system for Lean 4.

![Pantograph](doc/icon.svg)

## Installation

Install `elan` and `lean4`. Then, execute
``` sh
lake build
```
Then, setup the `LEAN_PATH` environment variable so it contains the library path of lean libraries. The libraries must be built in advance. For example, if `mathlib4` is stored at `../lib/mathlib4`,
``` sh
LIB="../lib"
LIB_MATHLIB="$LIB/mathlib4/lake-packages"
export LEAN_PATH="$LIB/mathlib4/build/lib:$LIB_MATHLIB/aesop/build/lib:$LIB_MATHLIB/Qq/build/lib:$LIB_MATHLIB/std/build/lib"

LEAN_PATH=$LEAN_PATH build/bin/pantograph $@
```
Note that `lean-toolchain` must be present in the `$PWD` in order to run Pantograph! This is because Pantograph taps into Lean's internals.

## Usage

``` sh
build/bin/pantograph OPTIONS|MODULES
```

The REPL loop accepts commands as single-line JSON inputs and outputs either an
`Error:` (indicating malformed command) or a json return value indicating the
result of a command execution.  The command can be passed in one of two formats
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
$ build/bin/Pantograph Init
catalog
inspect {"name": "Nat.le_add_left"}
```
Example with `mathlib4` (~90k symbols, may stack overflow, see troubleshooting)
```
$ lake env build/bin/Pantograph Mathlib.Analysis.Seminorm
catalog
```
Example proving a theorem: (alternatively use `proof.start {"copyFrom": "Nat.add_comm"}`) to prime the proof
```
$ env build/bin/Pantograph Init
proof.start {"expr": "∀ (n m : Nat), n + m = m + n"}
proof.tactic {"treeId": 0, "stateId": 0, "goalId": 0, "tactic": "intro n m"}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "assumption"}
proof.printTree {"treeId": 0}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "rw [Nat.add_comm]"}
proof.printTree {"treeId": 0}
```
where the application of `assumption` should lead to a failure.

## Commands

See `Pantograph/Commands.lean` for a description of the parameters and return values in Json.
- `catalog`: Display a list of all safe Lean symbols in the current context
- `inspect {"name": <name>}`: Show the type and package of a given symbol
- `clear`: Delete all cached expressions and proof trees
- `expr.type {"expr": <expr>}`: Determine the type of an expression and round-trip it
- `proof.start {["name": <name>], ["expr": <expr>], ["copyFrom": <symbol>]}`: Start a new proof state from a given expression or symbol
- `proof.tactic {"treeId": <id>, "stateId": <id>, "goalId": <id>, "tactic": string}`: Execute a tactic on a given proof state
- `proof.printTree {"treeId": <id>}`: Print the topological structure of a proof tree

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

