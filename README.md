# Pantograph

An interaction system for Lean 4.

![Pantograph](doc/icon.svg)

## Installation

Install `elan` and `lake`. Execute
``` sh
make build/bin/pantograph
```
setup the `LEAN_PATH` environment variable so it contains the library path of lean libraries. The libraries must be built in advance. For example, if `mathlib4` is stored at `../lib/mathlib4`,
``` sh
LIB="../lib"
LIB_MATHLIB="$LIB/mathlib4/lake-packages"
export LEAN_PATH="$LIB/mathlib4/build/lib:$LIB_MATHLIB/aesop/build/lib:$LIB_MATHLIB/Qq/build/lib:$LIB_MATHLIB/std/build/lib"

LEAN_PATH=$LEAN_PATH build/bin/pantograph $@
```
The provided `flake.nix` has a develop environment with Lean already setup.

## Usage

``` sh
pantograph MODULES|LEAN_OPTIONS
```

The REPL loop accepts commands as single-line JSON inputs and outputs either an
`Error:` (indicating malformed command) or a JSON return value indicating the
result of a command execution.  The command can be passed in one of two formats
```
command { ... }
{ "cmd": command, "payload": ... }
```
The list of available commands can be found in `Pantograph/Protocol.lean` and below. An
empty command aborts the REPL.

The `pantograph` executable must be run with a list of modules to import. It can
also accept lean options of the form `--key=value` e.g. `--pp.raw=true`.

Example: (~5k symbols)
```
$ pantograph Init
env.catalog
env.inspect {"name": "Nat.le_add_left"}
```
Example with `mathlib4` (~90k symbols, may stack overflow, see troubleshooting)
```
$ pantograph Mathlib.Analysis.Seminorm
env.catalog
```
Example proving a theorem: (alternatively use `goal.start {"copyFrom": "Nat.add_comm"}`) to prime the proof
```
$ pantograph Init
goal.start {"expr": "∀ (n m : Nat), n + m = m + n"}
goal.tactic {"stateId": 0, "goalId": 0, "tactic": "intro n m"}
goal.tactic {"stateId": 1, "goalId": 0, "tactic": "assumption"}
goal.delete {"stateIds": [0]}
stat {}
goal.tactic {"stateId": 1, "goalId": 0, "tactic": "rw [Nat.add_comm]"}
stat
```
where the application of `assumption` should lead to a failure.

## Commands

See `Pantograph/Protocol.lean` for a description of the parameters and return values in JSON.
- `reset`: Delete all cached expressions and proof trees
- `expr.echo {"expr": <expr>}`: Determine the type of an expression and round-trip it
- `env.catalog`: Display a list of all safe Lean symbols in the current environment
- `env.inspect {"name": <name>, "value": <bool>}`: Show the type and package of a
  given symbol; If value flag is set, the value is printed or hidden. By default
  only the values of definitions are printed.
- `options.set { key: value, ... }`: Set one or more options (not Lean options; those
  have to be set via command line arguments.), for options, see `Pantograph/Protocol.lean`
- `options.print`: Display the current set of options
- `goal.start {["name": <name>], ["expr": <expr>], ["copyFrom": <symbol>]}`: Start a new goal from a given expression or symbol
- `goal.tactic {"stateId": <id>, "goalId": <id>, ["tactic": <tactic>], ["expr": <expr>]}`: Execute a tactic string on a given goal
- `goal.continue {"stateId": <id>, ["branch": <id>], ["goals": <names>]}`: Continue from a proof state
- `goal.remove {"stateIds": [<id>]}"`: Remove a bunch of stored goals.
- `goal.print {"stateId": <id>}"`: Print a goal state
- `stat`: Display resource usage

## Errors

When an error pertaining to the execution of a command happens, the returning JSON structure is

``` json
{ error: "type", desc: "description" }
```
Common error forms:
* `command`: Indicates malformed command structure which results from either
  invalid command or a malformed JSON structure that cannot be fed to an
  individual command.
* `index`: Indicates an invariant maintained by the output of one command and
  input of another is broken. For example, attempting to query a symbol not
  existing in the library or indexing into a non-existent proof state.

## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```

## Testing

The tests are based on `LSpec`. To run tests,
``` sh
make test
```
