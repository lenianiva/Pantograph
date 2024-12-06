# Pantograph

A Machine-to-Machine interaction system for Lean 4.

![Pantograph](doc/icon.svg)

Pantograph provides interfaces to execute proofs, construct expressions, and
examine the symbol list of a Lean project for machine learning.

## Installation

For Nix users, run
``` sh
nix build .#{sharedLib,executable}
```
to build either the shared library or executable.

Install `elan` and `lake`, and run
``` sh
lake build
```
This builds the executable in `.lake/build/bin/pantograph-repl`.

## Executable Usage

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

For a list of commands, see [REPL Documentation](doc/repl.md).

### Project Environment

To use Pantograph in a project environment, setup the `LEAN_PATH` environment
variable so it contains the library path of lean libraries. The libraries must
be built in advance. For example, if `mathlib4` is stored at `../lib/mathlib4`,
the environment might be setup like this:

``` sh
LIB="../lib"
LIB_MATHLIB="$LIB/mathlib4/.lake"
export LEAN_PATH="$LIB/mathlib4/build/lib:$LIB_MATHLIB/aesop/build/lib:$LIB_MATHLIB/Qq/build/lib:$LIB_MATHLIB/std/build/lib"

LEAN_PATH=$LEAN_PATH build/bin/pantograph $@
```
The `$LEAN_PATH` executable of any project can be extracted by
``` sh
lake env printenv LEAN_PATH
```

### Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```

## Library Usage

`Pantograph/Library.lean` exposes a series of interfaces which allow FFI call
with `Pantograph` which mirrors the REPL commands above. It is recommended to
call Pantograph via this FFI since it provides a tremendous speed up.

The executable can be used as-is, but linking against the shared library
requires the presence of `lean-all`. Note that there isn't a 1-1 correspondence
between executable (REPL) commands and library functions.

Inject any project path via the `pantograph_init_search` function.

## Developing

A Lean development shell is provided in the Nix flake.

### Testing

The tests are based on `LSpec`. To run tests, use either
``` sh
nix flake check
```
or
``` sh
lake test
```
You can run an individual test by specifying a prefix

``` sh
lake test -- "Tactic/No Confuse"
```
