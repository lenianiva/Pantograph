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

### Commands

See `Pantograph/Protocol.lean` for a description of the parameters and return values in JSON.
* `reset`: Delete all cached expressions and proof trees
* `stat`: Display resource usage
* `expr.echo {"expr": <expr>, "type": <optional expected type>, ["levels": [<levels>]]}`: Determine the
  type of an expression and format it.
* `env.catalog`: Display a list of all safe Lean symbols in the current environment
* `env.inspect {"name": <name>, "value": <bool>}`: Show the type and package of a
  given symbol; If value flag is set, the value is printed or hidden. By default
  only the values of definitions are printed.
* `options.set { key: value, ... }`: Set one or more options (not Lean options; those
  have to be set via command line arguments.), for options, see `Pantograph/Protocol.lean`

  One particular option for interest for machine learning researchers is the
  automatic mode (flag: `"automaticMode"`).  By default it is turned on, with
  all goals automatically resuming. This makes Pantograph act like a gym,
  with no resumption necessary to manage your goals.
* `options.print`: Display the current set of options
* `goal.start {["name": <name>], ["expr": <expr>], ["levels": [<levels>]], ["copyFrom": <symbol>]}`:
  Start a new proof from a given expression or symbol
* `goal.tactic {"stateId": <id>, "goalId": <id>, ...}`: Execute a tactic string on a
  given goal. The tactic is supplied as additional key-value pairs in one of the following formats:
  - `{ "tactic": <tactic> }`: Execute an ordinary tactic
  - `{ "expr": <expr> }`: Assign the given proof term to the current goal
  - `{ "have": <expr>, "binderName": <name> }`: Execute `have` and creates a branch goal
  - `{ "calc": <expr> }`: Execute one step of a `calc` tactic. Each step must
    be of the form `lhs op rhs`. An `lhs` of `_` indicates that it should be set
    to the previous `rhs`.
  - `{ "conv": <bool> }`: Enter or exit conversion tactic mode. In the case of
    exit, the goal id is ignored.
* `goal.continue {"stateId": <id>, ["branch": <id>], ["goals": <names>]}`:
  Execute continuation/resumption
  - `{ "branch": <id> }`: Continue on branch state. The current state must have no goals.
  - `{ "goals": <names> }`: Resume the given goals
* `goal.remove {"stateIds": [<id>]}"`: Drop the goal states specified in the list
* `goal.print {"stateId": <id>}"`: Print a goal state
* `frontend.process { ["fileName": <fileName>",] ["file": <str>], invocations:
  <bool>, sorrys: <bool> }`: Executes the Lean frontend on a file, collecting
  either the tactic invocations (`"invocations": true`) or the sorrys into goal
  states (`"sorrys": true`)

### Errors

When an error pertaining to the execution of a command happens, the returning JSON structure is

``` json
{ "error": "type", "desc": "description" }
```
Common error forms:
* `command`: Indicates malformed command structure which results from either
  invalid command or a malformed JSON structure that cannot be fed to an
  individual command.
* `index`: Indicates an invariant maintained by the output of one command and
  input of another is broken. For example, attempting to query a symbol not
  existing in the library or indexing into a non-existent proof state.

### Project Environment

To use Pantograph in a project environment, setup the `LEAN_PATH` environment
variable so it contains the library path of lean libraries. The libraries must
be built in advance. For example, if `mathlib4` is stored at `../lib/mathlib4`,
the environment might be setup like this:

``` sh
LIB="../lib"
LIB_MATHLIB="$LIB/mathlib4/lake-packages"
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
