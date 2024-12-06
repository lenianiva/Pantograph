# REPL

## Commands

See `Pantograph/Protocol.lean` for a description of the parameters and return values in JSON.
* `reset`: Delete all cached expressions and proof trees
* `stat`: Display resource usage
* `expr.echo {"expr": <expr>, "type": <optional expected type>, ["levels": [<levels>]]}`: Determine the
  type of an expression and format it.
* `env.catalog`: Display a list of all safe Lean symbols in the current environment
* `env.inspect {"name": <name>, "value": <bool>}`: Show the type and package of a
  given symbol; If value flag is set, the value is printed or hidden. By default
  only the values of definitions are printed.
* `env.save { path }`, `env.load { path }`: Save/Load the current environment
  to/from a file
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
* `goal.save{ id, path }`, `goal.load { path }`: Save/Load a goal state to/from a
  file. The environment is not carried with the state. The user is responsible
  to ensure the sender/receiver instances share the same environment.
* `frontend.process { ["fileName": <fileName>",] ["file": <str>], invocations:
  <bool>, sorrys: <bool> }`: Executes the Lean frontend on a file, collecting
  either the tactic invocations (`"invocations": true`) or the sorrys into goal
  states (`"sorrys": true`)

## Errors

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
