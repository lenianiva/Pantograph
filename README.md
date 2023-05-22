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
build/bin/pantograph`. The REPL loop accepts commands as single-line JSON inputs
and outputs either an `Error:` (indicating malformed command) or a json return
value indicating the result of a command execution. The command can be passed in
one of two formats
```
command { ... }
{ "cmd": command, "payload": ... }
```
The list of available commands can be found in `Pantograph/Commands.lean`. An
empty command aborts the REPL.

Example: (~5k symbols)
```
$ lake env build/bin/Pantograph
create {"imports": ["Init"]}
catalog {"id": 0}
inspect {"id": 0, "symbol": "Nat.le_add_left"}
```
Example with `mathlib` (~90k symbols)
```
$ lake env build/bin/Pantograph
create {"imports": ["Mathlib.Analysis.Seminorm"]}
catalog {"id": 0}
```
Example proving a theorem: (alternatively use `proof.start {"id": 0, "name": "aa", "copyFrom": "Nat.add_comm", "expr": ""}`) to prime the proof
```
$ lake env build/bin/Pantograph
create {"imports": ["Init"]}
proof.start {"id": 0, "expr": "∀ (n m : Nat), n + m = m + n"}
proof.tactic {"treeId": 0, "stateId": 0, "goalId": 0, "tactic": "intro n m"}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "assumption"}
proof.printTree {"treeId": 0}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "rw [Nat.add_comm]"}
proof.printTree {"treeId": 0}
```
where the application of `assumption` should lead to a failure.

```
create {"imports": ["Init"]}
proof.start {"id": 0, "expr": "∀ (p q: Prop), p ∨ q → q ∨ p"}
proof.tactic {"treeId": 0, "stateId": 0, "goalId": 0, "tactic": "intro p q h"}
proof.tactic {"treeId": 0, "stateId": 1, "goalId": 0, "tactic": "cases h"}
proof.tactic {"treeId": 0, "stateId": 2, "goalId": 0, "tactic": "apply Or.inr"}
proof.tactic {"treeId": 0, "stateId": 2, "goalId": 0, "tactic": "apply Or.inl"}
```

## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```
Due to a current bug in Lean (which existed in Lean 3), [the default value of structures are not honoured when parsing Json's](https://github.com/leanprover/lean4/issues/2225).


## Testing

The tests are based on `LSpec`. To run tests,
``` sh
test/all.sh
```

