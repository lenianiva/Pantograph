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
build/bin/pantograph`. The REPL loop accepts commands and outputs either an
`Error:` (indicating malformed command) or a json return value indicating the
result of a command execution. The command can be passed in one of two formats
```
command { ... }
{ "cmd": command, "payload": ... }
```

Example: (~5k symbols)
```
$ lake env build/bin/Pantograph
create {"imports": ["Init"]}
catalog {"id": 0}
```
Example with `mathlib` (~90k symbols)
```
$ lake env build/bin/Pantograph
create {"imports": ["Mathlib.Analysis.Seminorm"]}
catalog {"id": 0}
```


## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```
