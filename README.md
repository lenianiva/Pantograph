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

The binary must be run inside a `lake env` environment.

Example: (~5k symbols)
```
$ lake env build/bin/Pantograph
{"cmd": "create", "payload": {"imports": ["Init"]}}
{"cmd": "catalog", "payload": {"id": 0}}
```
Example with `mathlib` (~90k symbols)
```
$ lake env build/bin/Pantograph
{"cmd": "create", "payload": {"imports": ["Mathlib.Analysis.Seminorm"]}}
{"cmd": "catalog", "payload": {"id": 0}}
```


## Troubleshooting

If lean encounters stack overflow problems when printing catalog, execute this before running lean:
```sh
ulimit -s unlimited
```
