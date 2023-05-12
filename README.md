# Pantograph

An interaction system for Lean 4.

## Installation

Install `elan` and `lean4`. Then, execute
``` sh
lake build
```
In order to use `mathlib`, its binary must also be built

``` sh
lake build std
lake build mathlib
```

## Usage

The binary must be run inside a `lake env` environment.
```
$ lake env build/bin/Pantograph
{"cmd": "create", "payload": {"imports": ["Mathlib.Analysis.Seminorm"]}}
{"cmd": "catalog", "payload": {"id": 0}}
```
There is temporarily a limit of 500 symbols to prevent stack overflow.


