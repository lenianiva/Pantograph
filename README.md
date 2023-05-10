# Pantograph

An interaction system for Lean 4.

## Installation

Install `elan` and `lean4`. Then, execute
``` sh
lake build
```

## Usage

Before usage, put the packages that you wish the REPL to use into a directory
and build them. Put this directory into the variable `$LEAN_PATH`. Then
``` 
$ build/bin/Pantograph
{"cmd": "create", "payload": {"imports": ["Mathlib.Analysis.Seminorm"]}}
```


