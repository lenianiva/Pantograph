# Pantograph

A Machine-to-Machine interaction system for Lean 4.

![Pantograph](doc/icon.svg)

Pantograph provides interfaces to execute proofs, construct expressions, and
examine the symbol list of a Lean project for machine learning.

See [documentations](doc/rationale.md) for design rationale and references.

## Installation

For Nix users, run
``` sh
nix build .#{sharedLib,executable}
```
to build either the shared library or executable.

Install `lake` and `lean` fixed to the version of the `lean-toolchain` file, and
run

``` sh
lake build
```
This builds the executable in `.lake/build/bin/pantograph-repl`.

### Executable Usage

See [Executable Usage](./doc/repl.md)

### Library Usage

`Pantograph/Library.lean` exposes a series of interfaces which allow FFI call
with `Pantograph` which mirrors the REPL commands above. Note that there isn't a
1-1 correspondence between executable (REPL) commands and library functions.

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
