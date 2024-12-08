# Design Rationale

A great problem in machine learning is to use ML agents to automatically prove
mathematical theorems. This sort of proof necessarily involves *search*.
Compatibility for search is the main reason for creating Pantograph.  The Lean 4
LSP interface is not conducive to search. Pantograph is designed with this in
mind. It emphasizes the difference between 3 views of a proof:

- **Presentation View**: The view of a written, polished proof. e.g. Mathlib and
  math papers are almost always written in this form.
- **Search View**: The view of a proof exploration trajectory. This is not
  explicitly supported by Lean LSP.
- **Kernel View**: The proof viewed as a set of metavariables.

Pantograph enables proof agents to operate on the search view.

## Name

The name Pantograph is a pun. It means two things
- A pantograph is an instrument for copying down writing. As an agent explores
  the vast proof search space, Pantograph records the current state to ensure
  the proof is sound.
- A pantograph is also an equipment for an electric train. It supplies power to
  a locomotive. In comparison the (relatively) simple Pantograph software powers
  theorem proving projects.

## References

* [Pantograph Paper](https://arxiv.org/abs/2410.16429)

