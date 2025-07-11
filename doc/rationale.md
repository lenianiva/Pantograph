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

## Caveats and Limitations

Pantograph does not exactly mimic Lean LSP's behaviour. That would not grant the
flexibility it offers.  To support tree search means Pantograph has to act
differently from Lean in some times, but never at the sacrifice of soundness.

- When Lean LSP says "don't know how to synthesize placeholder", this indicates
  the human operator needs to manually move the cursor to the placeholder and
  type in the correct expression. This error therefore should not halt the proof
  process, and the placeholder should be turned into a goal.
- When Lean LSP says "unresolved goals", that means a proof cannot finish where
  it is supposed to finish at the end of a `by` block. Pantograph will raise the
  error in this case, since it indicates the termination of a proof search branch.

Pantograph cannot perform things that are inherently constrained by Lean. These
include:

- If a tactic loses track of metavariables, it will not be caught until the end
  of the proof search. This is a bug in the tactic itself.
- Although a timeout feature exists in Pantograph, it relies on the coöperative
  multitasking from the tactic implementation. There is nothing preventing a
  buggy tactic from stalling Lean if it does not check for cancellation often.
- For the same reason as above, there is no graceful way to stop a tactic which
  leaks infinite memory. Users who wish to have this behaviour should run
  Pantograph in a controlled environment with limited allocations. e.g.
  Linux control groups.
- Interceptions of parsing errors generally cannot be turned into goals (e.g.
  `def mystery : Nat := :=`) due to Lean's parsing system. This question is also
  not well-defined.

## References

* [Pantograph Paper](https://arxiv.org/abs/2410.16429)

