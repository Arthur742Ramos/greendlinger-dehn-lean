# Greendlinger lemma and Dehn's algorithm in Lean

This project targets the classical theorem that finite symmetrized group presentations satisfying (C'(1/6)) admit an effective Dehn word-problem solver.

The intended theorem surface combines:

1. **Greendlinger's lemma:** a nonempty freely reduced word representing the identity contains a subword longer than half of a cyclic relator;
2. **Dehn correctness:** repeatedly replacing such a subword by the inverse complementary arc strictly shortens the word, preserves its group element, terminates, and returns the empty word exactly for the identity element.

The implementation uses finite relator lists and Mathlib's reduced free-group words, so the candidate search and Dehn procedure are executable.

## Current formalization status

- The exhaustive redex search is proved complete for the stated factorization predicate.
- A finite executable (C'(1/6)) checker is proved equivalent to the piece-based definition.
- Presented-group nullity has finite relator-certificate trees, and a minimum-area certificate exists.
- Kernel-checked examples exercise the checker and reducer on the symmetrized presentation \(\langle a\mid a^6\rangle\).
- Replacement is proved to preserve the presented-group element and strictly decrease free-word length.
- The fuel-bounded reducer is proved to terminate at an irreducible word.
- Dehn correctness is proved conditionally from the Greendlinger property.
- The proof deriving Greendlinger's property from reduced van Kampen diagrams and (C'(1/6)) is not yet formalized. This repository is therefore a research prototype, not a Palomar-ready submission.

The intended bridge uses reduced finite van Kampen diagrams and a combinatorial curvature argument. No Palomar intake or registration has been made.
