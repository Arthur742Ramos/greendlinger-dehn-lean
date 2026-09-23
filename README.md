# Greendlinger lemma and Dehn's algorithm in Lean

This project targets the classical theorem that finite symmetrized group presentations satisfying (C'(1/6)) admit an effective Dehn word-problem solver.

The intended theorem surface combines:

1. **Greendlinger's lemma:** a nonempty freely reduced null word has a cyclic rotation containing a subword longer than half of a relator;
2. **Cyclic Dehn correctness:** replacing that subword by the inverse complementary arc strictly shortens the representative, preserves identity in the presented group up to conjugacy, terminates, and returns the empty word exactly for the identity element.

The implementation uses finite relator lists and Mathlib's reduced free-group words, so the candidate search and Dehn procedure are executable.

## Current formalization status

- The exhaustive redex search is proved complete for the stated factorization predicate.
- A finite executable (C'(1/6)) checker is proved equivalent to the piece-based definition.
- Presented-group nullity has finite relator-certificate trees that flatten to products of conjugate relators, with a minimum-area certificate theorem.
- Kernel-checked examples exercise the checker and reducer on the symmetrized presentation \(\langle a\mid a^6\rangle\).
- Replacement is proved to preserve the presented-group element and strictly decrease free-word length.
- The fuel-bounded reducer is proved to terminate at an irreducible word.
- A cyclic redex search checks every rotation of the reduced word, including shells that cross the chosen boundary start.
- The cyclic fuel-bounded reducer strictly decreases free-word length and preserves identity through each conjugating rotation.
- Both linear and cyclic Dehn correctness are proved conditionally from their corresponding Greendlinger properties.
- The finite angle-counting lemma proves that positive total curvature forces a face with at most three internal arcs, given local incidence and Euler-curvature data for an arc-reduced disk diagram.
- The proof deriving Greendlinger's property from reduced van Kampen diagrams and (C'(1/6)) is not yet formalized. This repository is therefore a research prototype, not a Palomar-ready submission.

The remaining bridge must construct reduced finite diagrams from nullity certificates and derive the local incidence facts and total curvature from an actual disk-map model. The angle-counting lemma takes those as explicit inputs; it does not establish them. No Palomar intake or registration has been made.
