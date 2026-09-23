# Greendlinger lemma and Dehn's algorithm in Lean

This project targets the classical theorem that finite symmetrized group presentations satisfying (C'(1/6)) admit an effective Dehn word-problem solver.

The intended theorem surface combines:

1. **Greendlinger's lemma:** a nonempty freely reduced null word has a cyclic rotation containing a subword longer than half of a relator;
2. **Cyclic Dehn correctness:** replacing that subword by the inverse complementary arc strictly shortens the representative, preserves identity in the presented group up to conjugacy, terminates, and returns the empty word exactly for the identity element.

The implementation uses finite relator lists and Mathlib's reduced free-group words, so the candidate search and Dehn procedure are executable.

## Current formalization status

- The exhaustive redex search is proved complete for the stated factorization predicate.
- A finite executable (C'(1/6)) checker is proved equivalent to the piece definition, including repeated cyclic positions within a relator.
- Presented-group nullity has finite relator-certificate trees that flatten to products of conjugate relators, with a minimum-area certificate theorem.
- A proof that a word is quotient-null now yields an ordered finite list of relator-conjugate factor occurrences with explicit conjugator and relator labels. Their literal `g r g⁻¹` boundary words freely reduce, factor by factor and then globally, to the requested reduced boundary word. The nested cancellation trees replay as adjacent inverse-letter deletions that preserve the free-group element, and each tree's pair count exactly accounts for its length difference. This is proof-side algebraic boundary data, not yet a planar disk diagram.
- Kernel-checked examples accept a symmetrized relator with distinct cyclic letters, reject the periodic relator \(a^6\), and exercise the reducer on \(\langle a\mid a^6\rangle\).
- Replacement is proved to preserve the presented-group element and strictly decrease free-word length.
- The fuel-bounded reducer is proved to terminate at an irreducible word.
- A cyclic redex search checks every rotation of the reduced word, including shells that cross the chosen boundary start.
- The cyclic fuel-bounded reducer strictly decreases free-word length and preserves identity through each conjugating rotation.
- Both linear and cyclic Dehn correctness are proved conditionally from their corresponding Greendlinger properties.
- Each curvature face stores actual corner angles with local 1/2 and 2/3 bounds; the face angle cap is derived by summation, and side/corner counts come from the same finite corner list. A finite Gauss--Bonnet accounting theorem derives total face curvature 2 from Euler's disk equation and aggregate vertex-angle/edge-side counts; the angle-counting lemma then forces a face with at most three internal arcs under its local bounds.
- A finite arithmetic lemma proves that three or fewer internal arcs, each strictly shorter than one sixth of the relator perimeter, leave an exterior shell arc longer than half the relator.
- Given a shell decomposition whose internal arcs are actual `C'(1/6)` pieces, the shell theorem constructs the cyclic redex consumed by the executable reducer.
- For symmetrized presentations, one-step relator rotation closure is proved to cover every cyclic cut, so shell arcs at arbitrary face positions yield the required same-perimeter prefix bounds.
- The same piece bounds show that a complete relator boundary needs at least seven arcs; with the model's angle cap, this derives nonpositive curvature for an internal face.
- Combining that result with finite Gauss--Bonnet accounting lets the curvature argument force a small shell when every internal face has explicit C'(1/6) piece data.
- The composed curvature-and-shell theorem returns the exact cyclic redex searched by the algorithm from that finite profile. `CurvatureShellProfileProperty` isolates profile existence as the single remaining global diagram interface, and the end-to-end Dehn correctness theorem is conditional on that explicit property.
- The proof deriving Greendlinger's property from reduced van Kampen diagrams and (C'(1/6)) is not yet formalized. This repository is therefore a research prototype, not a Palomar-ready submission.

The remaining bridge must construct a reduced finite diagram from a nullity certificate and derive the aggregate accounting, external-face bounds, reducedness-to-piece facts, and shell boundary profile from an actual combinatorial diagram. It must also handle cut vertices and semi-exterior vertices, or prove a valid reduction to the disk case. The cancellation tree records noncrossing free cancellations but does not establish planarity or supply the required incidence identities. The composed theorem currently consumes that complete profile as explicit data. No Palomar intake or registration has been made.
