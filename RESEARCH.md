# Research case and theorem boundary

## Mathematical target

Let `X` be a finite alphabet and `R` a finite symmetrized set of nonempty cyclically reduced relators satisfying `C'(1/6)`. Greendlinger's lemma says that every nontrivial freely reduced word representing the identity has a cyclic rotation containing a contiguous subword `v` that is an initial segment of some `r ∈ R` and satisfies `2 * |v| > |r|`. This cyclic form is the theorem surface for the executable cyclic Dehn reducer.

The standard proof uses a reduced van Kampen diagram. The `C'(1/6)` condition bounds every internal arc by one sixth of each incident relator. An angle assignment gives interior corners weight at most `2/3` and exterior corners weight at most `1/2`, in units of `π`. Euler characteristic one for the disk makes the total face curvature positive; therefore an exterior shell has at most three internal arcs, and its complementary boundary arc is longer than half its relator.

The finite piece predicate keeps distinct cyclic start positions even when a proper power makes their rotated words equal; the executable checker therefore rejects the periodic relator `a^6` as `C'(1/6)`. Presented-group nullity is also characterized by finite relator-certificate trees. Each certificate flattens to a product of conjugates of defining relators (when the relator list is inverse-closed), and a minimum area exists. The cyclic executable procedure enumerates every rotation and relator cut, selects a valid long side, replaces it by the inverse complementary side, and freely reduces. Each step preserves identity under conjugacy and strictly decreases length. Its termination and word-problem correctness are proved assuming the cyclic Greendlinger property.

`SmallCancellation/Curvature.lean` formalizes the finite angle-counting implication: positive total curvature plus explicit local face-incidence bounds yields a shell with at most three internal arcs. It does not derive those inputs from a disk map. The release-blocking work remains (1) constructing a reduced planar diagram from a nullity certificate, (2) deriving disk Euler/angle identities and local incidence bounds from an actual combinatorial disk model, and (3) extracting the relator subword from the shell.

The same file also proves the numerical shell estimate in isolation: if a relator boundary is partitioned into an exterior arc and at most three internal arcs, and each internal arc is strictly shorter than one sixth of the perimeter, then the exterior arc is longer than half the perimeter. This closes the arithmetic step after an actual diagram supplies those arcs; it does not construct the diagram or establish that its internal arcs are pieces.

`SmallCancellation/Shell.lean` connects that estimate to the executable algorithm: from a specified shell decomposition, piece evidence, same-perimeter relator-prefix evidence, and a cyclic split of the boundary word, it constructs an `IsCyclicRedex` witness. Thus the remaining theorem is sharply localized to constructing an arc-reduced disk diagram from a nullity certificate and deriving the shell decomposition and piece evidence from that diagram.

## Why this theorem matters

Greendlinger's result is the classical bridge from a local overlap restriction on relators to an effective decision procedure for the word problem. The target combines substantial combinatorial group theory with a verified executable algorithm. The repository builds on Mathlib's free-group and presented-group foundations and adds the finite small-cancellation definitions, executable relator checker, exhaustive Dehn reducer, and conditional correctness theorems.

Primary references:

- Martin Greendlinger, “Dehn's algorithm for the word problem,” *Communications on Pure and Applied Mathematics* 13 (1960), 67–83. [DOI and publisher record](https://doi.org/10.1002/cpa.3160130108).
- Roger C. Lyndon, “On Dehn's Algorithm,” *Mathematische Annalen* 166 (1966), 208–228. [EuDML record](https://eudml.org/doc/161458).

An accessible exposition of the arc-reduced diagram and angle-counting proof is Martin T. Touikan, *An Introduction to Combinatorial Group Theory*, §3.5. [Course notes](https://ntouikan.ext.unb.ca/MATH6022/IntroCGGT/html_output/section-18.html).

Repository and code searches have not found a Lean formalization of this theorem. This is a search result, not a claim of global priority. Palomar eligibility will be evaluated only after the exact theorem is fully proved and all required release gates pass.
