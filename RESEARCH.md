# Research case and theorem boundary

## Mathematical target

Let (X) be a finite alphabet and let (R) be a finite symmetrized set of nonempty cyclically reduced relators. If (R) satisfies (C'(1/6)), then every nonempty freely reduced word (w) that is trivial in ⟨(Xmid R)⟩ contains a contiguous subword (v) that is an initial segment of some (r\in R) and satisfies (2|v|>|r|). The linear-word conclusion is the form needed by the executable Dehn reducer.

The intended proof derives this from a reduced van Kampen diagram: the (C'(1/6)) condition bounds internal arcs by one sixth of each adjacent relator; a combinatorial curvature count supplies an exterior shell with at most three internal arcs; the complementary exterior arc is therefore longer than half of its relator. Minimal diagrams with cut vertices require a block or terminal-disc argument to ensure the shell lies contiguously in the input word.

The formalization also identifies presented-group nullity with existence of a finite relator-certificate tree. Each certificate flattens to a finite product of conjugates of defining relators (when the list is inverse-closed), and the minimum number of relator factors exists. The executable procedure enumerates all finite relator cuts and subword occurrences, selects the first valid long side, replaces it by the inverse complementary side, and freely reduces. The checked generic theorem already proves preservation, strict length decrease, termination, and word-problem correctness assuming the Greendlinger property. Turning a minimum certificate into a reduced planar diagram, then proving the (C'(1/6)\Rightarrow\) Greendlinger shell estimate, is still missing and remains the release-blocking theorem.

## Why this theorem matters

Greendlinger's result is the classical bridge from a local overlap restriction on relators to a decision procedure for the word problem. It is a substantial theorem in combinatorial group theory rather than an isolated implementation exercise. The project uses Mathlib's free-group and presented-group foundations, and adds the finite small-cancellation definitions, executable relator checker, exhaustive Dehn reducer, and correctness proof.

Primary references:

- Martin Greendlinger, “Dehn's algorithm for the word problem,” *Communications on Pure and Applied Mathematics* 13 (1960), 67–83. [DOI and publisher record](https://doi.org/10.1002/cpa.3160130108).
- Roger C. Lyndon, “On Dehn's Algorithm,” *Mathematische Annalen* 166 (1966), 208–228. [EuDML record](https://eudml.org/doc/161458).

Repository and code searches have not found a Lean formalization of this theorem. This is a search result, not a claim of global priority. Palomar eligibility will be evaluated only after the exact theorem is fully proved and the required release gates pass.
