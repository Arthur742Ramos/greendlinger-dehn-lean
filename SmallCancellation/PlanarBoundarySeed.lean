import SmallCancellation.CertificateCancellation
import SmallCancellation.PlanarCancellation
import SmallCancellation.ReducedLollipop

namespace GreendlingerDehn

/-- The literal relator-conjugate boundary of a nullity seed reduces to the
requested reduced boundary word. This converts the algebraic cancellation
sequence into the indexed tree used to extract source occurrences. -/
noncomputable def RelatorFactorBoundarySeed.to_boundaryShape {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    FreeReductionShape seed.literalBoundary w.toWord := by
  have hword : FreeGroup.mk seed.literalBoundary = FreeGroup.mk w.toWord := by
    rw [seed.literalBoundary_mk, FreeGroup.mk_toWord]
  have hred := FreeGroup.reduce.sound hword
  have hnormal : FreeGroup.reduce seed.literalBoundary = w.toWord := by
    simpa [FreeGroup.isReduced_toWord.reduce_eq] using hred
  rw [← hnormal]
  exact FreeReductionShape.of_reduce seed.literalBoundary

/-- Minimum-area nullity data retain a noncrossing pairing of inverse source
letters and selected source positions spelling the reduced boundary. This is
still a combinatorial trace; it does not construct edge or vertex quotients. -/
theorem MinimalAreaRelatorBoundarySeed.boundaryTrace {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed R w) :
    ∃ trace : FreeReductionShape seed.boundary.literalBoundary w.toWord,
      trace.cancellationPairs.length = trace.cancellationCount ∧
      CancellationPairsNoncrossing trace.cancellationPairs ∧
      (∀ p ∈ trace.cancellationPairs,
        ∃ a, seed.boundary.literalBoundary[p.1]? = some a ∧
          seed.boundary.literalBoundary[p.2]? = some (inverseLetter a)) ∧
      (∀ p ∈ trace.cancellationPairs,
        p.1 < p.2 ∧ p.2 < trace.inputWord.length) ∧
      (pairEndpoints trace.cancellationPairs).Nodup ∧
      (pairEndpoints trace.cancellationPairs).length =
        2 * trace.cancellationCount ∧
      (∀ i ∈ pairEndpoints trace.cancellationPairs,
        i < trace.inputWord.length) ∧
      trace.survivorOccurrences.map Prod.snd = w.toWord ∧
      trace.survivorOccurrences.length = w.toWord.length ∧
      (trace.survivorOccurrences.map Prod.fst).Nodup ∧
      List.Pairwise (fun i j : Nat => i < j)
        (trace.survivorOccurrences.map Prod.fst) ∧
      (pairEndpoints trace.cancellationPairs).length +
          (trace.survivorOccurrences.map Prod.fst).length =
        trace.inputWord.length ∧
      (∀ o ∈ trace.survivorOccurrences,
        seed.boundary.literalBoundary[o.1]? = some o.2) ∧
      (∀ o ∈ trace.survivorOccurrences, o.1 < trace.inputWord.length) ∧
      (∀ o ∈ trace.survivorOccurrences, ∀ p ∈ trace.cancellationPairs,
        o.1 ≠ p.1 ∧ o.1 ≠ p.2) ∧
      (∀ p ∈ trace.cancellationPairs, ∀ o ∈ trace.survivorOccurrences,
        p.1 < o.1 → o.1 < p.2 → False) ∧
      (∀ i, i < trace.inputWord.length →
        i ∈ pairEndpoints trace.cancellationPairs ∨
          i ∈ trace.survivorOccurrences.map Prod.fst) := by
  let trace := seed.boundary.to_boundaryShape
  refine ⟨trace, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact trace.cancellationPairs_length
  · exact trace.cancellationPairs_noncrossing
  · exact trace.cancellationPairs_are_inverseLetterOccurrences
  · exact trace.cancellationPairs_inBounds
  · exact trace.cancellationEndpoints_nodup
  · exact trace.cancellationEndpoints_length
  · exact trace.cancellationEndpoints_inBounds
  · exact trace.survivorOccurrences_labels
  · exact trace.survivorOccurrences_length
  · exact trace.survivorOccurrencePositions_nodup
  · exact trace.survivorOccurrencePositions_strict
  · simpa using trace.survivorAndCancellationEndpointCount
  · exact trace.survivorOccurrences_are_sourceLetters
  · exact trace.survivorOccurrences_inBounds
  · exact trace.survivorOccurrences_disjointFromCancellationPairs
  · exact trace.cancellationPairs_contain_no_survivor
  · exact trace.sourcePositions_partition

/-- Retain both stages of the minimum-area seed's boundary reduction: each
literal conjugate-relator balloon reduces to its canonical factor word, and
the concatenated factor word reduces to the requested boundary. The returned
trace therefore preserves the precise local-then-global cancellation pairing
on the original literal boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.stagedBoundaryTrace
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed R w) :
    IndexedBoundaryTrace seed.boundary.literalBoundary w.toWord :=
  FreeReductionShape.composeIndexedBoundaryTrace
    seed.boundary.literalFactors_reduce seed.boundary.cancellation

/-- The minimum-area certificate also admits a boundary trace based on
cancellation-free relator balloons. Each literal lollipop boundary is already
the canonical factor word, so only the global factor cancellations remain. -/
noncomputable def MinimalAreaRelatorBoundarySeed.reducedLollipopBoundaryTrace
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    IndexedBoundaryTrace seed.boundary.reducedLiteralBoundary w.toWord :=
  FreeReductionShape.composeIndexedBoundaryTrace
    (FreeReductionShape.identity seed.boundary.reducedLiteralBoundary)
    seed.boundary.reducedLiteralBoundaryShape

theorem MinimalAreaRelatorBoundarySeed.reducedBalloonCount_eq_area
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    seed.boundary.reducedBalloons.length = seed.certificate.area := by
  calc
    seed.boundary.reducedBalloons.length = seed.boundary.factors.length := by
      simp [RelatorFactorBoundarySeed.reducedBalloons]
    _ = seed.certificate.factors.length := by rw [seed.boundary_factors]
    _ = seed.certificate.area := RelatorCertificate.factors_length seed.certificate

end GreendlingerDehn
