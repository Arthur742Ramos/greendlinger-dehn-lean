import SmallCancellation.CertificateCancellation
import SmallCancellation.PlanarCancellation

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
      trace.survivorOccurrences.map Prod.snd = w.toWord ∧
      trace.survivorOccurrences.length = w.toWord.length ∧
      (∀ o ∈ trace.survivorOccurrences,
        seed.boundary.literalBoundary[o.1]? = some o.2) ∧
      (∀ o ∈ trace.survivorOccurrences, o.1 < trace.inputWord.length) := by
  let trace := seed.boundary.to_boundaryShape
  refine ⟨trace, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact trace.cancellationPairs_length
  · exact trace.cancellationPairs_noncrossing
  · exact trace.cancellationPairs_are_inverseLetterOccurrences
  · exact trace.cancellationPairs_inBounds
  · exact trace.survivorOccurrences_labels
  · exact trace.survivorOccurrences_length
  · exact trace.survivorOccurrences_are_sourceLetters
  · exact trace.survivorOccurrences_inBounds

end GreendlingerDehn
