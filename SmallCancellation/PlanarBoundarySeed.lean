import SmallCancellation.CertificateCancellation
import SmallCancellation.PlanarCancellation
import SmallCancellation.ReducedLollipop
import SmallCancellation.CyclicDehn

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

/-- A null word certified by one relator occurrence already contains a full
relator as a Dehn redex. This is the zero-overlap base case for arguments that
build diagrams by increasing minimum area. -/
theorem MinimalAreaRelatorBoundarySeed.cyclicGreendlinger_of_area_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (harea : seed.certificate.area = 1) :
    ∃ c, IsCyclicRedex P.relators w c := by
  have hfactorLength : seed.boundary.factors.length = 1 := by
    calc
      seed.boundary.factors.length = seed.certificate.factors.length :=
        congrArg List.length seed.boundary_factors
      _ = seed.certificate.area := RelatorCertificate.factors_length seed.certificate
      _ = 1 := harea
  obtain ⟨factor, hfactor⟩ : ∃ factor, seed.boundary.factors = [factor] := by
    cases hlist : seed.boundary.factors with
    | nil => simp [hlist] at hfactorLength
    | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest => simp [hlist] at hfactorLength
      subst tail
      exact ⟨head, rfl⟩
  have hfactorW : factor = w := by
    have h := seed.boundary.product_eq
    simpa [hfactor] using h
  have hlabel : IsRelatorConjugate P.relators factor :=
    seed.boundary.factor_labels factor (by simp [hfactor])
  let balloon := ReducedRelatorBalloonData.of_isRelatorConjugate P hlabel
  have hballoonFactor : balloon.factor = factor := by
    simp [balloon]
  let d := balloon.label
  have hraw : d.rawWord = w.toWord := by
    calc
      d.rawWord = balloon.factor.toWord := balloon.boundary_eq_factorWord
      _ = factor.toWord := by rw [hballoonFactor]
      _ = w.toWord := by rw [hfactorW]
  have hrelatorLength : 0 < d.relator.toWord.length := by
    by_contra hpos
    have hzero : d.relator.toWord.length = 0 := Nat.eq_zero_of_not_pos hpos
    have hnil : d.relator.toWord = [] := by
      cases hword : d.relator.toWord with
      | nil => rfl
      | cons letter tail => simp [hword] at hzero
    have hone : d.relator = 1 := by
      apply FreeGroup.toWord_injective
      rw [hnil, FreeGroup.toWord_one]
    exact P.nontrivial d.relator d.relator_mem hone
  let redex : Redex α :=
    ⟨d.conjugator.toWord, d.relator.toWord,
      FreeGroup.invRev d.conjugator.toWord, d.relator, []⟩
  refine ⟨⟨[], w.toWord, redex⟩, ?_⟩
  constructor
  · simp
  · have hrotate : (FreeGroup.mk (w.toWord ++ [])).toWord = w.toWord := by
      simp
    rw [hrotate]
    refine ⟨?_, d.relator_mem, ?_, ?_⟩
    · calc
        w.toWord = d.rawWord := hraw.symm
        _ = d.conjugator.toWord ++ d.relator.toWord ++
            FreeGroup.invRev d.conjugator.toWord := by
              simp [RelatorConjugateWitness.rawWord, FreeGroup.toWord_inv]
    · simp [redex]
    · simp only [redex, List.length_nil]
      exact hrelatorLength

/-- A nontrivial null word with any relator certificate of area at most one
has a cyclic Dehn redex. Minimum area rules out area zero, reducing to the
one-occurrence base case above. -/
theorem cyclicGreendlinger_of_certificate_area_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (w : FreeGroup α)
    (hnull : PresentedGroup.mk (relationSet P.relators) w = 1)
    (hne : w ≠ 1)
    (certificate : RelatorCertificate P.relators w)
    (harea : certificate.area ≤ 1) :
    ∃ c, IsCyclicRedex P.relators w c := by
  let seed := MinimalAreaRelatorBoundarySeed.of_quotient_eq_one
    P.inverseClosed hnull
  have hminimum : seed.certificate.area ≤ 1 :=
    (seed.area_minimal certificate).trans harea
  have hpositive : 0 < seed.certificate.area :=
    seed.certificate.area_pos_of_ne_one hne
  have hminimumArea : seed.certificate.area = 1 := by omega
  exact seed.cyclicGreendlinger_of_area_one hminimumArea

/-- In the area-at-most-one case, the executable cyclic Dehn reducer makes a
strictly shorter result from every nontrivial null input. -/
theorem cyclicDehnReduce_norm_lt_of_certificate_area_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (w : FreeGroup α)
    (hnull : PresentedGroup.mk (relationSet P.relators) w = 1)
    (hne : w ≠ 1)
    (certificate : RelatorCertificate P.relators w)
    (harea : certificate.area ≤ 1) :
    (cyclicDehnReduce P.relators w).norm < w.norm := by
  apply cyclicDehnReduce_norm_lt_of_cyclicRedex
  exact cyclicGreendlinger_of_certificate_area_le_one
    P w hnull hne certificate harea

end GreendlingerDehn
