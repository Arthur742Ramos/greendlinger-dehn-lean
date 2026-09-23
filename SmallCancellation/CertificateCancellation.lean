import SmallCancellation.Cancellation
import SmallCancellation.Certificates

namespace GreendlingerDehn

/-- The unreduced concatenation of the reduced words of a finite list of free
group elements. -/
def rawProductWord {α : Type*} [DecidableEq α] (xs : List (FreeGroup α)) : Word α :=
  (xs.map FreeGroup.toWord).flatten

@[simp]
theorem rawProductWord_cons {α : Type*} [DecidableEq α]
    (x : FreeGroup α) (xs : List (FreeGroup α)) :
    rawProductWord (x :: xs) = x.toWord ++ rawProductWord xs := rfl

/-- An explicit witness that one factor is a conjugate of a defining relator. -/
structure RelatorConjugateWitness {α : Type*} (R : List (FreeGroup α))
    (factor : FreeGroup α) where
  conjugator : FreeGroup α
  relator : FreeGroup α
  relator_mem : relator ∈ R
  factor_eq : factor = conjugator * relator * conjugator⁻¹

/-- The literal lollipop boundary `g r g⁻¹` before free reduction. -/
def RelatorConjugateWitness.rawWord {α : Type*} [DecidableEq α]
    {R : List (FreeGroup α)} {factor : FreeGroup α}
    (d : RelatorConjugateWitness R factor) : Word α :=
  d.conjugator.toWord ++ d.relator.toWord ++ (d.conjugator⁻¹).toWord

theorem RelatorConjugateWitness.mk_rawWord {α : Type*} [DecidableEq α]
    {R : List (FreeGroup α)} {factor : FreeGroup α}
    (d : RelatorConjugateWitness R factor) :
    FreeGroup.mk d.rawWord = factor := by
  have hgr : FreeGroup.mk (d.conjugator.toWord ++ d.relator.toWord) =
      d.conjugator * d.relator := by
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  calc
    FreeGroup.mk d.rawWord =
        FreeGroup.mk (d.conjugator.toWord ++ d.relator.toWord) *
          FreeGroup.mk (d.conjugator⁻¹).toWord := by
      rw [RelatorConjugateWitness.rawWord, FreeGroup.mul_mk]
    _ = (d.conjugator * d.relator) * d.conjugator⁻¹ := by
      rw [hgr, FreeGroup.mk_toWord]
    _ = factor := d.factor_eq.symm

/-- Every explicit conjugate-relator boundary freely reduces to its canonical
free-group representative. -/
noncomputable def RelatorConjugateWitness.reductionShape {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {factor : FreeGroup α}
    (d : RelatorConjugateWitness R factor) :
    FreeReductionShape d.rawWord factor.toWord := by
  have hword : FreeGroup.mk d.rawWord = FreeGroup.mk factor.toWord := by
    rw [d.mk_rawWord, FreeGroup.mk_toWord]
  have hred := FreeGroup.reduce.sound hword
  have hnormal : FreeGroup.reduce d.rawWord = factor.toWord := by
    simpa [FreeGroup.isReduced_toWord.reduce_eq] using hred
  rw [← hnormal]
  exact FreeReductionShape.of_reduce d.rawWord

/-- Recover a typed conjugate-relator witness from the proposition that a
factor is conjugate to a defining relator. -/
noncomputable def RelatorConjugateWitness.of_isRelatorConjugate
    {α : Type*} {R : List (FreeGroup α)} {factor : FreeGroup α}
    (h : IsRelatorConjugate R factor) : RelatorConjugateWitness R factor := by
  have hn : Nonempty (RelatorConjugateWitness R factor) := by
    rcases h with ⟨g, r, hr, hfactor⟩
    exact ⟨⟨g, r, hr, hfactor⟩⟩
  exact Classical.choice hn

/-- Algebraic data for one relator-conjugate factor and its conjugating path.
This records labels and words, not a topological cell. -/
structure RelatorBalloonData {α : Type*} (R : List (FreeGroup α)) where
  factor : FreeGroup α
  label : RelatorConjugateWitness R factor

/-- Boundary word of a relator-cell occurrence with its conjugating path read
out and back. -/
def RelatorBalloonData.boundaryWord {α : Type*} [DecidableEq α]
    {R : List (FreeGroup α)} (b : RelatorBalloonData R) : Word α :=
  b.label.rawWord

theorem mk_rawProductWord_eq_prod {α : Type*} [DecidableEq α]
    (xs : List (FreeGroup α)) :
    FreeGroup.mk (rawProductWord xs) = xs.prod := by
  induction xs with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons x xs ih =>
      rw [rawProductWord_cons, List.prod_cons]
      rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, ih]

/-- The factor word of an algebraic nullity certificate: each factor is a
conjugate of a defining relator, and their product is the certified word. -/
def RelatorCertificate.rawFactorWord {α : Type*} [DecidableEq α]
    {R : List (FreeGroup α)}
    {w : FreeGroup α} (c : RelatorCertificate R w) : Word α :=
  rawProductWord c.factors

theorem RelatorCertificate.rawFactorWord_mk {α : Type*} [DecidableEq α]
    {R : List (FreeGroup α)} {w : FreeGroup α}
    (c : RelatorCertificate R w) :
    FreeGroup.mk c.rawFactorWord = w := by
  rw [RelatorCertificate.rawFactorWord, mk_rawProductWord_eq_prod]
  exact c.factors_prod

/-- A nullity certificate's relator-factor boundary freely reduces, through an
explicit nested cancellation tree, to the requested reduced word. -/
noncomputable def RelatorCertificate.factorCancellationShape {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (c : RelatorCertificate R w) :
    FreeReductionShape c.rawFactorWord w.toWord := by
  have hword : FreeGroup.mk c.rawFactorWord = FreeGroup.mk w.toWord := by
    rw [c.rawFactorWord_mk, FreeGroup.mk_toWord]
  have hred := FreeGroup.reduce.sound hword
  have hnormal : FreeGroup.reduce c.rawFactorWord = w.toWord := by
    simpa [FreeGroup.isReduced_toWord.reduce_eq] using hred
  rw [← hnormal]
  exact FreeReductionShape.of_reduce c.rawFactorWord

/-- Every null word supplies a relator-factor list together with its nested
free-cancellation tree. This is the algebraic seed for a later planar gluing
construction. -/
theorem exists_factorCancellationSeed_of_quotient_eq_one {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (h : PresentedGroup.mk (relationSet R) w = 1) :
    Nonempty (Σ c : RelatorCertificate R w,
      FreeReductionShape c.rawFactorWord w.toWord) := by
  obtain ⟨c⟩ := relatorCertificate_iff_quotient_eq_one.mpr h
  exact ⟨⟨c, c.factorCancellationShape⟩⟩

/-- The algebraic boundary data of a nullity certificate, retaining for each
factor both its relator-conjugate label and the noncrossing free cancellations
that reduce the concatenated factor words to the requested boundary word.
This is the combinatorial input needed before a planar diagram can be built. -/
structure RelatorFactorBoundarySeed {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : FreeGroup α) where
  factors : List (FreeGroup α)
  product_eq : factors.prod = w
  factor_labels : ∀ x ∈ factors, IsRelatorConjugate R x
  cancellation : FreeReductionShape (rawProductWord factors) w.toWord

/-- For any factor, its label witness exposes the literal conjugated-relator
boundary and the cancellation tree reducing that boundary to the factor word. -/
noncomputable def RelatorFactorBoundarySeed.factorLoopSeed {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) {x : FreeGroup α}
    (hx : x ∈ seed.factors) :
    Σ d : RelatorConjugateWitness R x,
      FreeReductionShape d.rawWord x.toWord := by
  let d := RelatorConjugateWitness.of_isRelatorConjugate
    (seed.factor_labels x hx)
  exact ⟨d, d.reductionShape⟩

/-- A finite ordered list of relator-conjugate factor occurrences underlying
the certificate factors. -/
noncomputable def RelatorFactorBoundarySeed.balloons {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) : List (RelatorBalloonData R) :=
  seed.factors.attach.map fun x =>
    ⟨x.1, (seed.factorLoopSeed (x := x.1) x.2).1⟩

theorem RelatorFactorBoundarySeed.balloonFactors {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    seed.balloons.map RelatorBalloonData.factor = seed.factors := by
  simp [balloons]

/-- Literal `g r g⁻¹` boundary words for all relator factors, in certificate
order. -/
noncomputable def RelatorFactorBoundarySeed.literalFactorWords {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) : List (Word α) :=
  seed.factors.attach.map fun x =>
    (seed.factorLoopSeed (x := x.1) x.2).1.rawWord

theorem RelatorFactorBoundarySeed.literalFactorWords_eq_balloons {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    seed.literalFactorWords = seed.balloons.map RelatorBalloonData.boundaryWord := by
  simp [literalFactorWords, balloons, RelatorBalloonData.boundaryWord]

/-- The literal boundary of the factor balloons is the concatenation of their
conjugator-relator-conjugator paths. -/
noncomputable def RelatorFactorBoundarySeed.literalBoundary {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) : Word α :=
  seed.literalFactorWords.flatten

/-- The factorwise conjugate-relator reductions combine into one nested
reduction from literal balloon boundaries to the certificate's raw factor
words. -/
noncomputable def RelatorFactorBoundarySeed.literalFactors_reduce
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    FreeReductionShape seed.literalBoundary (rawProductWord seed.factors) := by
  let raw : {x // x ∈ seed.factors} → Word α := fun x =>
    (seed.factorLoopSeed (x := x.1) x.2).1.rawWord
  let canonical : {x // x ∈ seed.factors} → Word α := fun x => x.1.toWord
  have h := FreeReductionShape.flatten_map seed.factors.attach raw canonical
    (by
      intro x hx
      exact (seed.factorLoopSeed (x := x.1) x.2).2)
  simpa [literalBoundary, literalFactorWords, rawProductWord, raw, canonical,
    List.attach_map_val] using h

/-- All literal conjugate-relator boundaries in a nullity certificate freely
reduce to the requested boundary word. This is a finite algebraic precursor to
the planar van Kampen diagram construction. -/
noncomputable def RelatorFactorBoundarySeed.to_boundaryReduction
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
  FreeCancellationSequence seed.literalBoundary w.toWord :=
  (seed.literalFactors_reduce.to_cancellationSequence).trans
    seed.cancellation.to_cancellationSequence

theorem RelatorFactorBoundarySeed.literalBoundary_mk
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    FreeGroup.mk seed.literalBoundary = w := by
  rw [seed.to_boundaryReduction.sound, FreeGroup.mk_toWord]

theorem RelatorFactorBoundarySeed.total_cancellation_count
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    seed.literalBoundary.length = w.toWord.length + 2 *
      (seed.literalFactors_reduce.cancellationCount +
        seed.cancellation.cancellationCount) := by
  have hlocal := seed.literalFactors_reduce.length_eq_cancellationCount
  have hglobal := seed.cancellation.length_eq_cancellationCount
  omega

/-- Replay the seed's nested proof in a concrete order of adjacent cancellations. -/
noncomputable def RelatorFactorBoundarySeed.boundaryReduction {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    FreeCancellationSequence (rawProductWord seed.factors) w.toWord :=
  seed.cancellation.to_cancellationSequence

theorem RelatorFactorBoundarySeed.boundaryReduction_preserves_word
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    FreeGroup.mk (rawProductWord seed.factors) = FreeGroup.mk w.toWord :=
  seed.boundaryReduction.sound

/-- Presented-group nullity supplies relator-conjugate factors together with
an explicit cancellation tree for their boundary concatenation. -/
noncomputable def RelatorFactorBoundarySeed.of_quotient_eq_one {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (hinv : ∀ r ∈ R, r⁻¹ ∈ R)
    (h : PresentedGroup.mk (relationSet R) w = 1) :
    RelatorFactorBoundarySeed R w := by
  let c : RelatorCertificate R w :=
    Classical.choice (relatorCertificate_iff_quotient_eq_one.mpr h)
  exact ⟨c.factors, c.factors_prod,
    c.factors_are_conjugates hinv, c.factorCancellationShape⟩

/-- A boundary seed paired with a relator certificate of minimum area. This
retains the algebraic minimality needed to rule out cancellable face pairs in
a later diagram construction. -/
structure MinimalAreaRelatorBoundarySeed {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : FreeGroup α) where
  certificate : RelatorCertificate R w
  area_minimal : ∀ c : RelatorCertificate R w, certificate.area ≤ c.area
  boundary : RelatorFactorBoundarySeed R w
  boundary_factors : boundary.factors = certificate.factors

/-- Every quotient-null word has a boundary seed coming from a minimum-area
relator certificate. -/
noncomputable def MinimalAreaRelatorBoundarySeed.of_quotient_eq_one
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (hinv : ∀ r ∈ R, r⁻¹ ∈ R)
    (h : PresentedGroup.mk (relationSet R) w = 1) :
    MinimalAreaRelatorBoundarySeed R w := by
  have hcert : Nonempty (RelatorCertificate R w) :=
    relatorCertificate_iff_quotient_eq_one.mpr h
  have hexists : ∃ c : RelatorCertificate R w,
      ∀ d : RelatorCertificate R w, c.area ≤ d.area :=
    RelatorCertificate.exists_minimum_area hcert
  let c : RelatorCertificate R w := Classical.choose hexists
  have hmin : ∀ d : RelatorCertificate R w, c.area ≤ d.area :=
    Classical.choose_spec hexists
  let boundary : RelatorFactorBoundarySeed R w :=
    ⟨c.factors, c.factors_prod, c.factors_are_conjugates hinv,
      c.factorCancellationShape⟩
  exact ⟨c, hmin, boundary, rfl⟩

theorem MinimalAreaRelatorBoundarySeed.factorOccurrenceCount_eq_area
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed R w) :
    seed.boundary.balloons.length = seed.certificate.area := by
  calc
    seed.boundary.balloons.length = seed.boundary.factors.length := by
      simp [RelatorFactorBoundarySeed.balloons]
    _ = seed.certificate.factors.length := by rw [seed.boundary_factors]
    _ = seed.certificate.area := RelatorCertificate.factors_length seed.certificate

/-- The boundary seed gives a concrete cancellation sequence, hence an exact
count of how many inverse-letter pairs are removed. -/
theorem RelatorFactorBoundarySeed.cancellation_count {α : Type*}
    [DecidableEq α] {R : List (FreeGroup α)} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed R w) :
    (rawProductWord seed.factors).length =
      w.toWord.length + 2 * seed.cancellation.cancellationCount :=
  seed.cancellation.length_eq_cancellationCount

end GreendlingerDehn
