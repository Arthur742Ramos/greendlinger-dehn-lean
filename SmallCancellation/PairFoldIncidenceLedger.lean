import SmallCancellation.FoldedBoundarySeed
import Mathlib.Data.Fintype.BigOperators

namespace GreendlingerDehn

/-- A surviving occurrence in the reduced target boundary. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldBoundaryOccurrence
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  {i : Fin seed.boundary.reducedLiteralBoundary.length //
    i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst}

/-- The two kinds of occurrences counted by the pair-fold incidence ledger. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  seed.RelatorSideOccurrence ⊕ seed.PairFoldBoundaryOccurrence

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldBoundaryOccurrenceFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.PairFoldBoundaryOccurrence := by
  classical
  letI : Finite seed.PairFoldBoundaryOccurrence :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldRelatorSideOccurrenceFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.RelatorSideOccurrence := by
  classical
  change Fintype (Σ i : Fin seed.boundary.reducedBalloons.length,
    Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length))
  infer_instance

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldIncidenceFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.PairFoldIncidence := inferInstance

/-- Send a face-side or surviving-boundary occurrence to its folded
unoriented edge. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldIncidenceEdgeClass
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (x : seed.PairFoldIncidence) : seed.PairFoldEdgeClass :=
  match x with
  | Sum.inl side =>
      seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side)
  | Sum.inr boundary => seed.pairFoldEdgeClassAt boundary.1

/-- The incidence occurrences lying over one folded edge. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldIncidenceFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) :=
  {x : seed.PairFoldIncidence // seed.pairFoldIncidenceEdgeClass x = e}

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldIncidenceFiberFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) :
    Fintype (seed.PairFoldIncidenceFiber e) := by
  classical
  letI : Finite (seed.PairFoldIncidenceFiber e) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Splitting the incidence fiber by its two constructors recovers the
relator-side and boundary-occurrence fibers. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldIncidenceFiberEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) :
    seed.PairFoldIncidenceFiber e ≃
      seed.pairFoldRelatorSideFiber e ⊕ seed.pairFoldBoundaryFiber e := by
  classical
  refine
    { toFun := fun x => by
        rcases x with ⟨incidence, hclass⟩
        cases incidence with
        | inl side =>
            apply Sum.inl
            exact ⟨side, by
              simpa [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceEdgeClass]
                using hclass⟩
        | inr boundary =>
            apply Sum.inr
            exact ⟨boundary.1, boundary.2, by
              simpa [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceEdgeClass]
                using hclass⟩
      invFun := fun x =>
        match x with
        | Sum.inl side => ⟨Sum.inl side.1, side.2⟩
        | Sum.inr boundary =>
            ⟨Sum.inr ⟨boundary.1, boundary.2.1⟩, boundary.2.2⟩
      left_inv := by
        intro x
        rcases x with ⟨x, hx⟩
        cases x <;> rfl
      right_inv := by
        intro x
        rcases x with side | boundary
        · rfl
        · rfl }

/-- A folded edge class is used when at least one relator side or surviving
target-boundary occurrence represents it. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldUsedEdge
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  {e : seed.PairFoldEdgeClass //
    ∃ x : seed.PairFoldIncidence, seed.pairFoldIncidenceEdgeClass x = e}

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldDartFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Dart := by
  classical
  letI : Fintype seed.balloonBoundaryGraph.toDartGraph.Dart := by
    change Fintype
      (Fin seed.boundary.reducedLiteralBoundary.length × Bool)
    infer_instance
  have hfinite :
      Finite seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Dart := by
    change Finite
      (WalkFoldResult.foldPairs
        (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)
        seed.balloonBoundaryLoop).graph.toDartGraph.Dart
    exact Finite.of_surjective
      (WalkFoldResult.foldPairs
        (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)
        seed.balloonBoundaryLoop).hom.mapDart
      (WalkFoldResult.foldPairs
        (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)
        seed.balloonBoundaryLoop).hom_surjective
  letI : Finite seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Dart :=
    hfinite
  exact Fintype.ofFinite _

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.PairFoldEdgeClass := by
  classical
  letI := seed.pairFoldDartFintype
  letI : Finite seed.PairFoldEdgeClass :=
    Finite.of_surjective
      (fun d => Quotient.mk (UnorientedDartSetoid
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) d)
      Quotient.mk_surjective
  exact Fintype.ofFinite _

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldUsedEdgeFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.PairFoldUsedEdge := by
  classical
  letI := seed.pairFoldEdgeClassFintype
  letI : Finite seed.PairFoldUsedEdge :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceFiber_card_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldUsedEdge) :
    Nat.card (seed.PairFoldIncidenceFiber e.1) = 2 := by
  classical
  obtain ⟨incidence, hincidence⟩ := e.2
  have hsum : Nat.card (seed.pairFoldRelatorSideFiber e.1) +
      Nat.card (seed.pairFoldBoundaryFiber e.1) = 2 := by
    rcases incidence with side | boundary
    · have h := seed.pairFoldIncidenceCount_eq_two_of_relatorSide side
      change seed.pairFoldEdgeClassAt
        (seed.relatorSideOccurrencePosition side) = e.1 at hincidence
      rw [hincidence] at h
      exact h
    · have h := seed.pairFoldIncidenceCount_eq_two_of_boundary
        boundary.1 boundary.2
      change seed.pairFoldEdgeClassAt boundary.1 = e.1 at hincidence
      rw [hincidence] at h
      exact h
  calc
    Nat.card (seed.PairFoldIncidenceFiber e.1) =
        Nat.card (seed.pairFoldRelatorSideFiber e.1 ⊕
          seed.pairFoldBoundaryFiber e.1) :=
      Nat.card_congr (seed.pairFoldIncidenceFiberEquiv e.1)
    _ = _ := by rw [Nat.card_sum]; exact hsum

/-- The complete face-side/boundary incidence ledger contains exactly two
flags for every quotient edge that it reaches. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidence_count_eq_two_mul_usedEdges
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Nat.card seed.PairFoldIncidence = 2 * Nat.card seed.PairFoldUsedEdge := by
  classical
  letI := seed.pairFoldRelatorSideOccurrenceFintype
  letI := seed.pairFoldBoundaryOccurrenceFintype
  letI := seed.pairFoldIncidenceFintype
  letI := seed.pairFoldDartFintype
  letI := seed.pairFoldEdgeClassFintype
  letI := seed.pairFoldUsedEdgeFintype
  let fiber := fun e : seed.PairFoldUsedEdge =>
    seed.PairFoldIncidenceFiber e.1
  let sigmaEquiv : seed.PairFoldIncidence ≃ Σ e : seed.PairFoldUsedEdge, fiber e :=
    { toFun := fun x =>
        ⟨⟨seed.pairFoldIncidenceEdgeClass x, ⟨x, rfl⟩⟩, ⟨x, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := by intro x; rfl
      right_inv := by
        rintro ⟨⟨e, ⟨x, hx⟩⟩, ⟨y, hy⟩⟩
        dsimp at hx hy ⊢
        cases hy
        rfl }
  calc
    Nat.card seed.PairFoldIncidence = Nat.card (Σ e : seed.PairFoldUsedEdge, fiber e) :=
      Nat.card_congr sigmaEquiv
    _ = ∑ e : seed.PairFoldUsedEdge, Nat.card (fiber e) := by
      rw [Nat.card_sigma]
    _ = ∑ _e : seed.PairFoldUsedEdge, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      have h := seed.pairFoldIncidenceFiber_card_eq_two e
      simpa [fiber] using h
    _ = 2 * Nat.card seed.PairFoldUsedEdge := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _

end GreendlingerDehn
