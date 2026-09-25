import SmallCancellation.FoldedBoundarySeed
import Mathlib.Data.Fintype.BigOperators

namespace GreendlingerDehn

/-- The directly shortened boundary walk is carried by exactly the same graph
used by the global pair-fold incidence ledger. -/
theorem MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairReducedWalk_graph
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    seed.boundaryOccurrenceDartPairReducedWalk.graph =
      seed.boundaryOccurrenceDartPairFold.graph := by
  rfl

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

/-- The face-side occurrence type counts every relator side of every indexed
balloon exactly once. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldRelatorSideOccurrence_card
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Nat.card seed.RelatorSideOccurrence =
      ∑ i : Fin seed.boundary.reducedBalloons.length,
        ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length) := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card
      (Σ i : Fin seed.boundary.reducedBalloons.length,
        Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) = _
  rw [Fintype.card_sigma]
  simp

/-- Surviving boundary occurrences are in bijection with the letters of the
reduced target word. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldBoundaryOccurrence_card
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Nat.card seed.PairFoldBoundaryOccurrence = w.toWord.length := by
  classical
  let trace := seed.reducedLollipopBoundaryTrace
  let positions := trace.survivorOccurrences.map Prod.fst
  let positionFinset := positions.toFinset
  letI := seed.pairFoldBoundaryOccurrenceFintype
  letI : Fintype positionFinset := Fintype.ofFinite _
  let positionEquiv : positionFinset ≃
      seed.PairFoldBoundaryOccurrence :=
    { toFun := fun p => by
        refine ⟨⟨p.1, ?_⟩, ?_⟩
        · have hfinset : p.1 ∈ positions.toFinset := p.2
          have hmem : p.1 ∈ positions := List.mem_toFinset.mp hfinset
          rcases List.mem_map.mp hmem with ⟨o, ho, hposition⟩
          have hbound := trace.survivors_inBounds o ho
          omega
        · change p.1 ∈ positions
          exact List.mem_toFinset.mp p.2
      invFun := fun i =>
        ⟨i.1.1, List.mem_toFinset.mpr i.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        rfl }
  calc
    Nat.card seed.PairFoldBoundaryOccurrence =
        Fintype.card seed.PairFoldBoundaryOccurrence := Nat.card_eq_fintype_card
    _ = Fintype.card positionFinset :=
      Fintype.card_congr positionEquiv.symm
    _ = positionFinset.card := Fintype.card_coe positionFinset
    _ = positions.length :=
      List.toFinset_card_of_nodup trace.survivorPositions_nodup
    _ = trace.survivorOccurrences.length := by simp [positions]
    _ = w.toWord.length := trace.survivors_length

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

/-- Give each incidence its orientation in the assembled diagram. Face sides
are reversed because their induced boundary orientation opposes the exterior
boundary; surviving exterior occurrences retain their boundary orientation. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (x : seed.PairFoldIncidence) :
    seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Dart :=
  match x with
  | Sum.inl side =>
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side, false))
  | Sum.inr boundary =>
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (boundary.1, false)

@[simp] theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_side
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    seed.pairFoldIncidenceDart (Sum.inl side) =
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side, false)) := rfl

@[simp] theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_boundary
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (boundary : seed.PairFoldBoundaryOccurrence) :
    seed.pairFoldIncidenceDart (Sum.inr boundary) =
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (boundary.1, false) := rfl

/-- The face orientation of an incidence dart reads the inverse of the
relator's positive boundary letter. This keeps the face-side label explicit
after all stem and cancellation folds have been assembled. -/
@[simp] theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_label_side
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    seed.boundaryOccurrenceDartPairFold.graph.label
        (seed.pairFoldIncidenceDart (Sum.inl side)) =
      inverseLetter ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2]) := by
  let embedding := LabelledGraphHom.comp seed.balloonBoundaryHom
    (reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons side.1)
  let balloon := seed.boundary.reducedBalloons.get side.1
  have hlabel :
      (wordBoundaryGraphWithJoins seed.boundary.reducedLiteralBoundary
        seed.balloonEndpointPairs).label
        (embedding.mapDart (balloon.relatorSideDart side.2)) =
          balloon.label.relator.toWord[side.2] := by
    rw [embedding.map_label]
    exact balloon.relatorSideDart_label side.2
  have hposition :
      (seed.relatorSideOccurrencePosition side, false) =
        embedding.mapDart (balloon.relatorSideDart side.2) := by
    apply Prod.ext
    · rfl
    · have hdirection := reducedBalloonOccurrencePathEmbedding_direction
        seed.boundary.reducedBalloons side.1 (balloon.relatorSideDart side.2)
      change false = (((fun d => d) ∘
        (reducedBalloonOccurrencePathEmbedding
          seed.boundary.reducedBalloons side.1).mapDart)
        (balloon.relatorSideDart side.2)).2
      rw [Function.comp_apply]
      exact hdirection.symm
  calc
    seed.boundaryOccurrenceDartPairFold.graph.label
        (seed.pairFoldIncidenceDart (Sum.inl side)) =
        inverseLetter
          (seed.boundaryOccurrenceDartPairFold.graph.label
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side, false))) := by
      rw [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_side,
        seed.boundaryOccurrenceDartPairFold.graph.label_reverse]
    _ = inverseLetter
        ((wordBoundaryGraphWithJoins seed.boundary.reducedLiteralBoundary
          seed.balloonEndpointPairs).label
          (seed.relatorSideOccurrencePosition side, false)) := by
      exact congrArg inverseLetter
        ((seed.boundaryOccurrenceDartPairFold.hom).map_label
          (seed.relatorSideOccurrencePosition side, false))
    _ = inverseLetter
        (balloon.label.relator.toWord[side.2]) := by
      rw [hposition, hlabel]

/-- The flattened boundary dart for a relator-side occurrence is the image of
that exact occurrence under its indexed balloon embedding. -/
theorem MinimalAreaRelatorBoundarySeed.relatorSideOccurrencePosition_dart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    (seed.relatorSideOccurrencePosition side, false) =
      (LabelledGraphHom.comp seed.balloonBoundaryHom
        (reducedBalloonOccurrencePathEmbedding
          seed.boundary.reducedBalloons side.1)).mapDart
        ((seed.boundary.reducedBalloons.get side.1).relatorSideDart side.2) := by
  let embedding := LabelledGraphHom.comp seed.balloonBoundaryHom
    (reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons side.1)
  let balloon := seed.boundary.reducedBalloons.get side.1
  apply Prod.ext
  · rfl
  · have hdirection := reducedBalloonOccurrencePathEmbedding_direction
      seed.boundary.reducedBalloons side.1 (balloon.relatorSideDart side.2)
    change false = (((fun d => d) ∘
      (reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons side.1).mapDart)
      (balloon.relatorSideDart side.2)).2
    rw [Function.comp_apply]
    exact hdirection.symm

/-- The image position of a dart on a relator polygon inside its stored
conjugate-relator boundary. -/
def ReducedRelatorBalloonData.relatorPathDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (d : Fin b.label.relator.toWord.length × Bool) :
    (wordPathGraph b.label.rawWord).toDartGraph.Dart := by
  exact (⟨⟨b.label.conjugator.toWord.length + d.1.val, by
    rw [b.label.rawWord_length_eq]
    omega⟩, d.2⟩)

@[simp] theorem ReducedRelatorBalloonData.relatorPathDart_forward
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
    b.relatorPathDart (j, false) = b.relatorSideDart j := by
  apply Prod.ext
  · apply Fin.ext
    simp [ReducedRelatorBalloonData.relatorPathDart,
      ReducedRelatorBalloonData.relatorSideDart_index]
  · rfl

/-- The relator polygon embeds, with its exact side positions and labels, into
the raw boundary of its indexed balloon. -/
noncomputable def ReducedRelatorBalloonData.relatorPathHom
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P) :
    LabelledGraphHom (wordPathGraph b.label.relator.toWord)
      (wordPathGraph b.label.rawWord) where
  mapVertex := fun v => by
    change Nat at v
    exact b.label.conjugator.toWord.length + v
  mapDart := b.relatorPathDart
  map_reverse := by
    intro d
    change Fin b.label.relator.toWord.length × Bool at d
    rcases d with ⟨j, direction⟩
    cases direction <;>
      simp [ReducedRelatorBalloonData.relatorPathDart, wordPathGraph]
  map_source := by
    intro d
    change Fin b.label.relator.toWord.length × Bool at d
    rcases d with ⟨j, direction⟩
    cases direction <;>
      simp [wordPathGraph, ReducedRelatorBalloonData.relatorPathDart] <;> omega
  map_target := by
    intro d
    change Fin b.label.relator.toWord.length × Bool at d
    rcases d with ⟨j, direction⟩
    cases direction <;>
      simp [wordPathGraph, ReducedRelatorBalloonData.relatorPathDart] <;> omega
  map_label := by
    intro d
    change Fin b.label.relator.toWord.length × Bool at d
    rcases d with ⟨j, direction⟩
    have hforward : (wordPathGraph b.label.rawWord).label
        (b.relatorPathDart (j, false)) = b.label.relator.toWord[j] := by
      rw [b.relatorPathDart_forward]
      exact b.relatorSideDart_label j
    cases direction
    · simpa [wordPathGraph] using hforward
    · change (wordPathGraph b.label.rawWord).label
        (b.relatorPathDart (j, true)) =
          inverseLetter (b.label.relator.toWord[j])
      have hreverse : b.relatorPathDart (j, true) =
          (wordPathGraph b.label.rawWord).toDartGraph.reverse
            (b.relatorPathDart (j, false)) := by
        simp [ReducedRelatorBalloonData.relatorPathDart, wordPathGraph]
      rw [hreverse, (wordPathGraph b.label.rawWord).label_reverse, hforward]

@[simp] theorem ReducedRelatorBalloonData.relatorPathHom_mapDart_forward
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
    b.relatorPathHom.mapDart (j, false) = b.relatorSideDart j := by
  change b.relatorPathDart (j, false) = b.relatorSideDart j
  exact b.relatorPathDart_forward j

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

/-- The two incidence records over one folded edge carry opposite dart
orientations. The side orientation is chosen to be opposite to its raw
relator traversal, including the case where a side survives on the exterior
boundary at the same source position. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_opposite_of_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass)
    (a b : seed.PairFoldIncidenceFiber e) (hne : a ≠ b) :
    let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
    seed.pairFoldIncidenceDart b.1 = G.reverse (seed.pairFoldIncidenceDart a.1) := by
  classical
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have hab : a ≠ b := by
    intro hab
    apply hne
    apply Subtype.ext
    exact hab
  have hclass : seed.pairFoldIncidenceEdgeClass a =
      seed.pairFoldIncidenceEdgeClass b := ha.trans hb.symm
  cases a with
  | inl sideA =>
      cases b with
      | inl sideB =>
          change seed.pairFoldEdgeClassAt
              (seed.relatorSideOccurrencePosition sideA) =
            seed.pairFoldEdgeClassAt
              (seed.relatorSideOccurrencePosition sideB) at hclass
          have hposNe : seed.relatorSideOccurrencePosition sideA ≠
              seed.relatorSideOccurrencePosition sideB := by
            intro hpos
            have hside : sideA = sideB :=
              seed.relatorSideOccurrencePosition_injective hpos
            exact hab (congrArg Sum.inl hside)
          have hstemA : seed.balloonStemOccurrencePairing.partner
              (seed.relatorSideOccurrencePosition sideA) = none := by
            apply (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint _).2
            exact seed.relatorSidePosition_unmatched_by_stem sideA.1 sideA.2
          have hstemB : seed.balloonStemOccurrencePairing.partner
              (seed.relatorSideOccurrencePosition sideB) = none := by
            apply (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint _).2
            exact seed.relatorSidePosition_unmatched_by_stem sideB.1 sideB.2
          have hdir := seed.mapDart_reverse_of_edgeClass_eq_stemUnpaired
            (seed.relatorSideOccurrencePosition sideA)
            (seed.relatorSideOccurrencePosition sideB)
            hclass hposNe hstemA hstemB
          simp [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart, hdir]
      | inr boundaryB =>
          change seed.pairFoldEdgeClassAt
              (seed.relatorSideOccurrencePosition sideA) =
            seed.pairFoldEdgeClassAt boundaryB.1 at hclass
          by_cases hpos : seed.relatorSideOccurrencePosition sideA = boundaryB.1
          · have hinv :=
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse_involutive
            simpa [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart, hpos] using
              (hinv (seed.boundaryOccurrenceDartPairFold.hom.mapDart
                (boundaryB.1, false))).symm
          · have hstemA : seed.balloonStemOccurrencePairing.partner
                (seed.relatorSideOccurrencePosition sideA) = none := by
              apply (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint _).2
              exact seed.relatorSidePosition_unmatched_by_stem sideA.1 sideA.2
            have hcancelB : seed.boundaryCancellationPairing.partner boundaryB.1 = none :=
              (seed.boundaryCancellationPairing_unpaired_iff_survivor boundaryB.1).2
                boundaryB.2
            have hdir := seed.mapDart_eq_of_edgeClass_eq_stemToBoundary
              (seed.relatorSideOccurrencePosition sideA) boundaryB.1
              hclass hpos hstemA hcancelB
            have hinv :=
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse_involutive
            simpa [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart] using
              hdir.trans (hinv _).symm
  | inr boundaryA =>
      cases b with
      | inl sideB =>
          change seed.pairFoldEdgeClassAt boundaryA.1 =
            seed.pairFoldEdgeClassAt
              (seed.relatorSideOccurrencePosition sideB) at hclass
          by_cases hpos : boundaryA.1 = seed.relatorSideOccurrencePosition sideB
          · simp [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart, hpos]
          · have hcancelA : seed.boundaryCancellationPairing.partner boundaryA.1 = none :=
              (seed.boundaryCancellationPairing_unpaired_iff_survivor boundaryA.1).2
                boundaryA.2
            have hstemB : seed.balloonStemOccurrencePairing.partner
                (seed.relatorSideOccurrencePosition sideB) = none := by
              apply (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint _).2
              exact seed.relatorSidePosition_unmatched_by_stem sideB.1 sideB.2
            have hdir := seed.mapDart_eq_of_edgeClass_eq_boundaryToStem
              boundaryA.1 (seed.relatorSideOccurrencePosition sideB)
              hclass hpos hcancelA hstemB
            simpa [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart] using
              congrArg G.reverse hdir
      | inr boundaryB =>
          change seed.pairFoldEdgeClassAt boundaryA.1 =
            seed.pairFoldEdgeClassAt boundaryB.1 at hclass
          have hposNe : boundaryA.1 ≠ boundaryB.1 := by
            intro hpos
            have hboundary : boundaryA = boundaryB := Subtype.ext hpos
            exact hab (congrArg Sum.inr hboundary)
          have hcancelA : seed.boundaryCancellationPairing.partner boundaryA.1 = none :=
            (seed.boundaryCancellationPairing_unpaired_iff_survivor boundaryA.1).2
              boundaryA.2
          have hcancelB : seed.boundaryCancellationPairing.partner boundaryB.1 = none :=
            (seed.boundaryCancellationPairing_unpaired_iff_survivor boundaryB.1).2
              boundaryB.2
          have hdir := seed.mapDart_reverse_of_edgeClass_eq_boundaryUnpaired
            boundaryA.1 boundaryB.1 hclass hposNe hcancelA hcancelB
          simpa [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart] using hdir

/-- Relator letters on the two face-side incidences of one folded edge are
inverse. This is the one-letter compatibility required to extend a shared
edge to a common piece arc. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSideLetters_inverse
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (sideA sideB : seed.RelatorSideOccurrence)
    (hEdge : seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideB))
    (hne : sideA ≠ sideB) :
    (seed.boundary.reducedBalloons.get sideB.1).label.relator.toWord[sideB.2] =
      inverseLetter
        ((seed.boundary.reducedBalloons.get sideA.1).label.relator.toWord[sideA.2]) := by
  let edge := seed.pairFoldIncidenceEdgeClass (Sum.inl sideA)
  let a : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideA, rfl⟩
  let b : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideB, hEdge.symm⟩
  have hab : a ≠ b := by
    intro h
    apply hne
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hop := seed.pairFoldIncidenceDart_opposite_of_ne edge a b hab
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
  have hop' : seed.pairFoldIncidenceDart (Sum.inl sideB) =
      G.reverse (seed.pairFoldIncidenceDart (Sum.inl sideA)) := by
    simpa [a, b, G] using hop
  have hlabels := congrArg seed.boundaryOccurrenceDartPairFold.graph.label hop'
  rw [seed.boundaryOccurrenceDartPairFold.graph.label_reverse] at hlabels
  simp only [MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_label_side]
    at hlabels
  have h := congrArg inverseLetter hlabels
  simpa [inverseLetter] using h

/-- A shared face-side edge is a one-letter piece once the corresponding
inverse relator rotations are distinct. The final premise is the precise
local dipole exclusion required from a reduced diagram. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSide_singletonPiece_of_noDipole
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (sideA sideB : seed.RelatorSideOccurrence)
    (hEdge : seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideB))
    (hne : sideA ≠ sideB)
    (preA tailA preB tailB : Word α)
    (hcutA :
      (seed.boundary.reducedBalloons.get sideA.1).label.relator.toWord =
        preA ++
          ((seed.boundary.reducedBalloons.get sideA.1).label.relator.toWord[sideA.2] ::
            tailA))
    (hcutB :
      (seed.boundary.reducedBalloons.get sideB.1).label.relator⁻¹.toWord =
        preB ++
          (inverseLetter
              ((seed.boundary.reducedBalloons.get sideB.1).label.relator.toWord[sideB.2]) ::
            tailB))
    (hnoDipole : ∀ r s, r ∈ P.relators → s ∈ P.relators →
      r.toWord =
        (seed.boundary.reducedBalloons.get sideA.1).label.relator.toWord[sideA.2] ::
          (tailA ++ preA) →
      s.toWord =
        (seed.boundary.reducedBalloons.get sideA.1).label.relator.toWord[sideA.2] ::
          (tailB ++ preB) → r ≠ s) :
    IsPiece P.relators
      [(seed.boundary.reducedBalloons.get sideA.1).label.relator.toWord[sideA.2]] := by
  let relatorA := (seed.boundary.reducedBalloons.get sideA.1).label.relator
  let relatorB := (seed.boundary.reducedBalloons.get sideB.1).label.relator
  let letter := relatorA.toWord[sideA.2]
  have hletter : relatorB.toWord[sideB.2] = inverseLetter letter :=
    seed.pairFoldFaceSideLetters_inverse sideA sideB hEdge hne
  obtain ⟨rotatedA, hrotatedA, hwordA⟩ :=
    P.rotateRelator
      (seed.boundary.reducedBalloons.get sideA.1).label.relator_mem hcutA
  have hinverseB : relatorB⁻¹ ∈ P.relators :=
    P.inverseClosed relatorB
      (seed.boundary.reducedBalloons.get sideB.1).label.relator_mem
  obtain ⟨rotatedB, hrotatedB, hwordB⟩ :=
    P.rotateRelator hinverseB hcutB
  have hheadA : rotatedA.toWord = letter :: (tailA ++ preA) := by
    simpa [letter, relatorA, List.append_assoc] using hwordA
  have hletter' : inverseLetter (relatorB.toWord[sideB.2]) = letter := by
    rw [hletter]
    simp [letter, relatorA, inverseLetter]
  have hheadB : rotatedB.toWord = letter :: (tailB ++ preB) := by
    calc
      rotatedB.toWord =
          (inverseLetter (relatorB.toWord[sideB.2]) :: tailB) ++ preB := hwordB
      _ = letter :: (tailB ++ preB) := by rw [hletter']; rfl
  have hdistinct := hnoDipole rotatedA rotatedB hrotatedA hrotatedB hheadA hheadB
  exact IsPiece.singleton_of_distinctRelators_commonHead
    hrotatedA hrotatedB hdistinct hheadA hheadB

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

/-- The total relator perimeter and reduced boundary length are the two sides
of the global folded edge-incidence count. -/
theorem MinimalAreaRelatorBoundarySeed.pairFold_totalPerimeter_add_boundaryLength_eq_two_mul_usedEdges
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    (∑ i : Fin seed.boundary.reducedBalloons.length,
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length) +
        w.toWord.length =
      2 * Nat.card seed.PairFoldUsedEdge := by
  calc
    _ = Nat.card seed.RelatorSideOccurrence +
        Nat.card seed.PairFoldBoundaryOccurrence := by
      rw [← seed.pairFoldRelatorSideOccurrence_card,
        ← seed.pairFoldBoundaryOccurrence_card]
    _ = Nat.card seed.PairFoldIncidence := by
      change Nat.card seed.RelatorSideOccurrence +
        Nat.card seed.PairFoldBoundaryOccurrence =
          Nat.card (seed.RelatorSideOccurrence ⊕
            seed.PairFoldBoundaryOccurrence)
      rw [Nat.card_sum]
    _ = 2 * Nat.card seed.PairFoldUsedEdge :=
      seed.pairFoldIncidence_count_eq_two_mul_usedEdges

end GreendlingerDehn
