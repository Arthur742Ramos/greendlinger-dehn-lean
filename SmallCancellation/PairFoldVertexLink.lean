import SmallCancellation.PairFoldFiniteComplex

namespace GreendlingerDehn

/-- The local face-link graph at one vertex of the direct pair-fold complex.
Its vertices are relator-side endpoint germs. An adjacency either passes
around a polygon corner or across an edge with two face-side incidences. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkGraph
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    SimpleGraph (seed.PairFoldFaceGermsAtVertex hne v) :=
  SimpleGraph.fromRel fun a b =>
    seed.pairFoldFaceCornerMateAtVertex hne a = b ∨
      seed.PairFoldFaceEdgeStepAtVertex hne a b

@[simp]
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkGraph_adj_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex)
    (a b : seed.PairFoldFaceGermsAtVertex hne v) :
    (seed.pairFoldFaceLinkGraph hne v).Adj a b ↔
      seed.pairFoldFaceCornerMateAtVertex hne a = b ∨
        seed.PairFoldFaceEdgeStepAtVertex hne a b := by
  change (SimpleGraph.fromRel (fun a b =>
    seed.pairFoldFaceCornerMateAtVertex hne a = b ∨
      seed.PairFoldFaceEdgeStepAtVertex hne a b)).Adj a b ↔ _
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (h | h) | (h | h)⟩
    · exact Or.inl h
    · exact Or.inr h
    · left
      calc
        seed.pairFoldFaceCornerMateAtVertex hne a =
            seed.pairFoldFaceCornerMateAtVertex hne
              (seed.pairFoldFaceCornerMateAtVertex hne b) :=
          congrArg (seed.pairFoldFaceCornerMateAtVertex hne) h.symm
        _ = b := seed.pairFoldFaceCornerMateAtVertex_involutive hne b
    · exact Or.inr (seed.pairFoldFaceEdgeStepAtVertex_symm hne h)
  · rintro (h | h)
    · refine ⟨?_, Or.inl (Or.inl h)⟩
      intro hab
      exact seed.pairFoldFaceCornerMateAtVertex_ne hne a
        (h.trans hab.symm)
    · refine ⟨?_, Or.inl (Or.inr h)⟩
      intro hab
      exact h.1.1 (congrArg Prod.fst (congrArg Subtype.val hab))

/-- Every face-endpoint germ has its polygon-corner neighbor in the local
link graph. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkGraph_corner_adj
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    [Fintype (seed.PairFoldFaceGermsAtVertex hne v)]
    (a : seed.PairFoldFaceGermsAtVertex hne v) :
    (seed.pairFoldFaceLinkGraph hne v).Adj a
      (seed.pairFoldFaceCornerMateAtVertex hne a) := by
  apply (seed.pairFoldFaceLinkGraph_adj_iff hne v a _).2
  exact Or.inl rfl

/-- An across-edge partner is exactly an additional local-link neighbor. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkGraph_edge_adj
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    {a b : seed.PairFoldFaceGermsAtVertex hne v}
    (h : seed.PairFoldFaceEdgeStepAtVertex hne a b) :
    (seed.pairFoldFaceLinkGraph hne v).Adj a b := by
  apply (seed.pairFoldFaceLinkGraph_adj_iff hne v a b).2
  exact Or.inr h

/-- Edge-partner uniqueness says there is at most one neighbor of the second
kind at any endpoint germ. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkGraph_edge_neighbor_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    {a b c : seed.PairFoldFaceGermsAtVertex hne v}
    (hb : seed.PairFoldFaceEdgeStepAtVertex hne a b)
    (hc : seed.PairFoldFaceEdgeStepAtVertex hne a c) : b = c :=
  seed.pairFoldFaceEdgeStepAtVertex_unique hne hb hc

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkNeighborFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex)
    (a : seed.PairFoldFaceGermsAtVertex hne v) :
    Fintype ((seed.pairFoldFaceLinkGraph hne v).neighborSet a) := by
  classical
  letI := seed.pairFoldFaceGermsAtVertexFintype hne v
  letI : Finite ((seed.pairFoldFaceLinkGraph hne v).neighborSet a) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The local link graph has degree at most two: a germ has one polygon-corner
neighbor and at most one neighbor across its folded edge. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceLinkGraph_degree_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (a : seed.PairFoldFaceGermsAtVertex hne v) :
    ((seed.pairFoldFaceLinkGraph hne v).neighborFinset a).card ≤ 2 := by
  classical
  let corner := seed.pairFoldFaceCornerMateAtVertex hne a
  let across := seed.pairFoldFaceEdgeMateAtVertex? hne a
  let G := seed.pairFoldFaceLinkGraph hne v
  have hsubset : G.neighborFinset a ⊆ insert corner across.toFinset := by
    intro b hb
    have hadj : G.Adj a b := by
      exact (G.mem_neighborFinset (v := a) b).mp hb
    rcases (seed.pairFoldFaceLinkGraph_adj_iff hne v a b).mp hadj with
      hcorner | hedge
    · exact Finset.mem_insert.mpr (Or.inl (by
        simpa [corner] using hcorner.symm))
    · have hmate := seed.pairFoldFaceEdgeMateAtVertex?_of_edgeStep hne a b hedge
      exact Finset.mem_insert.mpr (Or.inr (by
        simp [across, hmate]))
  have hacross : across.toFinset.card ≤ 1 := by
    cases across <;> simp
  have hcard : (insert corner across.toFinset).card ≤ 2 := by
    calc
      (insert corner across.toFinset).card ≤ across.toFinset.card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add_right hacross 1
      _ = 2 := by omega
  exact (Finset.card_le_card hsubset).trans hcard

end GreendlingerDehn
