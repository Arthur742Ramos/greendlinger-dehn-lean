import SmallCancellation.PairFoldVertexLink

namespace GreendlingerDehn

/-- A finite multigraph presentation keeps edge occurrences distinct, even if
two corners happen to have the same pair of endpoint darts. -/
structure FiniteIncidenceMultigraph where
  Vertex : Type
  Edge : Type
  source : Edge → Vertex
  target : Edge → Vertex

/-- The two endpoint incidences of every edge occurrence, retaining both
ends even when the multigraph has parallel edges or loops. -/
abbrev FiniteIncidenceMultigraph.Endpoint (G : FiniteIncidenceMultigraph) :=
  G.Edge × Bool

/-- The vertex touched by one endpoint incidence. -/
def FiniteIncidenceMultigraph.endpointVertex
    (G : FiniteIncidenceMultigraph) (endpoint : G.Endpoint) : G.Vertex :=
  if endpoint.2 then G.target endpoint.1 else G.source endpoint.1

/-- Incidence degree counts corner endpoints, not merely neighboring vertices;
parallel corners therefore contribute separately. -/
noncomputable def FiniteIncidenceMultigraph.degree
    (G : FiniteIncidenceMultigraph) [Fintype G.Edge]
    (v : G.Vertex)
    [Fintype {endpoint : G.Endpoint // G.endpointVertex endpoint = v}] : Nat :=
  Fintype.card {endpoint : G.Endpoint // G.endpointVertex endpoint = v}

/-- Summing incidence degrees counts the two endpoints of every edge
occurrence exactly once. -/
theorem FiniteIncidenceMultigraph.sum_degree_eq_two_mul_edge_card
    (G : FiniteIncidenceMultigraph) [Fintype G.Vertex] [Fintype G.Edge]
    [DecidableEq G.Vertex]
    [∀ v, Fintype {endpoint : G.Endpoint // G.endpointVertex endpoint = v}] :
    (∑ v : G.Vertex, G.degree v) = 2 * Fintype.card G.Edge := by
  classical
  let fibersEquiv :
      (Σ v : G.Vertex, {endpoint : G.Endpoint // G.endpointVertex endpoint = v}) ≃
        G.Endpoint :=
    { toFun := fun x => x.2.1
      invFun := fun endpoint => ⟨G.endpointVertex endpoint, ⟨endpoint, rfl⟩⟩
      left_inv := by
        rintro ⟨v, ⟨endpoint, h⟩⟩
        cases h
        rfl
      right_inv := by intro endpoint; rfl }
  calc
    (∑ v : G.Vertex, G.degree v) =
        Fintype.card
          (Σ v : G.Vertex, {endpoint : G.Endpoint //
            G.endpointVertex endpoint = v}) := by
      simp [FiniteIncidenceMultigraph.degree, Fintype.card_sigma]
    _ = Fintype.card G.Endpoint := Fintype.card_congr fibersEquiv
    _ = 2 * Fintype.card G.Edge := by
      simp [FiniteIncidenceMultigraph.Endpoint, Fintype.card_prod,
        Fintype.card_bool, Nat.mul_comm]

/-- For a finite loopless or loopy incidence multigraph whose degree is at
most two, the number of corner edges cannot exceed the number of edge ends. -/
theorem FiniteIncidenceMultigraph.edge_card_le_vertex_card_of_degree_le_two
    (G : FiniteIncidenceMultigraph) [Fintype G.Vertex] [Fintype G.Edge]
    [DecidableEq G.Vertex]
    [∀ v, Fintype {endpoint : G.Endpoint // G.endpointVertex endpoint = v}]
    (hdegree : ∀ v, G.degree v ≤ 2) :
    Fintype.card G.Edge ≤ Fintype.card G.Vertex := by
  have hupper : (∑ v : G.Vertex, G.degree v) ≤
      ∑ _v : G.Vertex, 2 :=
    Finset.sum_le_sum fun v _ => hdegree v
  rw [G.sum_degree_eq_two_mul_edge_card] at hupper
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hupper
  have hupper' : 2 * Fintype.card G.Edge ≤ 2 * Fintype.card G.Vertex := by
    nlinarith [hupper]
  omega

private theorem reducedWord_consecutive_not_inverse
    {α : Type*} {word : Word α} (hred : FreeGroup.IsReduced word)
    (i : Nat) (hi : i + 1 < word.length) :
    word[i] ≠ inverseLetter word[i + 1] := by
  change List.IsChain
    (fun a b : Letter α => a.1 = b.1 → a.2 = b.2) word at hred
  rw [List.isChain_iff_getElem] at hred
  have hadj := hred i hi
  intro hinv
  have hgen : (word[i]).1 = (word[i + 1]).1 := by
    have h := congrArg Prod.fst hinv
    simpa [inverseLetter] using h
  have hbit := hadj hgen
  have hflip : (word[i]).2 = !(word[i + 1]).2 := by
    have h := congrArg Prod.snd hinv
    simpa [inverseLetter] using h
  cases hb : (word[i + 1]).2 <;> simp_all

private theorem cyclicReducedWord_last_not_inverse_head
    {α : Type*} {word : Word α} (hcyc : FreeGroup.IsCyclicallyReduced word)
    (hne : word ≠ []) :
    word.getLast hne ≠ inverseLetter (word.head hne) := by
  have hlast : word.getLast hne ∈ word.getLast? := by
    simp [List.getLast?_eq_getLast_of_ne_nil hne]
  have hhead : word.head hne ∈ word.head? := by
    rw [List.head?_eq_some_head hne]
    simp
  intro hinv
  have hgen : (word.getLast hne).1 = (word.head hne).1 := by
    have h := congrArg Prod.fst hinv
    simpa [inverseLetter] using h
  have hbit := hcyc.2 _ hlast _ hhead hgen
  have hflip : (word.getLast hne).2 = !(word.head hne).2 := by
    have h := congrArg Prod.snd hinv
    simpa [inverseLetter] using h
  cases hb : (word.head hne).2 <;> simp_all

/-- An oriented edge end at one quotient vertex of the folded complex. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldVertexLinkDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :=
  {d : seed.pairFoldFiniteGraph.toDartGraph.Dart //
    seed.pairFoldFiniteGraph.toDartGraph.source d = v}

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldVertexLinkDartFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    Fintype (seed.PairFoldVertexLinkDart hne v) := by
  classical
  letI : Fintype seed.pairFoldFiniteGraph.toDartGraph.Dart := by
    change Fintype seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Dart
    exact seed.pairFoldDartFintype
  letI : Finite (seed.PairFoldVertexLinkDart hne v) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- One occurrence of a relator polygon corner at the selected quotient
vertex, indexed by the side immediately following the corner. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldFaceCornerAtVertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :=
  {side : seed.RelatorSideOccurrence //
    seed.pairFoldFaceGermVertex hne (side, false) = v}

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerAtVertexFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    Fintype (seed.PairFoldFaceCornerAtVertex hne v) := by
  classical
  letI := seed.pairFoldRelatorSideOccurrenceFintype
  letI : Finite (seed.PairFoldFaceCornerAtVertex hne v) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Send a face-endpoint germ to the outgoing dart of its incident edge at the
same quotient vertex. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    seed.PairFoldVertexLinkDart hne v := by
  classical
  let G := seed.pairFoldFiniteGraph.toDartGraph
  let d := seed.pairFoldFiniteIncidenceDart hne (Sum.inl germ.1.1)
  cases hend : germ.1.2
  · refine ⟨G.reverse d, ?_⟩
    have hv := seed.pairFoldFaceGermVertex_eq_incidenceEndpoint hne germ.1
    rw [hend] at hv
    calc
      G.source (G.reverse d) = G.target d := G.source_reverse d
      _ = seed.pairFoldFaceGermVertex hne germ.1 := hv.symm
      _ = v := germ.2
  · refine ⟨d, ?_⟩
    have hv := seed.pairFoldFaceGermVertex_eq_incidenceEndpoint hne germ.1
    rw [hend] at hv
    exact hv.symm.trans germ.2

private theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart_label_source
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (side : seed.RelatorSideOccurrence)
    (hv : seed.pairFoldFaceGermVertex hne (side, false) = v) :
    seed.pairFoldFiniteGraph.label
      (seed.pairFoldFaceGermOutDart hne ⟨(side, false), hv⟩).val =
        (seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2] := by
  let d := seed.pairFoldFiniteIncidenceDart hne (Sum.inl side)
  have hd : seed.pairFoldFiniteGraph.label d =
      inverseLetter
        ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2]) := by
    calc
      _ = seed.boundaryOccurrenceDartPairFold.graph.label
          (seed.pairFoldIncidenceDart (Sum.inl side)) :=
        seed.pairFoldFiniteIncidenceDart_label hne (Sum.inl side)
      _ = _ := seed.pairFoldIncidenceDart_label_side side
  change seed.pairFoldFiniteGraph.label
    (seed.pairFoldFiniteGraph.toDartGraph.reverse d) = _
  rw [seed.pairFoldFiniteGraph.label_reverse, hd, inverseLetter_inverseLetter]

private theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart_label_target
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (side : seed.RelatorSideOccurrence)
    (hv : seed.pairFoldFaceGermVertex hne (side, true) = v) :
    seed.pairFoldFiniteGraph.label
      (seed.pairFoldFaceGermOutDart hne ⟨(side, true), hv⟩).val =
        inverseLetter
          ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2]) := by
  exact seed.pairFoldFiniteIncidenceDart_label hne (Sum.inl side) |>.trans
    (seed.pairFoldIncidenceDart_label_side side)

private noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkDartEdgeClass
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {hne : w ≠ 1} {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (d : seed.PairFoldVertexLinkDart hne v) : seed.PairFoldEdgeClass :=
  Quotient.mk (UnorientedDartSetoid
    seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) d.1

private theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart_edgeClass
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    seed.pairFoldCellLinkDartEdgeClass
        (seed.pairFoldFaceGermOutDart hne germ) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl germ.1.1) := by
  rcases germ with ⟨⟨side, endpoint⟩, hv⟩
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
  let raw := seed.boundaryOccurrenceDartPairFold.hom.mapDart
    (seed.relatorSideOccurrencePosition side, false)
  have hinc :
      seed.pairFoldFiniteIncidenceDart hne (Sum.inl side) = G.reverse raw := by
    simp [MinimalAreaRelatorBoundarySeed.pairFoldFiniteIncidenceDart,
      MinimalAreaRelatorBoundarySeed.pairFoldFiniteHom,
      MinimalAreaRelatorBoundarySeed.pairFoldFiniteGraph,
      LabelledDartGraph.endpointRestrictionHom,
      MinimalAreaRelatorBoundarySeed.pairFoldIncidenceDart_side, raw, G]
    rfl
  have hreverseRaw :
      seed.pairFoldFiniteGraph.toDartGraph.reverse raw = G.reverse raw := rfl
  cases endpoint
  · have hout :
      (seed.pairFoldFaceGermOutDart hne ⟨(side, false), hv⟩).1 = raw := by
      simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart,
        hinc, raw, G]
      rw [← hreverseRaw]
      exact seed.pairFoldFiniteGraph.toDartGraph.reverse_involutive raw
    change Quotient.mk (UnorientedDartSetoid G)
        (seed.pairFoldFaceGermOutDart hne ⟨(side, false), hv⟩).1 =
      Quotient.mk (UnorientedDartSetoid G) raw
    rw [hout]
  · have hout :
        (seed.pairFoldFaceGermOutDart hne ⟨(side, true), hv⟩).1 = G.reverse raw := by
      simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart,
        hinc, raw, G]
    change Quotient.mk (UnorientedDartSetoid G)
        (seed.pairFoldFaceGermOutDart hne ⟨(side, true), hv⟩).1 =
      Quotient.mk (UnorientedDartSetoid G) raw
    rw [hout]
    exact unorientedDartClass_eq_of_reverse (G := G) rfl

private theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteGraph_reverse_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (d : seed.PairFoldVertexLinkDart hne v) :
    seed.pairFoldFiniteGraph.toDartGraph.reverse d.1 ≠ d.1 := by
  intro h
  have hlabel := congrArg seed.pairFoldFiniteGraph.label h
  rw [seed.pairFoldFiniteGraph.label_reverse] at hlabel
  cases hl : seed.pairFoldFiniteGraph.label d.1 with
  | mk generator sign =>
      simp [hl, inverseLetter] at hlabel

private theorem letter_ne_inverseLetter {α : Type*} (a : Letter α) :
    a ≠ inverseLetter a := by
  cases a with
  | mk generator sign => cases sign <;> simp [inverseLetter]

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDartFiberFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (d : seed.PairFoldVertexLinkDart hne v) :
    Fintype {germ : seed.PairFoldFaceGermsAtVertex hne v //
      seed.pairFoldFaceGermOutDart hne germ = d} := by
  classical
  letI := seed.pairFoldFaceGermsAtVertexFintype hne v
  letI : Finite {germ : seed.PairFoldFaceGermsAtVertex hne v //
      seed.pairFoldFaceGermOutDart hne germ = d} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The face-endpoint germs at one vertex that name a fixed oriented edge end
inject into the exact two-incidence ledger. Thus at most two face germs can
map to the same edge end. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart_fiber_card_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    [Fintype (seed.PairFoldFaceGermsAtVertex hne v)]
    (d : seed.PairFoldVertexLinkDart hne v)
    (hexists : ∃ germ : seed.PairFoldFaceGermsAtVertex hne v,
      seed.pairFoldFaceGermOutDart hne germ = d) :
    Fintype.card
      {germ : seed.PairFoldFaceGermsAtVertex hne v //
        seed.pairFoldFaceGermOutDart hne germ = d} ≤ 2 := by
  classical
  let germ0 := Classical.choose hexists
  have hgerm0 := Classical.choose_spec hexists
  let edgeClass := seed.pairFoldCellLinkDartEdgeClass d
  have hclassD : edgeClass =
      seed.pairFoldIncidenceEdgeClass (Sum.inl germ0.1.1) := by
    calc
      edgeClass = seed.pairFoldCellLinkDartEdgeClass
          (seed.pairFoldFaceGermOutDart hne germ0) :=
        congrArg seed.pairFoldCellLinkDartEdgeClass hgerm0.symm
      _ = seed.pairFoldIncidenceEdgeClass (Sum.inl germ0.1.1) :=
        seed.pairFoldFaceGermOutDart_edgeClass hne germ0
  let usedEdge : seed.PairFoldUsedEdge :=
    ⟨edgeClass, ⟨Sum.inl germ0.1.1, hclassD.symm⟩⟩
  letI := seed.pairFoldIncidenceFiberFintype usedEdge.1
  let germFiber := {germ : seed.PairFoldFaceGermsAtVertex hne v //
    seed.pairFoldFaceGermOutDart hne germ = d}
  let incidenceFiber := seed.PairFoldIncidenceFiber usedEdge.1
  let f : germFiber → incidenceFiber := fun x =>
    ⟨Sum.inl x.1.1.1, by
      calc
        seed.pairFoldIncidenceEdgeClass (Sum.inl x.1.1.1) =
            seed.pairFoldCellLinkDartEdgeClass
              (seed.pairFoldFaceGermOutDart hne x.1) :=
          (seed.pairFoldFaceGermOutDart_edgeClass hne x.1).symm
        _ = seed.pairFoldCellLinkDartEdgeClass d :=
          congrArg seed.pairFoldCellLinkDartEdgeClass x.2
        _ = usedEdge.1 := rfl⟩
  have hf : Function.Injective f := by
    intro x y hxy
    rcases x with ⟨⟨⟨sideX, endX⟩, hvX⟩, houtX⟩
    rcases y with ⟨⟨⟨sideY, endY⟩, hvY⟩, houtY⟩
    have hside : sideX = sideY := Sum.inl.inj (congrArg Subtype.val hxy)
    subst sideY
    cases endX <;> cases endY
    · apply Subtype.ext
      apply Subtype.ext
      rfl
    · have heq := houtX.trans houtY.symm
      have heqD :
          seed.pairFoldFiniteGraph.toDartGraph.reverse
              (seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideX)) =
            seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideX) := by
        simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart] using
          congrArg Subtype.val heq
      exact False.elim ((seed.pairFoldFiniteGraph_reverse_ne hne
        (seed.pairFoldFaceGermOutDart hne ⟨(sideX, true), hvY⟩)) heqD)
    · have heq := houtX.trans houtY.symm
      have heqD :
          seed.pairFoldFiniteGraph.toDartGraph.reverse
              (seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideX)) =
            seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideX) := by
        simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart] using
          (congrArg Subtype.val heq).symm
      exact False.elim ((seed.pairFoldFiniteGraph_reverse_ne hne
        (seed.pairFoldFaceGermOutDart hne ⟨(sideX, true), hvX⟩)) heqD)
    · apply Subtype.ext
      apply Subtype.ext
      rfl
  have hcard : Fintype.card incidenceFiber = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact seed.pairFoldIncidenceFiber_card_eq_two usedEdge
  have hle := Fintype.card_le_of_injective f hf
  simpa [germFiber, incidenceFiber, hcard] using hle

/-- The two endpoint germs identified across a face-shared folded edge name
the same oriented edge end in the actual finite quotient graph. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermOutDart_eq_of_edgeStep
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (a b : seed.PairFoldFaceGermsAtVertex hne v)
    (h : seed.PairFoldFaceEdgeStepAtVertex hne a b) :
    seed.pairFoldFaceGermOutDart hne a =
      seed.pairFoldFaceGermOutDart hne b := by
  classical
  rcases a with ⟨⟨sideA, endpointA⟩, ha⟩
  rcases b with ⟨⟨sideB, endpointB⟩, hb⟩
  change seed.PairFoldFaceEdgeStep (sideA, endpointA) (sideB, endpointB) at h
  rcases h with ⟨⟨hsideNe, hEdge⟩, hendpointNe⟩
  let edge := seed.pairFoldIncidenceEdgeClass (Sum.inl sideA)
  let incidenceA : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideA, rfl⟩
  let incidenceB : seed.PairFoldIncidenceFiber edge :=
    ⟨Sum.inl sideB, hEdge.symm⟩
  have hincidenceNe : incidenceA ≠ incidenceB := by
    intro heq
    apply hsideNe
    exact Sum.inl.inj (congrArg Subtype.val heq)
  have hop := seed.pairFoldFiniteIncidenceDart_opposite_of_ne
    hne edge incidenceA incidenceB hincidenceNe
  let G := seed.pairFoldFiniteGraph.toDartGraph
  let dartA := seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideA)
  let dartB := seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideB)
  have hop' : dartB = G.reverse dartA := by
    simpa [dartA, dartB, incidenceA, incidenceB] using hop
  cases endpointA <;> cases endpointB
  · simp at hendpointNe
  · apply Subtype.ext
    change G.reverse dartA = dartB
    exact hop'.symm
  · apply Subtype.ext
    change dartA = G.reverse dartB
    calc
      dartA = G.reverse (G.reverse dartA) :=
        (G.reverse_involutive dartA).symm
      _ = G.reverse dartB := congrArg G.reverse hop'.symm
  · simp at hendpointNe

/-- The two edge ends of the corner immediately preceding a side and the side
itself. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerEndDarts
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (corner : seed.PairFoldFaceCornerAtVertex hne v) :
    seed.PairFoldVertexLinkDart hne v × seed.PairFoldVertexLinkDart hne v := by
  let nextGerm : seed.PairFoldFaceGermsAtVertex hne v :=
    ⟨(corner.1, false), corner.2⟩
  have hprev : seed.pairFoldFaceGermVertex hne
      (seed.pairFoldFaceCornerMate (corner.1, false)) = v := by
    exact (seed.pairFoldFaceCornerMate_vertex hne (corner.1, false)).trans
      corner.2
  let prevGerm : seed.PairFoldFaceGermsAtVertex hne v :=
    ⟨seed.pairFoldFaceCornerMate (corner.1, false), hprev⟩
  exact (seed.pairFoldFaceGermOutDart hne prevGerm,
    seed.pairFoldFaceGermOutDart hne nextGerm)

/-- The cell-link multigraph has all outgoing edge ends as vertices and one
distinct edge for each incident relator corner. This is the combinatorial link
incidence data before its components are classified. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    FiniteIncidenceMultigraph where
  Vertex := seed.PairFoldVertexLinkDart hne v
  Edge := seed.PairFoldFaceCornerAtVertex hne v
  source := fun corner => (seed.pairFoldFaceCornerEndDarts hne corner).1
  target := fun corner => (seed.pairFoldFaceCornerEndDarts hne corner).2

/-- One endpoint incidence of a corner edge, retaining parallel corner edges
as separate occurrences. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldCellLinkEndpoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :=
  (seed.PairFoldFaceCornerAtVertex hne v) × Bool

/-- The oriented edge end incident to one specified corner endpoint. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (endpoint : seed.PairFoldCellLinkEndpoint hne v) :
    seed.PairFoldVertexLinkDart hne v :=
  if endpoint.2 then
    (seed.pairFoldCellLinkAt hne v).target endpoint.1
  else
    (seed.pairFoldCellLinkAt hne v).source endpoint.1

/-- Identify a corner-end incidence with its face-endpoint germ. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointGerm
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (endpoint : seed.PairFoldCellLinkEndpoint hne v) :
    seed.PairFoldFaceGermsAtVertex hne v := by
  rcases endpoint with ⟨corner, which⟩
  cases which
  · have hprev : seed.pairFoldFaceGermVertex hne
        (seed.pairFoldFaceCornerMate (corner.1, false)) = v := by
      exact (seed.pairFoldFaceCornerMate_vertex hne (corner.1, false)).trans
        corner.2
    exact ⟨seed.pairFoldFaceCornerMate (corner.1, false), hprev⟩
  · exact ⟨(corner.1, false), corner.2⟩

private noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkGermToEndpoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    seed.PairFoldCellLinkEndpoint hne v := by
  rcases germ with ⟨⟨side, endpoint⟩, hv⟩
  cases endpoint
  · exact (⟨⟨side, hv⟩, true⟩)
  · have hnext : seed.pairFoldFaceGermVertex hne
        (seed.pairFoldFaceCornerMate (side, true)) = v := by
      exact (seed.pairFoldFaceCornerMate_vertex hne (side, true)).trans hv
    exact (⟨⟨seed.pairFoldFaceSideNext side, by
      simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate] using hnext⟩,
      false⟩)

private noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointGermEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex} :
    seed.PairFoldCellLinkEndpoint hne v ≃
      seed.PairFoldFaceGermsAtVertex hne v where
  toFun := seed.pairFoldCellLinkEndpointGerm hne
  invFun := seed.pairFoldCellLinkGermToEndpoint hne
  left_inv := by
    intro endpoint
    rcases endpoint with ⟨corner, which⟩
    cases which <;>
      simp [pairFoldCellLinkGermToEndpoint,
        pairFoldCellLinkEndpointGerm,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate]
  right_inv := by
    intro germ
    rcases germ with ⟨⟨side, endpoint⟩, hv⟩
    cases endpoint <;>
      apply Subtype.ext <;>
      simp [pairFoldCellLinkGermToEndpoint,
        pairFoldCellLinkEndpointGerm,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev,
        MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate]

private theorem MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointDart_eq_germ
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (endpoint : seed.PairFoldCellLinkEndpoint hne v) :
    seed.pairFoldCellLinkEndpointDart hne endpoint =
      seed.pairFoldFaceGermOutDart hne
        (seed.pairFoldCellLinkEndpointGerm hne endpoint) := by
  rcases endpoint with ⟨corner, which⟩
  cases which <;>
    simp [pairFoldCellLinkEndpointDart,
      pairFoldCellLinkEndpointGerm,
      pairFoldCellLinkAt,
      pairFoldFaceCornerEndDarts]

private noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointFiberEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (d : seed.PairFoldVertexLinkDart hne v) :
    {endpoint : seed.PairFoldCellLinkEndpoint hne v //
      seed.pairFoldCellLinkEndpointDart hne endpoint = d} ≃
    {germ : seed.PairFoldFaceGermsAtVertex hne v //
      seed.pairFoldFaceGermOutDart hne germ = d} where
  toFun := fun endpoint => ⟨
    seed.pairFoldCellLinkEndpointGerm hne endpoint.1,
    (seed.pairFoldCellLinkEndpointDart_eq_germ hne endpoint.1).symm.trans endpoint.2⟩
  invFun := fun germ => ⟨
    seed.pairFoldCellLinkGermToEndpoint hne germ.1,
    (seed.pairFoldCellLinkEndpointDart_eq_germ hne
      (seed.pairFoldCellLinkGermToEndpoint hne germ.1)).trans
      ((congrArg (seed.pairFoldFaceGermOutDart hne)
        ((seed.pairFoldCellLinkEndpointGermEquiv hne).apply_symm_apply germ.1)).trans
        germ.2)⟩
  left_inv := by
    intro endpoint
    apply Subtype.ext
    exact (seed.pairFoldCellLinkEndpointGermEquiv hne).symm_apply_apply endpoint.1
  right_inv := by
    intro germ
    apply Subtype.ext
    exact (seed.pairFoldCellLinkEndpointGermEquiv hne).apply_symm_apply germ.1

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointFiberFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (d : seed.PairFoldVertexLinkDart hne v) :
    Fintype {endpoint : seed.PairFoldCellLinkEndpoint hne v //
      seed.pairFoldCellLinkEndpointDart hne endpoint = d} := by
  classical
  letI : Fintype (seed.PairFoldCellLinkEndpoint hne v) := inferInstance
  letI : Finite {endpoint : seed.PairFoldCellLinkEndpoint hne v //
      seed.pairFoldCellLinkEndpointDart hne endpoint = d} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The corner-incidence multigraph has degree at most two at each oriented
edge end. Its corner-end incidences biject with face germs, and the exact
two-incidence edge ledger bounds each germ fiber. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt_degree_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (d : (seed.pairFoldCellLinkAt hne v).Vertex) :
    @Fintype.card
      {endpoint : seed.PairFoldCellLinkEndpoint hne v //
        seed.pairFoldCellLinkEndpointDart hne endpoint = d}
      (seed.pairFoldCellLinkEndpointFiberFintype hne d) ≤ 2 := by
  classical
  let endpointFiber := {endpoint : seed.PairFoldCellLinkEndpoint hne v //
    seed.pairFoldCellLinkEndpointDart hne endpoint = d}
  let germFiber := {germ : seed.PairFoldFaceGermsAtVertex hne v //
    seed.pairFoldFaceGermOutDart hne germ = d}
  letI : Fintype endpointFiber :=
    seed.pairFoldCellLinkEndpointFiberFintype hne d
  letI : Fintype germFiber :=
    seed.pairFoldFaceGermOutDartFiberFintype hne d
  by_cases hexists : ∃ germ : seed.PairFoldFaceGermsAtVertex hne v,
      seed.pairFoldFaceGermOutDart hne germ = d
  · calc
      Fintype.card endpointFiber = Fintype.card germFiber :=
        Fintype.card_congr (seed.pairFoldCellLinkEndpointFiberEquiv hne d)
      _ ≤ 2 := by
        simpa only [germFiber] using
          seed.pairFoldFaceGermOutDart_fiber_card_le_two hne d hexists
  · have hempty : ∀ endpoint : endpointFiber, False := by
      intro endpoint
      apply hexists
      refine ⟨seed.pairFoldCellLinkEndpointGerm hne endpoint.1, ?_⟩
      exact (seed.pairFoldCellLinkEndpointDart_eq_germ hne endpoint.1).symm.trans
        endpoint.2
    letI : IsEmpty endpointFiber := ⟨hempty⟩
    simp [endpointFiber]

/-- At every quotient vertex the number of relator corners is at most the
number of oriented edge ends. This is the finite handshaking identity applied
to the loopless local incidence multigraph and its degree bound. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt_corner_card_le_dart_card
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    @Fintype.card (seed.PairFoldFaceCornerAtVertex hne v)
      (seed.pairFoldFaceCornerAtVertexFintype hne v) ≤
    @Fintype.card (seed.PairFoldVertexLinkDart hne v)
      (seed.pairFoldVertexLinkDartFintype hne v) := by
  classical
  let G := seed.pairFoldCellLinkAt hne v
  letI : Fintype G.Vertex := seed.pairFoldVertexLinkDartFintype hne v
  letI : Fintype G.Edge := seed.pairFoldFaceCornerAtVertexFintype hne v
  letI : ∀ d : G.Vertex,
      Fintype {endpoint : G.Endpoint // G.endpointVertex endpoint = d} := by
    intro d
    exact seed.pairFoldCellLinkEndpointFiberFintype hne d
  have hdegree : ∀ d : G.Vertex, G.degree d ≤ 2 := by
    intro d
    simpa [G, FiniteIncidenceMultigraph.degree,
      FiniteIncidenceMultigraph.endpointVertex,
      MinimalAreaRelatorBoundarySeed.pairFoldCellLinkEndpointDart,
      MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt] using
        seed.pairFoldCellLinkAt_degree_le_two hne d
  exact G.edge_card_le_vertex_card_of_degree_le_two hdegree

/-- Every relator corner joins two distinct edge ends. A loop in this link
would make adjacent relator letters inverse, including the cyclic basepoint
corner; reducedness and cyclic reduction exclude both cases. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerEndDarts_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (corner : seed.PairFoldFaceCornerAtVertex hne v) :
    (seed.pairFoldFaceCornerEndDarts hne corner).1 ≠
      (seed.pairFoldFaceCornerEndDarts hne corner).2 := by
  let side := corner.1
  let prev := seed.pairFoldFaceSidePrev side
  intro heq
  have hlabels := congrArg
    (fun d : seed.PairFoldVertexLinkDart hne v =>
      seed.pairFoldFiniteGraph.label d.1) heq
  have hcurrent :
      seed.pairFoldFiniteGraph.label
          (seed.pairFoldFaceGermOutDart hne
            ⟨(side, false), corner.2⟩).val =
        (seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2] :=
    seed.pairFoldFaceGermOutDart_label_source hne side corner.2
  have hprevVertex :
      seed.pairFoldFaceGermVertex hne (prev, true) = v := by
    have h := seed.pairFoldFaceCornerMate_vertex hne (side, false)
    simpa [prev, MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate] using h.trans corner.2
  have hprevious :
      seed.pairFoldFiniteGraph.label
          (seed.pairFoldFaceGermOutDart hne
            ⟨(prev, true), hprevVertex⟩).val =
        inverseLetter
          ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord[prev.2]) := by
    dsimp [prev, MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev]
    exact seed.pairFoldFaceGermOutDart_label_target hne _ hprevVertex
  have hletter :
      (seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2] =
        inverseLetter
          ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord[prev.2]) := by
    change seed.pairFoldFiniteGraph.label
        (seed.pairFoldFaceGermOutDart hne ⟨(prev, true), hprevVertex⟩).val = _
      at hlabels
    change _ = seed.pairFoldFiniteGraph.label
        (seed.pairFoldFaceGermOutDart hne ⟨(side, false), corner.2⟩).val
      at hlabels
    rw [hprevious, hcurrent] at hlabels
    exact hlabels.symm
  have hrelatorMem :
      (seed.boundary.reducedBalloons.get side.1).label.relator ∈ P.relators :=
    (seed.boundary.reducedBalloons.get side.1).label.relator_mem
  let hword := (seed.boundary.reducedBalloons.get side.1).label.relator.toWord
  by_cases hzero : side.2.val = 0
  · have hlenNat :
        0 < (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length := by
      have hbound := side.2.isLt
      omega
    have hlast : prev.2.val + 1 = hword.length := by
      change (cyclicPrevFin side.2).val + 1 =
        (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length
      have hsub := Nat.sub_add_cancel
        (show 1 ≤ (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length
          by omega)
      simpa [cyclicPrevFin, hzero] using hsub
    have hlen : 0 < hword.length := by
      simpa [hword] using hlenNat
    have hneWord : hword ≠ [] := by
      exact List.ne_nil_of_length_pos hlen
    have hhead : hword[side.2] = hword.head hneWord := by
      rw [List.head_eq_getElem_zero hneWord]
      simp [Fin.getElem_fin, hzero]
    have hprevVal : prev.2.val = hword.length - 1 := by omega
    have hprevLast : hword[prev.2] = hword.getLast (by
        exact hneWord) := by
      rw [List.getLast_eq_getElem hneWord]
      simp [Fin.getElem_fin, hprevVal]
    have hrot := congrArg inverseLetter hletter
    have hrot' : hword[prev.2] = inverseLetter (hword[side.2]) := by
      simpa only [inverseLetter_inverseLetter] using hrot.symm
    have hlastInv : hword.getLast (by
        exact hneWord) = inverseLetter (hword.head hneWord) := by
      calc
        hword.getLast hneWord = hword[prev.2] := hprevLast.symm
        _ = inverseLetter (hword[side.2]) := hrot'
        _ = inverseLetter (hword.head hneWord) := congrArg inverseLetter hhead
    exact (cyclicReducedWord_last_not_inverse_head
      (P.relator_isCyclicallyReduced hrelatorMem)
      hneWord) hlastInv
  · have hpositive : 0 < side.2.val := by omega
    have hidx : prev.2.val + 1 = side.2.val := by
      simp [prev, MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev,
        cyclicPrevFin, hpositive]
      omega
    have hred := reducedWord_consecutive_not_inverse
      (FreeGroup.isReduced_toWord : FreeGroup.IsReduced
        ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord))
      prev.2.val (by omega)
    have hreverse :
        (seed.boundary.reducedBalloons.get side.1).label.relator.toWord[prev.2] =
          inverseLetter
            ((seed.boundary.reducedBalloons.get side.1).label.relator.toWord[side.2]) := by
      have h := congrArg inverseLetter hletter
      simpa only [inverseLetter_inverseLetter] using h.symm
    apply hred
    simpa [Fin.getElem_fin, hidx] using hreverse

/-- The local finite cell link has no loop edges: a polygon corner always
joins the two distinct edge ends of its adjacent relator sides. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt_loopless
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex)
    (corner : (seed.pairFoldCellLinkAt hne v).Edge) :
    (seed.pairFoldCellLinkAt hne v).source corner ≠
      (seed.pairFoldCellLinkAt hne v).target corner := by
  exact seed.pairFoldFaceCornerEndDarts_ne hne corner

@[simp]
theorem MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt_vertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    (seed.pairFoldCellLinkAt hne v).Vertex =
      seed.PairFoldVertexLinkDart hne v := rfl

@[simp]
theorem MinimalAreaRelatorBoundarySeed.pairFoldCellLinkAt_edge
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    (seed.pairFoldCellLinkAt hne v).Edge =
      seed.PairFoldFaceCornerAtVertex hne v := rfl

end GreendlingerDehn
