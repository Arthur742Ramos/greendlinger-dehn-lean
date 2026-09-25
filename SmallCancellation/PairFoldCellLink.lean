import SmallCancellation.PairFoldVertexLink

namespace GreendlingerDehn

/-- A finite multigraph presentation keeps edge occurrences distinct, even if
two corners happen to have the same pair of endpoint darts. -/
structure FiniteIncidenceMultigraph where
  Vertex : Type
  Edge : Type
  source : Edge → Vertex
  target : Edge → Vertex

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
