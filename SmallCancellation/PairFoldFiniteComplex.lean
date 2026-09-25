import SmallCancellation.PairFoldRelatorLoops

namespace GreendlingerDehn

/-- The direct pair-fold graph restricted to vertices incident to a dart. The
occurrence-path quotient has unused natural-number vertices; this finite
support graph keeps the same darts and all edge classes. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteGraph
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) := by
  letI := seed.pairFoldDartFintype
  exact seed.boundaryOccurrenceDartPairFold.graph.endpointRestriction

/-- Map the direct quotient into its finite support graph. The nontrivial
reduced boundary supplies an incident dart for the endpoint restriction. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteHom
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :
    LabelledGraphHom seed.boundaryOccurrenceDartPairFold.graph
      seed.pairFoldFiniteGraph := by
  classical
  letI := seed.pairFoldDartFintype
  have hword : w.toWord ≠ [] := by
    intro hnil
    exact hne (FreeGroup.toWord_eq_nil_iff.mp hnil)
  have hdart : Nonempty
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Dart :=
    LabelledWalk.exists_dart_of_word_ne_nil
      seed.boundaryOccurrenceDartPairReducedWalk.walk hword
  exact seed.boundaryOccurrenceDartPairFold.graph.endpointRestrictionHom hdart

/-- The target boundary remains a closed walk in the finite support graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteBoundaryWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :=
  seed.boundaryOccurrenceDartPairReducedWalk.walk.map
    (seed.pairFoldFiniteHom hne)

/-- The image of the joined boundary's initial vertex in the finite graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteBasepoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :
    seed.pairFoldFiniteGraph.toDartGraph.Vertex :=
  (seed.pairFoldFiniteHom hne).mapVertex
    (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
      (Quotient.mk (BoundaryVertexJoinSetoid
        seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs) 0))

/-- Every vertex in the finite pair-fold graph is reachable from the boundary
basepoint. This confirms that the finite face and boundary walks share one
connected 1-skeleton. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteVertex_reachable
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    ∃ word, Nonempty (LabelledWalk seed.pairFoldFiniteGraph
      (seed.pairFoldFiniteBasepoint hne) v word) := by
  classical
  letI := seed.pairFoldDartFintype
  obtain ⟨d, hd⟩ :=
    seed.boundaryOccurrenceDartPairFold.graph.activeVertex_incident v
  have hsource : ∃ e,
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source e = v.1 := by
    rcases hd with hs | ht
    · exact ⟨d, hs⟩
    · exact ⟨seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse d, by
        rw [seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source_reverse]
        exact ht⟩
  obtain ⟨dFinal, hdFinal⟩ := hsource
  obtain ⟨dSource, hdSource⟩ :=
    seed.boundaryOccurrenceDartPairFold.hom_surjective dFinal
  let prefixWalk := wordBoundaryPrefixWalkToDartSource
    seed.boundary.reducedLiteralBoundary seed.balloonEndpointPairs dSource
  let mappedWalk := (prefixWalk.map
      seed.boundaryOccurrenceDartPairFold.hom).map (seed.pairFoldFiniteHom hne)
  have htargetRaw :
      seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryGraph.toDartGraph.source dSource) =
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source dFinal := by
    calc
      _ = seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source
          (seed.boundaryOccurrenceDartPairFold.hom.mapDart dSource) :=
        (seed.boundaryOccurrenceDartPairFold.hom.map_source dSource).symm
      _ = seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source dFinal :=
        congrArg seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source hdSource
  have htarget :
      (seed.pairFoldFiniteHom hne).mapVertex
          (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
            (seed.balloonBoundaryGraph.toDartGraph.source dSource)) = v := by
    apply Subtype.ext
    calc
      _ = seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.source dFinal := by
        rw [htargetRaw]
        simp [MinimalAreaRelatorBoundarySeed.pairFoldFiniteHom]
      _ = v.1 := hdFinal
  refine ⟨(seed.boundary.reducedLiteralBoundary).take
      (if dSource.2 then dSource.1.val + 1 else dSource.1.val), ?_⟩
  exact ⟨htarget ▸ mappedWalk⟩

/-- The reduced target word is a based loop in the finite pair-fold graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteBoundaryLoop
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :
    LabelledWalk seed.pairFoldFiniteGraph
      (seed.pairFoldFiniteBasepoint hne)
      (seed.pairFoldFiniteBasepoint hne) w.toWord := by
  exact seed.pairFoldFiniteBoundaryWalk hne

/-- Face-side and surviving-boundary flags keep their selected dart in the
finite support graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteIncidenceDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (x : seed.PairFoldIncidence) :
    seed.pairFoldFiniteGraph.toDartGraph.Dart :=
  (seed.pairFoldFiniteHom hne).mapDart (seed.pairFoldIncidenceDart x)

/-- The finite-support map preserves the label of every incidence dart. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteIncidenceDart_label
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (x : seed.PairFoldIncidence) :
    seed.pairFoldFiniteGraph.label (seed.pairFoldFiniteIncidenceDart hne x) =
      seed.boundaryOccurrenceDartPairFold.graph.label
        (seed.pairFoldIncidenceDart x) := by
  exact (seed.pairFoldFiniteHom hne).map_label _

/-- Distinct flags over a used edge have opposite orientations after the
finite-support restriction as well. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteIncidenceDart_opposite_of_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (e : seed.PairFoldEdgeClass)
    (a b : seed.PairFoldIncidenceFiber e) (hab : a ≠ b) :
    seed.pairFoldFiniteIncidenceDart hne b.1 =
    seed.pairFoldFiniteGraph.toDartGraph.reverse
        (seed.pairFoldFiniteIncidenceDart hne a.1) := by
  have h := seed.pairFoldIncidenceDart_opposite_of_ne e a b hab
  change seed.pairFoldIncidenceDart b.1 =
    seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
      (seed.pairFoldIncidenceDart a.1) at h
  have hmap := congrArg (seed.pairFoldFiniteHom hne).mapDart h
  calc
    seed.pairFoldFiniteIncidenceDart hne b.1 =
        (seed.pairFoldFiniteHom hne).mapDart
          (seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
            (seed.pairFoldIncidenceDart a.1)) := by
      simpa [MinimalAreaRelatorBoundarySeed.pairFoldFiniteIncidenceDart] using hmap
    _ = seed.pairFoldFiniteGraph.toDartGraph.reverse
          (seed.pairFoldFiniteIncidenceDart hne a.1) := by
      simpa [MinimalAreaRelatorBoundarySeed.pairFoldFiniteIncidenceDart] using
        ((seed.pairFoldFiniteHom hne).map_reverse
          (seed.pairFoldIncidenceDart a.1)).symm

/-- Each indexed relator balloon supplies a relator boundary loop in the same
finite graph as the target boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorLoopAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    RelatorBoundaryLoop P seed.pairFoldFiniteGraph := by
  classical
  let balloon := seed.boundary.reducedBalloons.get i
  let hrelatorLoop := seed.pairFoldBalloon_hasRelatorLoop
    balloon (List.get_mem _ _)
  let vertex := Classical.choose hrelatorLoop
  have hloop := Classical.choose_spec hrelatorLoop
  let loop : LabelledWalk seed.boundaryOccurrenceDartPairFold.graph
      vertex vertex balloon.label.relator.toWord := Classical.choice hloop
  let hom := seed.pairFoldFiniteHom hne
  refine ⟨balloon.label.relator, balloon.label.relator_mem,
    P.relator_isCyclicallyReduced balloon.label.relator_mem,
    hom.mapVertex vertex, ?_⟩
  simpa [balloon, hom] using loop.map hom

/-- The indexed relator polygon's attaching map into the finite direct
pair-fold graph. It retains the actual occurrence map through the balloon,
boundary, and fold quotients. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorPathHomAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    LabelledGraphHom
      (wordPathGraph ((seed.boundary.reducedBalloons.get i).label.relator.toWord))
      seed.pairFoldFiniteGraph := by
  let balloon := seed.boundary.reducedBalloons.get i
  exact LabelledGraphHom.comp (seed.pairFoldFiniteHom hne)
    (LabelledGraphHom.comp seed.boundaryOccurrenceDartPairFold.hom
      (LabelledGraphHom.comp seed.balloonBoundaryHom
        (LabelledGraphHom.comp (seed.balloonOccurrenceEmbedding i)
          balloon.relatorPathHom)))

/-- Reading the indexed relator polygon in the direct quotient gives its
canonical relator loop, from the polygon's indexed occurrence map. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorPathAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :=
  (wordPathWalk (seed.boundary.reducedBalloons.get i).label.relator.toWord).map
    (seed.pairFoldFiniteRelatorPathHomAt hne i)

/-- Each indexed relator polygon closes at its base vertex in the direct
pair-fold quotient. Empty stems close by their endpoint join; nonempty stems
close by the occurrence-specific innermost stem fold. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorPathHomAt_endpoints_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    (seed.pairFoldFiniteRelatorPathHomAt hne i).mapVertex (0 : Nat) =
      (seed.pairFoldFiniteRelatorPathHomAt hne i).mapVertex
        ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length) := by
  let balloon := seed.boundary.reducedBalloons.get i
  let embedding := seed.balloonOccurrenceEmbedding i
  by_cases hstem : balloon.label.conjugator.toWord.length = 0
  · let positions := (embedding.mapVertex (0 : Nat),
      embedding.mapVertex balloon.label.rawWord.length)
    have hpositions : positions ∈ seed.balloonEndpointPairs := by
      simpa [positions, balloon, embedding] using
        seed.balloonOccurrenceEmbedding_endpoints_mem i
    have hjoin := wordBoundary_join_eq seed.boundary.reducedLiteralBoundary
      seed.balloonEndpointPairs positions hpositions
    have hrawlen : balloon.label.rawWord.length =
        balloon.label.relator.toWord.length := by
      rw [balloon.label.rawWord_length_eq, hstem]
      simp
    have hboundary : seed.balloonBoundaryHom.mapVertex
          (embedding.mapVertex (0 : Nat)) =
        seed.balloonBoundaryHom.mapVertex
          (embedding.mapVertex balloon.label.relator.toWord.length) := by
      change (Quotient.mk (BoundaryVertexJoinSetoid
          seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs)
            (embedding.mapVertex (0 : Nat)) :
          WordBoundaryVertexWithJoins seed.boundary.reducedLiteralBoundary
            seed.balloonEndpointPairs) =
        Quotient.mk (BoundaryVertexJoinSetoid
          seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs)
            (embedding.mapVertex balloon.label.relator.toWord.length)
      simpa [positions, hrawlen] using hjoin
    have hclose := congrArg (seed.pairFoldFiniteHom hne).mapVertex
      (congrArg seed.boundaryOccurrenceDartPairFold.hom.mapVertex hboundary)
    change (seed.pairFoldFiniteHom hne).mapVertex
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex
              (balloon.label.conjugator.toWord.length + (0 : Nat))))) =
      (seed.pairFoldFiniteHom hne).mapVertex
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex
              (balloon.label.conjugator.toWord.length +
                balloon.label.relator.toWord.length))))
    simpa [hstem] using hclose
  · let localPair := balloon.innermostStemPair hstem
    have hlocalPair : LabelledDartPair.map embedding localPair ∈
        seed.balloonStemPairs := by
      change LabelledDartPair.map
        (reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i)
        localPair ∈ reducedBalloonStemPairs seed.boundary.reducedBalloons
      exact reducedBalloonOccurrencePathEmbedding_stemPair_mem
        seed.boundary.reducedBalloons i localPair
        (balloon.innermostStemPair_mem hstem)
    let pair := LabelledDartPair.map seed.balloonBoundaryHom
      (LabelledDartPair.map embedding localPair)
    have hpairMem : pair ∈ seed.boundaryBalloonStemPairs := by
      unfold MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs
      exact List.mem_map.mpr
        ⟨LabelledDartPair.map embedding localPair, hlocalPair, rfl⟩
    have hpairFolded :=
      seed.boundaryOccurrenceDartPairFold_stem_reverse pair hpairMem
    have hendpoints := LabelledGraphHom.mapVertex_source_second_eq_target_first
      seed.boundaryOccurrenceDartPairFold.hom pair hpairFolded
    have hsource : seed.balloonBoundaryGraph.toDartGraph.source pair.second =
        seed.balloonBoundaryHom.mapVertex
          (embedding.mapVertex
            (balloon.label.conjugator.toWord.length +
              balloon.label.relator.toWord.length)) := by
      calc
        _ = seed.balloonBoundaryHom.mapVertex
              ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.source
                (embedding.mapDart localPair.second)) := by
          simpa [pair, LabelledDartPair.map,
            MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph] using
              seed.balloonBoundaryHom.map_source (embedding.mapDart localPair.second)
        _ = seed.balloonBoundaryHom.mapVertex
              (embedding.mapVertex
                ((wordPathGraph balloon.label.rawWord).toDartGraph.source
                  localPair.second)) :=
          congrArg seed.balloonBoundaryHom.mapVertex
            (embedding.map_source localPair.second)
        _ = _ := by rw [balloon.innermostStemPair_source_second hstem]
    have htarget : seed.balloonBoundaryGraph.toDartGraph.target pair.first =
        seed.balloonBoundaryHom.mapVertex
          (embedding.mapVertex balloon.label.conjugator.toWord.length) := by
      calc
        _ = seed.balloonBoundaryHom.mapVertex
              ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.target
                (embedding.mapDart localPair.first)) := by
          simpa [pair, LabelledDartPair.map,
            MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph] using
              seed.balloonBoundaryHom.map_target (embedding.mapDart localPair.first)
        _ = seed.balloonBoundaryHom.mapVertex
              (embedding.mapVertex
                ((wordPathGraph balloon.label.rawWord).toDartGraph.target
                  localPair.first)) :=
          congrArg seed.balloonBoundaryHom.mapVertex
            (embedding.map_target localPair.first)
        _ = _ := by rw [balloon.innermostStemPair_target_first hstem]
    have hcloseBase : seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex balloon.label.conjugator.toWord.length)) =
        seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex
              (balloon.label.conjugator.toWord.length +
                balloon.label.relator.toWord.length))) := by
      calc
        _ = seed.boundaryOccurrenceDartPairFold.hom.mapVertex
              (seed.balloonBoundaryGraph.toDartGraph.target pair.first) :=
          congrArg seed.boundaryOccurrenceDartPairFold.hom.mapVertex htarget.symm
        _ = seed.boundaryOccurrenceDartPairFold.hom.mapVertex
              (seed.balloonBoundaryGraph.toDartGraph.source pair.second) :=
          hendpoints.symm
        _ = _ := congrArg seed.boundaryOccurrenceDartPairFold.hom.mapVertex hsource
    have hclose := congrArg (seed.pairFoldFiniteHom hne).mapVertex hcloseBase
    change (seed.pairFoldFiniteHom hne).mapVertex
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex
              (balloon.label.conjugator.toWord.length + (0 : Nat))))) =
      (seed.pairFoldFiniteHom hne).mapVertex
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex
              (balloon.label.conjugator.toWord.length +
                balloon.label.relator.toWord.length))))
    simpa [Nat.add_zero] using hclose

/-- The occurrence-indexed relator attaching path is a closed walk in the
finite direct pair-fold graph, with its basepoint fixed by the occurrence map. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorCellAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    RelatorBoundaryLoop P seed.pairFoldFiniteGraph := by
  let balloon := seed.boundary.reducedBalloons.get i
  let hom := seed.pairFoldFiniteRelatorPathHomAt hne i
  have hclose := seed.pairFoldFiniteRelatorPathHomAt_endpoints_eq hne i
  refine ⟨balloon.label.relator, balloon.label.relator_mem,
    P.relator_isCyclicallyReduced balloon.label.relator_mem,
    hom.mapVertex (0 : Nat), ?_⟩
  exact Eq.mp (congrArg
    (fun endpoint => LabelledWalk seed.pairFoldFiniteGraph
      (hom.mapVertex (0 : Nat)) endpoint balloon.label.relator.toWord)
    hclose.symm) (seed.pairFoldFiniteRelatorPathAt hne i)

/-- Every relator-loop side is the oppositely oriented face-side incidence
with the same indexed balloon and cyclic position. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorPathHomAt_side
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    (seed.pairFoldFiniteRelatorPathHomAt hne i).mapDart (j, false) =
      seed.pairFoldFiniteGraph.toDartGraph.reverse
        (seed.pairFoldFiniteIncidenceDart hne (Sum.inl ⟨i, j⟩)) := by
  let side : seed.RelatorSideOccurrence := ⟨i, j⟩
  let finiteHom := seed.pairFoldFiniteHom hne
  let pairHom := seed.boundaryOccurrenceDartPairFold.hom
  have hposition := seed.relatorSideOccurrencePosition_dart side
  have hforward :
      (seed.pairFoldFiniteRelatorPathHomAt hne i).mapDart (j, false) =
        finiteHom.mapDart
          (pairHom.mapDart (seed.relatorSideOccurrencePosition side, false)) := by
    change finiteHom.mapDart
      (pairHom.mapDart
        (seed.balloonBoundaryHom.mapDart
          ((seed.balloonOccurrenceEmbedding i).mapDart
            ((seed.boundary.reducedBalloons.get i).relatorPathHom.mapDart
              (j, false))))) = _
    rw [ReducedRelatorBalloonData.relatorPathHom_mapDart_forward]
    change finiteHom.mapDart
      (pairHom.mapDart
        ((seed.balloonBoundaryHom.comp
          (reducedBalloonOccurrencePathEmbedding
            seed.boundary.reducedBalloons i)).mapDart
          ((seed.boundary.reducedBalloons.get i).relatorSideDart j))) = _
    rw [hposition]
  have hreverse :
      seed.pairFoldFiniteGraph.toDartGraph.reverse
          (finiteHom.mapDart
            (seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
              (pairHom.mapDart (seed.relatorSideOccurrencePosition side, false)))) =
        finiteHom.mapDart
          (pairHom.mapDart (seed.relatorSideOccurrencePosition side, false)) := by
    rw [finiteHom.map_reverse,
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse_involutive]
  calc
    (seed.pairFoldFiniteRelatorPathHomAt hne i).mapDart (j, false) =
        finiteHom.mapDart
          (pairHom.mapDart (seed.relatorSideOccurrencePosition side, false)) := hforward
    _ = seed.pairFoldFiniteGraph.toDartGraph.reverse
          (finiteHom.mapDart
            (seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
              (pairHom.mapDart (seed.relatorSideOccurrencePosition side, false)))) :=
      hreverse.symm
    _ = seed.pairFoldFiniteGraph.toDartGraph.reverse
          (seed.pairFoldFiniteIncidenceDart hne (Sum.inl side)) := by
      rfl

/-- The source vertex of a positive relator side is the target of its
oppositely oriented face-side incidence dart. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorPathHomAt_side_source
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    (seed.pairFoldFiniteRelatorPathHomAt hne i).mapVertex (j.val : Nat) =
      seed.pairFoldFiniteGraph.toDartGraph.target
        (seed.pairFoldFiniteIncidenceDart hne (Sum.inl ⟨i, j⟩)) := by
  let hom := seed.pairFoldFiniteRelatorPathHomAt hne i
  let incidence := seed.pairFoldFiniteIncidenceDart hne (Sum.inl ⟨i, j⟩)
  calc
    hom.mapVertex (j.val : Nat) =
        seed.pairFoldFiniteGraph.toDartGraph.source (hom.mapDart (j, false)) :=
      (hom.map_source (j, false)).symm
    _ = seed.pairFoldFiniteGraph.toDartGraph.source
          (seed.pairFoldFiniteGraph.toDartGraph.reverse incidence) := by
      rw [seed.pairFoldFiniteRelatorPathHomAt_side]
    _ = seed.pairFoldFiniteGraph.toDartGraph.target incidence :=
      seed.pairFoldFiniteGraph.toDartGraph.source_reverse incidence

/-- The target vertex of a positive relator side is the source of its
oppositely oriented face-side incidence dart. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFiniteRelatorPathHomAt_side_target
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    (seed.pairFoldFiniteRelatorPathHomAt hne i).mapVertex (j.val + 1) =
      seed.pairFoldFiniteGraph.toDartGraph.source
        (seed.pairFoldFiniteIncidenceDart hne (Sum.inl ⟨i, j⟩)) := by
  let hom := seed.pairFoldFiniteRelatorPathHomAt hne i
  let incidence := seed.pairFoldFiniteIncidenceDart hne (Sum.inl ⟨i, j⟩)
  calc
    hom.mapVertex (j.val + 1) =
        seed.pairFoldFiniteGraph.toDartGraph.target (hom.mapDart (j, false)) :=
      (hom.map_target (j, false)).symm
    _ = seed.pairFoldFiniteGraph.toDartGraph.target
          (seed.pairFoldFiniteGraph.toDartGraph.reverse incidence) := by
      rw [seed.pairFoldFiniteRelatorPathHomAt_side]
    _ = seed.pairFoldFiniteGraph.toDartGraph.source incidence :=
      seed.pairFoldFiniteGraph.toDartGraph.target_reverse incidence

/-- An endpoint germ of an indexed relator side. `false` selects the source
of the positive polygon side, and `true` its target. These germs are the
vertices from which the local face-link graph will be assembled. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldFaceGerm
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  seed.RelatorSideOccurrence × Bool

/-- The image vertex of an endpoint germ in the finite pair-fold graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (germ : seed.PairFoldFaceGerm) :
    seed.pairFoldFiniteGraph.toDartGraph.Vertex :=
  if germ.2 then
    (seed.pairFoldFiniteRelatorPathHomAt hne germ.1.1).mapVertex
      (germ.1.2.val + 1)
  else
    (seed.pairFoldFiniteRelatorPathHomAt hne germ.1.1).mapVertex
      (germ.1.2.val : Nat)

/-- Each relator endpoint germ lies at the matching endpoint of its
oppositely oriented ledger dart. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_eq_incidenceEndpoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (germ : seed.PairFoldFaceGerm) :
    seed.pairFoldFaceGermVertex hne germ =
      if germ.2 then
        seed.pairFoldFiniteGraph.toDartGraph.source
          (seed.pairFoldFiniteIncidenceDart hne (Sum.inl germ.1))
      else
        seed.pairFoldFiniteGraph.toDartGraph.target
          (seed.pairFoldFiniteIncidenceDart hne (Sum.inl germ.1)) := by
  cases germ with
  | mk side endpoint =>
      cases endpoint
      · exact seed.pairFoldFiniteRelatorPathHomAt_side_source
          hne side.1 side.2
      · exact seed.pairFoldFiniteRelatorPathHomAt_side_target
          hne side.1 side.2

/-- The next side index on a nonempty cyclic word path. -/
def cyclicNextFin {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, by omega⟩

/-- The preceding side index on a nonempty cyclic word path. -/
def cyclicPrevFin {n : Nat} (i : Fin n) : Fin n :=
  if h : 0 < i.val then ⟨i.val - 1, by omega⟩ else ⟨n - 1, by omega⟩

@[simp] theorem cyclicPrevFin_cyclicNextFin {n : Nat} (i : Fin n) :
    cyclicPrevFin (cyclicNextFin i) = i := by
  apply Fin.ext
  by_cases h : i.val + 1 < n
  · simp [cyclicNextFin, cyclicPrevFin, h]
  · have hlast : i.val + 1 = n := by omega
    simp [cyclicNextFin, cyclicPrevFin, hlast]
    omega

@[simp] theorem cyclicNextFin_cyclicPrevFin {n : Nat} (i : Fin n) :
    cyclicNextFin (cyclicPrevFin i) = i := by
  apply Fin.ext
  by_cases h : 0 < i.val
  · have hprev : i.val - 1 + 1 < n := by omega
    simp [cyclicPrevFin, cyclicNextFin, h, hprev]
    omega
  · have hzero : i.val = 0 := by omega
    have hn : 0 < n := by omega
    have hwrap : ¬ n - 1 + 1 < n := by omega
    simp [cyclicPrevFin, cyclicNextFin, hzero, hwrap]

/-- The relator-side occurrence immediately after a given side, with cyclic
wrap at the end of its indexed polygon. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) : seed.RelatorSideOccurrence :=
  ⟨side.1, cyclicNextFin side.2⟩

/-- The relator-side occurrence immediately before a given side, with cyclic
wrap at the beginning of its indexed polygon. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) : seed.RelatorSideOccurrence :=
  ⟨side.1, cyclicPrevFin side.2⟩

/-- The other face-endpoint germ at the same polygon corner. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ : seed.PairFoldFaceGerm) : seed.PairFoldFaceGerm :=
  if germ.2 then (seed.pairFoldFaceSideNext germ.1, false)
  else (seed.pairFoldFaceSidePrev germ.1, true)

/-- Turning across a polygon corner is an involution on its endpoint germs. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate_involutive
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ : seed.PairFoldFaceGerm) :
    seed.pairFoldFaceCornerMate (seed.pairFoldFaceCornerMate germ) = germ := by
  rcases germ with ⟨side, endpoint⟩
  cases endpoint <;>
    simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev]

/-- The corner turn changes the endpoint side of each germ, so it has no
fixed endpoint germ. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ : seed.PairFoldFaceGerm) :
    seed.pairFoldFaceCornerMate germ ≠ germ := by
  rcases germ with ⟨side, endpoint⟩
  cases endpoint <;>
    simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev]

/-- The two endpoint germs adjacent at a relator corner map to the same
vertex in the finite pair-fold graph. This includes the cyclic basepoint join. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_source
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (side : seed.RelatorSideOccurrence) :
    seed.pairFoldFaceGermVertex hne (side, false) =
      (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
        (side.2.val : Nat) := by
  rfl

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_target
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (side : seed.RelatorSideOccurrence) :
    seed.pairFoldFaceGermVertex hne (side, true) =
      (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
        ((side.2.val + 1 : Nat)) := by
  rfl

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMate_vertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (germ : seed.PairFoldFaceGerm) :
    seed.pairFoldFaceGermVertex hne (seed.pairFoldFaceCornerMate germ) =
      seed.pairFoldFaceGermVertex hne germ := by
  rcases germ with ⟨side, endpoint⟩
  have hclose := seed.pairFoldFiniteRelatorPathHomAt_endpoints_eq hne side.1
  cases endpoint
  · -- A source endpoint meets the previous side's target endpoint.
    change seed.pairFoldFaceGermVertex hne
        (seed.pairFoldFaceSidePrev side, true) =
      seed.pairFoldFaceGermVertex hne (side, false)
    rw [MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_target,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_source]
    simp only [MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePrev]
    by_cases hprev : 0 < side.2.val
    · have hval : (cyclicPrevFin side.2).val + 1 = side.2.val := by
        simp [cyclicPrevFin, hprev]
        omega
      exact congrArg
        (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex hval
    · have hzero : side.2.val = 0 := by omega
      have hlength_pos : 0 <
          (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length := by
        have h := side.2.isLt
        omega
      have hlast : (cyclicPrevFin side.2).val + 1 =
          (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length := by
        simp only [cyclicPrevFin, dite_eq_right hprev]
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlength_pos)
      calc
        (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
            ((cyclicPrevFin side.2).val + 1 : Nat) =
            (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
              (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length :=
          congrArg (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex hlast
        _ = (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex (0 : Nat) :=
          hclose.symm
        _ = (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
              (side.2.val : Nat) := by rw [hzero]
  · -- A target endpoint meets the next side's source endpoint.
    change seed.pairFoldFaceGermVertex hne
        (seed.pairFoldFaceSideNext side, false) =
      seed.pairFoldFaceGermVertex hne (side, true)
    rw [MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_source,
      MinimalAreaRelatorBoundarySeed.pairFoldFaceGermVertex_target]
    simp only [MinimalAreaRelatorBoundarySeed.pairFoldFaceSideNext]
    by_cases hnext : side.2.val + 1 <
        (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length
    · have hval : (cyclicNextFin side.2).val = side.2.val + 1 := by
        unfold cyclicNextFin
        split
        · rfl
        · omega
      exact congrArg
        (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex hval
    · have hlast : side.2.val + 1 =
          (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length := by
        omega
      have hzero : (cyclicNextFin side.2).val = 0 := by
        unfold cyclicNextFin
        split
        · omega
        · rfl
      calc
        (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
            ((cyclicNextFin side.2).val : Nat) =
            (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
              (0 : Nat) := by rw [hzero]
        _ = (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
              (seed.boundary.reducedBalloons.get side.1).label.relator.toWord.length :=
          hclose
        _ = (seed.pairFoldFiniteRelatorPathHomAt hne side.1).mapVertex
              (side.2.val + 1 : Nat) := by
          rw [hlast]

/-- At an edge shared by two distinct relator sides, the source endpoint of
one side is the target endpoint of the other in the folded graph. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGerm_source_eq_other_target
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (sideA sideB : seed.RelatorSideOccurrence)
    (hEdge : seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideB))
    (hDistinct : sideA ≠ sideB) :
    seed.pairFoldFaceGermVertex hne (sideA, false) =
      seed.pairFoldFaceGermVertex hne (sideB, true) := by
  let edge := seed.pairFoldIncidenceEdgeClass (Sum.inl sideA)
  let a : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideA, rfl⟩
  let b : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideB, hEdge.symm⟩
  have hab : a ≠ b := by
    intro h
    apply hDistinct
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hop := seed.pairFoldFiniteIncidenceDart_opposite_of_ne
    hne edge a b hab
  let G := seed.pairFoldFiniteGraph.toDartGraph
  let incidenceA := seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideA)
  let incidenceB := seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideB)
  have hop' : incidenceB = G.reverse incidenceA := by
    simpa [incidenceA, incidenceB, a, b] using hop
  have hA : seed.pairFoldFaceGermVertex hne (sideA, false) =
      G.target incidenceA := by
    simpa [incidenceA, G] using
      seed.pairFoldFaceGermVertex_eq_incidenceEndpoint hne (sideA, false)
  have hB : seed.pairFoldFaceGermVertex hne (sideB, true) =
      G.source incidenceB := by
    simpa [incidenceB, G] using
      seed.pairFoldFaceGermVertex_eq_incidenceEndpoint hne (sideB, true)
  have hends : G.source incidenceB = G.target incidenceA := by
    calc
      G.source incidenceB = G.source (G.reverse incidenceA) := by rw [hop']
      _ = G.target incidenceA := G.source_reverse incidenceA
  calc
    seed.pairFoldFaceGermVertex hne (sideA, false) = G.target incidenceA := hA
    _ = G.source incidenceB := hends.symm
    _ = seed.pairFoldFaceGermVertex hne (sideB, true) := hB.symm

/-- At an edge shared by two distinct relator sides, the target endpoint of
one side is the source endpoint of the other in the folded graph. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceGerm_target_eq_other_source
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (sideA sideB : seed.RelatorSideOccurrence)
    (hEdge : seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideB))
    (hDistinct : sideA ≠ sideB) :
    seed.pairFoldFaceGermVertex hne (sideA, true) =
      seed.pairFoldFaceGermVertex hne (sideB, false) := by
  let edge := seed.pairFoldIncidenceEdgeClass (Sum.inl sideA)
  let a : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideA, rfl⟩
  let b : seed.PairFoldIncidenceFiber edge := ⟨Sum.inl sideB, hEdge.symm⟩
  have hab : a ≠ b := by
    intro h
    apply hDistinct
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hop := seed.pairFoldFiniteIncidenceDart_opposite_of_ne
    hne edge a b hab
  let G := seed.pairFoldFiniteGraph.toDartGraph
  let incidenceA := seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideA)
  let incidenceB := seed.pairFoldFiniteIncidenceDart hne (Sum.inl sideB)
  have hop' : incidenceB = G.reverse incidenceA := by
    simpa [incidenceA, incidenceB, a, b] using hop
  have hA : seed.pairFoldFaceGermVertex hne (sideA, true) =
      G.source incidenceA := by
    simpa [incidenceA, G] using
      seed.pairFoldFaceGermVertex_eq_incidenceEndpoint hne (sideA, true)
  have hB : seed.pairFoldFaceGermVertex hne (sideB, false) =
      G.target incidenceB := by
    simpa [incidenceB, G] using
      seed.pairFoldFaceGermVertex_eq_incidenceEndpoint hne (sideB, false)
  have hends : G.target incidenceB = G.source incidenceA := by
    calc
      G.target incidenceB = G.target (G.reverse incidenceA) := by rw [hop']
      _ = G.source incidenceA := G.target_reverse incidenceA
  calc
    seed.pairFoldFaceGermVertex hne (sideA, true) = G.source incidenceA := hA
    _ = G.target incidenceB := hends.symm
    _ = seed.pairFoldFaceGermVertex hne (sideB, false) := hB.symm

/-- A side of a folded edge has at most one distinct relator-side partner.
The exact two-incidence ledger rules out three different face-side flags. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSide_partner_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (sideA sideB sideC : seed.RelatorSideOccurrence)
    (hEdgeAB : seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideB))
    (hEdgeAC : seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideC))
    (hAB : sideA ≠ sideB) (hAC : sideA ≠ sideC) :
    sideB = sideC := by
  classical
  by_contra hBC
  let edge := seed.pairFoldIncidenceEdgeClass (Sum.inl sideA)
  let used : seed.PairFoldUsedEdge :=
    ⟨edge, ⟨Sum.inl sideA, rfl⟩⟩
  let fiber := seed.PairFoldIncidenceFiber edge
  letI := seed.pairFoldIncidenceFiberFintype edge
  let a : fiber := ⟨Sum.inl sideA, rfl⟩
  let b : fiber := ⟨Sum.inl sideB, hEdgeAB.symm⟩
  let c : fiber := ⟨Sum.inl sideC, hEdgeAC.symm⟩
  have hab : a ≠ b := by
    intro h
    apply hAB
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hac : a ≠ c := by
    intro h
    apply hAC
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hbc : b ≠ c := by
    intro h
    apply hBC
    exact Sum.inl.inj (congrArg Subtype.val h)
  let f : Fin 3 → fiber := fun i =>
    if i.val = 0 then a else if i.val = 1 then b else c
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcard : Fintype.card fiber = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact seed.pairFoldIncidenceFiber_card_eq_two used
  have hle : 3 ≤ Fintype.card fiber := by
    simpa [f] using Fintype.card_le_of_injective f hf
  omega

/-- The partial matching of distinct relator sides that represent the same
folded edge. -/
def MinimalAreaRelatorBoundarySeed.PairFoldFaceSidesShareEdge
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (sideA sideB : seed.RelatorSideOccurrence) : Prop :=
  sideA ≠ sideB ∧
    seed.pairFoldIncidenceEdgeClass (Sum.inl sideA) =
      seed.pairFoldIncidenceEdgeClass (Sum.inl sideB)

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSidesShareEdge_symm
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {sideA sideB : seed.RelatorSideOccurrence}
    (h : seed.PairFoldFaceSidesShareEdge sideA sideB) :
    seed.PairFoldFaceSidesShareEdge sideB sideA :=
  ⟨h.1.symm, h.2.symm⟩

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSidesShareEdge_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (sideA sideB sideC : seed.RelatorSideOccurrence)
    (hAB : seed.PairFoldFaceSidesShareEdge sideA sideB)
    (hAC : seed.PairFoldFaceSidesShareEdge sideA sideC) :
    sideB = sideC :=
  seed.pairFoldFaceSide_partner_unique sideA sideB sideC
    hAB.2 hAC.2 hAB.1 hAC.1

/-- An edge-link step crosses a folded edge between its two distinct face
side incidences, matching source to target. -/
def MinimalAreaRelatorBoundarySeed.PairFoldFaceEdgeStep
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germA germB : seed.PairFoldFaceGerm) : Prop :=
  seed.PairFoldFaceSidesShareEdge germA.1 germB.1 ∧ germA.2 ≠ germB.2

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeStep_symm
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {germA germB : seed.PairFoldFaceGerm}
    (h : seed.PairFoldFaceEdgeStep germA germB) :
    seed.PairFoldFaceEdgeStep germB germA :=
  ⟨seed.pairFoldFaceSidesShareEdge_symm h.1, h.2.symm⟩

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeStep_vertex_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {germA germB : seed.PairFoldFaceGerm}
    (h : seed.PairFoldFaceEdgeStep germA germB) :
    seed.pairFoldFaceGermVertex hne germA =
      seed.pairFoldFaceGermVertex hne germB := by
  rcases germA with ⟨sideA, endpointA⟩
  rcases germB with ⟨sideB, endpointB⟩
  rcases h with ⟨⟨hDistinct, hEdge⟩, hEndpoint⟩
  cases endpointA <;> cases endpointB
  · simp at hEndpoint
  · exact seed.pairFoldFaceGerm_source_eq_other_target
      hne sideA sideB hEdge hDistinct
  · exact seed.pairFoldFaceGerm_target_eq_other_source
      hne sideA sideB hEdge hDistinct
  · simp at hEndpoint

/-- Every face-side endpoint germ has at most one across-edge partner in its
folded vertex link. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeStep_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {germ germB germC : seed.PairFoldFaceGerm}
    (hB : seed.PairFoldFaceEdgeStep germ germB)
    (hC : seed.PairFoldFaceEdgeStep germ germC) :
    germB = germC := by
  rcases germ with ⟨sideA, endpointA⟩
  rcases germB with ⟨sideB, endpointB⟩
  rcases germC with ⟨sideC, endpointC⟩
  have hside := seed.pairFoldFaceSidesShareEdge_unique
    sideA sideB sideC hB.1 hC.1
  cases hside
  have hEndpoint : endpointB = endpointC := by
    cases endpointA <;> cases endpointB <;> cases endpointC <;>
      simp_all [PairFoldFaceEdgeStep]
  cases hEndpoint
  rfl

/-- Choose the unique other relator side in the same folded-edge class, when
the second incidence is another face side. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePartner?
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    Option seed.RelatorSideOccurrence := by
  classical
  exact if h : ∃ other, seed.PairFoldFaceSidesShareEdge side other then
    some (Classical.choose h)
  else none

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePartner?_spec
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side other : seed.RelatorSideOccurrence)
    (h : seed.pairFoldFaceSidePartner? side = some other) :
    seed.PairFoldFaceSidesShareEdge side other := by
  classical
  by_cases hex : ∃ x, seed.PairFoldFaceSidesShareEdge side x
  · have heq : Classical.choose hex = other := by
      simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePartner?, hex] using h
    cases heq
    exact Classical.choose_spec hex
  · simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePartner?, hex] at h

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePartner?_of_shareEdge
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side other : seed.RelatorSideOccurrence)
    (h : seed.PairFoldFaceSidesShareEdge side other) :
    seed.pairFoldFaceSidePartner? side = some other := by
  classical
  let hex : ∃ x, seed.PairFoldFaceSidesShareEdge side x := ⟨other, h⟩
  have heq : Classical.choose hex = other :=
    seed.pairFoldFaceSidesShareEdge_unique side (Classical.choose hex) other
      (Classical.choose_spec hex) h
  simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceSidePartner?, hex, heq]

/-- The selected across-edge transition on endpoint germs, when the opposite
incidence is another relator side. Boundary incidences have no such transition. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ : seed.PairFoldFaceGerm) : Option seed.PairFoldFaceGerm :=
  (seed.pairFoldFaceSidePartner? germ.1).map
    (fun side => (side, !germ.2))

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?_spec
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ other : seed.PairFoldFaceGerm)
    (h : seed.pairFoldFaceEdgeMate? germ = some other) :
    seed.PairFoldFaceEdgeStep germ other := by
  classical
  rcases germ with ⟨side, endpoint⟩
  cases hpartner : seed.pairFoldFaceSidePartner? side with
  | none => simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?, hpartner] at h
  | some otherSide =>
      have hside : seed.PairFoldFaceSidesShareEdge side otherSide :=
        seed.pairFoldFaceSidePartner?_spec side otherSide hpartner
      have hEndpoint : endpoint ≠ !endpoint := by
        cases endpoint <;> decide
      have heq : other = (otherSide, !endpoint) := by
        simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?, hpartner] using h.symm
      cases heq
      exact ⟨hside, hEndpoint⟩

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?_of_edgeStep
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ other : seed.PairFoldFaceGerm)
    (h : seed.PairFoldFaceEdgeStep germ other) :
    seed.pairFoldFaceEdgeMate? germ = some other := by
  classical
  have hside := seed.pairFoldFaceSidePartner?_of_shareEdge germ.1 other.1 h.1
  have hbool : other.2 = !germ.2 := by
    rcases h with ⟨_, hboolNe⟩
    cases hG : germ.2 <;> cases hO : other.2
    · simp [hG, hO] at hboolNe
    · rfl
    · rfl
    · simp [hG, hO] at hboolNe
  simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?, hside]
  apply Prod.ext
  · rfl
  · exact hbool.symm

/-- The optional edge transition is a symmetric partial involution on face
endpoint germs. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMate?_involutive
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (germ other : seed.PairFoldFaceGerm)
    (h : seed.pairFoldFaceEdgeMate? germ = some other) :
    seed.pairFoldFaceEdgeMate? other = some germ := by
  apply seed.pairFoldFaceEdgeMate?_of_edgeStep
  exact seed.pairFoldFaceEdgeStep_symm
    (seed.pairFoldFaceEdgeMate?_spec germ other h)

/-- The finite set of face-endpoint germs lying over one quotient vertex. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldFaceGermsAtVertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (hne : w ≠ 1) (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :=
  {germ : seed.PairFoldFaceGerm // seed.pairFoldFaceGermVertex hne germ = v}

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldFaceGermsAtVertexFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.pairFoldFiniteGraph.toDartGraph.Vertex) :
    Fintype (seed.PairFoldFaceGermsAtVertex hne v) := by
  classical
  letI : Fintype seed.PairFoldFaceGerm := by
    unfold MinimalAreaRelatorBoundarySeed.PairFoldFaceGerm
    infer_instance
  letI : Finite (seed.PairFoldFaceGermsAtVertex hne v) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The cyclic corner transition restricts to an involution on the germs at
each quotient vertex. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMateAtVertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    seed.PairFoldFaceGermsAtVertex hne v :=
  ⟨seed.pairFoldFaceCornerMate germ.1,
    (seed.pairFoldFaceCornerMate_vertex hne germ.1).trans germ.2⟩

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMateAtVertex_involutive
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    seed.pairFoldFaceCornerMateAtVertex hne
      (seed.pairFoldFaceCornerMateAtVertex hne germ) = germ := by
  apply Subtype.ext
  exact seed.pairFoldFaceCornerMate_involutive germ.1

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceCornerMateAtVertex_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (hne : w ≠ 1) {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    seed.pairFoldFaceCornerMateAtVertex hne germ ≠ germ := by
  intro h
  apply seed.pairFoldFaceCornerMate_ne germ.1
  exact congrArg Subtype.val h

/-- The across-edge transition restricted to endpoint germs at one quotient
vertex. -/
def MinimalAreaRelatorBoundarySeed.PairFoldFaceEdgeStepAtVertex
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germA germB : seed.PairFoldFaceGermsAtVertex hne v) : Prop :=
  seed.PairFoldFaceEdgeStep germA.1 germB.1

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeStepAtVertex_symm
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    {germA germB : seed.PairFoldFaceGermsAtVertex hne v}
    (h : seed.PairFoldFaceEdgeStepAtVertex hne germA germB) :
    seed.PairFoldFaceEdgeStepAtVertex hne germB germA :=
  seed.pairFoldFaceEdgeStep_symm h

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeStepAtVertex_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    {germ germB germC : seed.PairFoldFaceGermsAtVertex hne v}
    (hB : seed.PairFoldFaceEdgeStepAtVertex hne germ germB)
    (hC : seed.PairFoldFaceEdgeStepAtVertex hne germ germC) :
    germB = germC := by
  apply Subtype.ext
  exact seed.pairFoldFaceEdgeStep_unique hB hC

/-- The optional across-edge partner remains inside the indexed local link. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ : seed.PairFoldFaceGermsAtVertex hne v) :
    Option (seed.PairFoldFaceGermsAtVertex hne v) := by
  classical
  exact if h : ∃ other,
      seed.PairFoldFaceEdgeStepAtVertex hne germ other then
    some (Classical.choose h)
  else none

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?_spec
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ other : seed.PairFoldFaceGermsAtVertex hne v)
    (h : seed.pairFoldFaceEdgeMateAtVertex? hne germ = some other) :
    seed.PairFoldFaceEdgeStepAtVertex hne germ other := by
  classical
  by_cases hex : ∃ x,
      seed.PairFoldFaceEdgeStepAtVertex hne germ x
  · have heq : Classical.choose hex = other := by
      simpa [MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?, hex]
        using h
    cases heq
    exact Classical.choose_spec hex
  · simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?, hex] at h

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?_of_edgeStep
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ other : seed.PairFoldFaceGermsAtVertex hne v)
    (h : seed.PairFoldFaceEdgeStepAtVertex hne germ other) :
    seed.pairFoldFaceEdgeMateAtVertex? hne germ = some other := by
  classical
  let hex : ∃ x,
      seed.PairFoldFaceEdgeStepAtVertex hne germ x := ⟨other, h⟩
  let chosen : seed.PairFoldFaceGermsAtVertex hne v := Classical.choose hex
  have hchosen : seed.PairFoldFaceEdgeStepAtVertex hne germ chosen :=
    Classical.choose_spec hex
  have heq : chosen = other :=
    seed.pairFoldFaceEdgeStepAtVertex_unique hne hchosen h
  simp [MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?, hex,
    chosen, heq]

theorem MinimalAreaRelatorBoundarySeed.pairFoldFaceEdgeMateAtVertex?_involutive
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    {v : seed.pairFoldFiniteGraph.toDartGraph.Vertex}
    (germ other : seed.PairFoldFaceGermsAtVertex hne v)
    (h : seed.pairFoldFaceEdgeMateAtVertex? hne germ = some other) :
    seed.pairFoldFaceEdgeMateAtVertex? hne other = some germ := by
  apply seed.pairFoldFaceEdgeMateAtVertex?_of_edgeStep hne
  exact seed.pairFoldFaceEdgeStepAtVertex_symm hne
    (seed.pairFoldFaceEdgeMateAtVertex?_spec hne germ other h)

end GreendlingerDehn
