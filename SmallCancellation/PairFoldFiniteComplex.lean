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

end GreendlingerDehn
