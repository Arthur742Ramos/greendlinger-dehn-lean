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

end GreendlingerDehn
