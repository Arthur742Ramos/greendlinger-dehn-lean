import SmallCancellation.PairFoldIncidenceLedger

namespace GreendlingerDehn

/-- Every indexed relator balloon has a closed relator walk in the direct
quotient that folds all stem pairs and all boundary-cancellation pairs at
once. The proof uses the innermost stem pair for nonempty conjugators and
the balloon endpoint join for empty conjugators. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldBalloon_hasRelatorLoop
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (b : ReducedRelatorBalloonData P)
    (hb : b ∈ seed.boundary.reducedBalloons) :
    ∃ vertex : seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.Vertex,
      Nonempty (LabelledWalk seed.boundaryOccurrenceDartPairFold.graph
        vertex vertex b.label.relator.toWord) := by
  by_cases hstem : b.label.conjugator.toWord.length = 0
  · obtain ⟨embedding, hends⟩ := reducedBalloonEndpointPairs_contains
      seed.boundary.reducedBalloons b hb
    let positions := (embedding.mapVertex (0 : Nat),
      embedding.mapVertex b.label.rawWord.length)
    have hpositions : positions ∈ seed.balloonEndpointPairs := by
      simpa [positions, MinimalAreaRelatorBoundarySeed.balloonEndpointPairs] using hends
    have hjoin := wordBoundary_join_eq seed.boundary.reducedLiteralBoundary
      seed.balloonEndpointPairs positions hpositions
    have hrawlen : b.label.rawWord.length = b.label.relator.toWord.length := by
      rw [b.label.rawWord_length_eq, hstem]
      simp
    have hloop :
        seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))) =
        seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex b.label.relator.toWord.length)) := by
      have hjoin' : seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex (0 : Nat)) =
          seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex b.label.rawWord.length) := by
        change (Quotient.mk (BoundaryVertexJoinSetoid
            seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs)
              (embedding.mapVertex (0 : Nat)) :
            WordBoundaryVertexWithJoins seed.boundary.reducedLiteralBoundary
              seed.balloonEndpointPairs) =
          Quotient.mk (BoundaryVertexJoinSetoid
            seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs)
              (embedding.mapVertex b.label.rawWord.length)
        exact hjoin
      have hmap := congrArg seed.boundaryOccurrenceDartPairFold.hom.mapVertex hjoin'
      simpa [hrawlen] using hmap
    let segment := (((b.relatorSegmentWalk.map embedding).map
      seed.balloonBoundaryHom).map seed.boundaryOccurrenceDartPairFold.hom)
    refine ⟨seed.boundaryOccurrenceDartPairFold.hom.mapVertex
      (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))), ?_⟩
    have hwalk : LabelledWalk seed.boundaryOccurrenceDartPairFold.graph
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))))
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex b.label.relator.toWord.length)))
        b.label.relator.toWord := by
      simpa [segment, hstem, hrawlen] using segment
    exact ⟨Eq.mp (congrArg
      (fun endpoint => LabelledWalk seed.boundaryOccurrenceDartPairFold.graph
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))))
        endpoint b.label.relator.toWord) hloop.symm) hwalk⟩
  · let localPair := b.innermostStemPair hstem
    obtain ⟨embedding, hlocalPair⟩ := reducedBalloonStemPairs_contains
      seed.boundary.reducedBalloons b hb localPair
      (b.innermostStemPair_mem hstem)
    let boundaryHom := seed.balloonBoundaryHom
    let pair := LabelledDartPair.map boundaryHom
      (LabelledDartPair.map embedding localPair)
    have hpairMem : pair ∈ seed.boundaryBalloonStemPairs := by
      unfold MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs
      exact List.mem_map.mpr ⟨LabelledDartPair.map embedding localPair,
        hlocalPair, rfl⟩
    have hpairFolded :=
      seed.boundaryOccurrenceDartPairFold_stem_reverse pair hpairMem
    have hendpoints := LabelledGraphHom.mapVertex_source_second_eq_target_first
      seed.boundaryOccurrenceDartPairFold.hom pair hpairFolded
    have hsource :
        seed.balloonBoundaryGraph.toDartGraph.source pair.second =
          boundaryHom.mapVertex
            (embedding.mapVertex
              (b.label.conjugator.toWord.length + b.label.relator.toWord.length)) := by
      calc
        _ = boundaryHom.mapVertex
              ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.source
                (embedding.mapDart localPair.second)) := by
          simpa [pair, LabelledDartPair.map,
            MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph] using
            boundaryHom.map_source (embedding.mapDart localPair.second)
        _ = boundaryHom.mapVertex
              (embedding.mapVertex
                ((wordPathGraph b.label.rawWord).toDartGraph.source localPair.second)) :=
          congrArg boundaryHom.mapVertex (embedding.map_source localPair.second)
        _ = _ := by rw [b.innermostStemPair_source_second hstem]
    have htarget :
        seed.balloonBoundaryGraph.toDartGraph.target pair.first =
          boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length) := by
      calc
        _ = boundaryHom.mapVertex
              ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.target
                (embedding.mapDart localPair.first)) := by
          simpa [pair, LabelledDartPair.map,
            MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph] using
            boundaryHom.map_target (embedding.mapDart localPair.first)
        _ = boundaryHom.mapVertex
              (embedding.mapVertex
                ((wordPathGraph b.label.rawWord).toDartGraph.target localPair.first)) :=
          congrArg boundaryHom.mapVertex (embedding.map_target localPair.first)
        _ = _ := by rw [b.innermostStemPair_target_first hstem]
    have hloop :
        seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length)) =
        seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex
              (b.label.conjugator.toWord.length + b.label.relator.toWord.length))) := by
      calc
        _ = seed.boundaryOccurrenceDartPairFold.hom.mapVertex
              (seed.balloonBoundaryGraph.toDartGraph.target pair.first) :=
            congrArg seed.boundaryOccurrenceDartPairFold.hom.mapVertex htarget.symm
        _ = seed.boundaryOccurrenceDartPairFold.hom.mapVertex
              (seed.balloonBoundaryGraph.toDartGraph.source pair.second) := hendpoints.symm
        _ = _ := congrArg seed.boundaryOccurrenceDartPairFold.hom.mapVertex hsource
    let segment := (((b.relatorSegmentWalk).map embedding).map boundaryHom).map
      seed.boundaryOccurrenceDartPairFold.hom
    refine ⟨seed.boundaryOccurrenceDartPairFold.hom.mapVertex
      (boundaryHom.mapVertex
        (embedding.mapVertex b.label.conjugator.toWord.length)), ?_⟩
    have hwalk : LabelledWalk seed.boundaryOccurrenceDartPairFold.graph
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length)))
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex
              (b.label.conjugator.toWord.length + b.label.relator.toWord.length))))
        b.label.relator.toWord := by
      simpa [segment] using segment
    exact ⟨Eq.mp (congrArg
      (fun endpoint => LabelledWalk seed.boundaryOccurrenceDartPairFold.graph
        (seed.boundaryOccurrenceDartPairFold.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length)))
        endpoint b.label.relator.toWord) hloop.symm) hwalk⟩

end GreendlingerDehn
