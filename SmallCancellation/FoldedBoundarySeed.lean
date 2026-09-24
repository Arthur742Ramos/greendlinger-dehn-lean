import SmallCancellation.PlanarBoundarySeed
import SmallCancellation.LollipopFolds
import SmallCancellation.StemPairEndpoints
import SmallCancellation.FiniteSupport

namespace GreendlingerDehn

/-- A complete conjugate-relator balloon boundary carried by a graph. Unlike
`RelatorBoundaryLoop`, this retains the doubled conjugator stem that belongs
to the attaching map of the relator cell. -/
structure RelatorBalloonBoundaryLoop {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (G : LabelledDartGraph α) where
  balloon : ReducedRelatorBalloonData P
  base : G.toDartGraph.Vertex
  walk : LabelledWalk G base base balloon.label.rawWord

/-- A face boundary carried by a finite map, with its defining-relator
provenance retained explicitly. -/
structure RelatorBoundaryLoop {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (G : LabelledDartGraph α) where
  relator : FreeGroup α
  relator_mem : relator ∈ P.relators
  relator_cyclicallyReduced : FreeGroup.IsCyclicallyReduced relator.toWord
  base : G.toDartGraph.Vertex
  walk : LabelledWalk G base base relator.toWord

/-- Fold the occurrence boundary of a minimum-area lollipop seed along its
certified free-reduction trace. The output is a labeled quotient graph and a
closed boundary walk spelling the requested reduced word. This is a genuine
1-skeleton construction; it does not yet attach or certify relator faces. -/
noncomputable def MinimalAreaRelatorBoundarySeed.foldedBoundaryWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  seed.foldedBalloonBoundaryWalk

/-- The sequential folds preserve a based closed walk and reduce its label to
the canonical word for the null element. -/
noncomputable def MinimalAreaRelatorBoundarySeed.foldedBoundaryWalk_isLoop
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    LabelledWalk seed.foldedBoundaryWalk.graph
      (seed.foldedBoundaryWalk.hom.mapVertex
        (Quotient.mk (BoundaryVertexJoinSetoid
          seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs) 0))
      (seed.foldedBoundaryWalk.hom.mapVertex
      (Quotient.mk (BoundaryVertexJoinSetoid
        seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs) 0)) w.toWord :=
  seed.foldedBoundaryWalk.walk

/-- The quotient dart type remains finite through the seed's successive folds. -/
@[instance_reducible]
noncomputable def MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryDartFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Fintype seed.foldedBoundaryWalk.graph.toDartGraph.Dart := by
  classical
  letI : Fintype seed.balloonBoundaryGraph.toDartGraph.Dart := by
    change Fintype
      ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.Dart)
    dsimp [wordPathGraph]
    exact Fintype.ofFinite _
  have hfinite : Finite seed.foldedBoundaryWalk.graph.toDartGraph.Dart := by
    change Finite
      (WalkFoldResult.foldPairsThenReduce seed.boundaryBalloonStemPairs
        seed.boundary.reducedLiteralBoundaryShape.to_cancellationSequence
        seed.balloonBoundaryLoop).graph.toDartGraph.Dart
    exact WalkFoldResult.foldPairsThenReduce_finite
        seed.boundaryBalloonStemPairs
        seed.boundary.reducedLiteralBoundaryShape.to_cancellationSequence
        seed.balloonBoundaryLoop
  letI : Finite seed.foldedBoundaryWalk.graph.toDartGraph.Dart := hfinite
  exact Fintype.ofFinite _

/-- The finite graph on the vertices incident to the seed's folded darts.
The occurrence-path construction uses natural-number vertices and hence has
unused vertices; restricting to dart endpoints yields the finite support used
for future incidence data. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryGraph
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) := by
  letI := seed.finiteFoldedBoundaryDartFintype
  exact seed.foldedBoundaryWalk.graph.endpointRestriction

/-- Map the folded boundary graph into its finite incident-vertex support.
Nontriviality of the requested reduced word supplies a dart, so the map can
send any unused source vertices to a fixed incident vertex. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryHom
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :
    LabelledGraphHom seed.foldedBoundaryWalk.graph
      seed.finiteFoldedBoundaryGraph := by
  classical
  letI := seed.finiteFoldedBoundaryDartFintype
  have hword : w.toWord ≠ [] := by
    intro hnil
    exact hne (FreeGroup.toWord_eq_nil_iff.mp hnil)
  have hdart : Nonempty seed.foldedBoundaryWalk.graph.toDartGraph.Dart :=
    LabelledWalk.exists_dart_of_word_ne_nil
      seed.foldedBoundaryWalk.walk hword
  exact seed.foldedBoundaryWalk.graph.endpointRestrictionHom hdart

/-- The root vertex of the finite folded boundary graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryBasepoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.Vertex :=
  (seed.finiteFoldedBoundaryHom hne).mapVertex
    (seed.foldedBoundaryWalk.hom.mapVertex
      (Quotient.mk (BoundaryVertexJoinSetoid
        seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs) 0))

/-- The target boundary walk on the finite incident-vertex graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :=
  seed.foldedBoundaryWalk.walk.map (seed.finiteFoldedBoundaryHom hne)

/-- Every vertex of the finite folded one-skeleton is joined to its boundary
basepoint by a labeled walk. The source word path visits every dart endpoint,
and the successive quotient maps preserve those walks. -/
theorem MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryVertex_reachable
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (v : seed.finiteFoldedBoundaryGraph.toDartGraph.Vertex) :
    ∃ word, Nonempty (LabelledWalk seed.finiteFoldedBoundaryGraph
      (seed.finiteFoldedBoundaryBasepoint hne) v word) := by
  classical
  letI := seed.finiteFoldedBoundaryDartFintype
  obtain ⟨d, hd⟩ := seed.foldedBoundaryWalk.graph.activeVertex_incident v
  have hsource : ∃ e, seed.foldedBoundaryWalk.graph.toDartGraph.source e = v.1 := by
    rcases hd with hs | ht
    · exact ⟨d, hs⟩
    · exact ⟨seed.foldedBoundaryWalk.graph.toDartGraph.reverse d, by
        rw [seed.foldedBoundaryWalk.graph.toDartGraph.source_reverse]
        exact ht⟩
  obtain ⟨dFinal, hdFinal⟩ := hsource
  obtain ⟨dSource, hdSource⟩ :=
    seed.foldedBoundaryWalk.hom_surjective dFinal
  let prefixWalk := wordBoundaryPrefixWalkToDartSource
    seed.boundary.reducedLiteralBoundary seed.balloonEndpointPairs dSource
  let mappedWalk := (prefixWalk.map seed.foldedBoundaryWalk.hom).map
    (seed.finiteFoldedBoundaryHom hne)
  have htargetRaw :
      seed.foldedBoundaryWalk.hom.mapVertex
          (seed.balloonBoundaryGraph.toDartGraph.source dSource) =
        seed.foldedBoundaryWalk.graph.toDartGraph.source dFinal := by
    calc
      _ = seed.foldedBoundaryWalk.graph.toDartGraph.source
          (seed.foldedBoundaryWalk.hom.mapDart dSource) :=
        (seed.foldedBoundaryWalk.hom.map_source dSource).symm
      _ = seed.foldedBoundaryWalk.graph.toDartGraph.source dFinal :=
        congrArg seed.foldedBoundaryWalk.graph.toDartGraph.source hdSource
  have htarget :
      (seed.finiteFoldedBoundaryHom hne).mapVertex
          (seed.foldedBoundaryWalk.hom.mapVertex
            (seed.balloonBoundaryGraph.toDartGraph.source dSource)) = v := by
    apply Subtype.ext
    calc
      _ = seed.foldedBoundaryWalk.graph.toDartGraph.source dFinal := by
        rw [htargetRaw]
        simp [MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryHom]
      _ = v.1 := hdFinal
  refine ⟨(seed.boundary.reducedLiteralBoundary).take
      (if dSource.2 then dSource.1.val + 1 else dSource.1.val), ?_⟩
  exact ⟨htarget ▸ mappedWalk⟩

/-- The indexed relator-face loop family, now carried by the same finite graph
as the target boundary walk. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteBalloonRelatorLoopAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    RelatorBoundaryLoop P seed.finiteFoldedBoundaryGraph := by
  let hom := seed.finiteFoldedBoundaryHom hne
  let balloon := seed.boundary.reducedBalloons.get i
  let loop := seed.balloonRelatorLoopAt i
  refine ⟨balloon.label.relator, balloon.label.relator_mem,
    P.relator_isCyclicallyReduced balloon.label.relator_mem,
    hom.mapVertex loop.1, ?_⟩
  simpa [balloon] using loop.2.map hom

/-- The occurrence-specific embedding before the boundary and folding
quotients. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonOccurrenceEmbedding
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length) :=
  reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i

/-- Its two endpoint positions are the indexed balloon's own endpoint join,
so repeated equal balloon values remain distinct occurrences. -/
theorem MinimalAreaRelatorBoundarySeed.balloonOccurrenceEmbedding_endpoints_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length) :
    ((seed.balloonOccurrenceEmbedding i).mapVertex (0 : Nat),
      (seed.balloonOccurrenceEmbedding i).mapVertex
        ((seed.boundary.reducedBalloons.get i).label.rawWord.length)) ∈
      seed.balloonEndpointPairs := by
  simpa [MinimalAreaRelatorBoundarySeed.balloonOccurrenceEmbedding,
    MinimalAreaRelatorBoundarySeed.balloonEndpointPairs] using
    reducedBalloonOccurrencePathEmbedding_endpoints_mem
      seed.boundary.reducedBalloons i

/-- An individual oriented side occurrence of an indexed balloon face. -/
abbrev RelatorBalloonFaceSide {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  Σ i : Fin seed.boundary.reducedBalloons.length,
    Fin ((seed.boundary.reducedBalloons.get i).label.rawWord.length)

/-- The occurrence-specific graph map from one balloon boundary path to the
finite folded graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteBalloonOccurrenceHom
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    LabelledGraphHom
      (wordPathGraph ((seed.boundary.reducedBalloons.get i).label.rawWord))
      seed.finiteFoldedBoundaryGraph := by
  exact LabelledGraphHom.comp (seed.finiteFoldedBoundaryHom hne)
    (LabelledGraphHom.comp seed.foldedBalloonBoundaryWalk.hom
      (LabelledGraphHom.comp seed.balloonBoundaryHom
        (seed.balloonOccurrenceEmbedding i)))

/-- The complete conjugate-relator boundary of each indexed balloon is a loop
in the same finite folded graph as the target boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteBalloonBoundaryLoopAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length) :
    RelatorBalloonBoundaryLoop P seed.finiteFoldedBoundaryGraph := by
  classical
  let balloon := seed.boundary.reducedBalloons.get i
  let embedding := seed.balloonOccurrenceEmbedding i
  let hom := seed.finiteBalloonOccurrenceHom hne i
  let ends := (embedding.mapVertex (0 : Nat),
    embedding.mapVertex balloon.label.rawWord.length)
  have hends : ends ∈ seed.balloonEndpointPairs := by
    simpa [ends, balloon] using
      seed.balloonOccurrenceEmbedding_endpoints_mem i
  have hjoin := wordBoundary_join_eq seed.boundary.reducedLiteralBoundary
    seed.balloonEndpointPairs ends hends
  have hboundary : seed.balloonBoundaryHom.mapVertex
        (embedding.mapVertex (0 : Nat)) =
      seed.balloonBoundaryHom.mapVertex
        (embedding.mapVertex balloon.label.rawWord.length) := by
    change (Quotient.mk (BoundaryVertexJoinSetoid
        seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs)
        (embedding.mapVertex (0 : Nat))) =
      Quotient.mk (BoundaryVertexJoinSetoid
        seed.boundary.reducedLiteralBoundary.length seed.balloonEndpointPairs)
        (embedding.mapVertex balloon.label.rawWord.length)
    exact hjoin
  let start := hom.mapVertex (0 : Nat)
  let finish := hom.mapVertex balloon.label.rawWord.length
  have hstartFinish : start = finish := by
    change (seed.finiteFoldedBoundaryHom hne).mapVertex
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex (0 : Nat)))) =
      (seed.finiteFoldedBoundaryHom hne).mapVertex
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex balloon.label.rawWord.length)))
    exact congrArg
      (fun v => (seed.finiteFoldedBoundaryHom hne).mapVertex
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex v)) hboundary
  have hwalk : LabelledWalk seed.finiteFoldedBoundaryGraph start finish
      balloon.label.rawWord := by
    simpa [start, finish, balloon] using
      (wordPathWalk balloon.label.rawWord).map hom
  refine ⟨balloon, start, ?_⟩
  exact Eq.mp (congrArg
    (fun endpoint => LabelledWalk seed.finiteFoldedBoundaryGraph
      start endpoint balloon.label.rawWord) hstartFinish.symm) hwalk

/-- The occurrence-indexed face-side map into the finite folded graph. The
index preserves each side even when two balloon words or relator labels agree.
-/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteBalloonFaceSideDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.rawWord.length)) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.Dart := by
  exact (seed.finiteBalloonOccurrenceHom hne i).mapDart (j, false)

/-- The indexed face-side map preserves the attaching-word label. -/
@[simp]
theorem MinimalAreaRelatorBoundarySeed.finiteBalloonFaceSideDart_label
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.rawWord.length)) :
    seed.finiteFoldedBoundaryGraph.label
      (seed.finiteBalloonFaceSideDart hne i j) =
      (seed.boundary.reducedBalloons.get i).label.rawWord[j] := by
  change seed.finiteFoldedBoundaryGraph.label
    ((seed.finiteBalloonOccurrenceHom hne i).mapDart (j, false)) = _
  simpa [wordPathGraph] using
    (seed.finiteBalloonOccurrenceHom hne i).map_label (j, false)

/-- The indexed relator sides inside a balloon, transported to the finite
folded graph. The index is in the defining relator rather than the longer
lollipop boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteBalloonRelatorSideDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.Dart :=
  (seed.finiteBalloonOccurrenceHom hne i).mapDart
    ((seed.boundary.reducedBalloons.get i).relatorSideDart j)

/-- Every transported relator side has exactly its source relator label. -/
@[simp] theorem MinimalAreaRelatorBoundarySeed.finiteBalloonRelatorSideDart_label
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    seed.finiteFoldedBoundaryGraph.label
      (seed.finiteBalloonRelatorSideDart hne i j) =
        (seed.boundary.reducedBalloons.get i).label.relator.toWord[j] := by
  change seed.finiteFoldedBoundaryGraph.label
      ((seed.finiteBalloonOccurrenceHom hne i).mapDart
        ((seed.boundary.reducedBalloons.get i).relatorSideDart j)) = _
  rw [(seed.finiteBalloonOccurrenceHom hne i).map_label]
  exact (seed.boundary.reducedBalloons.get i).relatorSideDart_label j

/-- Relator-side endpoints map from the exact position in the lollipop
occurrence path. -/
theorem MinimalAreaRelatorBoundarySeed.finiteBalloonRelatorSideDart_source
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.source
      (seed.finiteBalloonRelatorSideDart hne i j) =
      (seed.finiteBalloonOccurrenceHom hne i).mapVertex
        ((seed.boundary.reducedBalloons.get i).label.conjugator.toWord.length +
          j.val) := by
  change seed.finiteFoldedBoundaryGraph.toDartGraph.source
      ((seed.finiteBalloonOccurrenceHom hne i).mapDart
        ((seed.boundary.reducedBalloons.get i).relatorSideDart j)) = _
  rw [(seed.finiteBalloonOccurrenceHom hne i).map_source]
  simp [wordPathGraph, ReducedRelatorBalloonData.relatorSideDart_index]

theorem MinimalAreaRelatorBoundarySeed.finiteBalloonRelatorSideDart_target
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.target
      (seed.finiteBalloonRelatorSideDart hne i j) =
      (seed.finiteBalloonOccurrenceHom hne i).mapVertex
        ((seed.boundary.reducedBalloons.get i).label.conjugator.toWord.length +
          j.val + 1) := by
  change seed.finiteFoldedBoundaryGraph.toDartGraph.target
      ((seed.finiteBalloonOccurrenceHom hne i).mapDart
        ((seed.boundary.reducedBalloons.get i).relatorSideDart j)) = _
  rw [(seed.finiteBalloonOccurrenceHom hne i).map_target]
  simp [wordPathGraph, ReducedRelatorBalloonData.relatorSideDart_index]

/-- The source of each face-side dart is the corresponding occurrence-path
vertex under the indexed face map. -/
theorem MinimalAreaRelatorBoundarySeed.finiteBalloonFaceSideDart_source
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.rawWord.length)) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.source
      (seed.finiteBalloonFaceSideDart hne i j) =
      (seed.finiteBalloonOccurrenceHom hne i).mapVertex j.val := by
  change seed.finiteFoldedBoundaryGraph.toDartGraph.source
      ((seed.finiteBalloonOccurrenceHom hne i).mapDart (j, false)) = _
  simpa [wordPathGraph] using
    (seed.finiteBalloonOccurrenceHom hne i).map_source (j, false)

/-- The target of each face-side dart is the next occurrence-path vertex under
the indexed face map. -/
theorem MinimalAreaRelatorBoundarySeed.finiteBalloonFaceSideDart_target
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.rawWord.length)) :
    seed.finiteFoldedBoundaryGraph.toDartGraph.target
      (seed.finiteBalloonFaceSideDart hne i j) =
      (seed.finiteBalloonOccurrenceHom hne i).mapVertex (j.val + 1) := by
  change seed.finiteFoldedBoundaryGraph.toDartGraph.target
      ((seed.finiteBalloonOccurrenceHom hne i).mapDart (j, false)) = _
  simpa [wordPathGraph] using
    (seed.finiteBalloonOccurrenceHom hne i).map_target (j, false)

/-- The sum of the attaching-word side counts of the indexed balloon faces is
the complete lollipop boundary length, including the letters removed by the
later boundary cancellations. -/
theorem MinimalAreaRelatorBoundarySeed.sum_balloonBoundary_length
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    (seed.boundary.reducedBalloons.map
      (fun b => b.label.rawWord.length)).sum =
      w.toWord.length + 2 * seed.boundary.cancellation.cancellationCount := by
  have hlength : seed.boundary.reducedLiteralBoundary.length =
      (seed.boundary.reducedBalloons.map
        (fun b => b.label.rawWord.length)).sum := by
    simp [RelatorFactorBoundarySeed.reducedLiteralBoundary, Function.comp_def]
  rw [← hlength]
  exact seed.boundary.reducedLiteralBoundary_length_eq

end GreendlingerDehn
