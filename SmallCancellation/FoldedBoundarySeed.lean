import SmallCancellation.PlanarBoundarySeed
import SmallCancellation.LollipopFolds
import SmallCancellation.FiniteSupport

namespace GreendlingerDehn

/-- A face boundary carried by a finite map, with its defining-relator
provenance retained explicitly. -/
structure RelatorBoundaryLoop {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (G : LabelledDartGraph α) where
  relator : FreeGroup α
  relator_mem : relator ∈ P.relators
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

/-- The target boundary walk on the finite incident-vertex graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.finiteFoldedBoundaryWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) (hne : w ≠ 1) :=
  seed.foldedBoundaryWalk.walk.map (seed.finiteFoldedBoundaryHom hne)

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
    hom.mapVertex loop.1, ?_⟩
  simpa [balloon] using loop.2.map hom

end GreendlingerDehn
