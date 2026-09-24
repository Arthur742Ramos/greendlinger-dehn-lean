import SmallCancellation.PlanarBoundarySeed
import SmallCancellation.LollipopFolds

namespace GreendlingerDehn

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

end GreendlingerDehn
