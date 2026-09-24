import SmallCancellation.DartGraphFold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

namespace GreendlingerDehn

namespace LabelledWalk

/-- Any nonempty labeled walk contains a dart. -/
theorem exists_dart_of_word_ne_nil {α : Type*}
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    {word : Word α} (walk : LabelledWalk G u v word)
    (hword : word ≠ []) : Nonempty G.toDartGraph.Dart := by
  cases walk with
  | nil vertex => simp at hword
  | cons dart hsource htarget tail => exact ⟨dart⟩

end LabelledWalk

namespace WalkFoldResult

/-- Finiteness of the input darts passes to the final successive-fold graph. -/
theorem foldPairsThenReduce_finite {α : Type*}
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    {raw reduced : Word α}
    [Finite G.toDartGraph.Dart]
    (pairs : List (LabelledDartPair G))
    (steps : FreeCancellationSequence raw reduced)
    (walk : LabelledWalk G u v raw) :
    Finite (foldPairsThenReduce pairs steps walk).graph.toDartGraph.Dart := by
  exact Finite.of_surjective
    (foldPairsThenReduce pairs steps walk).hom.mapDart
    (foldPairsThenReduce pairs steps walk).hom_surjective

end WalkFoldResult

namespace LabelledDartGraph

/-- The finite set of vertices incident to at least one dart. This cuts away
the unused natural-number vertices in occurrence-path quotients. -/
noncomputable def endpointFinset {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] : Finset G.toDartGraph.Vertex := by
  classical
  exact (Finset.univ.image G.toDartGraph.source) ∪
    (Finset.univ.image G.toDartGraph.target)

/-- A vertex in the finite support of a finite-dart graph. -/
abbrev ActiveVertex {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] :=
  {v : G.toDartGraph.Vertex // v ∈ G.endpointFinset}

noncomputable instance activeVertexFintype {α : Type*}
    (G : LabelledDartGraph α) [Fintype G.toDartGraph.Dart] :
    Fintype G.ActiveVertex := by
  classical
  exact Fintype.ofFinset G.endpointFinset (by intro v; rfl)

theorem source_mem_endpointFinset {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] (d : G.toDartGraph.Dart) :
    G.toDartGraph.source d ∈ G.endpointFinset := by
  classical
  unfold endpointFinset
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩

theorem target_mem_endpointFinset {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] (d : G.toDartGraph.Dart) :
    G.toDartGraph.target d ∈ G.endpointFinset := by
  classical
  unfold endpointFinset
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩

/-- Every vertex in the finite support is incident to an edge dart. -/
theorem activeVertex_incident {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] (v : G.ActiveVertex) :
    ∃ d, G.toDartGraph.source d = v.1 ∨ G.toDartGraph.target d = v.1 := by
  classical
  have hv := v.2
  unfold endpointFinset at hv
  rcases Finset.mem_union.mp hv with hs | ht
  · rcases Finset.mem_image.mp hs with ⟨d, _, h⟩
    exact ⟨d, Or.inl h⟩
  · rcases Finset.mem_image.mp ht with ⟨d, _, h⟩
    exact ⟨d, Or.inr h⟩

/-- The restriction of a finite-dart graph to precisely its incident
vertices. Its dart and label data are unchanged. -/
def endpointRestriction {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] : LabelledDartGraph α where
  toDartGraph := {
    Dart := G.toDartGraph.Dart
    Vertex := G.ActiveVertex
    reverse := G.toDartGraph.reverse
    source := fun d => ⟨G.toDartGraph.source d, G.source_mem_endpointFinset d⟩
    target := fun d => ⟨G.toDartGraph.target d, G.target_mem_endpointFinset d⟩
    reverse_involutive := G.toDartGraph.reverse_involutive
    source_reverse := by
      intro d
      apply Subtype.ext
      exact G.toDartGraph.source_reverse d
    target_reverse := by
      intro d
      apply Subtype.ext
      exact G.toDartGraph.target_reverse d
  }
  label := G.label
  label_reverse := G.label_reverse

/-- Map arbitrary vertices into the finite support. A missing endpoint is
sent to a fixed incident vertex; graph homomorphisms only inspect dart
endpoints, which are always retained exactly. -/
noncomputable def endpointMap {α : Type*} (G : LabelledDartGraph α)
    [Fintype G.toDartGraph.Dart] (hne : Nonempty G.toDartGraph.Dart)
    (v : G.toDartGraph.Vertex) : G.ActiveVertex := by
  classical
  by_cases hv : v ∈ G.endpointFinset
  · exact ⟨v, hv⟩
  · exact ⟨G.toDartGraph.source (Classical.choice hne),
      G.source_mem_endpointFinset (Classical.choice hne)⟩

/-- The canonical graph homomorphism from a finite-dart graph to its finite
incident-vertex restriction. -/
noncomputable def endpointRestrictionHom {α : Type*}
    (G : LabelledDartGraph α) [Fintype G.toDartGraph.Dart]
    (hne : Nonempty G.toDartGraph.Dart) :
    LabelledGraphHom G G.endpointRestriction where
  mapVertex := G.endpointMap hne
  mapDart := id
  map_reverse := by intro d; rfl
  map_source := by
    intro d
    change (⟨G.toDartGraph.source d, G.source_mem_endpointFinset d⟩ :
      G.ActiveVertex) = G.endpointMap hne (G.toDartGraph.source d)
    apply Subtype.ext
    simp [endpointMap, G.source_mem_endpointFinset]
  map_target := by
    intro d
    change (⟨G.toDartGraph.target d, G.target_mem_endpointFinset d⟩ :
      G.ActiveVertex) = G.endpointMap hne (G.toDartGraph.target d)
    apply Subtype.ext
    simp [endpointMap, G.target_mem_endpointFinset]
  map_label := by intro d; rfl

@[simp] theorem endpointRestrictionHom_mapVertex_source {α : Type*}
    (G : LabelledDartGraph α) [Fintype G.toDartGraph.Dart]
    (hne : Nonempty G.toDartGraph.Dart) (d : G.toDartGraph.Dart) :
    (G.endpointRestrictionHom hne).mapVertex (G.toDartGraph.source d) =
      ⟨G.toDartGraph.source d, G.source_mem_endpointFinset d⟩ := by
  change G.endpointMap hne (G.toDartGraph.source d) = _
  simp [endpointMap, G.source_mem_endpointFinset]

@[simp] theorem endpointRestrictionHom_mapVertex_source_val {α : Type*}
    (G : LabelledDartGraph α) [Fintype G.toDartGraph.Dart]
    (hne : Nonempty G.toDartGraph.Dart) (d : G.toDartGraph.Dart) :
    ((G.endpointRestrictionHom hne).mapVertex
      (G.toDartGraph.source d)).1 = G.toDartGraph.source d := by
  simp [endpointRestrictionHom, endpointMap, G.source_mem_endpointFinset]

end LabelledDartGraph

end GreendlingerDehn
