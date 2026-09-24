import SmallCancellation.DartGraphFold

namespace GreendlingerDehn

/-- The occurrence path of a finite word. Darts are source positions with a
forward or reverse orientation; vertices are natural-number positions. -/
def wordPathGraph {α : Type*} (word : Word α) : LabelledDartGraph α where
  toDartGraph := {
    Dart := Fin word.length × Bool
    Vertex := Nat
    reverse := fun d => (d.1, !d.2)
    source := fun d => if d.2 then d.1.val + 1 else d.1.val
    target := fun d => if d.2 then d.1.val else d.1.val + 1
    reverse_involutive := by
      intro d
      cases d with
      | mk i direction => cases direction <;> rfl
    source_reverse := by
      intro d
      cases d with
      | mk i direction => cases direction <;> rfl
    target_reverse := by
      intro d
      cases d with
      | mk i direction => cases direction <;> rfl
  }
  label := fun d => if d.2 then inverseLetter (word[d.1]) else word[d.1]
  label_reverse := by
    intro d
    cases d with
    | mk i direction =>
        cases direction <;> simp [inverseLetter]

/-- Shift the occurrence path of a suffix into the corresponding suffix of a
larger word. -/
def wordPathShiftHom {α : Type*} (a : Letter α) (tail : Word α) :
    LabelledGraphHom (wordPathGraph tail) (wordPathGraph (a :: tail)) where
  mapVertex := Nat.succ
  mapDart := fun d => (Fin.succ d.1, d.2)
  map_reverse := by
    intro d
    cases d with
    | mk i direction => cases direction <;> rfl
  map_source := by
    intro d
    cases d with
    | mk i direction => cases direction <;> rfl
  map_target := by
    intro d
    cases d with
    | mk i direction => cases direction <;> rfl
  map_label := by
    intro d
    cases d with
    | mk i direction => cases direction <;> simp [wordPathGraph]

/-- Every word is the label sequence of its canonical occurrence path. -/
noncomputable def wordPathWalk {α : Type*} :
    (word : Word α) →
      LabelledWalk (wordPathGraph word) (0 : Nat) word.length word
  | [] => LabelledWalk.nil (G := wordPathGraph ([] : Word α)) (0 : Nat)
  | a :: tail => by
      let shifted := (wordPathWalk tail).map (wordPathShiftHom a tail)
      let firstDart : Fin (a :: tail).length × Bool :=
        (⟨0, by simp⟩, false)
      have hsource :
          (wordPathGraph (a :: tail)).toDartGraph.source
              firstDart = (0 : Nat) := rfl
      have htarget :
          (wordPathGraph (a :: tail)).toDartGraph.target
              firstDart = (1 : Nat) := rfl
      simpa [wordPathGraph, firstDart, wordPathShiftHom, shifted] using
        (LabelledWalk.cons firstDart hsource htarget shifted)

/-- The generating identification that closes the ends of the occurrence
path into a polygonal boundary circuit. -/
def BoundaryVertexGenerator (n : Nat) (x y : Nat) : Prop :=
  (x = 0 ∧ y = n) ∨ (x = n ∧ y = 0)

/-- Vertex equivalence relation for the polygonal boundary of a word. -/
def BoundaryVertexSetoid (n : Nat) : Setoid Nat :=
  Relation.EqvGen.setoid (BoundaryVertexGenerator n)

/-- Vertices in the boundary circuit of a word. -/
abbrev WordBoundaryVertex {α : Type*} (word : Word α) :=
  Quotient (BoundaryVertexSetoid word.length)

/-- The occurrence path with its two endpoints identified. -/
def wordBoundaryGraph {α : Type*} (word : Word α) : LabelledDartGraph α where
  toDartGraph := {
    Dart := (wordPathGraph word).toDartGraph.Dart
    Vertex := WordBoundaryVertex word
    reverse := (wordPathGraph word).toDartGraph.reverse
    source := fun d => Quotient.mk (BoundaryVertexSetoid word.length)
      ((wordPathGraph word).toDartGraph.source d)
    target := fun d => Quotient.mk (BoundaryVertexSetoid word.length)
      ((wordPathGraph word).toDartGraph.target d)
    reverse_involutive := (wordPathGraph word).toDartGraph.reverse_involutive
    source_reverse := by
      intro d
      exact congrArg (Quotient.mk (BoundaryVertexSetoid word.length))
        ((wordPathGraph word).toDartGraph.source_reverse d)
    target_reverse := by
      intro d
      exact congrArg (Quotient.mk (BoundaryVertexSetoid word.length))
        ((wordPathGraph word).toDartGraph.target_reverse d)
  }
  label := (wordPathGraph word).label
  label_reverse := (wordPathGraph word).label_reverse

/-- The quotient map from the word path to its boundary circuit. -/
def wordPathBoundaryHom {α : Type*} (word : Word α) :
    LabelledGraphHom (wordPathGraph word) (wordBoundaryGraph word) where
  mapVertex := Quotient.mk (BoundaryVertexSetoid word.length)
  mapDart := fun d => d
  map_reverse := by intro d; rfl
  map_source := by intro d; rfl
  map_target := by intro d; rfl
  map_label := by intro d; rfl

/-- The endpoints of a word path coincide in its boundary circuit. -/
theorem wordBoundary_endpoints_eq {α : Type*} (word : Word α) :
    (Quotient.mk (BoundaryVertexSetoid word.length) 0 : WordBoundaryVertex word) =
      Quotient.mk (BoundaryVertexSetoid word.length) word.length := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩)

/-- Every finite word is represented by a based loop around its polygonal
boundary. -/
noncomputable def wordBoundaryLoop {α : Type*} (word : Word α) :
    LabelledWalk (wordBoundaryGraph word)
      (Quotient.mk (BoundaryVertexSetoid word.length) 0)
      (Quotient.mk (BoundaryVertexSetoid word.length) 0) word :=
  let boundaryWalk := (wordPathWalk word).map (wordPathBoundaryHom word)
  Eq.mp
    (congrArg
      (fun endpoint : WordBoundaryVertex word =>
        LabelledWalk (wordBoundaryGraph word)
          (Quotient.mk (BoundaryVertexSetoid word.length) 0) endpoint word)
      (wordBoundary_endpoints_eq word).symm)
    boundaryWalk

end GreendlingerDehn
