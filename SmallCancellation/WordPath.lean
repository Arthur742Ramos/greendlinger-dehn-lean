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

/-- The literal boundary word of a lollipop with stem `stem` and relator
boundary `relator`. -/
abbrev lollipopBoundaryWord {α : Type*} (stem relator : Word α) : Word α :=
  stem ++ relator ++ FreeGroup.invRev stem

/-- The position of a stem letter on the outward side of a lollipop. -/
abbrev lollipopStemFirstIndex {α : Type*} (stem relator : Word α)
    (i : Fin stem.length) : Fin (lollipopBoundaryWord stem relator).length :=
  ⟨i.val, by simp [lollipopBoundaryWord, FreeGroup.invRev_length]; omega⟩

/-- The position paired to a stem letter on the return side of a lollipop. -/
abbrev lollipopStemMateIndex {α : Type*} (stem relator : Word α)
    (i : Fin stem.length) : Fin (lollipopBoundaryWord stem relator).length :=
  ⟨stem.length + relator.length + (stem.length - (i.val + 1)), by
    simp [lollipopBoundaryWord, FreeGroup.invRev_length]
    omega⟩

/-- A forward occurrence of a stem letter has the inverse label at its paired
return occurrence. -/
theorem lollipopBoundaryWord_get_stemMate {α : Type*}
    (stem relator : Word α) (i : Fin stem.length) :
    (lollipopBoundaryWord stem relator).get (lollipopStemMateIndex stem relator i) =
      inverseLetter (stem.get i) := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [lollipopBoundaryWord]
  have hprefix : (stem ++ relator).length ≤
      stem.length + relator.length + (stem.length - (i.val + 1)) := by
    simp only [List.length_append]
    omega
  rw [List.getElem_append_right hprefix]
  have hindex :
      stem.length + relator.length + (stem.length - (i.val + 1)) -
        (stem ++ relator).length = stem.length - 1 - i.val := by
    simp only [List.length_append]
    omega
  simp only [hindex]
  have hdouble : stem.length - 1 - (stem.length - 1 - i.val) = i.val := by omega
  simp [FreeGroup.invRev, List.getElem_reverse, hdouble, inverseLetter]

/-- The outward stem position carries its original letter. -/
theorem lollipopBoundaryWord_get_stem {α : Type*}
    (stem relator : Word α) (i : Fin stem.length) :
    (lollipopBoundaryWord stem relator).get (lollipopStemFirstIndex stem relator i) =
      stem.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [lollipopBoundaryWord]
  rw [List.getElem_append_left (by
    simp only [List.length_append]
    omega)]
  rw [List.getElem_append_left i.isLt]

/-- The edge-occurrence pair that folds one doubled conjugator edge in the
lollipop boundary path. -/
def lollipopStemPair {α : Type*} (stem relator : Word α)
    (i : Fin stem.length) :
    LabelledDartPair (wordPathGraph (lollipopBoundaryWord stem relator)) where
  first := (lollipopStemFirstIndex stem relator i, false)
  second := (lollipopStemMateIndex stem relator i, false)
  inverse_labels := by
    change (lollipopBoundaryWord stem relator).get (lollipopStemFirstIndex stem relator i) =
      inverseLetter ((lollipopBoundaryWord stem relator).get
        (lollipopStemMateIndex stem relator i))
    rw [lollipopBoundaryWord_get_stem, lollipopBoundaryWord_get_stemMate]
    simp [LabelledDartGraph.inverseLetter_inverse]

/-- All doubled stem-edge pairs in one lollipop, in order from the basepoint
toward the relator face. -/
def lollipopStemPairs {α : Type*} (stem relator : Word α) :
    List (LabelledDartPair (wordPathGraph (lollipopBoundaryWord stem relator))) :=
  (List.finRange stem.length).map (lollipopStemPair stem relator)

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

/-- Embed the occurrence path of a prefix into the path of a concatenation. -/
def wordPathPrefixHom {α : Type*} (pre suf : Word α) :
    LabelledGraphHom (wordPathGraph pre)
      (wordPathGraph (pre ++ suf)) where
  mapVertex := id
  mapDart := fun d => (⟨d.1.val, by simp; omega⟩, d.2)
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
    | mk i direction =>
      cases direction <;>
        simp [wordPathGraph, List.getElem_append_left]

/-- Embed the occurrence path of a suffix into the suffix segment of a
concatenated word's occurrence path. -/
def wordPathSuffixHom {α : Type*} (pre suf : Word α) :
    LabelledGraphHom (wordPathGraph suf)
      (wordPathGraph (pre ++ suf)) where
  mapVertex := by
    intro v
    change Nat at v
    change Nat
    exact pre.length + v
  mapDart := fun d =>
    (⟨pre.length + d.1.val, by
      simp only [List.length_append]
      omega⟩, d.2)
  map_reverse := by
    intro d
    cases d with
    | mk i direction => cases direction <;> rfl
  map_source := by
    intro d
    cases d with
    | mk i direction =>
        cases direction <;> simp [wordPathGraph]
        all_goals omega
  map_target := by
    intro d
    cases d with
    | mk i direction =>
        cases direction <;> simp [wordPathGraph]
        all_goals omega
  map_label := by
    intro d
    cases d with
    | mk i direction =>
      cases direction <;>
        simp [wordPathGraph, List.getElem_append_right]

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
      exact LabelledWalk.cons firstDart hsource htarget shifted

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

/-- Additional vertex identifications used when a concatenated boundary is
viewed as a wedge of its lollipop loops. -/
def BoundaryVertexJoinGenerator (n : Nat) (joins : List (Nat × Nat))
    (x y : Nat) : Prop :=
  BoundaryVertexGenerator n x y ∨
    ∃ pair ∈ joins, x = pair.1 ∧ y = pair.2

/-- Vertex equivalence generated by the polygon closure and selected lollipop
endpoint joins. -/
def BoundaryVertexJoinSetoid (n : Nat) (joins : List (Nat × Nat)) : Setoid Nat :=
  Relation.EqvGen.setoid (BoundaryVertexJoinGenerator n joins)

/-- Vertices in a polygonal boundary with extra lollipop endpoint joins. -/
abbrev WordBoundaryVertexWithJoins {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) :=
  Quotient (BoundaryVertexJoinSetoid word.length joins)

/-- The occurrence path with its outer endpoints closed and each requested
lollipop endpoint pair identified. -/
def wordBoundaryGraphWithJoins {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) : LabelledDartGraph α where
  toDartGraph := {
    Dart := (wordPathGraph word).toDartGraph.Dart
    Vertex := WordBoundaryVertexWithJoins word joins
    reverse := (wordPathGraph word).toDartGraph.reverse
    source := fun d => Quotient.mk (BoundaryVertexJoinSetoid word.length joins)
      ((wordPathGraph word).toDartGraph.source d)
    target := fun d => Quotient.mk (BoundaryVertexJoinSetoid word.length joins)
      ((wordPathGraph word).toDartGraph.target d)
    reverse_involutive := (wordPathGraph word).toDartGraph.reverse_involutive
    source_reverse := by
      intro d
      exact congrArg (Quotient.mk (BoundaryVertexJoinSetoid word.length joins))
        ((wordPathGraph word).toDartGraph.source_reverse d)
    target_reverse := by
      intro d
      exact congrArg (Quotient.mk (BoundaryVertexJoinSetoid word.length joins))
        ((wordPathGraph word).toDartGraph.target_reverse d)
  }
  label := (wordPathGraph word).label
  label_reverse := (wordPathGraph word).label_reverse

/-- Map an occurrence path into its polygon boundary with endpoint joins. -/
def wordPathBoundaryHomWithJoins {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) :
    LabelledGraphHom (wordPathGraph word)
      (wordBoundaryGraphWithJoins word joins) where
  mapVertex := Quotient.mk (BoundaryVertexJoinSetoid word.length joins)
  mapDart := fun d => d
  map_reverse := by intro d; rfl
  map_source := by intro d; rfl
  map_target := by intro d; rfl
  map_label := by intro d; rfl

/-- The outer endpoints remain identified after adding lollipop joins. -/
theorem wordBoundary_endpoints_eq_withJoins {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) :
    (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0 :
      WordBoundaryVertexWithJoins word joins) =
        Quotient.mk (BoundaryVertexJoinSetoid word.length joins) word.length := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inl (Or.inl ⟨rfl, rfl⟩))

/-- Every selected lollipop endpoint pair is equal in the joined boundary
vertex quotient. -/
theorem wordBoundary_join_eq {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) (pair : Nat × Nat) (hpair : pair ∈ joins) :
    (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) pair.1 :
      WordBoundaryVertexWithJoins word joins) =
        Quotient.mk (BoundaryVertexJoinSetoid word.length joins) pair.2 := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _
    (Or.inr ⟨pair, hpair, rfl, rfl⟩)

/-- Every concatenated word is a based loop in its polygon boundary after the
requested lollipop endpoint joins have been installed. -/
noncomputable def wordBoundaryLoopWithJoins {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) :
    LabelledWalk (wordBoundaryGraphWithJoins word joins)
      (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0)
      (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0) word :=
  let boundaryWalk :=
    (wordPathWalk word).map (wordPathBoundaryHomWithJoins word joins)
  Eq.mp
    (congrArg
      (fun endpoint => LabelledWalk (wordBoundaryGraphWithJoins word joins)
        (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0) endpoint word)
      (wordBoundary_endpoints_eq_withJoins word joins).symm)
    boundaryWalk

/-- The prefix of a polygon boundary reaches the vertex at its cut position.
This makes every occurrence vertex accessible from the boundary basepoint. -/
noncomputable def wordBoundaryPrefixWalkWithJoins {α : Type*}
    (word : Word α) (joins : List (Nat × Nat)) (k : Nat)
    (hk : k ≤ word.length) :
    LabelledWalk (wordBoundaryGraphWithJoins word joins)
      (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0)
      (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) k)
      (word.take k) := by
  let preWord := word.take k
  let sufWord := word.drop k
  have hsplit : preWord ++ sufWord = word := List.take_append_drop k word
  have hlen : preWord.length = k := by
    dsimp [preWord]
    simp [List.length_take, Nat.min_eq_left hk]
  let path := (wordPathWalk preWord).map (wordPathPrefixHom preWord sufWord)
  have path' : LabelledWalk (wordPathGraph word) (0 : Nat) (k : Nat) preWord := by
    rw [← hsplit]
    simpa [path, wordPathPrefixHom, id, hlen] using path
  exact path'.map (wordPathBoundaryHomWithJoins word joins)

/-- A directed edge occurrence starts at a vertex reached by a boundary
prefix. -/
noncomputable def wordBoundaryPrefixWalkToDartSource {α : Type*}
    (word : Word α) (joins : List (Nat × Nat))
    (d : (wordBoundaryGraphWithJoins word joins).toDartGraph.Dart) :
    LabelledWalk (wordBoundaryGraphWithJoins word joins)
      (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0)
      ((wordBoundaryGraphWithJoins word joins).toDartGraph.source d)
      (word.take (if d.2 then d.1.val + 1 else d.1.val)) := by
  let k := if d.2 then d.1.val + 1 else d.1.val
  have hk : k ≤ word.length := by
    dsimp [k]
    by_cases hd : d.2
    · simp [hd]
      omega
    · simp [hd]
  let prefixWalk := wordBoundaryPrefixWalkWithJoins word joins k hk
  have hsource :
      (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) k :
        WordBoundaryVertexWithJoins word joins) =
        (wordBoundaryGraphWithJoins word joins).toDartGraph.source d := by
    cases d with
    | mk i direction =>
        cases direction <;>
          simp [k, wordBoundaryGraphWithJoins, wordPathGraph]
  simpa [prefixWalk, k] using hsource ▸ prefixWalk

end GreendlingerDehn
