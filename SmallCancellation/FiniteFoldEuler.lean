import SmallCancellation.DartGraphFold
import SmallCancellation.FiniteQuotientCounting
import Mathlib.SetTheory.Cardinal.Finite

namespace GreendlingerDehn

/-- A fold of a finite graph remains finite on both vertices and darts. -/
theorem LabelledDartGraph.folded_finite {α : Type*}
    (G : LabelledDartGraph α) [Finite G.toDartGraph.Vertex]
    [Finite G.toDartGraph.Dart] (a b : G.toDartGraph.Dart)
    (hlabels : G.label a = inverseLetter (G.label b)) :
    Finite (G.folded α a b hlabels).toDartGraph.Vertex ∧
      Finite (G.folded α a b hlabels).toDartGraph.Dart := by
  constructor
  · change Finite (FoldedVertex G.toDartGraph a b)
    exact Finite.of_surjective (Quotient.mk _) Quotient.mk_surjective
  · change Finite (FoldedDart G.toDartGraph.reverse a b)
    exact Finite.of_surjective (Quotient.mk _) Quotient.mk_surjective

/-- Cardinality of a type with an explicit finiteness proof. -/
noncomputable def finiteCard {α : Type*} (h : Finite α) : Nat := by
  letI := h
  exact Nat.card α

/-- Number of unoriented edges of a finite-dart graph. -/
noncomputable def finiteUnorientedEdgeCard (G : DartGraph)
    (hD : Finite G.Dart) : Nat := by
  letI : Finite (UnorientedDartClass G) :=
    Finite.of_surjective (Quotient.mk (UnorientedDartSetoid G))
      Quotient.mk_surjective
  exact Nat.card (UnorientedDartClass G)

/-- A quotient whose relation is equality has the same finite cardinality as
its representative type. -/
noncomputable def quotientEquivOfRelationEq {α : Type*} (s : Setoid α)
    (hrel : ∀ a b, s.r a b ↔ a = b) : Quotient s ≃ α where
  toFun := Quotient.lift id (by
    intro a b hab
    exact (hrel a b).mp hab)
  invFun := Quotient.mk s
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    rfl
  right_inv := by intro a; rfl

private theorem pairCollapse_relation_iff_eq_of_same {α : Type*}
    (x : α) (a b : α) :
    (PairCollapseSetoid x x).r a b ↔ a = b := by
  change Relation.EqvGen (PairCollapseGenerator x x) a b ↔ a = b
  constructor
  · intro h
    induction h with
    | rel a b h =>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    subst b
    exact Relation.EqvGen.refl _

/-- If two folded darts already meet head-to-tail, their vertex fold is just
the quotient identifying the two outer endpoints. -/
private theorem vertexFold_relation_iff_pairCollapse
    {G : DartGraph} (a b : G.Dart)
    (hadj : G.target a = G.source b) (x y : G.Vertex) :
    (VertexFoldSetoid G a b).r x y ↔
      (PairCollapseSetoid (G.source a) (G.target b)).r x y := by
  change Relation.EqvGen (VertexFoldGenerator G a b) x y ↔
    Relation.EqvGen (PairCollapseGenerator (G.source a) (G.target b)) x y
  constructor
  · intro h
    induction h with
    | rel x y h =>
        rcases h with h | h
        · exact Relation.EqvGen.rel _ _ (Or.inl h)
        · rcases h with ⟨rfl, rfl⟩
          simpa [hadj] using
            (Relation.EqvGen.refl (G.target a) :
              Relation.EqvGen (PairCollapseGenerator (G.source a)
                (G.target b)) (G.target a) (G.target a))
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h =>
        rcases h with h | h
        · exact Relation.EqvGen.rel _ _ (Or.inl h)
        · rcases h with ⟨hx, hy⟩
          subst x
          subst y
          exact Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩))
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A single graph fold whose darts are adjacent in a walk and whose outer
endpoints are distinct reduces the finite vertex count by exactly one. -/
theorem DartGraph.foldedVertex_card_add_one_of_adjacent
    {G : DartGraph} [Fintype G.Vertex] (a b : G.Dart)
    (hadj : G.target a = G.source b)
    [Fintype (FoldedVertex G a b)]
    (houter : G.source a ≠ G.target b) :
    Fintype.card (FoldedVertex G a b) + 1 = Fintype.card G.Vertex := by
  classical
  let e := Quotient.congrRight
    (vertexFold_relation_iff_pairCollapse a b hadj)
  letI : Fintype (Quotient (PairCollapseSetoid (G.source a) (G.target b))) :=
    Fintype.ofEquiv (FoldedVertex G a b) e
  rw [Fintype.card_congr e]
  exact pairCollapse_quotient_card (G.source a) (G.target b) houter

private theorem vertexFold_relation_iff_pairCollapse_at_target
    {G : DartGraph} (a b : G.Dart)
    (hadj : G.source a = G.target b) (x y : G.Vertex) :
    (VertexFoldSetoid G a b).r x y ↔
      (PairCollapseSetoid (G.target a) (G.source b)).r x y := by
  change Relation.EqvGen (VertexFoldGenerator G a b) x y ↔
    Relation.EqvGen (PairCollapseGenerator (G.target a) (G.source b)) x y
  constructor
  · intro h
    induction h with
    | rel x y h =>
        rcases h with h | h
        · rcases h with ⟨rfl, rfl⟩
          simpa [hadj] using
            (Relation.EqvGen.refl (G.source a) :
              Relation.EqvGen (PairCollapseGenerator (G.target a)
                (G.source b)) (G.source a) (G.source a))
        · exact Relation.EqvGen.rel _ _ (Or.inl h)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h =>
        rcases h with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
        · exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
        · subst x
          subst y
          exact Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩))
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The same count applies when the fold's already identified endpoints are
the source of the first dart and target of the second. -/
theorem DartGraph.foldedVertex_card_add_one_of_sourceAdjacent
    {G : DartGraph} [Fintype G.Vertex] (a b : G.Dart)
    (hadj : G.source a = G.target b)
    [Fintype (FoldedVertex G a b)]
    (houter : G.target a ≠ G.source b) :
    Fintype.card (FoldedVertex G a b) + 1 = Fintype.card G.Vertex := by
  classical
  let e := Quotient.congrRight
    (vertexFold_relation_iff_pairCollapse_at_target a b hadj)
  letI : Fintype (Quotient (PairCollapseSetoid (G.target a) (G.source b))) :=
    Fintype.ofEquiv (FoldedVertex G a b) e
  rw [Fintype.card_congr e]
  exact pairCollapse_quotient_card (G.target a) (G.source b) houter

/-- If both endpoint identifications of a fold are already present, the
vertex quotient does not change the vertex set. -/
theorem DartGraph.foldedVertex_card_eq_of_bothEndpoints
    {G : DartGraph} [Fintype G.Vertex] (a b : G.Dart)
    (hsource : G.source a = G.target b)
    (htarget : G.target a = G.source b)
    [Fintype (FoldedVertex G a b)] :
    Fintype.card (FoldedVertex G a b) = Fintype.card G.Vertex := by
  classical
  have hrel : ∀ x y, (VertexFoldSetoid G a b).r x y ↔ x = y := by
    intro x y
    change Relation.EqvGen (VertexFoldGenerator G a b) x y ↔ x = y
    constructor
    · intro h
      induction h with
      | rel x y h =>
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hsource]
          · rw [htarget]
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro h
      subst y
      exact Relation.EqvGen.refl _
  let e := quotientEquivOfRelationEq (VertexFoldSetoid G a b) hrel
  exact Fintype.card_congr e

abbrev FoldedEdgeClass {G : DartGraph} (a b : G.Dart) :=
  UnorientedDartClass (G.foldedGraph a b)

abbrev PairFoldEdgeSetoid {G : DartGraph} (a b : G.Dart) :=
  PairCollapseSetoid
    (Quotient.mk (UnorientedDartSetoid G) a)
    (Quotient.mk (UnorientedDartSetoid G) b)

/-- Folding two darts identifies exactly their unoriented edge classes. The
oriented quotient's two generating relations become one pair relation after
forgetting edge direction. -/
noncomputable def DartGraph.foldedEdgeClass_equiv_pairQuotient
    (G : DartGraph) (a b : G.Dart) :
    FoldedEdgeClass a b ≃ Quotient (PairFoldEdgeSetoid a b) := by
  classical
  let oldSetoid := UnorientedDartSetoid G
  let pairSetoid := PairFoldEdgeSetoid a b
  let toPairDart : FoldedDart G.reverse a b → Quotient pairSetoid :=
    Quotient.lift
      (fun d => Quotient.mk pairSetoid
        (Quotient.mk oldSetoid d)) (by
        intro d e hde
        change Relation.EqvGen (EdgeFoldGenerator G.reverse a b) d e at hde
        induction hde with
        | rel d e h =>
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · have hrev :
                (Quotient.mk oldSetoid (G.reverse b) : UnorientedDartClass G) =
                  Quotient.mk oldSetoid b := by
                apply Quotient.sound
                exact Or.inr rfl
              rw [hrev]
              apply Quotient.sound
              exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩)
            · have hrev :
                (Quotient.mk oldSetoid (G.reverse a) : UnorientedDartClass G) =
                  Quotient.mk oldSetoid a := by
                apply Quotient.sound
                exact Or.inr rfl
              rw [hrev]
              apply Quotient.sound
              exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩)
        | refl d => rfl
        | symm d e _ ih => exact ih.symm
        | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  have htoPairDart_reverse (d : FoldedDart G.reverse a b) :
      toPairDart
        (foldedReverse a b G.reverse_involutive d) = toPairDart d := by
    refine Quotient.inductionOn d ?_
    intro d
    change Quotient.mk pairSetoid
        (Quotient.mk oldSetoid (G.reverse d)) = _
    apply congrArg (Quotient.mk pairSetoid)
    apply Quotient.sound
    exact Or.inr rfl
  let toPair : FoldedEdgeClass a b → Quotient pairSetoid :=
    Quotient.lift toPairDart (by
      intro d e hde
      rcases hde with rfl | hde
      · rfl
      · rw [hde]
        exact htoPairDart_reverse e)
  let invBase : UnorientedDartClass G → FoldedEdgeClass a b :=
    Quotient.lift
      (fun d => Quotient.mk (UnorientedDartSetoid (G.foldedGraph a b))
        (Quotient.mk (EdgeFoldSetoid G.reverse a b) d)) (by
        intro d e hde
        rcases hde with rfl | hde
        · rfl
        · rw [hde]
          apply unorientedDartClass_eq_of_reverse
          rfl)
  let inv : Quotient pairSetoid → FoldedEdgeClass a b :=
    Quotient.lift invBase (by
      intro d e hde
      change Relation.EqvGen
        (PairCollapseGenerator
          (Quotient.mk oldSetoid a) (Quotient.mk oldSetoid b)) d e at hde
      induction hde with
      | rel d e h =>
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · apply unorientedDartClass_eq_of_reverse
            exact fold_boundary_darts_eq_reverse G.reverse a b
          · exact (unorientedDartClass_eq_of_reverse
              (fold_boundary_darts_eq_reverse G.reverse a b)).symm
      | refl d => rfl
      | symm d e _ ih => exact ih.symm
      | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  refine ⟨toPair, inv, ?_, ?_⟩
  · intro e
    refine Quotient.inductionOn e ?_
    intro d
    refine Quotient.inductionOn d ?_
    intro d
    rfl
  · intro q
    refine Quotient.inductionOn q ?_
    intro d
    refine Quotient.inductionOn d ?_
    intro d
    rfl

/-- When the two input edge classes are distinct, a graph fold removes exactly
one unoriented edge from a finite graph. -/
theorem DartGraph.foldedEdge_card_add_one_of_distinct
    {G : DartGraph} [Fintype (UnorientedDartClass G)]
    (a b : G.Dart)
    [Fintype (FoldedEdgeClass a b)]
    (hne : (Quotient.mk (UnorientedDartSetoid G) a : UnorientedDartClass G) ≠
      Quotient.mk (UnorientedDartSetoid G) b) :
    Fintype.card (FoldedEdgeClass a b) + 1 =
      Fintype.card (UnorientedDartClass G) := by
  classical
  let e := G.foldedEdgeClass_equiv_pairQuotient a b
  letI : Fintype (Quotient (PairFoldEdgeSetoid a b)) :=
    Fintype.ofEquiv (FoldedEdgeClass a b) e
  rw [Fintype.card_congr e]
  exact pairCollapse_quotient_card
    (Quotient.mk (UnorientedDartSetoid G) a)
    (Quotient.mk (UnorientedDartSetoid G) b) hne

/-- If the selected darts already represent the same edge, the fold does not
change the number of unoriented edges. -/
theorem DartGraph.foldedEdge_card_eq_of_samePair
    {G : DartGraph} [Fintype (UnorientedDartClass G)]
    (a b : G.Dart)
    [Fintype (FoldedEdgeClass a b)]
    (hsame : (Quotient.mk (UnorientedDartSetoid G) a :
      UnorientedDartClass G) = Quotient.mk (UnorientedDartSetoid G) b) :
    Fintype.card (FoldedEdgeClass a b) =
      Fintype.card (UnorientedDartClass G) := by
  classical
  have hrel : ∀ x y, (PairFoldEdgeSetoid a b).r x y ↔ x = y := by
    intro x y
    change Relation.EqvGen
      (PairCollapseGenerator
        (Quotient.mk (UnorientedDartSetoid G) a)
        (Quotient.mk (UnorientedDartSetoid G) b)) x y ↔ x = y
    rw [hsame]
    exact pairCollapse_relation_iff_eq_of_same
      (Quotient.mk (UnorientedDartSetoid G) b) x y
  let e := G.foldedEdgeClass_equiv_pairQuotient a b
  let eqv := quotientEquivOfRelationEq (PairFoldEdgeSetoid a b) hrel
  letI : Fintype (Quotient (PairFoldEdgeSetoid a b)) :=
    Fintype.ofEquiv (FoldedEdgeClass a b) e
  rw [Fintype.card_congr e, Fintype.card_congr eqv]

/-- An already equal edge pair with one endpoint identification in place
forces both vertex identifications to be redundant. -/
theorem DartGraph.foldedVertex_card_eq_of_sameEdge_and_endpoint
    {G : DartGraph} [Fintype G.Vertex] (a b : G.Dart)
    (hsame : (Quotient.mk (UnorientedDartSetoid G) a :
      UnorientedDartClass G) = Quotient.mk (UnorientedDartSetoid G) b)
    (hmatch : G.target a = G.source b ∨ G.source a = G.target b)
    [Fintype (FoldedVertex G a b)] :
    Fintype.card (FoldedVertex G a b) = Fintype.card G.Vertex := by
  have hrep : a = b ∨ a = G.reverse b :=
    (unorientedDartClass_eq_iff a b).mp hsame
  have hsource : G.source a = G.target b := by
    rcases hrep with hab | hab
    · subst b
      rcases hmatch with h | h
      · exact h.symm
      · exact h
    · subst a
      exact G.source_reverse b
  have htarget : G.target a = G.source b := by
    rcases hrep with hab | hab
    · subst b
      rcases hmatch with h | h
      · exact h
      · exact h.symm
    · subst a
      exact G.target_reverse b
  exact G.foldedVertex_card_eq_of_bothEndpoints a b hsource htarget

/-- For an adjacent edge fold, the graph Euler count `|V| - |E|` cannot
decrease. It is preserved when both the vertex and edge pairs are new, and it
increases when an endpoint identification was already present. -/
theorem DartGraph.fold_euler_count_nondecreasing
    {G : DartGraph} [Fintype G.Vertex]
    [Fintype (UnorientedDartClass G)] (a b : G.Dart)
    [Fintype (FoldedVertex G a b)]
    [Fintype (FoldedEdgeClass a b)]
    (hmatch : G.target a = G.source b ∨ G.source a = G.target b) :
    Fintype.card G.Vertex + Fintype.card (FoldedEdgeClass a b) ≤
      Fintype.card (FoldedVertex G a b) +
        Fintype.card (UnorientedDartClass G) := by
  classical
  by_cases hsame : (Quotient.mk (UnorientedDartSetoid G) a :
      UnorientedDartClass G) = Quotient.mk (UnorientedDartSetoid G) b
  · have hV := G.foldedVertex_card_eq_of_sameEdge_and_endpoint a b hsame hmatch
    have hE := G.foldedEdge_card_eq_of_samePair a b hsame
    omega
  · have hE := G.foldedEdge_card_add_one_of_distinct a b hsame
    rcases hmatch with hadj | hadj
    · by_cases houter : G.source a = G.target b
      · have hV := G.foldedVertex_card_eq_of_bothEndpoints a b houter hadj
        omega
      · have hV := G.foldedVertex_card_add_one_of_adjacent a b hadj houter
        omega
    · by_cases houter : G.target a = G.source b
      · have hV := G.foldedVertex_card_eq_of_bothEndpoints a b hadj houter
        omega
      · have hV := G.foldedVertex_card_add_one_of_sourceAdjacent a b hadj houter
        omega

/-- The same one-fold Euler bound with explicit finiteness witnesses instead
of externally supplied `Fintype` instances. -/
theorem DartGraph.fold_euler_count_nondecreasing_of_finite
    {G : DartGraph} (a b : G.Dart)
    (hV : Finite G.Vertex) (hD : Finite G.Dart)
    (hFoldV : Finite (FoldedVertex G a b))
    (hFoldD : Finite (FoldedDart G.reverse a b))
    (hmatch : G.target a = G.source b ∨ G.source a = G.target b) :
    finiteCard hV + finiteUnorientedEdgeCard
        (G.foldedGraph a b) hFoldD ≤
      finiteCard hFoldV + finiteUnorientedEdgeCard G hD := by
  classical
  letI : Finite G.Dart := hD
  letI : Fintype G.Vertex := Fintype.ofFinite _
  letI : Fintype G.Dart := Fintype.ofFinite _
  letI : Fintype (UnorientedDartClass G) := Fintype.ofFinite _
  letI : Fintype (FoldedVertex G a b) := Fintype.ofFinite _
  letI : Finite (G.foldedGraph a b).Dart := hFoldD
  letI : Fintype (FoldedDart G.reverse a b) := Fintype.ofFinite _
  letI : Finite (UnorientedDartClass (G.foldedGraph a b)) :=
    Finite.of_surjective (Quotient.mk (UnorientedDartSetoid
      (G.foldedGraph a b))) Quotient.mk_surjective
  letI : Fintype (UnorientedDartClass (G.foldedGraph a b)) :=
    Fintype.ofFinite _
  have h := G.fold_euler_count_nondecreasing a b hmatch
  simpa [finiteCard, finiteUnorientedEdgeCard, Nat.card_eq_fintype_card] using h

/-- The endpoint condition needed to replay an occurrence-pair fold list
without decreasing the finite graph Euler count. Later pairs are stated in
the graph produced by all earlier folds. -/
inductive LabelledDartPairFoldAdjacency {α : Type*} :
    (G : LabelledDartGraph α) → (pairs : List (LabelledDartPair G)) → Prop where
  | nil (G : LabelledDartGraph α) : LabelledDartPairFoldAdjacency G []
  | cons {G : LabelledDartGraph α} (pair : LabelledDartPair G)
      (rest : List (LabelledDartPair G))
      (hpair : G.toDartGraph.target pair.first =
          G.toDartGraph.source pair.second ∨
        G.toDartGraph.source pair.first = G.toDartGraph.target pair.second)
      (hrest : LabelledDartPairFoldAdjacency
        (G.folded α pair.first pair.second pair.inverse_labels)
        (rest.map (LabelledDartPair.map
          (LabelledGraphHom.fold G pair.first pair.second pair.inverse_labels)))) :
      LabelledDartPairFoldAdjacency G (pair :: rest)

/-- A finite sequence of inverse-labeled pair folds whose current endpoints
are adjacent has nondecreasing graph Euler count. -/
theorem LabelledDartPairFoldResult.foldAll_euler_data
    {α : Type*} {G : LabelledDartGraph α}
    (pairs : List (LabelledDartPair G))
    (hadj : LabelledDartPairFoldAdjacency G (pairs := pairs))
    (hV : Finite G.toDartGraph.Vertex)
    (hD : Finite G.toDartGraph.Dart) :
    ∃ hFinalV : Finite
        (LabelledDartPairFoldResult.foldAll G pairs).graph.toDartGraph.Vertex,
      ∃ hFinalD : Finite
        (LabelledDartPairFoldResult.foldAll G pairs).graph.toDartGraph.Dart,
        finiteCard hV + finiteUnorientedEdgeCard
            (LabelledDartPairFoldResult.foldAll G pairs).graph.toDartGraph hFinalD ≤
          finiteCard hFinalV + finiteUnorientedEdgeCard G.toDartGraph hD := by
  induction hadj with
  | nil G =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [LabelledDartPairFoldResult.foldAll] using hV
      · simpa [LabelledDartPairFoldResult.foldAll] using hD
      · simp [LabelledDartPairFoldResult.foldAll, finiteCard,
          finiteUnorientedEdgeCard]
  | @cons G pair rest hpairAdjacent hrestAdjacent ih =>
      let firstGraph := G.folded α pair.first pair.second pair.inverse_labels
      let firstHom := LabelledGraphHom.fold G pair.first pair.second pair.inverse_labels
      let transported := rest.map (LabelledDartPair.map firstHom)
      letI : Finite G.toDartGraph.Vertex := hV
      letI : Finite G.toDartGraph.Dart := hD
      have hfinite := LabelledDartGraph.folded_finite G pair.first pair.second
        pair.inverse_labels
      have hfirst := G.toDartGraph.fold_euler_count_nondecreasing_of_finite
        pair.first pair.second hV hD hfinite.1 hfinite.2 hpairAdjacent
      obtain ⟨hFinalV, hFinalD, hrest⟩ :=
        ih hfinite.1 hfinite.2
      have hFinalV' : Finite
          (LabelledDartPairFoldResult.foldAll G (pair :: rest)).graph.toDartGraph.Vertex := by
        rw [LabelledDartPairFoldResult.foldAll.eq_2]
        simpa [firstGraph, firstHom, transported] using hFinalV
      have hFinalD' : Finite
          (LabelledDartPairFoldResult.foldAll G (pair :: rest)).graph.toDartGraph.Dart := by
        rw [LabelledDartPairFoldResult.foldAll.eq_2]
        simpa [firstGraph, firstHom, transported] using hFinalD
      refine ⟨hFinalV', hFinalD', ?_⟩
      have hfirst' : finiteCard hV +
          finiteUnorientedEdgeCard firstGraph.toDartGraph hfinite.2 ≤
        finiteCard hfinite.1 + finiteUnorientedEdgeCard G.toDartGraph hD := by
        simpa [firstGraph, LabelledDartGraph.folded, DartGraph.foldedGraph] using hfirst
      have hrest' : finiteCard hfinite.1 +
          finiteUnorientedEdgeCard
            (LabelledDartPairFoldResult.foldAll firstGraph transported).graph.toDartGraph
            hFinalD ≤ finiteCard hFinalV +
          finiteUnorientedEdgeCard firstGraph.toDartGraph hfinite.2 := by
        simpa [transported] using hrest
      have hcombined : finiteCard hV +
          finiteUnorientedEdgeCard
            (LabelledDartPairFoldResult.foldAll firstGraph transported).graph.toDartGraph
            hFinalD ≤ finiteCard hFinalV +
          finiteUnorientedEdgeCard G.toDartGraph hD := by
        omega
      simpa [LabelledDartPairFoldResult.foldAll, firstGraph, firstHom,
        transported] using hcombined

/-- Replaying a certified free cancellation preserves or increases the finite
graph Euler count at every step. The result includes finiteness witnesses for
the final quotient graph. -/
theorem LabelledWalk.foldSequence_euler_data
    {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    (walk : LabelledWalk G u v raw)
    (hV : Finite G.toDartGraph.Vertex)
    (hD : Finite G.toDartGraph.Dart) :
    ∃ hFinalV : Finite
        (LabelledWalk.foldSequence steps walk).graph.toDartGraph.Vertex,
      ∃ hFinalD : Finite
        (LabelledWalk.foldSequence steps walk).graph.toDartGraph.Dart,
        finiteCard hV + finiteUnorientedEdgeCard
            (LabelledWalk.foldSequence steps walk).graph.toDartGraph hFinalD ≤
          finiteCard hFinalV + finiteUnorientedEdgeCard G.toDartGraph hD := by
  induction steps generalizing G u v hV hD with
  | refl word =>
      refine ⟨hV, hD, ?_⟩
      simp [LabelledWalk.foldSequence]
  | @cons raw middle reduced step rest ih =>
      let first := LabelledWalk.foldCancellation step walk
      let data := LabelledWalk.foldCancellationWithPair step walk
      letI : Finite G.toDartGraph.Vertex := hV
      letI : Finite G.toDartGraph.Dart := hD
      have hfinite := LabelledDartGraph.folded_finite G
        data.pair.first data.pair.second data.pair.inverse_labels
      have hFirstV : Finite first.graph.toDartGraph.Vertex := by
        change Finite (LabelledWalk.foldCancellationWithPair step walk).result.graph.toDartGraph.Vertex
        rw [LabelledWalk.foldCancellationWithPair_graph step walk]
        exact hfinite.1
      have hFirstD : Finite first.graph.toDartGraph.Dart := by
        change Finite (LabelledWalk.foldCancellationWithPair step walk).result.graph.toDartGraph.Dart
        rw [LabelledWalk.foldCancellationWithPair_graph step walk]
        exact hfinite.2
      have hfirst := G.toDartGraph.fold_euler_count_nondecreasing_of_finite
        data.pair.first data.pair.second hV hD hfinite.1 hfinite.2
        (Or.inl data.adjacent)
      have hgraph : first.graph.toDartGraph =
          G.toDartGraph.foldedGraph data.pair.first data.pair.second := by
        change (LabelledWalk.foldCancellationWithPair step walk).result.graph.toDartGraph = _
        rw [LabelledWalk.foldCancellationWithPair_graph]
        rfl
      obtain ⟨hFinalV, hFinalD, hrest⟩ := ih first.walk hFirstV hFirstD
      refine ⟨hFinalV, hFinalD, ?_⟩
      have hfirst' : finiteCard hV +
        finiteUnorientedEdgeCard first.graph.toDartGraph hFirstD ≤
        finiteCard hFirstV + finiteUnorientedEdgeCard G.toDartGraph hD := by
        simpa [finiteCard, finiteUnorientedEdgeCard, DartGraph.foldedGraph,
          hgraph] using hfirst
      have hrest' : finiteCard hFirstV +
          finiteUnorientedEdgeCard
            (LabelledWalk.foldSequence rest first.walk).graph.toDartGraph hFinalD ≤
        finiteCard hFinalV + finiteUnorientedEdgeCard first.graph.toDartGraph hFirstD := by
        simpa [first] using hrest
      simpa [LabelledWalk.foldSequence, first] using (show
        finiteCard hV + finiteUnorientedEdgeCard
            (LabelledWalk.foldSequence rest first.walk).graph.toDartGraph hFinalD ≤
          finiteCard hFinalV + finiteUnorientedEdgeCard G.toDartGraph hD by omega)

/-- The complete stem-fold and free-cancellation pipeline has nondecreasing
finite graph Euler count whenever each selected pair is adjacent at the time
it is folded. -/
theorem WalkFoldResult.foldPairsThenReduce_euler_data
    {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {raw reduced : Word α}
    (pairs : List (LabelledDartPair G))
    (steps : FreeCancellationSequence raw reduced)
    (walk : LabelledWalk G u v raw)
    (hadj : LabelledDartPairFoldAdjacency G (pairs := pairs))
    (hV : Finite G.toDartGraph.Vertex)
    (hD : Finite G.toDartGraph.Dart) :
    ∃ hFinalV : Finite
        (WalkFoldResult.foldPairsThenReduce pairs steps walk).graph.toDartGraph.Vertex,
      ∃ hFinalD : Finite
        (WalkFoldResult.foldPairsThenReduce pairs steps walk).graph.toDartGraph.Dart,
        finiteCard hV + finiteUnorientedEdgeCard
            (WalkFoldResult.foldPairsThenReduce pairs steps walk).graph.toDartGraph hFinalD ≤
          finiteCard hFinalV + finiteUnorientedEdgeCard G.toDartGraph hD := by
  let paired := WalkFoldResult.foldPairs pairs walk
  obtain ⟨hPairedV, hPairedD, hpairCount⟩ :=
    LabelledDartPairFoldResult.foldAll_euler_data pairs hadj hV hD
  have hPairedV' : Finite paired.graph.toDartGraph.Vertex := by
    simpa [paired, WalkFoldResult.foldPairs] using hPairedV
  have hPairedD' : Finite paired.graph.toDartGraph.Dart := by
    simpa [paired, WalkFoldResult.foldPairs] using hPairedD
  obtain ⟨hFinalV, hFinalD, hstepsCount⟩ :=
    LabelledWalk.foldSequence_euler_data steps paired.walk hPairedV' hPairedD'
  have hpairCount' : finiteCard hV + finiteUnorientedEdgeCard
        paired.graph.toDartGraph hPairedD' ≤
      finiteCard hPairedV' + finiteUnorientedEdgeCard G.toDartGraph hD := by
    simpa [paired, WalkFoldResult.foldPairs] using hpairCount
  have hstepsCount' : finiteCard hPairedV' + finiteUnorientedEdgeCard
        (LabelledWalk.foldSequence steps paired.walk).graph.toDartGraph hFinalD ≤
      finiteCard hFinalV + finiteUnorientedEdgeCard paired.graph.toDartGraph hPairedD' := by
    simpa [paired, WalkFoldResult.foldPairs] using hstepsCount
  refine ⟨hFinalV, hFinalD, ?_⟩
  have hcombined : finiteCard hV + finiteUnorientedEdgeCard
        (LabelledWalk.foldSequence steps paired.walk).graph.toDartGraph hFinalD ≤
      finiteCard hFinalV + finiteUnorientedEdgeCard G.toDartGraph hD := by
    omega
  simpa [WalkFoldResult.foldPairsThenReduce, paired] using hcombined

end GreendlingerDehn
