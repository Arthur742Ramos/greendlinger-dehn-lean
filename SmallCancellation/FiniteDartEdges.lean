import SmallCancellation.FiniteSupport
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

namespace GreendlingerDehn

namespace LabelledDartGraph

variable {α : Type*} (G : LabelledDartGraph α)

/-- The two orientations of an edge are always distinct in a labeled graph. -/
theorem reverse_ne_self (d : G.toDartGraph.Dart) :
    G.toDartGraph.reverse d ≠ d := by
  intro h
  have hlabels := G.label_reverse d
  rw [h] at hlabels
  cases hletter : G.label d with
  | mk generator orientation =>
      cases orientation <;> simp [hletter, inverseLetter] at hlabels

/-- Two darts represent the same unoriented edge when they are equal up to
reversal. -/
def DartEdgeRelation (d e : G.toDartGraph.Dart) : Prop :=
  d = e ∨ d = G.toDartGraph.reverse e

/-- The unoriented-edge equivalence classes of the dart set. -/
def dartEdgeSetoid : Setoid G.toDartGraph.Dart where
  r := G.DartEdgeRelation
  iseqv := ⟨
    by intro d; exact Or.inl rfl,
    by
      intro d e h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        have hrev := congrArg G.toDartGraph.reverse h
        rw [G.toDartGraph.reverse_involutive e] at hrev
        exact hrev.symm,
    by
      intro d e f hde hef
      rcases hde with hde | hde
      · rcases hef with hef | hef
        · exact Or.inl (hde.trans hef)
        · exact Or.inr (hde.trans hef)
      · rcases hef with hef | hef
        · exact Or.inr (hde.trans (congrArg G.toDartGraph.reverse hef))
        · exact Or.inl (hde.trans <| (congrArg G.toDartGraph.reverse hef).trans
            (G.toDartGraph.reverse_involutive f))⟩

/-- The finite type of unoriented edges represented by dart reversal classes. -/
abbrev EdgeClass := Quotient G.dartEdgeSetoid

/-- The quotient map from oriented darts to undirected edges. -/
def edgeClassMk (d : G.toDartGraph.Dart) : G.EdgeClass :=
  Quotient.mk G.dartEdgeSetoid d

theorem edgeClass_eq_iff (d e : G.toDartGraph.Dart) :
    G.edgeClassMk d = G.edgeClassMk e ↔
      d = e ∨ d = G.toDartGraph.reverse e := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    apply Quotient.sound
    exact h

/-- A finite dart set induces a finite set of orientation classes. -/
noncomputable instance edgeClassFintype [Fintype G.toDartGraph.Dart] :
    Fintype G.EdgeClass := by
  classical
  exact Fintype.ofFinite _

/-- Each unoriented edge class has exactly two orientations. -/
noncomputable def edgeFiberEquivBool [Fintype G.toDartGraph.Dart]
    (e : G.EdgeClass) : {d : G.toDartGraph.Dart // G.edgeClassMk d = e} ≃ Bool := by
  classical
  let rep := Quotient.out e
  have hrep : G.edgeClassMk rep = e := Quotient.out_eq e
  have hrev : G.edgeClassMk (G.toDartGraph.reverse rep) = e := by
    calc
      G.edgeClassMk (G.toDartGraph.reverse rep) = G.edgeClassMk rep :=
        Quotient.sound (Or.inr rfl)
      _ = e := hrep
  refine
    { toFun := fun x => if x.1 = rep then false else true
      invFun := fun b =>
        match b with
        | false => ⟨rep, hrep⟩
        | true => ⟨G.toDartGraph.reverse rep, hrev⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    rcases x with ⟨d, hd⟩
    have hrel : d = rep ∨ d = G.toDartGraph.reverse rep := by
      apply (G.edgeClass_eq_iff d rep).mp
      exact hd.trans hrep.symm
    rcases hrel with h | h
    · subst d
      simp [rep]
    · subst d
      have hne : G.toDartGraph.reverse rep ≠ rep := G.reverse_ne_self rep
      simp [rep, hne]
  · intro b
    cases b with
    | false => simp [rep]
    | true =>
        have hne : G.toDartGraph.reverse rep ≠ rep := G.reverse_ne_self rep
        simp [rep, hne]

theorem edgeFiber_card [Fintype G.toDartGraph.Dart] (e : G.EdgeClass)
    [Fintype {d : G.toDartGraph.Dart // G.edgeClassMk d = e}] :
    Fintype.card {d : G.toDartGraph.Dart // G.edgeClassMk d = e} = 2 := by
  classical
  rw [Fintype.card_congr (G.edgeFiberEquivBool e)]
  simp

/-- Every undirected edge contributes exactly two darts. -/
theorem dart_card_eq_two_edgeClass_card [Fintype G.toDartGraph.Dart] :
    Fintype.card G.toDartGraph.Dart = 2 * Fintype.card G.EdgeClass := by
  classical
  calc
    Fintype.card G.toDartGraph.Dart =
        Fintype.card (Σ e : G.EdgeClass,
          {d : G.toDartGraph.Dart // G.edgeClassMk d = e}) := by
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.edgeClassMk).symm
    _ = ∑ e : G.EdgeClass,
          Fintype.card {d : G.toDartGraph.Dart // G.edgeClassMk d = e} :=
      Fintype.card_sigma
    _ = ∑ _e : G.EdgeClass, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.edgeFiber_card e
    _ = 2 * Fintype.card G.EdgeClass := by simp [Nat.mul_comm]

/-- The number of outgoing darts at a vertex. -/
noncomputable def outDegree [Fintype G.toDartGraph.Dart]
    (v : G.toDartGraph.Vertex) : Nat := by
  classical
  exact Fintype.card {d : G.toDartGraph.Dart // G.toDartGraph.source d = v}

/-- Summing outgoing degrees counts every dart once. -/
theorem sum_outDegree_eq_dart_card [Fintype G.toDartGraph.Dart]
    [Fintype G.toDartGraph.Vertex] :
    (∑ v : G.toDartGraph.Vertex, G.outDegree v) =
      Fintype.card G.toDartGraph.Dart := by
  classical
  calc
    (∑ v : G.toDartGraph.Vertex, G.outDegree v) =
        Fintype.card (Σ v : G.toDartGraph.Vertex,
          {d : G.toDartGraph.Dart // G.toDartGraph.source d = v}) :=
      Fintype.card_sigma.symm
    _ = Fintype.card G.toDartGraph.Dart :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv G.toDartGraph.source)

/-- The vertex degree sum is twice the number of undirected edges. This is
the dart-count identity needed by finite vertex-link curvature ledgers. -/
theorem sum_outDegree_eq_two_edgeClass_card [Fintype G.toDartGraph.Dart]
    [Fintype G.toDartGraph.Vertex] :
    (∑ v : G.toDartGraph.Vertex, G.outDegree v) =
      2 * Fintype.card G.EdgeClass := by
  rw [G.sum_outDegree_eq_dart_card, G.dart_card_eq_two_edgeClass_card]

/-- The source vertex of a dart, viewed in the finite incident support. -/
def activeSource [Fintype G.toDartGraph.Dart] (d : G.toDartGraph.Dart) :
    G.ActiveVertex :=
  ⟨G.toDartGraph.source d, G.source_mem_endpointFinset d⟩

/-- Out-degree on the finite incident-vertex support. -/
noncomputable def activeOutDegree [Fintype G.toDartGraph.Dart]
    (v : G.ActiveVertex) : Nat := by
  classical
  exact Fintype.card {d : G.toDartGraph.Dart // G.activeSource d = v}

/-- Every vertex retained by finite support has positive outgoing degree. -/
theorem activeOutDegree_pos [Fintype G.toDartGraph.Dart]
    (v : G.ActiveVertex) : 0 < G.activeOutDegree v := by
  classical
  obtain ⟨d, hd⟩ := G.activeVertex_incident v
  have hsource : ∃ e, G.toDartGraph.source e = v.1 := by
    rcases hd with hs | ht
    · exact ⟨d, hs⟩
    · exact ⟨G.toDartGraph.reverse d, by
        rw [G.toDartGraph.source_reverse]
        exact ht⟩
  obtain ⟨e, he⟩ := hsource
  have heActive : G.activeSource e = v := Subtype.ext he
  rw [activeOutDegree]
  exact Fintype.card_pos_iff.mpr ⟨⟨e, heActive⟩⟩

/-- On the finite incident-vertex support, outgoing degrees count each
unoriented edge twice. This is the graph-level form of the `darts_total`
identity in `LinkCornerMapData`. -/
theorem sum_activeOutDegree_eq_two_edgeClass_card
    [Fintype G.toDartGraph.Dart] :
    (∑ v : G.ActiveVertex, G.activeOutDegree v) =
      2 * Fintype.card G.EdgeClass := by
  classical
  calc
    (∑ v : G.ActiveVertex, G.activeOutDegree v) =
        Fintype.card (Σ v : G.ActiveVertex,
          {d : G.toDartGraph.Dart // G.activeSource d = v}) := by
      exact Fintype.card_sigma.symm
    _ = Fintype.card G.toDartGraph.Dart :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv G.activeSource)
    _ = 2 * Fintype.card G.EdgeClass := G.dart_card_eq_two_edgeClass_card

end LabelledDartGraph

end GreendlingerDehn
