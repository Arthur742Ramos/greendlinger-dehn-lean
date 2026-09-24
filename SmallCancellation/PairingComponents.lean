import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import SmallCancellation.PlanarCancellation

/-!
# Endpoints in a finite graph of maximum degree two

This file isolates a small graph-theoretic fact used in the planned
incidence analysis of the two pairings on a cancelled lollipop boundary.
It does not by itself construct the planar map needed for Greendlinger's
lemma.
-/

open Finset

namespace SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- In a finite connected graph of maximum degree two, there are at most two
vertices whose degree is at most one.  The proof is a degree-sum count: the
connected graph has at least `|V|-1` edges, while every low-degree vertex
contributes a deficit of at least one from the maximum degree two. -/
theorem card_degree_le_one_le_two (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hdegree : ∀ v, G.degree v ≤ 2) :
    Fintype.card {v : V // G.degree v ≤ 1} ≤ 2 := by
  classical
  let low : Finset V := univ.filter fun v => G.degree v ≤ 1
  have hsum_bound :
      (∑ v ∈ (univ : Finset V), G.degree v) + low.card ≤ 2 * Fintype.card V := by
    have hterm : ∀ v ∈ (univ : Finset V),
        G.degree v + (if v ∈ low then 1 else 0) ≤ 2 := by
      intro v hv
      by_cases hlow : v ∈ low
      · have hdeg : G.degree v ≤ 1 := (mem_filter.mp hlow).2
        simp [hlow]
        omega
      · simp [hlow]
        exact hdegree v
    calc
      (∑ v ∈ (univ : Finset V), G.degree v) + low.card
          = ∑ v ∈ (univ : Finset V),
              (G.degree v + if v ∈ low then 1 else 0) := by
                simp [low, Finset.sum_add_distrib, Finset.sum_boole]
      _ ≤ ∑ _v ∈ (univ : Finset V), (2 : ℕ) := by
            apply Finset.sum_le_sum
            intro v hv
            exact hterm v (Finset.mem_univ v)
      _ = 2 * Fintype.card V := by simp [Nat.mul_comm]
  have hconnected : Fintype.card V ≤ #G.edgeFinset + 1 := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hdegrees := G.sum_degrees_eq_twice_card_edges
  have hlow_card : low.card ≤ 2 := by
    rw [hdegrees] at hsum_bound
    omega
  have hcard : Fintype.card {v : V // G.degree v ≤ 1} = low.card := by
    simp [low, Fintype.card_subtype]
  omega

end SimpleGraph

namespace SimpleGraph

theorem Walk.map_eq_of_adj {V : Type*} {G : SimpleGraph V}
    {u v : V} {β : Sort*} (walk : G.Walk u v) (f : V → β)
    (hstep : ∀ x y, G.Adj x y → f x = f y) : f u = f v := by
  induction walk with
  | nil => rfl
  | @cons x y z hadj tail ih => exact (hstep x y hadj).trans ih

theorem Reachable.map_eq_of_adj {V : Type*} {G : SimpleGraph V}
    {u v : V} {β : Sort*} (hreach : G.Reachable u v) (f : V → β)
    (hstep : ∀ x y, G.Adj x y → f x = f y) : f u = f v := by
  rcases hreach with ⟨walk⟩
  exact walk.map_eq_of_adj f hstep

end SimpleGraph

namespace GreendlingerDehn

/-- A finite partial pairing of occurrences. Every occurrence has at most one
partner, paired occurrences point back to one another, and no occurrence is
paired with itself. -/
structure PartialOccurrencePairing (V : Type*) where
  partner : V → Option V
  partner_symm : ∀ {v w}, partner v = some w → partner w = some v
  partner_ne : ∀ {v}, partner v ≠ some v

namespace PartialOccurrencePairing

/-- A default target is convenient for expressing the finite set containing
the (at most one) partner of an occurrence. -/
def target {V : Type*} (P : PartialOccurrencePairing V) (v : V) : V :=
  P.partner v |>.getD v

/-- Choose the unique neighbor of an occurrence in a symmetric functional
relation, if it has one. -/
noncomputable def choosePartner {V : Type*} (R : V → V → Prop) (v : V) : Option V :=
  by
    classical
    exact if h : ∃ w, R v w then some (Classical.choose h) else none

theorem choosePartner_eq_some_iff {V : Type*} (R : V → V → Prop)
    (hfunctional : ∀ v w₁ w₂, R v w₁ → R v w₂ → w₁ = w₂) (v w : V) :
    choosePartner R v = some w ↔ R v w := by
  classical
  unfold choosePartner
  by_cases hex : ∃ z, R v z
  · rw [dif_pos hex]
    simp only [Option.some.injEq]
    constructor
    · intro heq
      rw [← heq]
      exact Classical.choose_spec hex
    · intro h
      exact hfunctional v (Classical.choose hex) w
        (Classical.choose_spec hex) h
  · rw [dif_neg hex]
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (hex ⟨w, h⟩)

/-- Restrict a partial pairing to pairs whose two endpoints both lie in a
vertex set. -/
noncomputable def restrictedPartner {V : Type*} (P : PartialOccurrencePairing V)
    (s : Set V) (v : s) : Option s :=
  choosePartner (fun x y : s => P.partner x.1 = some y.1) v

theorem restrictedPartner_eq_some_iff {V : Type*}
    (P : PartialOccurrencePairing V) (s : Set V) (v w : s) :
    restrictedPartner P s v = some w ↔ P.partner v.1 = some w.1 := by
  exact choosePartner_eq_some_iff _
    (by
      intro x y z hxy hxz
      apply Subtype.ext
      exact Option.some.inj (hxy.symm.trans hxz)) v w

/-- Restricting a partial pairing to a set of vertices is again a partial
pairing. -/
noncomputable def restrictToSet {V : Type*} (P : PartialOccurrencePairing V)
    (s : Set V) : PartialOccurrencePairing s where
  partner := restrictedPartner P s
  partner_symm := by
    intro v w h
    apply (restrictedPartner_eq_some_iff P s w v).2
    exact P.partner_symm ((restrictedPartner_eq_some_iff P s v w).1 h)
  partner_ne := by
    intro v h
    exact P.partner_ne ((restrictedPartner_eq_some_iff P s v v).1 h)

/-- Turn a symmetric irreflexive relation with at most one partner per
occurrence into a partial pairing. -/
noncomputable def ofRelation {V : Type*} (R : V → V → Prop)
    (hsymm : ∀ {v w}, R v w → R w v)
    (hirrefl : ∀ v, ¬ R v v)
    (hfunctional : ∀ v w₁ w₂, R v w₁ → R v w₂ → w₁ = w₂) :
    PartialOccurrencePairing V where
  partner := choosePartner R
  partner_symm := by
    intro v w h
    apply (choosePartner_eq_some_iff R hfunctional w v).2
    exact hsymm ((choosePartner_eq_some_iff R hfunctional v w).1 h)
  partner_ne := by
    intro v h
    exact hirrefl v ((choosePartner_eq_some_iff R hfunctional v v).1 h)

end PartialOccurrencePairing

/-- The undirected graph generated by two partial pairings. Its edges encode
the equivalence relation generated by the two kinds of occurrence fold. -/
def twoPairingGraph {V : Type*} (P Q : PartialOccurrencePairing V) :
    SimpleGraph V where
  Adj v w := P.partner v = some w ∨ Q.partner v = some w
  symm := {
    symm _ _ h := by
      rcases h with hp | hq
      · exact Or.inl (P.partner_symm hp)
      · exact Or.inr (Q.partner_symm hq)
  }
  loopless := {
    irrefl v h := by
      rcases h with hp | hq
      · exact P.partner_ne hp
      · exact Q.partner_ne hq
  }

instance twoPairingGraphDecidableRel {V : Type*} [DecidableEq V]
    (P Q : PartialOccurrencePairing V) :
    DecidableRel (twoPairingGraph P Q).Adj := by
  intro v w
  change Decidable (P.partner v = some w ∨ Q.partner v = some w)
  infer_instance

theorem twoPairingGraph_degree_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V) (v : V) :
    (twoPairingGraph P Q).degree v ≤ 2 := by
  classical
  let G := twoPairingGraph P Q
  have hsubset : G.neighborFinset v ⊆
      ({P.target v, Q.target v} : Finset V) := by
    intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    change P.partner v = some w ∨ Q.partner v = some w at hadj
    rcases hadj with hp | hq
    · have htarget : P.target v = w := by
        simp [PartialOccurrencePairing.target, hp]
      simp [htarget]
    · have htarget : Q.target v = w := by
        simp [PartialOccurrencePairing.target, hq]
      simp [htarget]
  calc
    G.degree v = (G.neighborFinset v).card := rfl
    _ ≤ ({P.target v, Q.target v} : Finset V).card := Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

theorem twoPairingGraph_degree_le_one_of_unpaired_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V) (v : V)
    (hleft : P.partner v = none) :
    (twoPairingGraph P Q).degree v ≤ 1 := by
  classical
  let G := twoPairingGraph P Q
  have hsubset : G.neighborFinset v ⊆ {Q.target v} := by
    intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    change P.partner v = some w ∨ Q.partner v = some w at hadj
    rcases hadj with hp | hq
    · simp [hleft] at hp
    · have htarget : Q.target v = w := by
        simp [PartialOccurrencePairing.target, hq]
      simp [htarget]
  calc
    G.degree v = (G.neighborFinset v).card := rfl
    _ ≤ ({Q.target v} : Finset V).card := Finset.card_le_card hsubset
    _ = 1 := Finset.card_singleton _

/-- Any occurrence unmatched by at least one of the two pairings has degree at
most one in their union graph. -/
theorem twoPairingGraph_degree_le_one_of_unpaired_either
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V) (v : V)
    (h : P.partner v = none ∨ Q.partner v = none) :
    (twoPairingGraph P Q).degree v ≤ 1 := by
  classical
  rcases h with hleft | hright
  · exact twoPairingGraph_degree_le_one_of_unpaired_left P Q v hleft
  · let G := twoPairingGraph P Q
    have hsubset : G.neighborFinset v ⊆ {P.target v} := by
      intro w hw
      have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
      change P.partner v = some w ∨ Q.partner v = some w at hadj
      rcases hadj with hp | hq
      · have htarget : P.target v = w := by
          simp [PartialOccurrencePairing.target, hp]
        simp [htarget]
      · simp [hright] at hq
    calc
      G.degree v = (G.neighborFinset v).card := rfl
      _ ≤ ({P.target v} : Finset V).card := Finset.card_le_card hsubset
      _ = 1 := Finset.card_singleton _

/-- In a connected graph generated by two partial pairings, at most two
occurrences are unmatched by at least one pairing. These are the only possible
endpoints of an alternating pairing component. -/
theorem card_unpaired_either_le_two_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V)
    (hconn : (twoPairingGraph P Q).Connected) :
    Fintype.card {v : V // P.partner v = none ∨ Q.partner v = none} ≤ 2 := by
  classical
  let G := twoPairingGraph P Q
  have hmono := Fintype.card_subtype_mono
    (fun v => P.partner v = none ∨ Q.partner v = none)
    (fun v => G.degree v ≤ 1)
    (by
      intro v hv
      exact twoPairingGraph_degree_le_one_of_unpaired_either P Q v hv)
  exact hmono.trans (G.card_degree_le_one_le_two hconn
    (fun v => twoPairingGraph_degree_le_two P Q v))

/-- In a connected component generated by two partial pairings, the number of
unmatched pairing ends is at most two. The sum type keeps the two colors
separate, so a vertex unmatched by both pairings contributes two ends. -/
theorem card_unpaired_pairing_slots_le_two_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V)
    (hconn : (twoPairingGraph P Q).Connected) :
    Nat.card
      ({v : V // P.partner v = none} ⊕ {v : V // Q.partner v = none}) ≤ 2 := by
  classical
  let leftPred := fun v : V => P.partner v = none
  let rightPred := fun v : V => Q.partner v = none
  let leftSlots := {v : V // leftPred v}
  let rightSlots := {v : V // rightPred v}
  let eitherSlots := {v : V // leftPred v ∨ rightPred v}
  by_cases hinter : ∃ v, leftPred v ∧ rightPred v
  · obtain ⟨v, hvLeft, hvRight⟩ := hinter
    let G := twoPairingGraph P Q
    have hnotNontrivial : ¬ Nontrivial V := by
      intro hnontrivial
      letI : Nontrivial V := hnontrivial
      have hisolated : G.IsIsolated v := by
        intro u hadj
        change P.partner v = some u ∨ Q.partner v = some u at hadj
        simp [leftPred, rightPred, hvLeft, hvRight] at hadj
      exact hconn.preconnected.not_isIsolated v hisolated
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnotNontrivial
    letI : Unique leftSlots :=
      ⟨⟨v, hvLeft⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩
    letI : Unique rightSlots :=
      ⟨⟨v, hvRight⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩
    simp [Nat.card_eq_fintype_card, leftSlots, rightSlots]
  · have hdisjoint : Disjoint leftPred rightPred := by
      exact Set.disjoint_left.mpr (fun v hvLeft hvRight =>
        hinter ⟨v, hvLeft, hvRight⟩)
    have hcardEither : Fintype.card eitherSlots =
        Fintype.card leftSlots + Fintype.card rightSlots :=
      Fintype.card_subtype_or_disjoint leftPred rightPred hdisjoint
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, ← hcardEither]
    exact card_unpaired_either_le_two_of_connected P Q hconn

/-- In a connected component generated by two occurrence pairings, at most
two occurrences can be unmatched by the first pairing. Each such occurrence
has degree at most one in the union graph, so the endpoints theorem applies.
This is the component bound needed for the stem/cancellation edge quotient. -/
theorem card_unpaired_left_le_two_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V)
    (hconn : (twoPairingGraph P Q).Connected) :
    Fintype.card {v : V // P.partner v = none} ≤ 2 := by
  classical
  let G := twoPairingGraph P Q
  have hmono := Fintype.card_subtype_mono
    (fun v => P.partner v = none) (fun v => G.degree v ≤ 1)
    (by
      intro v hv
      exact twoPairingGraph_degree_le_one_of_unpaired_left P Q v hv)
  exact hmono.trans (G.card_degree_le_one_le_two hconn
    (fun v => twoPairingGraph_degree_le_two P Q v))

/-- Flatten a list of unordered occurrence pairs into its list of endpoints. -/
def occurrencePairEndpoints {V : Type*} (pairs : List (V × V)) : List V :=
  pairs.flatMap fun p => [p.1, p.2]

theorem occurrencePairEndpoints_map {V W : Type*} {pairs : List (V × V)}
    (f : V → W) :
    occurrencePairEndpoints (pairs.map fun p => (f p.1, f p.2)) =
      (occurrencePairEndpoints pairs).map f := by
  simp [occurrencePairEndpoints, List.flatMap_map, List.map_flatMap]

/-- The symmetric relation generated by a list of ordered presentations of
unordered occurrence pairs. -/
def occurrencePairRel {V : Type*} (pairs : List (V × V)) (v w : V) : Prop :=
  ∃ p ∈ pairs, (p.1 = v ∧ p.2 = w) ∨ (p.1 = w ∧ p.2 = v)

theorem occurrencePairRel_exists_iff_mem_endpoints {V : Type*}
    (pairs : List (V × V)) (v : V) :
    (∃ w, occurrencePairRel pairs v w) ↔
      v ∈ occurrencePairEndpoints pairs := by
  constructor
  · rintro ⟨w, ⟨p, hp, hpv⟩⟩
    change v ∈ pairs.flatMap (fun p => [p.1, p.2])
    apply List.mem_flatMap.mpr
    refine ⟨p, hp, ?_⟩
    rcases hpv with ⟨h₁, _⟩ | ⟨_, h₂⟩
    · simp [h₁]
    · simp [h₂]
  · intro hv
    change v ∈ pairs.flatMap (fun p => [p.1, p.2]) at hv
    rcases List.mem_flatMap.mp hv with ⟨p, hp, hpv⟩
    have hpv' : v = p.1 ∨ v = p.2 := by simpa using hpv
    rcases hpv' with hpv | hpv
    · exact ⟨p.2, p, hp, Or.inl ⟨hpv.symm, rfl⟩⟩
    · exact ⟨p.1, p, hp, Or.inr ⟨rfl, hpv.symm⟩⟩

theorem occurrencePairRel_append_iff {V : Type*}
    (left right : List (V × V)) (v w : V) :
    occurrencePairRel (left ++ right) v w ↔
      occurrencePairRel left v w ∨ occurrencePairRel right v w := by
  constructor
  · rintro ⟨p, hp, h⟩
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨p, hp, h⟩
    · exact Or.inr ⟨p, hp, h⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, List.mem_append_left _ hp, h⟩
    · exact ⟨p, List.mem_append_right _ hp, h⟩

theorem occurrencePairLists_disjoint_endpoints {V : Type*}
    {pairs : List (V × V)} (hnodup : (occurrencePairEndpoints pairs).Nodup)
    {p q : V × V} (hp : p ∈ pairs) (hq : q ∈ pairs) (hpq : p ≠ q) :
    List.Disjoint [p.1, p.2] [q.1, q.2] := by
  have hparts := (List.nodup_flatMap.mp (by
    simpa [occurrencePairEndpoints] using hnodup)).2
  have hsymm : Std.Symm (Function.onFun List.Disjoint
      (fun p : V × V => [p.1, p.2])) :=
    ⟨fun a b h => List.disjoint_comm.mp h⟩
  exact @List.Pairwise.forall (V × V)
    (Function.onFun List.Disjoint (fun p => [p.1, p.2]))
    pairs hsymm hparts p hp q hq hpq

theorem occurrencePairRel_symmetric {V : Type*} (pairs : List (V × V))
    {v w : V} (h : occurrencePairRel pairs v w) :
    occurrencePairRel pairs w v := by
  rcases h with ⟨p, hp, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
  · exact ⟨p, hp, Or.inr ⟨h₁, h₂⟩⟩
  · exact ⟨p, hp, Or.inl ⟨h₁, h₂⟩⟩

theorem occurrencePairRel_irrefl {V : Type*} {pairs : List (V × V)}
    (hnoLoop : ∀ p ∈ pairs, p.1 ≠ p.2) (v : V) :
    ¬ occurrencePairRel pairs v v := by
  rintro ⟨p, hp, hpv⟩
  rcases hpv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hnoLoop p hp (h₁.trans h₂.symm)
  · exact hnoLoop p hp (h₁.trans h₂.symm)

theorem occurrencePairRel_functional {V : Type*} {pairs : List (V × V)}
    (hnodup : (occurrencePairEndpoints pairs).Nodup)
    (hnoLoop : ∀ p ∈ pairs, p.1 ≠ p.2)
    (v w₁ w₂ : V) (h₁ : occurrencePairRel pairs v w₁)
    (h₂ : occurrencePairRel pairs v w₂) : w₁ = w₂ := by
  obtain ⟨p, hp, hpv⟩ := h₁
  obtain ⟨q, hq, hqv⟩ := h₂
  by_cases hpq : p = q
  · subst q
    rcases hpv with ⟨hpv₁, hpv₂⟩ | ⟨hpv₁, hpv₂⟩
    · rcases hqv with ⟨hqv₁, hqv₂⟩ | ⟨hqv₁, hqv₂⟩
      · exact hpv₂.symm.trans hqv₂
      · have hloop : p.1 = p.2 := hpv₁.trans hqv₂.symm
        exact False.elim (hnoLoop p hp hloop)
    · rcases hqv with ⟨hqv₁, hqv₂⟩ | ⟨hqv₁, hqv₂⟩
      · have hloop : p.1 = p.2 := hqv₁.trans hpv₂.symm
        exact False.elim (hnoLoop p hp hloop)
      · exact hpv₁.symm.trans hqv₁
  · have hdis := occurrencePairLists_disjoint_endpoints hnodup hp hq hpq
    have hvp : v ∈ [p.1, p.2] := by
      rcases hpv with ⟨h₁, _⟩ | ⟨_, h₂⟩
      · simp [h₁]
      · simp [h₂]
    have hvq : v ∈ [q.1, q.2] := by
      rcases hqv with ⟨h₁, _⟩ | ⟨_, h₂⟩
      · simp [h₁]
      · simp [h₂]
    have hdisNe := List.disjoint_iff_ne.mp hdis
    exact False.elim ((hdisNe v hvp v hvq) rfl)

/-- Turn a pair list with distinct endpoints and no self-pairs into a partial
involution. Pair-list endpoint uniqueness proves that every occurrence has at
most one mate. -/
noncomputable def occurrencePairListToPairing {V : Type*}
    (pairs : List (V × V))
    (hnodup : (occurrencePairEndpoints pairs).Nodup)
    (hnoLoop : ∀ p ∈ pairs, p.1 ≠ p.2) : PartialOccurrencePairing V :=
  PartialOccurrencePairing.ofRelation (occurrencePairRel pairs)
    (by
      intro v w h
      exact occurrencePairRel_symmetric pairs h)
    (occurrencePairRel_irrefl hnoLoop)
    (occurrencePairRel_functional hnodup hnoLoop)

theorem occurrencePairListToPairing_spec {V : Type*}
    (pairs : List (V × V)) (hnodup : (occurrencePairEndpoints pairs).Nodup)
    (hnoLoop : ∀ p ∈ pairs, p.1 ≠ p.2) (v w : V) :
    (occurrencePairListToPairing pairs hnodup hnoLoop).partner v = some w ↔
      occurrencePairRel pairs v w :=
  by
    change PartialOccurrencePairing.choosePartner (occurrencePairRel pairs) v = some w ↔ _
    exact PartialOccurrencePairing.choosePartner_eq_some_iff _
      (occurrencePairRel_functional hnodup hnoLoop) v w

theorem occurrencePairListToPairing_partner_eq_none_iff_not_mem_endpoints
    {V : Type*} (pairs : List (V × V))
    (hnodup : (occurrencePairEndpoints pairs).Nodup)
    (hnoLoop : ∀ p ∈ pairs, p.1 ≠ p.2) (v : V) :
    (occurrencePairListToPairing pairs hnodup hnoLoop).partner v = none ↔
      v ∉ occurrencePairEndpoints pairs := by
  constructor
  · intro hnone hmem
    obtain ⟨w, hw⟩ := (occurrencePairRel_exists_iff_mem_endpoints pairs v).2 hmem
    have hsome := (occurrencePairListToPairing_spec pairs hnodup hnoLoop v w).2 hw
    rw [hnone] at hsome
    cases hsome
  · intro hnot
    cases hp : (occurrencePairListToPairing pairs hnodup hnoLoop).partner v with
    | none => rfl
    | some w =>
        have hrel := (occurrencePairListToPairing_spec pairs hnodup hnoLoop v w).1 hp
        exact False.elim (hnot
          ((occurrencePairRel_exists_iff_mem_endpoints pairs v).1 ⟨w, hrel⟩))

/-- In a connected component generated by two endpoint-disjoint pair lists,
at most two occurrences are untouched by the first list. This packages the
degree argument with the list-level matching invariant used by cancellation
traces. -/
theorem card_occurrences_unpaired_by_left_list_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (left right : List (V × V))
    [DecidablePred (fun v : V => ¬ ∃ w, occurrencePairRel left v w)]
    (hleftNodup : (occurrencePairEndpoints left).Nodup)
    (hleftNoLoop : ∀ p ∈ left, p.1 ≠ p.2)
    (hrightNodup : (occurrencePairEndpoints right).Nodup)
    (hrightNoLoop : ∀ p ∈ right, p.1 ≠ p.2)
    (hconn : (twoPairingGraph
      (occurrencePairListToPairing left hleftNodup hleftNoLoop)
      (occurrencePairListToPairing right hrightNodup hrightNoLoop)).Connected) :
    Fintype.card {v : V // ¬ ∃ w, occurrencePairRel left v w} ≤ 2 := by
  classical
  let P := occurrencePairListToPairing left hleftNodup hleftNoLoop
  let Q := occurrencePairListToPairing right hrightNodup hrightNoLoop
  have hmono := Fintype.card_subtype_mono
    (fun v => ¬ ∃ w, occurrencePairRel left v w)
    (fun v => P.partner v = none)
    (by
      intro v hv
      cases hpartner : P.partner v with
      | none => rfl
      | some w =>
          exact False.elim (hv ⟨w,
            (occurrencePairListToPairing_spec left hleftNodup hleftNoLoop v w).1
              (by simpa [P] using hpartner)⟩))
  have hpairing := card_unpaired_left_le_two_of_connected P Q (by simpa [P, Q] using hconn)
  exact hmono.trans (by simpa [P] using hpairing)

/-- Restrict the first pairing to one connected component of the graph formed
by both pairings. -/
noncomputable def componentLeftPairing {V : Type*} (P Q : PartialOccurrencePairing V)
    (C : (twoPairingGraph P Q).ConnectedComponent) :
    PartialOccurrencePairing C.supp :=
  P.restrictToSet C.supp

/-- Restrict the second pairing to one connected component of the graph formed
by both pairings. -/
noncomputable def componentRightPairing {V : Type*} (P Q : PartialOccurrencePairing V)
    (C : (twoPairingGraph P Q).ConnectedComponent) :
    PartialOccurrencePairing C.supp :=
  Q.restrictToSet C.supp

theorem twoPairingGraph_component_eq_induce {V : Type*} [DecidableEq V]
    (P Q : PartialOccurrencePairing V)
    (C : (twoPairingGraph P Q).ConnectedComponent) :
    twoPairingGraph (componentLeftPairing P Q C)
      (componentRightPairing P Q C) = C.toSimpleGraph := by
  classical
  let G := twoPairingGraph P Q
  ext x y
  change (PartialOccurrencePairing.restrictedPartner P C.supp x = some y ∨
    PartialOccurrencePairing.restrictedPartner Q C.supp x = some y) ↔
      G.Adj x.1 y.1
  rw [PartialOccurrencePairing.restrictedPartner_eq_some_iff
      P C.supp x y,
    PartialOccurrencePairing.restrictedPartner_eq_some_iff
      Q C.supp x y]
  rfl

/-- Every connected component generated by two partial pairings contains at
most two occurrences unmatched by the first pairing. -/
theorem card_component_unpaired_left_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V)
    (C : (twoPairingGraph P Q).ConnectedComponent) :
    Nat.card {v : C.supp // (componentLeftPairing P Q C).partner v = none} ≤ 2 := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  have hconn :
      (twoPairingGraph (componentLeftPairing P Q C)
        (componentRightPairing P Q C)).Connected := by
    rw [twoPairingGraph_component_eq_induce P Q C]
    exact C.connected_toSimpleGraph
  have hbound := card_unpaired_left_le_two_of_connected
    (componentLeftPairing P Q C) (componentRightPairing P Q C) hconn
  change Nat.card {v : C.supp // (componentLeftPairing P Q C).partner v = none} ≤ 2
  rw [Nat.card_eq_fintype_card]
  exact hbound

/-- Every connected component generated by two pairings contains at most two
occurrences that are unmatched by either pairing. -/
theorem card_component_unpaired_either_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : PartialOccurrencePairing V)
    (C : (twoPairingGraph P Q).ConnectedComponent) :
    Nat.card {v : C.supp //
      (componentLeftPairing P Q C).partner v = none ∨
      (componentRightPairing P Q C).partner v = none} ≤ 2 := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  have hconn :
      (twoPairingGraph (componentLeftPairing P Q C)
        (componentRightPairing P Q C)).Connected := by
    rw [twoPairingGraph_component_eq_induce P Q C]
    exact C.connected_toSimpleGraph
  have hbound := card_unpaired_either_le_two_of_connected
    (componentLeftPairing P Q C) (componentRightPairing P Q C) hconn
  change Nat.card {v : C.supp //
      (componentLeftPairing P Q C).partner v = none ∨
      (componentRightPairing P Q C).partner v = none} ≤ 2
  rw [Nat.card_eq_fintype_card]
  exact hbound

/-- Reify the cancellation endpoints in an indexed boundary trace as finite
occurrence indices, retaining their original pair order. -/
noncomputable def IndexedBoundaryTrace.cancellationOccurrencePairs
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    List (Fin raw.length × Fin raw.length) :=
  trace.cancellationPairs.attach.map fun entry =>
    let p := entry.1
    let hp := trace.pairs_inBounds p entry.2
    (⟨p.1, by omega⟩, ⟨p.2, hp.2⟩)

theorem IndexedBoundaryTrace.cancellationOccurrencePairs_endpoints_val
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    (occurrencePairEndpoints trace.cancellationOccurrencePairs).map Fin.val =
      pairEndpoints trace.cancellationPairs := by
  rw [← occurrencePairEndpoints_map Fin.val]
  congr 1
  dsimp [IndexedBoundaryTrace.cancellationOccurrencePairs, Function.comp_def]
  rw [List.map_map]
  change trace.cancellationPairs.attach.map Subtype.val = trace.cancellationPairs
  exact List.attach_map_subtype_val _

theorem IndexedBoundaryTrace.cancellationOccurrencePairs_endpoints_nodup
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    (occurrencePairEndpoints trace.cancellationOccurrencePairs).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [trace.cancellationOccurrencePairs_endpoints_val]
  exact trace.endpoints_nodup

theorem IndexedBoundaryTrace.cancellationOccurrencePairs_noLoop
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    ∀ p ∈ trace.cancellationOccurrencePairs, p.1 ≠ p.2 := by
  intro p hp heq
  have hval := congrArg Fin.val heq
  have hpairs := List.mem_map.mp hp
  rcases hpairs with ⟨entry, hentry, rfl⟩
  have hb := trace.pairs_inBounds entry.1 entry.property
  dsimp [IndexedBoundaryTrace.cancellationOccurrencePairs] at hval
  omega

noncomputable def IndexedBoundaryTrace.cancellationOccurrencePairing
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    PartialOccurrencePairing (Fin raw.length) :=
  occurrencePairListToPairing trace.cancellationOccurrencePairs
    trace.cancellationOccurrencePairs_endpoints_nodup
    trace.cancellationOccurrencePairs_noLoop

theorem IndexedBoundaryTrace.cancellationOccurrencePairing_spec
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) (i j : Fin raw.length) :
    trace.cancellationOccurrencePairing.partner i = some j ↔
      occurrencePairRel trace.cancellationOccurrencePairs i j := by
  exact occurrencePairListToPairing_spec
    trace.cancellationOccurrencePairs
    trace.cancellationOccurrencePairs_endpoints_nodup
    trace.cancellationOccurrencePairs_noLoop i j

theorem IndexedBoundaryTrace.cancellationOccurrencePairing_unpaired_iff_not_endpoint
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) (i : Fin raw.length) :
    trace.cancellationOccurrencePairing.partner i = none ↔
      i ∉ occurrencePairEndpoints trace.cancellationOccurrencePairs := by
  exact occurrencePairListToPairing_partner_eq_none_iff_not_mem_endpoints
    trace.cancellationOccurrencePairs
    trace.cancellationOccurrencePairs_endpoints_nodup
    trace.cancellationOccurrencePairs_noLoop i

theorem IndexedBoundaryTrace.cancellationOccurrencePairing_unpaired_iff_survivor
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) (i : Fin raw.length) :
    trace.cancellationOccurrencePairing.partner i = none ↔
      i.val ∈ trace.survivorOccurrences.map Prod.fst := by
  rw [trace.cancellationOccurrencePairing_unpaired_iff_not_endpoint]
  constructor
  · intro hnot
    rcases trace.sourcePositions_partition i.val i.isLt with hpair | hsurvivor
    · have hpairFin : i.val ∈
          (occurrencePairEndpoints trace.cancellationOccurrencePairs).map Fin.val := by
        rw [trace.cancellationOccurrencePairs_endpoints_val]
        exact hpair
      rcases List.mem_map.mp hpairFin with ⟨j, hj, hval⟩
      have hji : j = i := Fin.ext hval
      subst j
      exact (hnot hj).elim
    · exact hsurvivor
  · intro hsurvivor hpairFin
    have hpair : i.val ∈ pairEndpoints trace.cancellationPairs := by
      rw [← trace.cancellationOccurrencePairs_endpoints_val]
      exact List.mem_map.mpr ⟨i, hpairFin, rfl⟩
    exact (trace.endpoints_disjoint_survivors i.val hpair i.val hsurvivor) rfl

end GreendlingerDehn
