import SmallCancellation.Cancellation
import Mathlib.Tactic.Linarith

namespace GreendlingerDehn

/-- Shift the positions in a cancellation-pair list when it is embedded in a
larger concatenated word. -/
def shiftCancellationPairs (offset : Nat) (pairs : List (Nat × Nat)) :
    List (Nat × Nat) :=
  pairs.map fun p => (offset + p.1, offset + p.2)

/-- Flatten the two source endpoints of every cancellation pair. -/
def pairEndpoints (pairs : List (Nat × Nat)) : List Nat :=
  pairs.flatMap fun p => [p.1, p.2]

theorem pairEndpoints_shiftCancellationPairs {pairs : List (Nat × Nat)}
    (offset : Nat) :
    pairEndpoints (shiftCancellationPairs offset pairs) =
      (pairEndpoints pairs).map (offset + ·) := by
  simp [pairEndpoints, shiftCancellationPairs, List.flatMap_map,
    List.map_flatMap]

theorem pairEndpoints_length (pairs : List (Nat × Nat)) :
    (pairEndpoints pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps _ =>
      simp [pairEndpoints]
      omega

theorem pairEndpoints_append (left right : List (Nat × Nat)) :
    pairEndpoints (left ++ right) = pairEndpoints left ++ pairEndpoints right := by
  simp [pairEndpoints, List.flatMap_append]

theorem pairEndpoints_map {pairs : List (Nat × Nat)} (f : Nat → Nat) :
    pairEndpoints (pairs.map fun p => (f p.1, f p.2)) =
      (pairEndpoints pairs).map f := by
  simp [pairEndpoints, List.flatMap_map, List.map_flatMap]

/-- Shift surviving letter occurrences when their source word is embedded in a
larger concatenation. Each occurrence retains its source position and label. -/
def shiftLetterOccurrences (offset : Nat) (occurrences : List (Nat × Letter α)) :
    List (Nat × Letter α) :=
  occurrences.map fun o => (offset + o.1, o.2)

theorem shiftLetterOccurrences_preservesLabels {α : Type*} (offset : Nat)
    (occurrences : List (Nat × Letter α)) :
    (shiftLetterOccurrences offset occurrences).map Prod.snd =
      occurrences.map Prod.snd := by
  simp [shiftLetterOccurrences, Function.comp_def]

theorem shiftLetterOccurrences_positions {α : Type*} (offset : Nat)
    (occurrences : List (Nat × Letter α)) :
    (shiftLetterOccurrences offset occurrences).map Prod.fst =
      (occurrences.map Prod.fst).map (offset + ·) := by
  simp [shiftLetterOccurrences, List.map_map, Function.comp_def]

/-- Two ordered cancellation intervals are compatible when they are disjoint
or one contains the other. -/
def CancellationIntervalsCompatible (p q : Nat × Nat) : Prop :=
  p.2 < q.1 ∨ q.2 < p.1 ∨
    (p.1 ≤ q.1 ∧ q.2 ≤ p.2) ∨ (q.1 ≤ p.1 ∧ p.2 ≤ q.2)

theorem CancellationIntervalsCompatible.symm {p q : Nat × Nat}
    (h : CancellationIntervalsCompatible p q) :
    CancellationIntervalsCompatible q p := by
  rcases h with h | h | ⟨hpq₁, hqp₂⟩ | ⟨hqp₁, hpq₂⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr ⟨hpq₁, hqp₂⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hqp₁, hpq₂⟩))

def CancellationPairsNoncrossing (pairs : List (Nat × Nat)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs, CancellationIntervalsCompatible p q

/-- Finite source-position data for a word reduction. The record captures a
noncrossing inverse-letter pairing and the ordered surviving occurrences;
these are the combinatorial inputs to a later planar gluing construction. -/
structure IndexedBoundaryTrace {α : Type*} (raw reduced : Word α) where
  cancellationPairs : List (Nat × Nat)
  survivorOccurrences : List (Nat × Letter α)
  pairs_noncrossing : CancellationPairsNoncrossing cancellationPairs
  pairs_are_inverseLetters : ∀ p ∈ cancellationPairs,
    ∃ a, raw[p.1]? = some a ∧ raw[p.2]? = some (inverseLetter a)
  pairs_inBounds : ∀ p ∈ cancellationPairs,
    p.1 < p.2 ∧ p.2 < raw.length
  endpoints_nodup : (pairEndpoints cancellationPairs).Nodup
  endpoints_inBounds : ∀ i ∈ pairEndpoints cancellationPairs, i < raw.length
  survivors_labels : survivorOccurrences.map Prod.snd = reduced
  survivors_length : survivorOccurrences.length = reduced.length
  survivorPositions_nodup : (survivorOccurrences.map Prod.fst).Nodup
  survivorPositions_strict : List.Pairwise (fun i j : Nat => i < j)
    (survivorOccurrences.map Prod.fst)
  survivors_are_sourceLetters : ∀ o ∈ survivorOccurrences,
    raw[o.1]? = some o.2
  survivors_inBounds : ∀ o ∈ survivorOccurrences, o.1 < raw.length
  endpoints_disjoint_survivors : ∀ i ∈ pairEndpoints cancellationPairs,
    ∀ j ∈ survivorOccurrences.map Prod.fst, i ≠ j
  no_survivor_inside_pair : ∀ p ∈ cancellationPairs,
    ∀ o ∈ survivorOccurrences, p.1 < o.1 → o.1 < p.2 → False
  endpoint_survivor_count : (pairEndpoints cancellationPairs).length +
    (survivorOccurrences.map Prod.fst).length = raw.length
  sourcePositions_partition : ∀ i, i < raw.length →
    i ∈ pairEndpoints cancellationPairs ∨
      i ∈ survivorOccurrences.map Prod.fst

theorem IndexedBoundaryTrace.pair_endpoints_disjoint
    {α : Type*} {raw reduced : Word α} (trace : IndexedBoundaryTrace raw reduced)
    {p q : Nat × Nat} (hp : p ∈ trace.cancellationPairs)
    (hq : q ∈ trace.cancellationPairs) (hne : p ≠ q) :
    List.Disjoint [p.1, p.2] [q.1, q.2] := by
  have hsymm : Std.Symm (Function.onFun List.Disjoint
      (fun a : Nat × Nat => [a.1, a.2])) :=
    ⟨fun a b h => List.disjoint_comm.mp h⟩
  have hpairwise := (List.nodup_flatMap.mp (by
    simpa [pairEndpoints] using trace.endpoints_nodup)).2
  exact @List.Pairwise.forall (Nat × Nat)
    (Function.onFun List.Disjoint (fun a => [a.1, a.2]))
    trace.cancellationPairs hsymm hpairwise p hp q hq hne

theorem IndexedBoundaryTrace.pair_endpoints_ne
    {α : Type*} {raw reduced : Word α} (trace : IndexedBoundaryTrace raw reduced)
    {p q : Nat × Nat} (hp : p ∈ trace.cancellationPairs)
    (hq : q ∈ trace.cancellationPairs) (hne : p ≠ q) :
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
  have hdisjoint := trace.pair_endpoints_disjoint hp hq hne
  have hdisjointNe := List.disjoint_iff_ne.mp hdisjoint
  exact ⟨hdisjointNe _ (by simp) _ (by simp),
    hdisjointNe _ (by simp) _ (by simp),
    hdisjointNe _ (by simp) _ (by simp),
    hdisjointNe _ (by simp) _ (by simp)⟩

theorem IndexedBoundaryTrace.interior_pair_is_strictly_nested
    {α : Type*} {raw reduced : Word α} (trace : IndexedBoundaryTrace raw reduced)
    {p q : Nat × Nat} (hp : p ∈ trace.cancellationPairs)
    (hq : q ∈ trace.cancellationPairs) (hforward : q.1 < q.2)
    {i : Nat} (hleft : p.1 < i) (hright : i < p.2)
    (hendpoint : i = q.1 ∨ i = q.2) :
    p.1 < q.1 ∧ q.2 < p.2 := by
  have hpne : p ≠ q := by
    intro heq
    subst q
    rcases hendpoint with h | h <;> omega
  have hendpointsNe := trace.pair_endpoints_ne hp hq hpne
  have hcompat := trace.pairs_noncrossing p hp q hq
  rcases hcompat with hsep | hsep | ⟨hpq₁, hqp₂⟩ | ⟨hqp₁, hpq₂⟩
  · rcases hendpoint with h | h <;> omega
  · rcases hendpoint with h | h <;> omega
  · rcases hendpoint with h | h
    · subst i
      constructor
      · exact hleft
      · omega
    · subst i
      constructor
      · omega
      · exact hright
  · rcases hendpoint with h | h <;> omega

theorem IndexedBoundaryTrace.interior_position_has_pair
    {α : Type*} {raw reduced : Word α} (trace : IndexedBoundaryTrace raw reduced)
    {p : Nat × Nat} (hp : p ∈ trace.cancellationPairs)
    {i : Nat} (hleft : p.1 < i) (hright : i < p.2) :
    ∃ q ∈ trace.cancellationPairs,
      p.1 < q.1 ∧ q.2 < p.2 ∧ (i = q.1 ∨ i = q.2) := by
  have hpBound := trace.pairs_inBounds p hp
  have hInRaw : i < raw.length := Nat.lt_trans hright hpBound.2
  rcases trace.sourcePositions_partition i hInRaw with hiEndpoint | hiSurvivor
  · rcases List.mem_flatMap.mp hiEndpoint with ⟨q, hq, hiq⟩
    simp only [List.mem_cons, List.not_mem_nil] at hiq
    rcases hiq with hiq | hiq
    · have hforward := (trace.pairs_inBounds q hq).1
      obtain ⟨hfirst, hsecond⟩ :=
        trace.interior_pair_is_strictly_nested hp hq hforward hleft hright
          (Or.inl hiq)
      exact ⟨q, hq, hfirst, hsecond, Or.inl hiq⟩
    · rcases hiq with hiq | hfalse
      · have hforward := (trace.pairs_inBounds q hq).1
        obtain ⟨hfirst, hsecond⟩ :=
          trace.interior_pair_is_strictly_nested hp hq hforward hleft hright
            (Or.inr hiq)
        exact ⟨q, hq, hfirst, hsecond, Or.inr hiq⟩
      · cases hfalse
  · rcases List.mem_map.mp hiSurvivor with ⟨o, ho, hio⟩
    have hpos : o.1 = i := by simpa using hio
    exact False.elim (trace.no_survivor_inside_pair p hp o ho
      (by omega) (by omega))

theorem IndexedBoundaryTrace.first_interior_position_starts_pair
    {α : Type*} {raw reduced : Word α} (trace : IndexedBoundaryTrace raw reduced)
    {p : Nat × Nat} (hp : p ∈ trace.cancellationPairs)
    (hgap : p.1 + 1 < p.2) :
  ∃ q ∈ trace.cancellationPairs,
      q.1 = p.1 + 1 ∧ q.2 < p.2 := by
  obtain ⟨q, hq, hpq₁, hqp₂, hendpoint⟩ :=
    trace.interior_position_has_pair (i := p.1 + 1) hp (by omega) hgap
  rcases hendpoint with hq₁ | hq₂
  · exact ⟨q, hq, hq₁.symm, hqp₂⟩
  · exfalso
    have hqForward := (trace.pairs_inBounds q hq).1
    omega

theorem IndexedBoundaryTrace.next_interior_position_starts_pair
    {α : Type*} {raw reduced : Word α} (trace : IndexedBoundaryTrace raw reduced)
    {p q : Nat × Nat} (hp : p ∈ trace.cancellationPairs)
    (hq : q ∈ trace.cancellationPairs)
    (hqFirst : q.1 = p.1 + 1)
    (hgap : q.2 + 1 < p.2) :
    ∃ r ∈ trace.cancellationPairs,
      r.1 = q.2 + 1 ∧ r.2 < p.2 := by
  have hqForward := (trace.pairs_inBounds q hq).1
  obtain ⟨r, hr, hpr₁, hpr₂, hendpoint⟩ :=
    trace.interior_position_has_pair (i := q.2 + 1) hp (by omega) hgap
  rcases hendpoint with hstart | hclose
  · exact ⟨r, hr, hstart.symm, hpr₂⟩
  · exfalso
    have hrForward := (trace.pairs_inBounds r hr).1
    have hr2Eq : r.2 = q.2 + 1 := by omega
    have hne : q ≠ r := by
      intro heq
      have heq₂ : q.2 = r.2 := congrArg Prod.snd heq
      omega
    have hcompat := trace.pairs_noncrossing q hq r hr
    rcases hcompat with hsep | hsep | ⟨hq₁, hr₂⟩ | ⟨hr₁, hq₂⟩
    · omega
    · omega
    · omega
    · have hendpointsNe := trace.pair_endpoints_ne hq hr hne
      exact hendpointsNe.1 (by omega)

theorem CancellationIntervalsCompatible.map_strictMono {p q : Nat × Nat}
    {f : Nat → Nat} (hf : ∀ ⦃x y⦄, x < y → f x < f y)
    (h : CancellationIntervalsCompatible p q) :
    CancellationIntervalsCompatible
      (f p.1, f p.2) (f q.1, f q.2) := by
  have map_le {x y : Nat} (hxy : x ≤ y) : f x ≤ f y := by
    rcases Nat.eq_or_lt_of_le hxy with heq | hlt
    · subst y
      exact le_rfl
    · exact (hf hlt).le
  rcases h with h | h | ⟨hpq₁, hqp₂⟩ | ⟨hqp₁, hpq₂⟩
  · exact Or.inl (hf h)
  · exact Or.inr (Or.inl (hf h))
  · exact Or.inr (Or.inr (Or.inl ⟨map_le hpq₁, map_le hqp₂⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨map_le hqp₁, map_le hpq₂⟩))

theorem CancellationIntervalsCompatible.shift {p q : Nat × Nat}
    (h : CancellationIntervalsCompatible p q) (offset : Nat) :
    CancellationIntervalsCompatible (offset + p.1, offset + p.2)
      (offset + q.1, offset + q.2) := by
  rcases h with h | h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem shiftCancellationPairs_nonCrossing {pairs : List (Nat × Nat)}
    (h : CancellationPairsNoncrossing pairs) (offset : Nat) :
    CancellationPairsNoncrossing (shiftCancellationPairs offset pairs) := by
  intro p hp q hq
  rcases List.mem_map.mp hp with ⟨p₀, hp₀, rfl⟩
  rcases List.mem_map.mp hq with ⟨q₀, hq₀, rfl⟩
  exact (h p₀ hp₀ q₀ hq₀).shift offset

theorem getElem?_append_shift {α : Type*} (lhs suffix : List α) (i : Nat) :
    (lhs ++ suffix)[lhs.length + i]? = suffix[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem getElem?_append_middle {α : Type*} (lhs middle suffix : List α)
    {i : Nat} (hi : i < middle.length) :
    ((lhs ++ middle) ++ suffix)[lhs.length + i]? = middle[i]? := by
  have hleft : lhs.length + i < (lhs ++ middle).length := by
    simp only [List.length_append]
    omega
  rw [List.getElem?_append_left hleft]
  exact getElem?_append_shift lhs middle i

namespace FreeReductionShape

variable {α : Type*}

/-- The raw input word carried by a reduction shape. -/
def inputWord {raw reduced : Word α} (_ : FreeReductionShape raw reduced) : Word α := raw

/-- Absolute source positions of the inverse-letter pairs cancelled by a
reduction shape. Appending shifts the right subtree; a bracket places its
outer pair around the inner cancellations and before the suffix. -/
def cancellationPairs {raw reduced : Word α} (h : FreeReductionShape raw reduced) :
    List (Nat × Nat) :=
  match h with
  | .empty => []
  | .letter _ => []
  | .append left right =>
      left.cancellationPairs ++
        shiftCancellationPairs left.inputWord.length right.cancellationPairs
  | .bracket a inner suffix =>
      (0, inner.inputWord.length + 1) ::
        (shiftCancellationPairs 1 inner.cancellationPairs ++
        shiftCancellationPairs (inner.inputWord.length + 2) suffix.cancellationPairs)

/-- Ordered source occurrences of the letters left after free reduction.
Cancelled bracket interiors contribute no survivors; the suffix is shifted
past the opening letter, interior, and closing inverse letter. -/
def survivorOccurrences {raw reduced : Word α} (h : FreeReductionShape raw reduced) :
    List (Nat × Letter α) :=
  match h with
  | .empty => []
  | .letter a => [(0, a)]
  | .append left right =>
      left.survivorOccurrences ++
        shiftLetterOccurrences left.inputWord.length right.survivorOccurrences
  | .bracket _ inner suffix =>
      shiftLetterOccurrences (inner.inputWord.length + 2) suffix.survivorOccurrences

theorem survivorOccurrences_labels {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    h.survivorOccurrences.map Prod.snd = reduced := by
  induction h with
  | empty => rfl
  | letter a => rfl
  | append left right ihLeft ihRight =>
      simp [survivorOccurrences, ihLeft, ihRight,
        shiftLetterOccurrences_preservesLabels]
  | bracket a inner suffix ihInner ihSuffix =>
      simp [survivorOccurrences, ihSuffix,
        shiftLetterOccurrences_preservesLabels]

theorem survivorOccurrences_length {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    h.survivorOccurrences.length = reduced.length := by
  have hlabels := survivorOccurrences_labels h
  calc
    h.survivorOccurrences.length =
        (h.survivorOccurrences.map Prod.snd).length := by simp
    _ = reduced.length := by rw [hlabels]

theorem survivorOccurrences_inBounds {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ o ∈ h.survivorOccurrences, o.1 < h.inputWord.length := by
  induction h with
  | empty => simp [survivorOccurrences, inputWord]
  | letter a => simp [survivorOccurrences, inputWord]
  | @append u u' v v' left right ihLeft ihRight =>
      intro o ho
      simp only [survivorOccurrences, List.mem_append] at ho
      rcases ho with hoLeft | hoRight
      · have hleft := ihLeft o hoLeft
        have hleft' : o.1 < u.length := by simpa [inputWord] using hleft
        have hcombined : o.1 < (u ++ v).length := by
          simp only [List.length_append]
          omega
        simpa [inputWord] using hcombined
      · rcases List.mem_map.mp hoRight with ⟨q, hq, hqo⟩
        have hright := ihRight q hq
        have hright' : q.1 < v.length := by simpa [inputWord] using hright
        subst o
        simp only [inputWord, List.length_append]
        omega
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro o ho
      simp only [survivorOccurrences, shiftLetterOccurrences] at ho
      rcases List.mem_map.mp ho with ⟨q, hq, hqo⟩
      have hright := ihSuffix q hq
      have hright' : q.1 < suffix.length := by simpa [inputWord] using hright
      subst o
      simp only [inputWord, List.length_append, List.length_cons,
        List.length_nil]
      omega

theorem survivorOccurrencePositions_nodup {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    (h.survivorOccurrences.map Prod.fst).Nodup := by
  induction h with
  | empty => simp [survivorOccurrences]
  | letter a => simp [survivorOccurrences]
  | @append u u' v v' left right ihLeft ihRight =>
      simp only [survivorOccurrences, List.map_append,
        shiftLetterOccurrences_positions]
      change List.Pairwise (fun x y : Nat => x ≠ y)
        (left.survivorOccurrences.map Prod.fst ++
          (right.survivorOccurrences.map Prod.fst).map
            (left.inputWord.length + ·))
      rw [List.pairwise_append]
      refine ⟨ihLeft, ?_, ?_⟩
      · apply List.Nodup.map
        · intro x y hxy
          exact Nat.add_left_cancel hxy
        · exact ihRight
      · intro x hx y hy hxy
        rcases List.mem_map.mp hx with ⟨o, ho, rfl⟩
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        have hbound := left.survivorOccurrences_inBounds o ho
        omega
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      simp only [survivorOccurrences, shiftLetterOccurrences_positions]
      have hinjective : Function.Injective
          (fun x : Nat => innerShape.inputWord.length + 2 + x) := by
        intro x y hxy
        exact Nat.add_left_cancel hxy
      exact ihSuffix.map hinjective

theorem survivorOccurrencePositions_strict {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    List.Pairwise (fun x y : Nat => x < y)
      (h.survivorOccurrences.map Prod.fst) := by
  induction h with
  | empty => simp [survivorOccurrences]
  | letter a => simp [survivorOccurrences]
  | @append u u' v v' left right ihLeft ihRight =>
      simp only [survivorOccurrences, List.map_append,
        shiftLetterOccurrences_positions]
      change List.Pairwise (fun x y : Nat => x < y)
        (left.survivorOccurrences.map Prod.fst ++
          (right.survivorOccurrences.map Prod.fst).map
            (left.inputWord.length + ·))
      rw [List.pairwise_append]
      refine ⟨ihLeft, ?_, ?_⟩
      · rw [List.pairwise_map]
        apply ihRight.imp
        intro x y hxy
        omega
      · intro x hx y hy
        rcases List.mem_map.mp hx with ⟨o, ho, rfl⟩
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        have hbound := left.survivorOccurrences_inBounds o ho
        have hleft : o.1 < u.length := by
          simpa [inputWord] using hbound
        have hoffset : left.inputWord.length = u.length := by simp [inputWord]
        omega
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      simp only [survivorOccurrences, shiftLetterOccurrences_positions]
      rw [List.pairwise_map]
      apply ihSuffix.imp
      intro x y hxy
      omega

/-- The ordered source positions of the retained output letters. -/
def survivorPositions {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) : List Nat :=
  h.survivorOccurrences.map Prod.fst

theorem survivorPositions_length {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    (h.survivorPositions).length = reduced.length := by
  simp [survivorPositions, h.survivorOccurrences_length]

/-- Recover the source position of an output letter by its index in the
reduced word. The strict-order theorem makes this map an order embedding. -/
def survivorOutputIndex {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (i : Fin reduced.length) :
    Fin h.survivorPositions.length :=
  ⟨i.val, by
    rw [survivorPositions, List.length_map, h.survivorOccurrences_length]
    exact i.isLt⟩

def sourcePositionOfOutput {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (i : Fin reduced.length) : Nat :=
  h.survivorPositions.get (h.survivorOutputIndex i)

/-- Strictly increasing total extension of `sourcePositionOfOutput`. Out-of-
range output indices are placed after all source positions. -/
def sourcePositionOfOutputNat {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (i : Nat) : Nat :=
  if hi : i < reduced.length then h.sourcePositionOfOutput ⟨i, hi⟩
  else h.inputWord.length + (i - reduced.length)

theorem sourcePositionOfOutputNat_eq {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) {i : Nat} (hi : i < reduced.length) :
    h.sourcePositionOfOutputNat i = h.sourcePositionOfOutput ⟨i, hi⟩ := by
  simp [sourcePositionOfOutputNat, hi]

theorem survivorPositions_inBounds {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ i ∈ h.survivorPositions, i < h.inputWord.length := by
  intro i hi
  have hi' : i ∈ h.survivorOccurrences.map Prod.fst := by
    simpa only [survivorPositions] using hi
  rcases List.mem_map.mp hi' with ⟨o, ho, hEq⟩
  rw [← hEq]
  exact h.survivorOccurrences_inBounds o ho

theorem sourcePositionOfOutput_inBounds {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (i : Fin reduced.length) :
    h.sourcePositionOfOutput i < h.inputWord.length := by
  exact (List.forall_mem_iff_get.mp h.survivorPositions_inBounds)
    (h.survivorOutputIndex i)

theorem sourcePositionOfOutput_mem {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (i : Fin reduced.length) :
    h.sourcePositionOfOutput i ∈ h.survivorPositions := by
  change h.survivorPositions.get (h.survivorOutputIndex i) ∈ h.survivorPositions
  exact List.get_mem _ _

theorem sourcePositionOfOutput_strict {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) {i j : Fin reduced.length}
    (hij : i < j) : h.sourcePositionOfOutput i < h.sourcePositionOfOutput j := by
  have hij' : h.survivorOutputIndex i < h.survivorOutputIndex j :=
    Fin.mk_lt_mk.mpr hij
  have hstrict := h.survivorOccurrencePositions_strict.rel_get_of_lt hij'
  exact hstrict

theorem sourcePositionOfOutputNat_strict {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) {i j : Nat} (hij : i < j) :
    h.sourcePositionOfOutputNat i < h.sourcePositionOfOutputNat j := by
  by_cases hi : i < reduced.length
  · by_cases hj : j < reduced.length
    · rw [h.sourcePositionOfOutputNat_eq hi, h.sourcePositionOfOutputNat_eq hj]
      exact h.sourcePositionOfOutput_strict (Fin.mk_lt_mk.mpr hij)
    · rw [h.sourcePositionOfOutputNat_eq hi]
      have hbound := h.sourcePositionOfOutput_inBounds ⟨i, hi⟩
      have hj' : reduced.length ≤ j := Nat.le_of_not_gt hj
      simp [sourcePositionOfOutputNat, hj]
      omega
  · have hj : ¬ j < reduced.length := by omega
    simp [sourcePositionOfOutputNat, hi, hj]
    omega

theorem sourcePositionOfOutputNat_injective {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    Function.Injective h.sourcePositionOfOutputNat := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := h.sourcePositionOfOutputNat_strict hlt
    omega
  · have hstrict := h.sourcePositionOfOutputNat_strict hgt
    omega

theorem sourcePositionOfOutput_injective {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    Function.Injective h.sourcePositionOfOutput := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := h.sourcePositionOfOutput_strict hlt
    omega
  · have hstrict := h.sourcePositionOfOutput_strict hgt
    omega

/-- Lift a pair of output positions back to the corresponding source
occurrences of an earlier free reduction. -/
def liftCancellationPair {raw reduced : Word α}
    (h : FreeReductionShape raw reduced)
    (p : Fin reduced.length × Fin reduced.length) : Nat × Nat :=
  (h.sourcePositionOfOutput p.1, h.sourcePositionOfOutput p.2)

theorem liftCancellationPair_forward {raw reduced : Word α}
    (h : FreeReductionShape raw reduced)
    {p : Fin reduced.length × Fin reduced.length}
    (hp : p.1.val < p.2.val) :
    (h.liftCancellationPair p).1 < (h.liftCancellationPair p).2 := by
  exact h.sourcePositionOfOutput_strict (Fin.mk_lt_mk.mpr hp)

theorem liftCancellationPair_preserves_compatibility {raw reduced : Word α}
    (h : FreeReductionShape raw reduced)
    {p q : Fin reduced.length × Fin reduced.length}
    (hpq : CancellationIntervalsCompatible (p.1.val, p.2.val)
      (q.1.val, q.2.val)) :
    CancellationIntervalsCompatible (h.liftCancellationPair p)
      (h.liftCancellationPair q) := by
  have map_lt {i j : Fin reduced.length} (hij : i.val < j.val) :
      h.sourcePositionOfOutput i < h.sourcePositionOfOutput j :=
    h.sourcePositionOfOutput_strict (Fin.mk_lt_mk.mpr hij)
  have map_le {i j : Fin reduced.length} (hij : i.val ≤ j.val) :
      h.sourcePositionOfOutput i ≤ h.sourcePositionOfOutput j := by
    rcases Nat.eq_or_lt_of_le hij with heq | hlt
    · have hEq : i = j := Fin.ext heq
      subst j
      exact le_rfl
    · exact (map_lt hlt).le
  rcases hpq with hpq | hqp | ⟨hpq₁, hqp₂⟩ | ⟨hqp₁, hpq₂⟩
  · exact Or.inl (map_lt hpq)
  · exact Or.inr (Or.inl (map_lt hqp))
  · exact Or.inr (Or.inr (Or.inl ⟨map_le hpq₁, map_le hqp₂⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨map_le hqp₁, map_le hpq₂⟩))

/-- Apply the total monotone source-position map to an arbitrary pair of
integer output positions. -/
def liftCancellationPairNat {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (p : Nat × Nat) : Nat × Nat :=
  (h.sourcePositionOfOutputNat p.1, h.sourcePositionOfOutputNat p.2)

theorem liftCancellationPairNat_preserves_compatibility {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) {p q : Nat × Nat}
    (hpq : CancellationIntervalsCompatible p q) :
    CancellationIntervalsCompatible (h.liftCancellationPairNat p)
      (h.liftCancellationPairNat q) := by
  exact CancellationIntervalsCompatible.map_strictMono
    (fun {_ _} hij => h.sourcePositionOfOutputNat_strict hij) hpq

/-- Lift every cancellation pair in a later reduction through an earlier
reduction, using the source occurrence retained at each endpoint. -/
def liftCancellationPairs {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) : List (Nat × Nat) :=
  later.cancellationPairs.map fun p =>
    earlier.liftCancellationPairNat p

theorem liftCancellationPairs_eq_map {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    liftCancellationPairs earlier later =
      later.cancellationPairs.map fun p =>
        earlier.liftCancellationPairNat p := by
  rfl

/-- Lift the retained output occurrences of a later reduction through an
earlier reduction while preserving their labels and order. -/
def liftSurvivorOccurrences {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) : List (Nat × Letter α) :=
  later.survivorOccurrences.map fun o =>
    (earlier.sourcePositionOfOutputNat o.1, o.2)

theorem liftSurvivorOccurrences_eq_map {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    liftSurvivorOccurrences earlier later =
      later.survivorOccurrences.map fun o =>
        (earlier.sourcePositionOfOutputNat o.1, o.2) := by
  rfl

theorem liftSurvivorOccurrences_labels {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (liftSurvivorOccurrences earlier later).map Prod.snd = reduced := by
  rw [liftSurvivorOccurrences_eq_map]
  simpa [List.map_map, Function.comp_def] using later.survivorOccurrences_labels

theorem liftSurvivorOccurrences_length {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (liftSurvivorOccurrences earlier later).length = reduced.length := by
  rw [liftSurvivorOccurrences_eq_map]
  simp [later.survivorOccurrences_length]

theorem liftSurvivorOccurrences_positions {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (liftSurvivorOccurrences earlier later).map Prod.fst =
      later.survivorPositions.map earlier.sourcePositionOfOutputNat := by
  rw [liftSurvivorOccurrences_eq_map]
  simp [survivorPositions, List.map_map, Function.comp_def]

theorem liftSurvivorOccurrences_positions_strict {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    List.Pairwise (fun x y : Nat => x < y)
      ((liftSurvivorOccurrences earlier later).map Prod.fst) := by
  rw [liftSurvivorOccurrences_positions, List.pairwise_map]
  apply later.survivorOccurrencePositions_strict.imp
  intro x y hxy
  exact earlier.sourcePositionOfOutputNat_strict hxy

theorem liftSurvivorOccurrences_positions_nodup {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ((liftSurvivorOccurrences earlier later).map Prod.fst).Nodup := by
  have hstrict := earlier.liftSurvivorOccurrences_positions_strict later
  change List.Pairwise (fun x y : Nat => x ≠ y)
    ((liftSurvivorOccurrences earlier later).map Prod.fst)
  exact hstrict.imp (fun hlt => Nat.ne_of_lt hlt)

theorem liftSurvivorOccurrences_inBounds {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ o ∈ liftSurvivorOccurrences earlier later,
      o.1 < earlier.inputWord.length := by
  intro o ho
  rw [liftSurvivorOccurrences_eq_map] at ho
  rcases List.mem_map.mp ho with ⟨p, hp, rfl⟩
  have hpBound := later.survivorOccurrences_inBounds p hp
  have hpLt : p.1 < middle.length := by simpa [inputWord] using hpBound
  rw [earlier.sourcePositionOfOutputNat_eq hpLt]
  exact earlier.sourcePositionOfOutput_inBounds ⟨p.1, hpLt⟩

theorem survivorOccurrences_are_sourceLetters {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ o ∈ h.survivorOccurrences, raw[o.1]? = some o.2 := by
  induction h with
  | empty => simp [survivorOccurrences]
  | letter a => simp [survivorOccurrences]
  | @append u u' v v' left right ihLeft ihRight =>
      intro o ho
      simp only [survivorOccurrences, List.mem_append] at ho
      rcases ho with hoLeft | hoRight
      · have hbound := left.survivorOccurrences_inBounds o hoLeft
        have hleft : o.1 < u.length := by simpa [inputWord] using hbound
        have hsource := ihLeft o hoLeft
        simpa only [List.getElem?_append_left hleft] using hsource
      · rcases List.mem_map.mp hoRight with ⟨q, hq, hqo⟩
        subst o
        have hsource := ihRight q hq
        have hoffset : left.inputWord.length = u.length := by simp [inputWord]
        rw [hoffset, getElem?_append_shift]
        exact hsource
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro o ho
      simp only [survivorOccurrences, shiftLetterOccurrences] at ho
      rcases List.mem_map.mp ho with ⟨q, hq, hqo⟩
      subst o
      simp only [inputWord]
      have hsource := ihSuffix q hq
      have hlen : innerShape.inputWord.length = inner.length := by
        simp [inputWord]
      have hprefix : (([a] ++ inner) ++ [inverseLetter a]).length =
          inner.length + 2 := by
        simp [List.length_append]
      calc
        ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[
            inner.length + 2 + q.1]? =
            ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[
              (([a] ++ inner) ++ [inverseLetter a]).length + q.1]? := by
          rw [hprefix]
        _ = suffix[q.1]? := getElem?_append_shift
          (([a] ++ inner) ++ [inverseLetter a]) suffix q.1
        _ = q.2 := hsource

theorem sourcePositionOfOutput_sourceLetter {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) (i : Fin reduced.length) :
    raw[h.sourcePositionOfOutput i]? = some reduced[i.val] := by
  have hi : i.val < h.survivorOccurrences.length := by
    rw [h.survivorOccurrences_length]
    exact i.isLt
  let o : Nat × Letter α := h.survivorOccurrences[i.val]
  have ho : o ∈ h.survivorOccurrences := by
    dsimp [o]
    exact List.getElem_mem hi
  have hsource := h.survivorOccurrences_are_sourceLetters o ho
  have hposition : h.sourcePositionOfOutput i = o.1 := by
    dsimp [sourcePositionOfOutput, survivorOutputIndex, survivorPositions, o]
    simp
  have hlabel : o.2 = reduced[i.val] := by
    have hlabels := congrArg (fun xs : List (Letter α) => xs[i.val]?)
      h.survivorOccurrences_labels
    have hlabels' : (h.survivorOccurrences[i.val]?).map Prod.snd =
        some reduced[i.val] := by simpa using hlabels
    have ho' : h.survivorOccurrences[i.val]? = some o := by
      simp [o, hi]
    rw [ho'] at hlabels'
    injection hlabels' with hlabel
  calc
    raw[h.sourcePositionOfOutput i]? = raw[o.1]? := by rw [hposition]
    _ = some o.2 := hsource
    _ = some reduced[i.val] := by rw [hlabel]

theorem cancellationPairs_length {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    h.cancellationPairs.length = h.cancellationCount := by
  induction h with
  | empty => rfl
  | letter _ => rfl
  | append left right ihLeft ihRight =>
      simp [cancellationPairs, shiftCancellationPairs, cancellationCount,
        ihLeft, ihRight]
  | bracket a inner suffix ihInner ihSuffix =>
      simp [cancellationPairs, shiftCancellationPairs, cancellationCount,
        ihInner, ihSuffix]

/-- Every cancellation pair points forward and stays inside its source word.
The explicit indices are the finite combinatorial data for a later planar
gluing construction. -/
theorem cancellationPairs_inBounds {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ p ∈ h.cancellationPairs,
      p.1 < p.2 ∧ p.2 < h.inputWord.length := by
  induction h with
  | empty => simp [cancellationPairs]
  | letter a => simp [cancellationPairs]
  | @append u u' v v' left right ihLeft ihRight =>
      intro p hp
      simp only [cancellationPairs, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨horder, hbound⟩ := ihLeft p hp
        have hbound' : p.2 < u.length := by simpa [inputWord] using hbound
        exact ⟨horder, by simp only [inputWord, List.length_append]; omega⟩
      · rcases List.mem_map.mp hp with ⟨q, hq, hqp⟩
        have hqBound := ihRight q hq
        have hqOrder : q.1 < q.2 := hqBound.1
        have hqLength : q.2 < v.length := by
          simpa [inputWord] using hqBound.2
        subst p
        simp only [inputWord, List.length_append]
        constructor <;> omega
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro p hp
      simp only [cancellationPairs, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hp
      · subst p
        simp only [inputWord, List.length_append, List.length_cons, List.length_nil]
        constructor <;> omega
      · rcases hp with hp | hp
        · rcases List.mem_map.mp hp with ⟨q, hq, hqp⟩
          have hqBound := ihInner q hq
          have hqOrder : q.1 < q.2 := hqBound.1
          have hqLength : q.2 < inner.length := by
            simpa [inputWord] using hqBound.2
          subst p
          simp only [inputWord, List.length_append, List.length_cons,
            List.length_nil]
          constructor <;> omega
        · rcases List.mem_map.mp hp with ⟨q, hq, hqp⟩
          have hqBound := ihSuffix q hq
          have hqOrder : q.1 < q.2 := hqBound.1
          have hqLength : q.2 < suffix.length := by
            simpa [inputWord] using hqBound.2
          subst p
          simp only [inputWord, List.length_append, List.length_cons,
            List.length_nil]
          constructor <;> omega

theorem cancellationEndpoints_length {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    (pairEndpoints h.cancellationPairs).length = 2 * h.cancellationCount := by
  rw [pairEndpoints_length, h.cancellationPairs_length]

theorem cancellationEndpoints_inBounds {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ i ∈ pairEndpoints h.cancellationPairs, i < h.inputWord.length := by
  intro i hi
  rcases List.mem_flatMap.mp hi with ⟨p, hp, hpi⟩
  have hbounds := h.cancellationPairs_inBounds p hp
  simp only [List.mem_cons, List.not_mem_nil] at hpi
  rcases hpi with hpi | hpi
  · rw [hpi]
    exact Nat.lt_trans hbounds.1 hbounds.2
  · rcases hpi with hpi | hnil
    · rw [hpi]
      exact hbounds.2
    · cases hnil

theorem cancellationEndpoints_nodup {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    (pairEndpoints h.cancellationPairs).Nodup := by
  induction h with
  | empty => simp [cancellationPairs, pairEndpoints]
  | letter a => simp [cancellationPairs, pairEndpoints]
  | @append u u' v v' left right ihLeft ihRight =>
      simp only [cancellationPairs]
      rw [show pairEndpoints (left.cancellationPairs ++
          shiftCancellationPairs left.inputWord.length right.cancellationPairs) =
          pairEndpoints left.cancellationPairs ++
            pairEndpoints (shiftCancellationPairs left.inputWord.length
              right.cancellationPairs) by
        simp [pairEndpoints, List.flatMap_append]]
      rw [pairEndpoints_shiftCancellationPairs]
      change List.Pairwise (fun x y : Nat => x ≠ y)
        (pairEndpoints left.cancellationPairs ++
          (pairEndpoints right.cancellationPairs).map
            (left.inputWord.length + ·))
      rw [List.pairwise_append]
      refine ⟨ihLeft, ?_, ?_⟩
      · apply List.Nodup.map
        · intro x y hxy
          exact Nat.add_left_cancel hxy
        · exact ihRight
      · intro x hx y hy hxy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        have hbound := left.cancellationEndpoints_inBounds x hx
        have hoffset : left.inputWord.length = u.length := by simp [inputWord]
        omega
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      let n := innerShape.inputWord.length
      let inside := (pairEndpoints innerShape.cancellationPairs).map (1 + ·)
      let after := (pairEndpoints suffixShape.cancellationPairs).map (n + 2 + ·)
      have hinnerInjective : Function.Injective (fun x : Nat => 1 + x) := by
        intro x y hxy
        exact Nat.add_left_cancel hxy
      have hafterInjective :
          Function.Injective (fun x : Nat => n + 2 + x) := by
        intro x y hxy
        exact Nat.add_left_cancel hxy
      have hinsideNodup : inside.Nodup := by
        dsimp [inside]
        exact ihInner.map hinnerInjective
      have hafterNodup : after.Nodup := by
        dsimp [after]
        exact ihSuffix.map hafterInjective
      have hinsideBounds : ∀ x ∈ inside, 1 ≤ x ∧ x < n + 1 := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hybound := innerShape.cancellationEndpoints_inBounds y hy
        omega
      have hafterLower : ∀ x ∈ after, n + 2 ≤ x := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        omega
      have hrootNodup : ([0, n + 1] : List Nat).Nodup := by
        simp [n]
      have hfirst : List.Pairwise (fun x y : Nat => x ≠ y)
          ([0, n + 1] ++ inside) := by
        rw [List.pairwise_append]
        refine ⟨hrootNodup, hinsideNodup, ?_⟩
        intro x hx y hy hxy
        have hybounds := hinsideBounds y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> omega
      have hwhole : List.Pairwise (fun x y : Nat => x ≠ y)
          (([0, n + 1] ++ inside) ++ after) := by
        rw [List.pairwise_append]
        refine ⟨hfirst, hafterNodup, ?_⟩
        intro x hx y hy hxy
        have hybound := hafterLower y hy
        rcases List.mem_append.mp hx with hxRoot | hxInside
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxRoot
          rcases hxRoot with rfl | rfl <;> omega
        · have hxBounds := hinsideBounds x hxInside
          omega
      simp only [cancellationPairs]
      rw [show pairEndpoints ((0, innerShape.inputWord.length + 1) ::
          (shiftCancellationPairs 1 innerShape.cancellationPairs ++
            shiftCancellationPairs (innerShape.inputWord.length + 2)
              suffixShape.cancellationPairs)) =
          [0, innerShape.inputWord.length + 1] ++
            (pairEndpoints (shiftCancellationPairs 1
              innerShape.cancellationPairs) ++
              pairEndpoints (shiftCancellationPairs
                (innerShape.inputWord.length + 2)
                suffixShape.cancellationPairs)) by
        simp [pairEndpoints, List.flatMap_append]]
      rw [pairEndpoints_shiftCancellationPairs, pairEndpoints_shiftCancellationPairs]
      rw [← List.append_assoc]
      change List.Pairwise (fun x y : Nat => x ≠ y)
        (([0, n + 1] ++ inside) ++ after)
      exact hwhole

theorem survivorAndCancellationEndpointCount {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    (pairEndpoints h.cancellationPairs).length +
        h.survivorOccurrences.length = h.inputWord.length := by
  rw [cancellationEndpoints_length, h.survivorOccurrences_length]
  have hlength := h.length_eq_cancellationCount
  simp only [inputWord] at hlength ⊢
  omega

/-- A retained source letter is never an endpoint of a cancellation pair.
This keeps the eventual exterior boundary disjoint from the glued edge sides. -/
theorem survivorOccurrences_disjointFromCancellationPairs
    {raw reduced : Word α} (h : FreeReductionShape raw reduced) :
    ∀ o ∈ h.survivorOccurrences, ∀ p ∈ h.cancellationPairs,
      o.1 ≠ p.1 ∧ o.1 ≠ p.2 := by
  induction h with
  | empty => simp [survivorOccurrences, cancellationPairs]
  | letter a => simp [survivorOccurrences, cancellationPairs]
  | @append u u' v v' left right ihLeft ihRight =>
      intro o ho p hp
      simp only [survivorOccurrences, cancellationPairs,
        List.mem_append] at ho hp
      rcases ho with hoLeft | hoRight
      · rcases hp with hpLeft | hpRight
        · exact ihLeft o hoLeft p hpLeft
        · rcases List.mem_map.mp hpRight with ⟨q, hq, hqp⟩
          subst p
          have hbound := left.survivorOccurrences_inBounds o hoLeft
          have hleft : o.1 < u.length := by simpa [inputWord] using hbound
          have hoffset : left.inputWord.length = u.length := by simp [inputWord]
          constructor <;> omega
      · rcases List.mem_map.mp hoRight with ⟨q, hq, hqo⟩
        subst o
        rcases hp with hpLeft | hpRight
        · have hbound := left.cancellationPairs_inBounds p hpLeft
          have hleft : p.2 < u.length := by simpa [inputWord] using hbound.2
          have hoffset : left.inputWord.length = u.length := by simp [inputWord]
          constructor <;> omega
        · rcases List.mem_map.mp hpRight with ⟨r, hr, hrp⟩
          subst p
          have hdisjoint := ihRight q hq r hr
          have hoffset : left.inputWord.length = u.length := by simp [inputWord]
          constructor <;> omega
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro o ho p hp
      simp only [survivorOccurrences, shiftLetterOccurrences] at ho
      rcases List.mem_map.mp ho with ⟨q, hq, hqo⟩
      subst o
      simp only [cancellationPairs, List.mem_cons, List.mem_append] at hp
      rcases hp with hpRoot | hpRest
      · subst p
        simp only [inputWord]
        constructor <;> omega
      · rcases hpRest with hpInner | hpSuffix
        · rcases List.mem_map.mp hpInner with ⟨r, hr, hrp⟩
          subst p
          have hbound := innerShape.cancellationPairs_inBounds r hr
          have hinner : r.2 < inner.length := by simpa [inputWord] using hbound.2
          simp only [inputWord]
          constructor <;> omega
        · rcases List.mem_map.mp hpSuffix with ⟨r, hr, hrp⟩
          subst p
          have hdisjoint := ihSuffix q hq r hr
          simp only [inputWord]
          constructor <;> omega

/-- Each positional cancellation pair records inverse letters in the raw
source word. This is the occurrence-level fact needed before a pair can be
used as an edge identification in a polygonal diagram. -/
theorem cancellationPairs_are_inverseLetterOccurrences {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ p ∈ h.cancellationPairs,
      ∃ a, raw[p.1]? = some a ∧ raw[p.2]? = some (inverseLetter a) := by
  induction h with
  | empty => simp [cancellationPairs]
  | letter a => simp [cancellationPairs]
  | @append u u' v v' left right ihLeft ihRight =>
      intro p hp
      simp only [cancellationPairs, List.mem_append] at hp
      rcases hp with hpLeft | hpRight
      · obtain ⟨a, ha₁, ha₂⟩ := ihLeft p hpLeft
        change u[p.1]? = some a at ha₁
        change u[p.2]? = some (inverseLetter a) at ha₂
        have hbounds := left.cancellationPairs_inBounds p hpLeft
        have h₂ : p.2 < u.length := by simpa [inputWord] using hbounds.2
        have h₁ : p.1 < u.length := by omega
        refine ⟨a, ?_, ?_⟩
        · simpa only [List.getElem?_append_left h₁] using ha₁
        · simpa only [List.getElem?_append_left h₂] using ha₂
      · rcases List.mem_map.mp hpRight with ⟨q, hq, hqp⟩
        subst p
        obtain ⟨a, ha₁, ha₂⟩ := ihRight q hq
        change v[q.1]? = some a at ha₁
        change v[q.2]? = some (inverseLetter a) at ha₂
        have hoffset : left.inputWord.length = u.length := by simp [inputWord]
        refine ⟨a, ?_, ?_⟩
        · rw [hoffset, getElem?_append_shift]
          exact ha₁
        · rw [hoffset, getElem?_append_shift]
          exact ha₂
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro p hp
      simp only [cancellationPairs, List.mem_cons, List.mem_append] at hp
      rcases hp with hpRoot | hpRest
      · subst p
        simp only [inputWord]
        refine ⟨a, ?_, ?_⟩
        · simp [List.append_assoc]
        · have h := getElem?_append_shift ([a] ++ inner)
            ([inverseLetter a] ++ suffix) 0
          calc
            ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[inner.length + 1]? =
                (([a] ++ inner) ++ ([inverseLetter a] ++ suffix))[
                  ([a] ++ inner).length + 0]? := by
                    simp only [List.append_assoc, List.length_append,
                      List.length_cons, List.length_nil, Nat.add_comm,
                      Nat.add_left_comm]
            _ = ([inverseLetter a] ++ suffix)[0]? := h
            _ = some (inverseLetter a) := by simp
      · rcases hpRest with hpInner | hpSuffix
        · rcases List.mem_map.mp hpInner with ⟨q, hq, hqp⟩
          have hbounds := innerShape.cancellationPairs_inBounds q hq
          have h₂ : q.2 < inner.length := by simpa [inputWord] using hbounds.2
          have h₁ : q.1 < inner.length := by omega
          subst p
          obtain ⟨b, hb₁, hb₂⟩ := ihInner q hq
          change inner[q.1]? = some b at hb₁
          change inner[q.2]? = some (inverseLetter b) at hb₂
          refine ⟨b, ?_, ?_⟩
          · calc
              ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[1 + q.1]? =
                  inner[q.1]? := by
                simpa only [List.append_assoc, List.length_cons,
                  List.length_nil, Nat.zero_add] using
                  (getElem?_append_middle [a] inner
                    ([inverseLetter a] ++ suffix) h₁)
              _ = some b := hb₁
          · calc
              ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[1 + q.2]? =
                  inner[q.2]? := by
                simpa only [List.append_assoc, List.length_cons,
                  List.length_nil, Nat.zero_add] using
                  (getElem?_append_middle [a] inner
                    ([inverseLetter a] ++ suffix) h₂)
              _ = some (inverseLetter b) := hb₂
        · rcases List.mem_map.mp hpSuffix with ⟨q, hq, hqp⟩
          subst p
          obtain ⟨b, hb₁, hb₂⟩ := ihSuffix q hq
          change suffix[q.1]? = some b at hb₁
          change suffix[q.2]? = some (inverseLetter b) at hb₂
          simp only [inputWord]
          have hprefix : (([a] ++ inner) ++ [inverseLetter a]).length =
              inner.length + 2 := by
            simp [List.length_append]
          refine ⟨b, ?_, ?_⟩
          · calc
              ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[
                  inner.length + 2 + q.1]? = suffix[q.1]? := by
                rw [← hprefix]
                exact getElem?_append_shift
                  (([a] ++ inner) ++ [inverseLetter a]) suffix q.1
              _ = some b := hb₁
          · calc
              ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)[
                  inner.length + 2 + q.2]? = suffix[q.2]? := by
                rw [← hprefix]
                exact getElem?_append_shift
                  (([a] ++ inner) ++ [inverseLetter a]) suffix q.2
              _ = some (inverseLetter b) := hb₂

/-- The positional pairing generated by a reduction shape is noncrossing:
any two cancellation intervals are disjoint or nested. -/
theorem cancellationPairs_noncrossing {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    CancellationPairsNoncrossing h.cancellationPairs := by
  induction h with
  | empty => simp [CancellationPairsNoncrossing, cancellationPairs]
  | letter _ => simp [CancellationPairsNoncrossing, cancellationPairs]
  | @append u u' v v' left right ihLeft ihRight =>
      intro p hp q hq
      simp only [cancellationPairs, List.mem_append] at hp hq
      rcases hp with hpLeft | hpRight
      · rcases hq with hqLeft | hqRight
        · exact ihLeft p hpLeft q hqLeft
        · rcases List.mem_map.mp hqRight with ⟨q₀, hq₀, rfl⟩
          have hpBounds := left.cancellationPairs_inBounds p hpLeft
          have hpEnd : p.2 < u.length := by
            simpa [inputWord] using hpBounds.2
          exact Or.inl (by omega)
      · rcases List.mem_map.mp hpRight with ⟨p₀, hp₀, rfl⟩
        rcases hq with hqLeft | hqRight
        · have hqBounds := left.cancellationPairs_inBounds q hqLeft
          have hqEnd : q.2 < u.length := by
            simpa [inputWord] using hqBounds.2
          exact Or.inr (Or.inl (by omega))
        · rcases List.mem_map.mp hqRight with ⟨q₀, hq₀, rfl⟩
          exact shiftCancellationPairs_nonCrossing ihRight u.length
            (u.length + p₀.1, u.length + p₀.2)
            (List.mem_map.mpr ⟨p₀, hp₀, rfl⟩)
            (u.length + q₀.1, u.length + q₀.2)
            (List.mem_map.mpr ⟨q₀, hq₀, rfl⟩)
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro p hp q hq
      simp only [cancellationPairs, List.mem_cons, List.mem_append] at hp hq
      rcases hp with hpRoot | hpRest
      · subst p
        rcases hq with hqRoot | hqRest
        · subst q
          exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp⟩))
        · rcases hqRest with hqInner | hqSuffix
          · rcases List.mem_map.mp hqInner with ⟨q₀, hq₀, rfl⟩
            have hqBounds := innerShape.cancellationPairs_inBounds q₀ hq₀
            exact Or.inr (Or.inr (Or.inl (by omega)))
          · rcases List.mem_map.mp hqSuffix with ⟨q₀, hq₀, rfl⟩
            exact Or.inl (by omega)
      · rcases hpRest with hpInner | hpSuffix
        · rcases List.mem_map.mp hpInner with ⟨p₀, hp₀, rfl⟩
          have hpBounds := innerShape.cancellationPairs_inBounds p₀ hp₀
          rcases hq with hqRoot | hqRest
          · subst q
            exact Or.inr (Or.inr (Or.inr (by omega)))
          · rcases hqRest with hqInner | hqSuffix
            · rcases List.mem_map.mp hqInner with ⟨q₀, hq₀, rfl⟩
              exact shiftCancellationPairs_nonCrossing ihInner 1
                (1 + p₀.1, 1 + p₀.2)
                (List.mem_map.mpr ⟨p₀, hp₀, rfl⟩)
                (1 + q₀.1, 1 + q₀.2)
                (List.mem_map.mpr ⟨q₀, hq₀, rfl⟩)
            · rcases List.mem_map.mp hqSuffix with ⟨q₀, hq₀, rfl⟩
              have hqBounds := suffixShape.cancellationPairs_inBounds q₀ hq₀
              exact Or.inl (by omega)
        · rcases List.mem_map.mp hpSuffix with ⟨p₀, hp₀, rfl⟩
          have hpBounds := suffixShape.cancellationPairs_inBounds p₀ hp₀
          rcases hq with hqRoot | hqRest
          · subst q
            exact Or.inr (Or.inl (by omega))
          · rcases hqRest with hqInner | hqSuffix
            · rcases List.mem_map.mp hqInner with ⟨q₀, hq₀, rfl⟩
              have hqBounds := innerShape.cancellationPairs_inBounds q₀ hq₀
              exact Or.inr (Or.inl (by omega))
            · rcases List.mem_map.mp hqSuffix with ⟨q₀, hq₀, rfl⟩
              exact shiftCancellationPairs_nonCrossing ihSuffix
                (inner.length + 2)
                (inner.length + 2 + p₀.1, inner.length + 2 + p₀.2)
                (List.mem_map.mpr ⟨p₀, hp₀, rfl⟩)
                (inner.length + 2 + q₀.1, inner.length + 2 + q₀.2)
                (List.mem_map.mpr ⟨q₀, hq₀, rfl⟩)

end FreeReductionShape

namespace FreeReductionShape

variable {α : Type*}

/-- Every position in the unreduced source word is used exactly once by the
cancellation endpoints or the retained output occurrences. The disjointness,
boundedness, and count statements together establish coverage by finite-set
cardinality. -/
theorem sourcePositions_partition {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ i, i < h.inputWord.length →
      i ∈ pairEndpoints h.cancellationPairs ∨
        i ∈ h.survivorOccurrences.map Prod.fst := by
  classical
  let endpoints := pairEndpoints h.cancellationPairs
  let survivors := h.survivorOccurrences.map Prod.fst
  let endpointSet := endpoints.toFinset
  let survivorSet := survivors.toFinset
  let n := h.inputWord.length
  have hEndpointCard : endpointSet.card = endpoints.length := by
    change endpoints.toFinset.card = endpoints.length
    exact List.toFinset_card_of_nodup h.cancellationEndpoints_nodup
  have hSurvivorCard : survivorSet.card = survivors.length := by
    change survivors.toFinset.card = survivors.length
    exact List.toFinset_card_of_nodup h.survivorOccurrencePositions_nodup
  have hDisjoint : Disjoint endpointSet survivorSet := by
    rw [Finset.disjoint_left]
    intro i hiEndpoint hiSurvivor
    have hiEndpoint' : i ∈ endpoints := by
      simpa [endpointSet] using hiEndpoint
    have hiSurvivor' : i ∈ survivors := by
      simpa [survivorSet] using hiSurvivor
    rcases List.mem_flatMap.mp hiEndpoint' with ⟨p, hp, hpi⟩
    rcases List.mem_map.mp hiSurvivor' with ⟨o, ho, hoi⟩
    have hAvoid := h.survivorOccurrences_disjointFromCancellationPairs o ho p hp
    simp only [List.mem_cons, List.not_mem_nil] at hpi
    rcases hpi with hpi | hpi
    · have hEq : o.1 = p.1 := by
        calc
          o.1 = i := hoi
          _ = p.1 := hpi
      exact hAvoid.1 hEq
    · rcases hpi with hpi | hfalse
      · have hEq : o.1 = p.2 := by
          calc
            o.1 = i := hoi
            _ = p.2 := hpi
        exact hAvoid.2 hEq
      · cases hfalse
  have hEndpointSubset : endpointSet ⊆ Finset.range n := by
    intro i hi
    have hi' : i ∈ endpoints := by simpa [endpointSet] using hi
    exact Finset.mem_range.mpr (h.cancellationEndpoints_inBounds i hi')
  have hSurvivorSubset : survivorSet ⊆ Finset.range n := by
    intro i hi
    have hi' : i ∈ survivors := by simpa [survivorSet] using hi
    rcases List.mem_map.mp hi' with ⟨o, ho, hoi⟩
    have hbound := h.survivorOccurrences_inBounds o ho
    exact Finset.mem_range.mpr (by omega)
  have hUnionCard : (endpointSet ∪ survivorSet).card = (Finset.range n).card := by
    calc
      (endpointSet ∪ survivorSet).card = endpointSet.card + survivorSet.card :=
        Finset.card_union_of_disjoint hDisjoint
      _ = endpoints.length + survivors.length := by rw [hEndpointCard, hSurvivorCard]
      _ = n := by
        simpa [endpoints, survivors, n] using h.survivorAndCancellationEndpointCount
      _ = (Finset.range n).card := by simp
  have hUnionSubset : endpointSet ∪ survivorSet ⊆ Finset.range n :=
    Finset.union_subset hEndpointSubset hSurvivorSubset
  have hUnionEq : endpointSet ∪ survivorSet = Finset.range n :=
    Finset.eq_of_subset_of_card_le hUnionSubset (le_of_eq hUnionCard.symm)
  intro i hi
  have hiUnion : i ∈ endpointSet ∪ survivorSet := by
    rw [hUnionEq]
    exact Finset.mem_range.mpr hi
  rcases Finset.mem_union.mp hiUnion with hiEndpoint | hiSurvivor
  · exact Or.inl (by simpa [endpointSet, endpoints] using hiEndpoint)
  · exact Or.inr (by simpa [survivorSet, survivors] using hiSurvivor)

/-- A cancellation interval contains no retained source occurrence. The
bracketed subword reduces completely before its outer inverse pair is removed.
-/
theorem cancellationPairs_contain_no_survivor {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ p ∈ h.cancellationPairs, ∀ o ∈ h.survivorOccurrences,
      p.1 < o.1 → o.1 < p.2 → False := by
  induction h with
  | empty => simp [cancellationPairs, survivorOccurrences]
  | letter a => simp [cancellationPairs, survivorOccurrences]
  | @append u u' v v' left right ihLeft ihRight =>
      intro p hp o ho hbefore hafter
      simp only [cancellationPairs, List.mem_append] at hp
      simp only [survivorOccurrences, List.mem_append] at ho
      rcases hp with hpLeft | hpRight
      · rcases ho with hoLeft | hoRight
        · exact ihLeft p hpLeft o hoLeft hbefore hafter
        · rcases List.mem_map.mp hoRight with ⟨q, hq, hqo⟩
          subst o
          have hbound := left.cancellationPairs_inBounds p hpLeft
          have hupper : p.2 < u.length := by simpa [inputWord] using hbound.2
          have hoffset : left.inputWord.length = u.length := by simp [inputWord]
          omega
      · rcases List.mem_map.mp hpRight with ⟨p₀, hp₀, hpp⟩
        subst p
        rcases ho with hoLeft | hoRight
        · have hbound := left.survivorOccurrences_inBounds o hoLeft
          have hleft : o.1 < u.length := by simpa [inputWord] using hbound
          have hoffset : left.inputWord.length = u.length := by simp [inputWord]
          omega
        · rcases List.mem_map.mp hoRight with ⟨q, hq, hqo⟩
          subst o
          have hlen : left.inputWord.length = u.length := by simp [inputWord]
          have hbefore' : p₀.1 < q.1 := by omega
          have hafter' : q.1 < p₀.2 := by omega
          exact ihRight p₀ hp₀ q hq hbefore' hafter'
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      intro p hp o ho hbefore hafter
      simp only [cancellationPairs, List.mem_cons, List.mem_append] at hp
      simp only [survivorOccurrences, shiftLetterOccurrences] at ho
      rcases List.mem_map.mp ho with ⟨q, hq, hqo⟩
      subst o
      rcases hp with hroot | hpRest
      · subst p
        simp only [inputWord] at hafter
        omega
      · rcases hpRest with hpInner | hpSuffix
        · rcases List.mem_map.mp hpInner with ⟨p₀, hp₀, rfl⟩
          have hbound := innerShape.cancellationPairs_inBounds p₀ hp₀
          have hinner : innerShape.inputWord.length = inner.length := by
            simp [inputWord]
          simp only [inputWord] at hafter
          omega
        · rcases List.mem_map.mp hpSuffix with ⟨p₀, hp₀, rfl⟩
          have hbefore' : p₀.1 < q.1 := by omega
          have hafter' : q.1 < p₀.2 := by omega
          exact ihSuffix p₀ hp₀ q hq hbefore' hafter'

/-- Pairs introduced by a later reduction lift to intervals compatible with
every earlier cancellation interval. A lifted pair can enclose an earlier
interval, but its surviving endpoints cannot cross that interval. -/
theorem liftCancellationPair_compatible_with_earlier
    {raw middle : Word α} (h : FreeReductionShape raw middle)
    {p : Nat × Nat} (hp : p ∈ h.cancellationPairs)
    (q : Fin middle.length × Fin middle.length) (hq : q.1.val < q.2.val) :
    CancellationIntervalsCompatible p (h.liftCancellationPair q) := by
  let x := h.sourcePositionOfOutput q.1
  let y := h.sourcePositionOfOutput q.2
  have hxy : x < y := by
    dsimp [x, y]
    exact h.sourcePositionOfOutput_strict (Fin.mk_lt_mk.mpr hq)
  have hxmem : x ∈ h.survivorPositions := by
    dsimp [x]
    exact h.sourcePositionOfOutput_mem q.1
  have hymem : y ∈ h.survivorPositions := by
    dsimp [y]
    exact h.sourcePositionOfOutput_mem q.2
  have hxlist : x ∈ h.survivorOccurrences.map Prod.fst := by
    simpa [survivorPositions] using hxmem
  have hylist : y ∈ h.survivorOccurrences.map Prod.fst := by
    simpa [survivorPositions] using hymem
  obtain ⟨ox, hox, hoxx⟩ := List.mem_map.mp hxlist
  obtain ⟨oy, hoy, hoyy⟩ := List.mem_map.mp hylist
  have hAvoidX := h.survivorOccurrences_disjointFromCancellationPairs ox hox p hp
  have hAvoidY := h.survivorOccurrences_disjointFromCancellationPairs oy hoy p hp
  have hxNe1 : x ≠ p.1 := by simpa [hoxx] using hAvoidX.1
  have hxNe2 : x ≠ p.2 := by simpa [hoxx] using hAvoidX.2
  have hyNe1 : y ≠ p.1 := by simpa [hoyy] using hAvoidY.1
  have hyNe2 : y ≠ p.2 := by simpa [hoyy] using hAvoidY.2
  have hxNoInterior : ¬ (p.1 < x ∧ x < p.2) := by
    intro hx
    exact h.cancellationPairs_contain_no_survivor p hp ox hox
      (by simpa [hoxx] using hx.1) (by simpa [hoxx] using hx.2)
  have hyNoInterior : ¬ (p.1 < y ∧ y < p.2) := by
    intro hy
    exact h.cancellationPairs_contain_no_survivor p hp oy hoy
      (by simpa [hoyy] using hy.1) (by simpa [hoyy] using hy.2)
  have hpForward := h.cancellationPairs_inBounds p hp
  have hxOutside : x < p.1 ∨ p.2 < x := by
    by_cases hbefore : x < p.1
    · exact Or.inl hbefore
    · by_cases hafter : p.2 < x
      · exact Or.inr hafter
      · have hleft : p.1 < x := by omega
        have hright : x < p.2 := by omega
        exact False.elim (hxNoInterior ⟨hleft, hright⟩)
  have hyOutside : y < p.1 ∨ p.2 < y := by
    by_cases hbefore : y < p.1
    · exact Or.inl hbefore
    · by_cases hafter : p.2 < y
      · exact Or.inr hafter
      · have hleft : p.1 < y := by omega
        have hright : y < p.2 := by omega
        exact False.elim (hyNoInterior ⟨hleft, hright⟩)
  rcases hxOutside with hxBefore | hxAfter
  · rcases hyOutside with hyBefore | hyAfter
    · exact Or.inr (Or.inl (by dsimp [liftCancellationPair, x, y]; omega))
    · exact Or.inr (Or.inr (Or.inr
        (by dsimp [liftCancellationPair, x, y]; omega)))
  · rcases hyOutside with hyBefore | hyAfter
    · exfalso
      dsimp [x, y] at hxy
      omega
    · exact Or.inl (by dsimp [liftCancellationPair, x, y]; omega)

/-- Endpoint lists commute with lifting cancellation pairs. -/
theorem pairEndpoints_liftCancellationPairs {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    pairEndpoints (liftCancellationPairs earlier later) =
      (pairEndpoints later.cancellationPairs).map earlier.sourcePositionOfOutputNat := by
  rw [liftCancellationPairs_eq_map]
  change pairEndpoints (later.cancellationPairs.map fun p =>
    (earlier.sourcePositionOfOutputNat p.1,
      earlier.sourcePositionOfOutputNat p.2)) = _
  rw [pairEndpoints_map]

theorem liftCancellationPairs_nodup {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (pairEndpoints (liftCancellationPairs earlier later)).Nodup := by
  rw [pairEndpoints_liftCancellationPairs]
  exact later.cancellationEndpoints_nodup.map
    earlier.sourcePositionOfOutputNat_injective

theorem liftCancellationPairs_noncrossing {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    CancellationPairsNoncrossing (liftCancellationPairs earlier later) := by
  intro p hp q hq
  rw [liftCancellationPairs_eq_map] at hp hq
  rcases List.mem_map.mp hp with ⟨p₀, hp₀, rfl⟩
  rcases List.mem_map.mp hq with ⟨q₀, hq₀, rfl⟩
  exact earlier.liftCancellationPairNat_preserves_compatibility
    (later.cancellationPairs_noncrossing p₀ hp₀ q₀ hq₀)

theorem liftCancellationPairs_inBounds {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ p ∈ liftCancellationPairs earlier later,
      p.1 < p.2 ∧ p.2 < earlier.inputWord.length := by
  intro p hp
  rw [liftCancellationPairs_eq_map] at hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  have hqBound := later.cancellationPairs_inBounds q hq
  have hqFirst : q.1 < middle.length := by
    simpa [inputWord] using Nat.lt_trans hqBound.1 hqBound.2
  have hqSecond : q.2 < middle.length := by
    simpa [inputWord] using hqBound.2
  constructor
  · exact earlier.sourcePositionOfOutputNat_strict hqBound.1
  · change earlier.sourcePositionOfOutputNat q.2 < earlier.inputWord.length
    rw [earlier.sourcePositionOfOutputNat_eq hqSecond]
    exact earlier.sourcePositionOfOutput_inBounds ⟨q.2, hqSecond⟩

theorem survivorPositions_avoidCancellationPairEndpoints
    {raw reduced : Word α} (h : FreeReductionShape raw reduced)
    {i : Nat} (hi : i ∈ h.survivorPositions)
    {p : Nat × Nat} (hp : p ∈ h.cancellationPairs) :
    i ≠ p.1 ∧ i ≠ p.2 := by
  have hi' : i ∈ h.survivorOccurrences.map Prod.fst := by
    simpa only [survivorPositions] using hi
  rcases List.mem_map.mp hi' with ⟨o, ho, hio⟩
  have hAvoid := h.survivorOccurrences_disjointFromCancellationPairs o ho p hp
  constructor
  · intro heq
    apply hAvoid.1
    calc
      o.1 = i := hio
      _ = p.1 := heq
  · intro heq
    apply hAvoid.2
    calc
      o.1 = i := hio
      _ = p.2 := heq

theorem liftCancellationPairs_compatible_with_earlier
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced)
    {p : Nat × Nat} (hp : p ∈ earlier.cancellationPairs)
    {q : Nat × Nat} (hq : q ∈ liftCancellationPairs earlier later) :
    CancellationIntervalsCompatible p q := by
  rw [liftCancellationPairs_eq_map] at hq
  rcases List.mem_map.mp hq with ⟨q₀, hq₀, hqEq⟩
  have hqBound := later.cancellationPairs_inBounds q₀ hq₀
  have hqFirst : q₀.1 < middle.length := by
    simpa [inputWord] using Nat.lt_trans hqBound.1 hqBound.2
  have hqSecond : q₀.2 < middle.length := by
    simpa [inputWord] using hqBound.2
  let qFin : Fin middle.length × Fin middle.length :=
    (⟨q₀.1, hqFirst⟩, ⟨q₀.2, hqSecond⟩)
  have hcompat := earlier.liftCancellationPair_compatible_with_earlier
    hp qFin hqBound.1
  have hqEq'' : earlier.liftCancellationPair qFin = q := by
    simpa [liftCancellationPair, liftCancellationPairNat, qFin, hqFirst, hqSecond,
      sourcePositionOfOutputNat_eq] using hqEq
  have hqEq' : q = earlier.liftCancellationPair qFin := hqEq''.symm
  rw [hqEq']
  exact hcompat

theorem cancellationEndpoints_disjoint_liftCancellationPairs
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ i ∈ pairEndpoints earlier.cancellationPairs,
      i ∈ pairEndpoints (liftCancellationPairs earlier later) → False := by
  intro i hiEarlier hiLater
  rw [pairEndpoints_liftCancellationPairs] at hiLater
  rcases List.mem_map.mp hiLater with ⟨j, hj, hji⟩
  have hjBound := later.cancellationEndpoints_inBounds j hj
  have hjLt : j < middle.length := by
    simpa [inputWord] using hjBound
  have hsourceMem : earlier.sourcePositionOfOutputNat j ∈ earlier.survivorPositions := by
    rw [earlier.sourcePositionOfOutputNat_eq hjLt]
    exact earlier.sourcePositionOfOutput_mem ⟨j, hjLt⟩
  rcases List.mem_flatMap.mp hiEarlier with ⟨p, hp, hpi⟩
  simp only [List.mem_cons, List.not_mem_nil] at hpi
  rcases hpi with hpi | hpi
  · have hAvoid := earlier.survivorPositions_avoidCancellationPairEndpoints
      hsourceMem hp
    exact hAvoid.1 (hji.trans hpi)
  · rcases hpi with hpi | hfalse
    · have hAvoid := earlier.survivorPositions_avoidCancellationPairEndpoints
        hsourceMem hp
      exact hAvoid.2 (hji.trans hpi)
    · cases hfalse

theorem composedCancellationEndpoints_nodup
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (pairEndpoints
      (earlier.cancellationPairs ++ liftCancellationPairs earlier later)).Nodup := by
  rw [pairEndpoints_append]
  change List.Pairwise (fun x y : Nat => x ≠ y)
    (pairEndpoints earlier.cancellationPairs ++
      pairEndpoints (liftCancellationPairs earlier later))
  rw [List.pairwise_append]
  refine ⟨earlier.cancellationEndpoints_nodup,
    liftCancellationPairs_nodup earlier later, ?_⟩
  intro x hx y hy heq
  subst y
  exact (cancellationEndpoints_disjoint_liftCancellationPairs
    earlier later x hx hy).elim

theorem composedCancellationPairs_noncrossing
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    CancellationPairsNoncrossing
      (earlier.cancellationPairs ++ liftCancellationPairs earlier later) := by
  intro p hp q hq
  rw [List.mem_append] at hp hq
  rcases hp with hpEarlier | hpLater <;>
    rcases hq with hqEarlier | hqLater
  · exact earlier.cancellationPairs_noncrossing p hpEarlier q hqEarlier
  · exact earlier.liftCancellationPairs_compatible_with_earlier
      later hpEarlier hqLater
  · exact (earlier.liftCancellationPairs_compatible_with_earlier
      later hqEarlier hpLater).symm
  · exact liftCancellationPairs_noncrossing earlier later p hpLater q hqLater

theorem liftSurvivorOccurrences_are_sourceLetters
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ o ∈ liftSurvivorOccurrences earlier later,
      raw[o.1]? = some o.2 := by
  intro o ho
  rw [liftSurvivorOccurrences_eq_map] at ho
  rcases List.mem_map.mp ho with ⟨q, hq, rfl⟩
  have hbound := later.survivorOccurrences_inBounds q hq
  have hqLt : q.1 < middle.length := by
    simpa [inputWord] using hbound
  have hraw := earlier.sourcePositionOfOutput_sourceLetter ⟨q.1, hqLt⟩
  have hmid := later.survivorOccurrences_are_sourceLetters q hq
  change raw[earlier.sourcePositionOfOutputNat q.1]? = some q.2
  have hraw' : raw[earlier.sourcePositionOfOutputNat q.1]? =
      some middle[q.1] := by
    rw [earlier.sourcePositionOfOutputNat_eq hqLt]
    simpa using hraw
  have hmid' : middle[q.1] = q.2 := by
    rw [List.getElem?_eq_getElem hqLt] at hmid
    exact Option.some.inj hmid
  rw [hmid'] at hraw'
  exact hraw'

theorem liftCancellationPairs_are_inverseLetterOccurrences
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ p ∈ liftCancellationPairs earlier later,
      ∃ a, raw[p.1]? = some a ∧ raw[p.2]? = some (inverseLetter a) := by
  intro p hp
  rw [liftCancellationPairs_eq_map] at hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  obtain ⟨a, hq₁, hq₂⟩ := later.cancellationPairs_are_inverseLetterOccurrences q hq
  have hqBounds := later.cancellationPairs_inBounds q hq
  have hq₁Lt : q.1 < middle.length := by
    simpa [inputWord] using Nat.lt_trans hqBounds.1 hqBounds.2
  have hq₂Lt : q.2 < middle.length := by
    simpa [inputWord] using hqBounds.2
  have hraw₁ := earlier.sourcePositionOfOutput_sourceLetter ⟨q.1, hq₁Lt⟩
  have hraw₂ := earlier.sourcePositionOfOutput_sourceLetter ⟨q.2, hq₂Lt⟩
  dsimp [liftCancellationPairNat]
  change middle[q.1]? = some a at hq₁
  change middle[q.2]? = some (inverseLetter a) at hq₂
  have hraw₁' : raw[earlier.sourcePositionOfOutputNat q.1]? =
      some middle[q.1] := by
    rw [earlier.sourcePositionOfOutputNat_eq hq₁Lt]
    simpa using hraw₁
  have hraw₂' : raw[earlier.sourcePositionOfOutputNat q.2]? =
      some middle[q.2] := by
    rw [earlier.sourcePositionOfOutputNat_eq hq₂Lt]
    simpa using hraw₂
  have hq₁' : middle[q.1] = a := by
    rw [List.getElem?_eq_getElem hq₁Lt] at hq₁
    exact Option.some.inj hq₁
  have hq₂' : middle[q.2] = inverseLetter a := by
    rw [List.getElem?_eq_getElem hq₂Lt] at hq₂
    exact Option.some.inj hq₂
  rw [hq₁'] at hraw₁'
  rw [hq₂'] at hraw₂'
  exact ⟨a, hraw₁', hraw₂'⟩

def composedCancellationPairs {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) : List (Nat × Nat) :=
  earlier.cancellationPairs ++ liftCancellationPairs earlier later

def composedSurvivorOccurrences {raw middle reduced : Word α}
    (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) : List (Nat × Letter α) :=
  liftSurvivorOccurrences earlier later

theorem composedCancellationPairs_are_inverseLetterOccurrences
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ p ∈ composedCancellationPairs earlier later,
      ∃ a, raw[p.1]? = some a ∧ raw[p.2]? = some (inverseLetter a) := by
  intro p hp
  rw [composedCancellationPairs, List.mem_append] at hp
  rcases hp with hp | hp
  · exact earlier.cancellationPairs_are_inverseLetterOccurrences p hp
  · exact liftCancellationPairs_are_inverseLetterOccurrences earlier later p hp

theorem composedCancellationPairs_inBounds
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ p ∈ composedCancellationPairs earlier later,
      p.1 < p.2 ∧ p.2 < earlier.inputWord.length := by
  intro p hp
  rw [composedCancellationPairs, List.mem_append] at hp
  rcases hp with hp | hp
  · exact earlier.cancellationPairs_inBounds p hp
  · exact liftCancellationPairs_inBounds earlier later p hp

theorem composedSurvivorOccurrences_sourceLetters
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ o ∈ composedSurvivorOccurrences earlier later,
      raw[o.1]? = some o.2 :=
  liftSurvivorOccurrences_are_sourceLetters earlier later

theorem composedSurvivorOccurrences_labels
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (composedSurvivorOccurrences earlier later).map Prod.snd = reduced :=
  liftSurvivorOccurrences_labels earlier later

theorem composedSurvivorOccurrences_length
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (composedSurvivorOccurrences earlier later).length = reduced.length :=
  liftSurvivorOccurrences_length earlier later

theorem composedSurvivorOccurrences_positions_strict
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    List.Pairwise (fun x y : Nat => x < y)
      ((composedSurvivorOccurrences earlier later).map Prod.fst) :=
  liftSurvivorOccurrences_positions_strict earlier later

theorem composedSurvivorOccurrences_inBounds
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ o ∈ composedSurvivorOccurrences earlier later,
      o.1 < earlier.inputWord.length :=
  liftSurvivorOccurrences_inBounds earlier later

theorem composedCancellationEndpoints_length
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (pairEndpoints (composedCancellationPairs earlier later)).length =
      2 * (earlier.cancellationCount + later.cancellationCount) := by
  simp only [composedCancellationPairs]
  rw [pairEndpoints_append, List.length_append,
    earlier.cancellationEndpoints_length,
    pairEndpoints_liftCancellationPairs, List.length_map,
    later.cancellationEndpoints_length]
  omega

theorem composedSurvivorAndCancellationEndpointCount
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    (pairEndpoints (composedCancellationPairs earlier later)).length +
        (composedSurvivorOccurrences earlier later).length =
      earlier.inputWord.length := by
  rw [composedCancellationEndpoints_length,
    composedSurvivorOccurrences_length]
  have hearlier := earlier.length_eq_cancellationCount
  have hlater := later.length_eq_cancellationCount
  simp only [inputWord] at hearlier hlater ⊢
  omega

theorem composedSurvivorPositions_memEarlier
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) {i : Nat}
    (hi : i ∈ (composedSurvivorOccurrences earlier later).map Prod.fst) :
    i ∈ earlier.survivorPositions := by
  change i ∈ (liftSurvivorOccurrences earlier later).map Prod.fst at hi
  rw [liftSurvivorOccurrences_positions] at hi
  rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
  rcases List.mem_map.mp hj with ⟨o, ho, rfl⟩
  have hoBound := later.survivorOccurrences_inBounds o ho
  have hoLt : o.1 < middle.length := by simpa [inputWord] using hoBound
  rw [earlier.sourcePositionOfOutputNat_eq hoLt]
  exact earlier.sourcePositionOfOutput_mem ⟨o.1, hoLt⟩

theorem composedSurvivorPositions_avoidEarlierEndpoints
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) {i : Nat}
    (hi : i ∈ (composedSurvivorOccurrences earlier later).map Prod.fst)
    {p : Nat × Nat} (hp : p ∈ earlier.cancellationPairs) :
    i ≠ p.1 ∧ i ≠ p.2 := by
  exact earlier.survivorPositions_avoidCancellationPairEndpoints
    (composedSurvivorPositions_memEarlier earlier later hi) hp

theorem composedSurvivorPositions_disjointFromLiftedEndpoints
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) {i j : Nat}
    (hi : i ∈ (composedSurvivorOccurrences earlier later).map Prod.fst)
    (hj : j ∈ pairEndpoints (liftCancellationPairs earlier later)) :
    i ≠ j := by
  intro hEq
  change i ∈ (liftSurvivorOccurrences earlier later).map Prod.fst at hi
  rw [liftSurvivorOccurrences_positions] at hi
  rw [pairEndpoints_liftCancellationPairs] at hj
  rcases List.mem_map.mp hi with ⟨s, hs, rfl⟩
  rcases List.mem_map.mp hj with ⟨e, he, rfl⟩
  rcases List.mem_flatMap.mp he with ⟨p, hp, hpe⟩
  simp only [List.mem_cons, List.not_mem_nil] at hpe
  have hAvoid := later.survivorPositions_avoidCancellationPairEndpoints hs hp
  have hse : s = e := earlier.sourcePositionOfOutputNat_injective hEq
  rcases hpe with hpe | hpe
  · exact hAvoid.1 (hse.trans hpe)
  · rcases hpe with hpe | hfalse
    · exact hAvoid.2 (hse.trans hpe)
    · cases hfalse

theorem composedCancellationEndpoints_inBounds
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ i ∈ pairEndpoints (composedCancellationPairs earlier later),
      i < earlier.inputWord.length := by
  intro i hi
  rcases List.mem_flatMap.mp hi with ⟨p, hp, hpi⟩
  have hbound := composedCancellationPairs_inBounds earlier later p hp
  simp only [List.mem_cons, List.not_mem_nil] at hpi
  rcases hpi with hpi | hpi
  · rw [hpi]
    exact Nat.lt_trans hbound.1 hbound.2
  · rcases hpi with hpi | hnil
    · rw [hpi]
      exact hbound.2
    · cases hnil

theorem composedCancellationEndpoints_disjointSurvivorPositions
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ i ∈ pairEndpoints (composedCancellationPairs earlier later),
      ∀ j ∈ (composedSurvivorOccurrences earlier later).map Prod.fst,
        i ≠ j := by
  intro i hi j hj heq
  rcases List.mem_flatMap.mp hi with ⟨p, hp, hpi⟩
  simp only [List.mem_cons, List.not_mem_nil] at hpi
  rw [composedCancellationPairs, List.mem_append] at hp
  rcases hp with hpEarlier | hpLater
  · have hAvoid := composedSurvivorPositions_avoidEarlierEndpoints
      earlier later hj hpEarlier
    rcases hpi with hpi | hpi
    · apply hAvoid.1
      calc
        j = i := heq.symm
        _ = p.1 := hpi
    · rcases hpi with hpi | hfalse
      · apply hAvoid.2
        calc
          j = i := heq.symm
          _ = p.2 := hpi
      · cases hfalse
  · have hiLater : i ∈ pairEndpoints (liftCancellationPairs earlier later) := by
      apply List.mem_flatMap.mpr
      exact ⟨p, hpLater, by simpa using hpi⟩
    exact (composedSurvivorPositions_disjointFromLiftedEndpoints
      earlier later hj hiLater) heq.symm

theorem composedCancellationEndpoints_noncrossing
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    CancellationPairsNoncrossing (composedCancellationPairs earlier later) := by
  exact composedCancellationPairs_noncrossing earlier later

theorem composedSourcePositions_partition
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ i, i < earlier.inputWord.length →
      i ∈ pairEndpoints (composedCancellationPairs earlier later) ∨
        i ∈ (composedSurvivorOccurrences earlier later).map Prod.fst := by
  classical
  let endpoints := pairEndpoints (composedCancellationPairs earlier later)
  let survivors := (composedSurvivorOccurrences earlier later).map Prod.fst
  let endpointSet := endpoints.toFinset
  let survivorSet := survivors.toFinset
  let n := earlier.inputWord.length
  have hEndpointNodup : endpoints.Nodup := by
    exact composedCancellationEndpoints_nodup earlier later
  have hSurvivorNodup : survivors.Nodup := by
    have hstrict := composedSurvivorOccurrences_positions_strict earlier later
    change List.Pairwise (fun x y : Nat => x ≠ y) survivors
    exact hstrict.imp (fun hlt => Nat.ne_of_lt hlt)
  have hEndpointCard : endpointSet.card = endpoints.length := by
    change endpoints.toFinset.card = endpoints.length
    exact List.toFinset_card_of_nodup hEndpointNodup
  have hSurvivorCard : survivorSet.card = survivors.length := by
    change survivors.toFinset.card = survivors.length
    exact List.toFinset_card_of_nodup hSurvivorNodup
  have hDisjoint : Disjoint endpointSet survivorSet := by
    rw [Finset.disjoint_left]
    intro i hiEndpoint hiSurvivor
    have hiEndpoint' : i ∈ endpoints := by simpa [endpointSet] using hiEndpoint
    have hiSurvivor' : i ∈ survivors := by simpa [survivorSet] using hiSurvivor
    rcases List.mem_flatMap.mp hiEndpoint' with ⟨p, hp, hpi⟩
    simp only [List.mem_cons, List.not_mem_nil] at hpi
    rw [composedCancellationPairs, List.mem_append] at hp
    rcases hp with hpEarlier | hpLater
    · have hAvoid := composedSurvivorPositions_avoidEarlierEndpoints
        earlier later hiSurvivor' hpEarlier
      rcases hpi with hpi | hpi
      · exact hAvoid.1 hpi
      · rcases hpi with hpi | hfalse
        · exact hAvoid.2 hpi
        · cases hfalse
    · have hiLaterEndpoint : i ∈ pairEndpoints (liftCancellationPairs earlier later) := by
        apply List.mem_flatMap.mpr
        exact ⟨p, hpLater, by simpa using hpi⟩
      exact (composedSurvivorPositions_disjointFromLiftedEndpoints
        earlier later hiSurvivor' hiLaterEndpoint) rfl
  have hEndpointSubset : endpointSet ⊆ Finset.range n := by
    intro i hi
    have hi' : i ∈ endpoints := by simpa [endpointSet] using hi
    exact Finset.mem_range.mpr (composedCancellationEndpoints_inBounds
      earlier later i hi')
  have hSurvivorSubset : survivorSet ⊆ Finset.range n := by
    intro i hi
    have hi' : i ∈ survivors := by simpa [survivorSet] using hi
    rcases List.mem_map.mp hi' with ⟨o, ho, rfl⟩
    exact Finset.mem_range.mpr (composedSurvivorOccurrences_inBounds
      earlier later o ho)
  have hUnionCard : (endpointSet ∪ survivorSet).card = (Finset.range n).card := by
    calc
      (endpointSet ∪ survivorSet).card = endpointSet.card + survivorSet.card :=
        Finset.card_union_of_disjoint hDisjoint
      _ = endpoints.length + survivors.length := by rw [hEndpointCard, hSurvivorCard]
      _ = n := by
        simpa [endpoints, survivors, n] using
          composedSurvivorAndCancellationEndpointCount earlier later
      _ = (Finset.range n).card := by simp
  have hUnionSubset : endpointSet ∪ survivorSet ⊆ Finset.range n :=
    Finset.union_subset hEndpointSubset hSurvivorSubset
  have hUnionEq : endpointSet ∪ survivorSet = Finset.range n :=
    Finset.eq_of_subset_of_card_le hUnionSubset (le_of_eq hUnionCard.symm)
  intro i hi
  have hiUnion : i ∈ endpointSet ∪ survivorSet := by
    rw [hUnionEq]
    exact Finset.mem_range.mpr hi
  rcases Finset.mem_union.mp hiUnion with hiEndpoint | hiSurvivor
  · exact Or.inl (by simpa [endpointSet, endpoints] using hiEndpoint)
  · exact Or.inr (by simpa [survivorSet, survivors] using hiSurvivor)

theorem composedSurvivorOccurrences_hasEarlierOccurrence
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) {o : Nat × Letter α}
    (ho : o ∈ composedSurvivorOccurrences earlier later) :
    ∃ e ∈ earlier.survivorOccurrences, e.1 = o.1 := by
  have hpos : o.1 ∈
      (composedSurvivorOccurrences earlier later).map Prod.fst :=
    List.mem_map.mpr ⟨o, ho, rfl⟩
  have hEarlier := composedSurvivorPositions_memEarlier earlier later hpos
  change o.1 ∈ earlier.survivorOccurrences.map Prod.fst at hEarlier
  rcases List.mem_map.mp hEarlier with ⟨e, he, heo⟩
  exact ⟨e, he, heo⟩

theorem composedCancellationPairs_contain_no_survivor
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) :
    ∀ p ∈ composedCancellationPairs earlier later,
      ∀ o ∈ composedSurvivorOccurrences earlier later,
        p.1 < o.1 → o.1 < p.2 → False := by
  intro p hp o ho hbefore hafter
  rw [composedCancellationPairs, List.mem_append] at hp
  rcases hp with hpEarlier | hpLater
  · obtain ⟨e, he, hepos⟩ :=
      composedSurvivorOccurrences_hasEarlierOccurrence earlier later ho
    have hno := earlier.cancellationPairs_contain_no_survivor p hpEarlier e he
    apply hno
    · simpa [hepos] using hbefore
    · simpa [hepos] using hafter
  · rw [liftCancellationPairs_eq_map] at hpLater
    rcases List.mem_map.mp hpLater with ⟨q, hq, rfl⟩
    rw [composedSurvivorOccurrences, liftSurvivorOccurrences_eq_map] at ho
    rcases List.mem_map.mp ho with ⟨s, hs, rfl⟩
    have hqBefore : q.1 < s.1 := by
      by_contra hnot
      have hle : s.1 ≤ q.1 := Nat.le_of_not_gt hnot
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      ·
        have hbefore' : earlier.sourcePositionOfOutputNat q.1 <
            earlier.sourcePositionOfOutputNat s.1 := by
          simpa [liftCancellationPairNat] using hbefore
        rw [heq] at hbefore'
        exact Nat.lt_irrefl _ hbefore'
      · have hrev := earlier.sourcePositionOfOutputNat_strict hlt
        have hbefore' : earlier.sourcePositionOfOutputNat q.1 <
            earlier.sourcePositionOfOutputNat s.1 := by
          simpa [liftCancellationPairNat] using hbefore
        omega
    have hAfter : s.1 < q.2 := by
      by_contra hnot
      have hle : q.2 ≤ s.1 := Nat.le_of_not_gt hnot
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      ·
        have hafter' : earlier.sourcePositionOfOutputNat s.1 <
            earlier.sourcePositionOfOutputNat q.2 := by
          simpa [liftCancellationPairNat] using hafter
        rw [heq] at hafter'
        exact Nat.lt_irrefl _ hafter'
      · have hrev := earlier.sourcePositionOfOutputNat_strict hlt
        have hafter' : earlier.sourcePositionOfOutputNat s.1 <
            earlier.sourcePositionOfOutputNat q.2 := by
          simpa [liftCancellationPairNat] using hafter
        omega
    exact later.cancellationPairs_contain_no_survivor q hq s hs
      hqBefore hAfter

/-- Compose two free-reduction traces while retaining the original source
positions of every cancellation and final survivor. -/
def composeIndexedBoundaryTrace
    {raw middle reduced : Word α} (earlier : FreeReductionShape raw middle)
    (later : FreeReductionShape middle reduced) : IndexedBoundaryTrace raw reduced where
  cancellationPairs := composedCancellationPairs earlier later
  survivorOccurrences := composedSurvivorOccurrences earlier later
  pairs_noncrossing := composedCancellationPairs_noncrossing earlier later
  pairs_are_inverseLetters := composedCancellationPairs_are_inverseLetterOccurrences
    earlier later
  pairs_inBounds := composedCancellationPairs_inBounds earlier later
  endpoints_nodup := by
    exact composedCancellationEndpoints_nodup earlier later
  endpoints_inBounds := composedCancellationEndpoints_inBounds earlier later
  survivors_labels := composedSurvivorOccurrences_labels earlier later
  survivors_length := composedSurvivorOccurrences_length earlier later
  survivorPositions_nodup := by
    have hstrict := composedSurvivorOccurrences_positions_strict earlier later
    exact hstrict.imp (fun hlt => Nat.ne_of_lt hlt)
  survivorPositions_strict := composedSurvivorOccurrences_positions_strict earlier later
  survivors_are_sourceLetters := composedSurvivorOccurrences_sourceLetters earlier later
  survivors_inBounds := composedSurvivorOccurrences_inBounds earlier later
  endpoints_disjoint_survivors :=
    composedCancellationEndpoints_disjointSurvivorPositions earlier later
  no_survivor_inside_pair := composedCancellationPairs_contain_no_survivor
    earlier later
  endpoint_survivor_count := by
    simpa [inputWord] using composedSurvivorAndCancellationEndpointCount earlier later
  sourcePositions_partition := composedSourcePositions_partition earlier later

end FreeReductionShape

end GreendlingerDehn
