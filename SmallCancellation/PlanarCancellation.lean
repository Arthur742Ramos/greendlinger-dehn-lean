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

def CancellationPairsNoncrossing (pairs : List (Nat × Nat)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs, CancellationIntervalsCompatible p q

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

theorem sourcePositionOfOutput_strict {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) {i j : Fin reduced.length}
    (hij : i < j) : h.sourcePositionOfOutput i < h.sourcePositionOfOutput j := by
  have hij' : h.survivorOutputIndex i < h.survivorOutputIndex j :=
    Fin.mk_lt_mk.mpr hij
  have hstrict := h.survivorOccurrencePositions_strict.rel_get_of_lt hij'
  exact hstrict

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

end FreeReductionShape

end GreendlingerDehn
