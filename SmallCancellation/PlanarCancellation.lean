import SmallCancellation.Cancellation
import Mathlib.Tactic.Linarith

namespace GreendlingerDehn

/-- Shift the positions in a cancellation-pair list when it is embedded in a
larger concatenated word. -/
def shiftCancellationPairs (offset : Nat) (pairs : List (Nat × Nat)) :
    List (Nat × Nat) :=
  pairs.map fun p => (offset + p.1, offset + p.2)

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

end GreendlingerDehn
