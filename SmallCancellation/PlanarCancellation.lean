import SmallCancellation.Cancellation
import Mathlib.Tactic.Linarith

namespace GreendlingerDehn

/-- Shift the positions in a cancellation-pair list when it is embedded in a
larger concatenated word. -/
def shiftCancellationPairs (offset : Nat) (pairs : List (Nat × Nat)) :
    List (Nat × Nat) :=
  pairs.map fun p => (offset + p.1, offset + p.2)

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

end GreendlingerDehn
