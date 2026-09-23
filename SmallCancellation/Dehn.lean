import SmallCancellation.Words

namespace GreendlingerDehn

open List

variable {α : Type*} [DecidableEq α]

/-- The normal subgroup relations associated with an explicit finite relator list. -/
def relationSet (R : List (FreeGroup α)) : Set (FreeGroup α) := {r | r ∈ R}

/-- The quotient group presented by `R`. -/
abbrev PresentedBy (R : List (FreeGroup α)) := PresentedGroup (relationSet R)

theorem redex_mem_candidates {R : List (FreeGroup α)} {w : Word α} {c : Redex α}
    (h : IsRedex R w c) : c ∈ redexCandidates R w := by
  rcases h with ⟨hw, hr, hcut, hlen⟩
  simp only [redexCandidates, List.mem_flatMap, List.mem_map]
  refine ⟨(c.before, c.long ++ c.after), ?_⟩
  constructor
  · exact mem_splits_iff.mpr (by simpa [List.append_assoc] using hw)
  · refine ⟨(c.long, c.after), ?_⟩
    constructor
    · exact mem_splits_iff.mpr rfl
    · refine ⟨c.relator, hr, ?_⟩
      refine ⟨(c.long, c.short), ?_⟩
      constructor
      · exact mem_splits_iff.mpr hcut
      · rfl

theorem findRedexAux_complete {R : List (FreeGroup α)} {w : Word α}
    {cs : List (Redex α)} (h : ∃ c ∈ cs, IsRedex R w c) :
    ∃ c, findRedexAux R w cs = some c := by
  induction cs with
  | nil => rcases h with ⟨_, hc, _⟩; cases hc
  | cons a cs ih =>
    rcases h with ⟨c, hc, hred⟩
    simp only [List.mem_cons] at hc
    by_cases ha : IsRedex R w a
    · refine ⟨⟨a, ha⟩, ?_⟩
      change (if h : IsRedex R w a then some ⟨a, h⟩ else findRedexAux R w cs) = _
      rw [dif_pos ha]
    · have htail : c ∈ cs := by
        rcases hc with hca | hct
        · subst c
          exact (ha hred).elim
        · exact hct
      obtain ⟨d, hd⟩ := ih ⟨c, htail, hred⟩
      refine ⟨d, ?_⟩
      change (if h : IsRedex R w a then some ⟨a, h⟩ else findRedexAux R w cs) = _
      rw [dif_neg ha, hd]

theorem findRedex?_sound {R : List (FreeGroup α)} {w : Word α}
    {c : {c : Redex α // IsRedex R w c}}
    (_h : findRedex? R w = some c) : IsRedex R w c.1 := c.2

theorem findRedex?_complete {R : List (FreeGroup α)} {w : Word α}
    (h : ∃ c, IsRedex R w c) :
    ∃ c, findRedex? R w = some c := by
  rcases h with ⟨c, hc⟩
  obtain ⟨d, hd⟩ := findRedexAux_complete (R := R) (w := w)
    ⟨c, redex_mem_candidates hc, hc⟩
  exact ⟨d, hd⟩

theorem findRedex?_none_iff {R : List (FreeGroup α)} {w : Word α} :
    findRedex? R w = none ↔ ¬ ∃ c, IsRedex R w c := by
  constructor
  · intro h hred
    obtain ⟨c, hc⟩ := findRedex?_complete hred
    rw [h] at hc
    cases hc
  · intro h
    cases hfind : findRedex? R w with
    | none => rfl
    | some c =>
      have hc := findRedex?_sound hfind
      exact (h ⟨c.1, hc⟩).elim

theorem replacement_preserves_presented_word {R : List (FreeGroup α)}
    {w : FreeGroup α} {c : Redex α}
    (hc : IsRedex R w.toWord c) :
    PresentedGroup.mk (relationSet R) w =
      PresentedGroup.mk (relationSet R) (replaceRedex c) := by
  rcases hc with ⟨hw, hrel, hcut, _⟩
  let π := PresentedGroup.mk (relationSet R)
  have hrelator : π c.relator = 1 := PresentedGroup.one_of_mem hrel
  have hrelatorWord : c.relator = FreeGroup.mk (c.long ++ c.short) := by
    calc
      c.relator = FreeGroup.mk c.relator.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c.long ++ c.short) := congrArg FreeGroup.mk hcut
  have hmul : π (FreeGroup.mk c.long) * π (FreeGroup.mk c.short) = 1 := by
    calc
      π (FreeGroup.mk c.long) * π (FreeGroup.mk c.short) =
          π (FreeGroup.mk c.long * FreeGroup.mk c.short) := (π.map_mul _ _).symm
      _ = π (FreeGroup.mk (c.long ++ c.short)) := by rw [FreeGroup.mul_mk]
      _ = π c.relator := by rw [← hrelatorWord]
      _ = 1 := hrelator
  have hlong : π (FreeGroup.mk c.long) = (π (FreeGroup.mk c.short))⁻¹ := by
    calc
      π (FreeGroup.mk c.long) =
          π (FreeGroup.mk c.long) * (π (FreeGroup.mk c.short) *
            (π (FreeGroup.mk c.short))⁻¹) := by simp
      _ = (π (FreeGroup.mk c.long) * π (FreeGroup.mk c.short)) *
            (π (FreeGroup.mk c.short))⁻¹ := by rw [mul_assoc]
      _ = 1 * (π (FreeGroup.mk c.short))⁻¹ := by rw [hmul]
      _ = (π (FreeGroup.mk c.short))⁻¹ := by simp
  have hshortInv : π (FreeGroup.mk (FreeGroup.invRev c.short)) =
      (π (FreeGroup.mk c.short))⁻¹ := by
    rw [← FreeGroup.inv_mk, map_inv]
  have hsource : FreeGroup.mk (c.before ++ c.long ++ c.after) =
      FreeGroup.mk c.before * FreeGroup.mk c.long * FreeGroup.mk c.after := by
    calc
      FreeGroup.mk (c.before ++ c.long ++ c.after) =
          FreeGroup.mk (c.before ++ c.long) * FreeGroup.mk c.after := by
            rw [← FreeGroup.mul_mk]
      _ = (FreeGroup.mk c.before * FreeGroup.mk c.long) * FreeGroup.mk c.after := by
            rw [← FreeGroup.mul_mk]
      _ = FreeGroup.mk c.before * FreeGroup.mk c.long * FreeGroup.mk c.after := rfl
  have htarget : FreeGroup.mk (c.before ++ FreeGroup.invRev c.short ++ c.after) =
      FreeGroup.mk c.before * FreeGroup.mk (FreeGroup.invRev c.short) * FreeGroup.mk c.after := by
    calc
      FreeGroup.mk (c.before ++ FreeGroup.invRev c.short ++ c.after) =
          FreeGroup.mk (c.before ++ FreeGroup.invRev c.short) * FreeGroup.mk c.after := by
            rw [← FreeGroup.mul_mk]
      _ = (FreeGroup.mk c.before * FreeGroup.mk (FreeGroup.invRev c.short)) *
            FreeGroup.mk c.after := by
            rw [← FreeGroup.mul_mk]
      _ = FreeGroup.mk c.before * FreeGroup.mk (FreeGroup.invRev c.short) *
            FreeGroup.mk c.after := rfl
  have hwordEq : π (FreeGroup.mk (c.before ++ c.long ++ c.after)) =
      π (replaceRedex c) := by
    unfold replaceRedex
    rw [hsource, htarget]
    simp only [map_mul]
    rw [hlong, hshortInv]
  have hw' : w = FreeGroup.mk (c.before ++ c.long ++ c.after) := by
    calc
      w = FreeGroup.mk w.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c.before ++ c.long ++ c.after) := congrArg FreeGroup.mk hw
  change π w = π (replaceRedex c)
  rw [hw']
  exact hwordEq

theorem replacement_decreases_norm {R : List (FreeGroup α)} {w : FreeGroup α}
    {c : Redex α} (hc : IsRedex R w.toWord c) :
    (replaceRedex c).norm < w.norm := by
  rcases hc with ⟨hw, _, _, hlong⟩
  have hlen : c.before.length + c.short.length + c.after.length < w.toWord.length := by
    rw [hw]
    simp only [List.length_append]
    omega
  calc
    (replaceRedex c).norm ≤ (c.before ++ FreeGroup.invRev c.short ++ c.after).length := by
      rw [replaceRedex]
      exact FreeGroup.norm_mk_le
    _ = c.before.length + c.short.length + c.after.length := by
      simp only [List.length_append, FreeGroup.invRev_length]
    _ < w.toWord.length := hlen
    _ = w.norm := rfl

theorem dehnReduceFuel_preserves_presented_word {R : List (FreeGroup α)} :
    ∀ (n : Nat) (w : FreeGroup α),
      PresentedGroup.mk (relationSet R) (dehnReduceFuel R n w) =
        PresentedGroup.mk (relationSet R) w := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    unfold dehnReduceFuel
    cases hfind : findRedex? R w.toWord with
    | none => rfl
    | some c =>
      rw [ih]
      exact (replacement_preserves_presented_word (findRedex?_sound hfind)).symm

theorem dehnReduceFuel_noRedex {R : List (FreeGroup α)} :
    ∀ (n : Nat) (w : FreeGroup α), w.norm ≤ n →
      ¬ ∃ c, IsRedex R (dehnReduceFuel R n w).toWord c := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have hwone : w = 1 := (FreeGroup.norm_eq_zero).mp (Nat.eq_zero_of_le_zero hw)
    subst w
    intro h
    rcases h with ⟨c, ⟨hword, _, _, hlong⟩⟩
    simp only [dehnReduceFuel, FreeGroup.toWord_one] at hword
    have hlen := congrArg List.length hword
    simp only [List.length_nil, List.length_append] at hlen
    omega
  | succ n ih =>
    intro w hw
    unfold dehnReduceFuel
    cases hfind : findRedex? R w.toWord with
    | none =>
      exact (findRedex?_none_iff (R := R) (w := w.toWord)).mp hfind
    | some c =>
      apply ih (replaceRedex c.1)
      have hc := findRedex?_sound hfind
      have hdec := replacement_decreases_norm hc
      omega

theorem dehnReduce_preserves_presented_word {R : List (FreeGroup α)}
    (w : FreeGroup α) :
    PresentedGroup.mk (relationSet R) (dehnReduce R w) =
      PresentedGroup.mk (relationSet R) w := by
  simpa [dehnReduce] using dehnReduceFuel_preserves_presented_word (R := R) w.norm w

theorem dehnReduce_has_no_redex {R : List (FreeGroup α)} (w : FreeGroup α) :
    ¬ ∃ c, IsRedex R (dehnReduce R w).toWord c := by
  simpa [dehnReduce] using
    dehnReduceFuel_noRedex (R := R) w.norm w (le_rfl : w.norm ≤ w.norm)

theorem dehnReduce_correct_of_greendlinger {R : List (FreeGroup α)}
    (hgreen : HasGreendlingerProperty R) (w : FreeGroup α) :
    dehnReduce R w = 1 ↔ PresentedGroup.mk (relationSet R) w = 1 := by
  have hpres := dehnReduce_preserves_presented_word (R := R) w
  constructor
  · intro h
    rw [← hpres, h]
    rfl
  · intro h
    by_contra hne
    have hout : PresentedGroup.mk (relationSet R) (dehnReduce R w) = 1 := by
      rw [hpres]
      exact h
    obtain ⟨c, hc⟩ := hgreen (dehnReduce R w) hout hne
    exact (dehnReduce_has_no_redex (R := R) w) ⟨c, hc⟩

/-- Run Dehn reduction and decide whether its terminal free word is empty. -/
def dehnWordProblem (R : List (FreeGroup α)) (w : FreeGroup α) : Bool :=
  decide (dehnReduce R w = 1)

theorem dehnWordProblem_correct_of_greendlinger {R : List (FreeGroup α)}
    (hgreen : HasGreendlingerProperty R) (w : FreeGroup α) :
    dehnWordProblem R w = true ↔ PresentedGroup.mk (relationSet R) w = 1 := by
  simp only [dehnWordProblem, decide_eq_true_eq]
  exact dehnReduce_correct_of_greendlinger hgreen w

end GreendlingerDehn
