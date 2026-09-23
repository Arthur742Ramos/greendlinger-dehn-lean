import SmallCancellation.Words

namespace GreendlingerDehn

variable {α : Type*}

/-- The finite list of all prefixes of a word. -/
def prefixes (w : Word α) : List (Word α) := (splits w).map Prod.fst

theorem mem_prefixes_iff {u w : Word α} :
    u ∈ prefixes w ↔ ∃ tail, w = u ++ tail := by
  unfold prefixes
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨pre, suf⟩, hp, hpre⟩
    change pre = u at hpre
    subst pre
    exact ⟨suf, (mem_splits_iff.mp hp)⟩
  · rintro ⟨tail, hw⟩
    exact ⟨(u, tail), mem_splits_iff.mpr hw, rfl⟩

variable [DecidableEq α]

/-- Enumerate exactly the nonempty common prefixes of distinct relators. -/
def pieceCandidates (R : List (FreeGroup α)) : List (Word α) :=
  R.flatMap fun r =>
    R.flatMap fun s =>
      if r = s then [] else
        (prefixes r.toWord).filter fun u =>
          decide (u ≠ [] ∧ u ∈ prefixes s.toWord)

theorem pieceCandidates_sound {R : List (FreeGroup α)} {u : Word α}
    (hu : u ∈ pieceCandidates R) : IsPiece R u := by
  simp only [pieceCandidates, List.mem_flatMap] at hu
  rcases hu with ⟨r, hr, s, hs, hu⟩
  by_cases hrs : r = s
  · simp [hrs] at hu
  · simp only [if_neg hrs, List.mem_filter, decide_eq_true_eq] at hu
    rcases hu with ⟨hru, ⟨hne, hsu⟩⟩
    refine ⟨hne, r, hr, s, hs, hrs, ?_⟩
    obtain ⟨rt, hrt⟩ := mem_prefixes_iff.mp hru
    obtain ⟨st, hst⟩ := mem_prefixes_iff.mp hsu
    exact ⟨rt, st, hrt, hst⟩

theorem pieceCandidates_complete {R : List (FreeGroup α)} {u : Word α}
    (hu : IsPiece R u) : u ∈ pieceCandidates R := by
  rcases hu with ⟨hne, r, hr, s, hs, hrs, rt, st, hrt, hst⟩
  simp only [pieceCandidates, List.mem_flatMap]
  refine ⟨r, hr, s, hs, ?_⟩
  have hru : u ∈ prefixes r.toWord := mem_prefixes_iff.mpr ⟨rt, hrt⟩
  have hsu : u ∈ prefixes s.toWord := mem_prefixes_iff.mpr ⟨st, hst⟩
  simp [hrs, List.mem_filter, hru, hne, hsu]

/-- Executable checker for the metric small-cancellation condition C'(1/6). -/
def cPrimeSixCheck (R : List (FreeGroup α)) : Bool :=
  (pieceCandidates R).all fun u =>
    R.all fun r =>
      if u ∈ prefixes r.toWord then decide (6 * u.length < r.toWord.length) else true

theorem cPrimeSixCheck_correct {R : List (FreeGroup α)} :
    cPrimeSixCheck R = true ↔ CPrimeSix R := by
  constructor
  · intro h u r hpiece hr hprefix
    have hu : u ∈ pieceCandidates R := pieceCandidates_complete hpiece
    have hinner := (List.all_eq_true.mp h) u hu
    have hrcheck := (List.all_eq_true.mp hinner) r hr
    have hpre : u ∈ prefixes r.toWord := mem_prefixes_iff.mpr hprefix
    simpa [hpre] using hrcheck
  · intro h
    unfold cPrimeSixCheck
    apply (List.all_eq_true).2
    intro u hu
    apply (List.all_eq_true).2
    intro r hr
    by_cases hpref : u ∈ prefixes r.toWord
    · have hpiece := pieceCandidates_sound hu
      have hprefix : ∃ tail, r.toWord = u ++ tail := mem_prefixes_iff.mp hpref
      simpa [hpref] using h hpiece hr hprefix
    · simp [hpref]

end GreendlingerDehn
