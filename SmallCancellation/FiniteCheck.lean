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

/-- Enumerate nonempty common prefixes of distinct symmetrized relators. -/
def distinctPieceCandidates (R : List (FreeGroup α)) : List (Word α) :=
  R.flatMap fun r =>
    R.flatMap fun s =>
      if r = s then [] else
        (prefixes r.toWord).filter fun u =>
          decide (u ≠ [] ∧ u ∈ prefixes s.toWord)

/-- Enumerate common prefixes arising from distinct cyclic positions in one
relator, including positions whose rotations spell the same word. -/
def repeatedPieceCandidates (R : List (FreeGroup α)) : List (Word α) :=
  R.flatMap fun r =>
    (cyclicShifts r.toWord).flatMap fun p =>
      ((cyclicShifts r.toWord).filter fun q => decide (p.1 ≠ q.1)).flatMap fun q =>
        (prefixes p.2).filter fun u =>
          decide (u ≠ [] ∧ u ∈ prefixes q.2)

/-- Enumerate all finite small-cancellation pieces. -/
def pieceCandidates (R : List (FreeGroup α)) : List (Word α) :=
  distinctPieceCandidates R ++ repeatedPieceCandidates R

theorem pieceCandidates_sound {R : List (FreeGroup α)} {u : Word α}
    (hu : u ∈ pieceCandidates R) : IsPiece R u := by
  rcases List.mem_append.mp hu with hu | hu
  · simp only [distinctPieceCandidates, List.mem_flatMap] at hu
    rcases hu with ⟨r, hr, s, hs, hu⟩
    by_cases hrs : r = s
    · simp [hrs] at hu
    · simp only [if_neg hrs, List.mem_filter, decide_eq_true_eq] at hu
      rcases hu with ⟨hru, ⟨hne, hsu⟩⟩
      refine ⟨hne, Or.inl ?_⟩
      refine ⟨r, hr, s, hs, hrs, ?_⟩
      obtain ⟨rt, hrt⟩ := mem_prefixes_iff.mp hru
      obtain ⟨st, hst⟩ := mem_prefixes_iff.mp hsu
      exact ⟨rt, st, hrt, hst⟩
  · unfold repeatedPieceCandidates at hu
    rcases List.mem_flatMap.mp hu with ⟨r, hr, h₁⟩
    rcases List.mem_flatMap.mp h₁ with ⟨p, hp, h₂⟩
    rcases List.mem_flatMap.mp h₂ with ⟨q, hqfilter, h₃⟩
    rcases List.mem_filter.mp hqfilter with ⟨hq, hposBool⟩
    have hpos : p.1 ≠ q.1 := by simpa using hposBool
    rcases List.mem_filter.mp h₃ with ⟨hpu, hcondBool⟩
    have hcond : u ≠ [] ∧ u ∈ prefixes q.2 := by simpa using hcondBool
    rcases hcond with ⟨hne, hqu⟩
    obtain ⟨rTail, hrTail⟩ := mem_prefixes_iff.mp hpu
    obtain ⟨sTail, hsTail⟩ := mem_prefixes_iff.mp hqu
    exact ⟨hne, Or.inr ⟨r, hr, p.1, q.1, p.2, q.2, rTail, sTail,
      hpos, hp, hq, hrTail, hsTail⟩⟩

theorem pieceCandidates_complete {R : List (FreeGroup α)} {u : Word α}
    (hu : IsPiece R u) : u ∈ pieceCandidates R := by
  rcases hu with ⟨hne, hpiece⟩
  rcases hpiece with hpiece | hpiece
  · rcases hpiece with ⟨r, hr, s, hs, hrs, rt, st, hrt, hst⟩
    apply List.mem_append.mpr
    left
    simp only [distinctPieceCandidates, List.mem_flatMap]
    refine ⟨r, hr, s, hs, ?_⟩
    have hru : u ∈ prefixes r.toWord := mem_prefixes_iff.mpr ⟨rt, hrt⟩
    have hsu : u ∈ prefixes s.toWord := mem_prefixes_iff.mpr ⟨st, hst⟩
    simp [hrs, List.mem_filter, hru, hne, hsu]
  · rcases hpiece with ⟨r, hr, i, j, rShift, sShift, rTail, sTail,
      hpos, hri, hsj, hru, hsu⟩
    apply List.mem_append.mpr
    right
    apply List.mem_flatMap.mpr
    refine ⟨r, hr, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨(i, rShift), hri, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨(j, sShift), ?_, ?_⟩
    · apply List.mem_filter.mpr
      exact ⟨hsj, by simp [hpos]⟩
    · apply List.mem_filter.mpr
      refine ⟨mem_prefixes_iff.mpr ⟨rTail, hru⟩, ?_⟩
      simp [hne, mem_prefixes_iff.mpr ⟨sTail, hsu⟩]

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
