import SmallCancellation.Dehn
import Mathlib.Tactic.Group

namespace GreendlingerDehn

theorem mk_cyclicRotate {α : Type*} (pre suf : Word α) :
    FreeGroup.mk (suf ++ pre) =
      (FreeGroup.mk pre)⁻¹ * FreeGroup.mk (pre ++ suf) *
        FreeGroup.mk pre := by
  repeat rw [← FreeGroup.mul_mk]
  group

variable {α : Type*} [DecidableEq α]

/-- A candidate shell occurrence, allowing the occurrence to cross the chosen
start of the boundary word. `prefix` and `suffix` record the cyclic rotation
whose linear word contains the occurrence. -/
structure CyclicRedex (α : Type*) where
  pre : Word α
  suf : Word α
  redex : Redex α
  deriving DecidableEq

/-- A cyclic redex is an ordinary Dehn redex in one cyclic rotation. -/
@[reducible] def IsCyclicRedex (R : List (FreeGroup α)) (w : FreeGroup α)
    (c : CyclicRedex α) : Prop :=
  w.toWord = c.pre ++ c.suf ∧
  IsRedex R (FreeGroup.mk (c.suf ++ c.pre)).toWord c.redex

/-- Enumerate redexes in every cyclic rotation of the reduced input word. -/
def cyclicRedexCandidates (R : List (FreeGroup α)) (w : FreeGroup α) :
    List (CyclicRedex α) :=
  (splits w.toWord).flatMap fun p =>
    (redexCandidates R (FreeGroup.mk (p.2 ++ p.1)).toWord).map fun c =>
      ⟨p.1, p.2, c⟩

theorem cyclicRedex_mem_candidates {R : List (FreeGroup α)} {w : FreeGroup α}
    {c : CyclicRedex α} (hc : IsCyclicRedex R w c) :
    c ∈ cyclicRedexCandidates R w := by
  rcases hc with ⟨hsplit, hredex⟩
  simp only [cyclicRedexCandidates, List.mem_flatMap, List.mem_map]
  refine ⟨(c.pre, c.suf), ?_, c.redex, ?_, rfl⟩
  · exact mem_splits_iff.mpr hsplit
  · exact redex_mem_candidates hredex

/-- Search a finite list of cyclic redex candidates, retaining a proof that the
selected candidate is valid. -/
def findCyclicRedexAux (R : List (FreeGroup α)) (w : FreeGroup α) :
    List (CyclicRedex α) → Option {c : CyclicRedex α // IsCyclicRedex R w c}
  | [] => none
  | c :: cs =>
      if h : IsCyclicRedex R w c then some ⟨c, h⟩ else
        findCyclicRedexAux R w cs

/-- Deterministic executable search through all cyclic redexes. -/
def findCyclicRedex? (R : List (FreeGroup α)) (w : FreeGroup α) :=
  findCyclicRedexAux R w (cyclicRedexCandidates R w)

theorem findCyclicRedexAux_complete {R : List (FreeGroup α)} {w : FreeGroup α}
    {cs : List (CyclicRedex α)}
    (h : ∃ c ∈ cs, IsCyclicRedex R w c) :
    ∃ c, findCyclicRedexAux R w cs = some c := by
  induction cs with
  | nil => rcases h with ⟨_, hc, _⟩; cases hc
  | cons a cs ih =>
      rcases h with ⟨c, hc, hredex⟩
      simp only [List.mem_cons] at hc
      by_cases ha : IsCyclicRedex R w a
      · refine ⟨⟨a, ha⟩, ?_⟩
        change (if h : IsCyclicRedex R w a then some ⟨a, h⟩ else
          findCyclicRedexAux R w cs) = _
        rw [dif_pos ha]
      · have htail : c ∈ cs := by
          rcases hc with hca | hct
          · subst c
            exact (ha hredex).elim
          · exact hct
        obtain ⟨d, hd⟩ := ih ⟨c, htail, hredex⟩
        refine ⟨d, ?_⟩
        change (if h : IsCyclicRedex R w a then some ⟨a, h⟩ else
          findCyclicRedexAux R w cs) = _
        rw [dif_neg ha, hd]

theorem findCyclicRedex?_sound {R : List (FreeGroup α)} {w : FreeGroup α}
    {c : {c : CyclicRedex α // IsCyclicRedex R w c}}
    (_h : findCyclicRedex? R w = some c) : IsCyclicRedex R w c.1 := c.2

theorem findCyclicRedex?_complete {R : List (FreeGroup α)} {w : FreeGroup α}
    (h : ∃ c, IsCyclicRedex R w c) :
    ∃ c, findCyclicRedex? R w = some c := by
  rcases h with ⟨c, hc⟩
  obtain ⟨d, hd⟩ := findCyclicRedexAux_complete
    (R := R) (w := w) ⟨c, cyclicRedex_mem_candidates hc, hc⟩
  exact ⟨d, hd⟩

theorem findCyclicRedex?_none_iff {R : List (FreeGroup α)} {w : FreeGroup α} :
    findCyclicRedex? R w = none ↔ ¬ ∃ c, IsCyclicRedex R w c := by
  constructor
  · intro h hredex
    obtain ⟨c, hc⟩ := findCyclicRedex?_complete hredex
    rw [h] at hc
    cases hc
  · intro h
    cases hfind : findCyclicRedex? R w with
    | none => rfl
    | some c =>
        have hc := findCyclicRedex?_sound hfind
        exact (h ⟨c.1, hc⟩).elim

/-- Conjugation preserves and reflects equality to the identity. -/
theorem conjugate_eq_one_iff {G : Type*} [Group G] (a b : G) :
    a⁻¹ * b * a = 1 ↔ b = 1 := by
  constructor
  · intro h
    have hmul : b * a = a := by
      calc
        b * a = (a * a⁻¹) * (b * a) := by simp
        _ = a * (a⁻¹ * (b * a)) := by rw [mul_assoc]
        _ = a * (a⁻¹ * b * a) := by rw [mul_assoc]
        _ = a * 1 := by rw [h]
        _ = a := by simp
    calc
      b = (b * a) * a⁻¹ := by simp
      _ = a * a⁻¹ := by rw [hmul]
      _ = 1 := by simp
  · rintro rfl
    simp

/-- Replacing a cyclic redex preserves whether the presented-group element is
the identity. The intermediate word is a cyclic rotation, so equality of group
elements is intentionally stated modulo conjugacy. -/
theorem cyclicReplacement_identity_iff {R : List (FreeGroup α)}
    {w : FreeGroup α} {c : CyclicRedex α} (hc : IsCyclicRedex R w c) :
    PresentedGroup.mk (relationSet R) (replaceRedex c.redex) = 1 ↔
      PresentedGroup.mk (relationSet R) w = 1 := by
  rcases hc with ⟨hsplit, hredex⟩
  let π := PresentedGroup.mk (relationSet R)
  have hw : w = FreeGroup.mk (c.pre ++ c.suf) := by
    calc
      w = FreeGroup.mk w.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c.pre ++ c.suf) := congrArg FreeGroup.mk hsplit
  have hrotate := mk_cyclicRotate c.pre c.suf
  have hconj : π (FreeGroup.mk (c.suf ++ c.pre)) =
      (π (FreeGroup.mk c.pre))⁻¹ * π w * π (FreeGroup.mk c.pre) := by
    calc
      π (FreeGroup.mk (c.suf ++ c.pre)) =
          π ((FreeGroup.mk c.pre)⁻¹ * FreeGroup.mk (c.pre ++ c.suf) *
            FreeGroup.mk c.pre) := congrArg π hrotate
      _ = π ((FreeGroup.mk c.pre)⁻¹) * π (FreeGroup.mk (c.pre ++ c.suf)) *
            π (FreeGroup.mk c.pre) := by rw [map_mul, map_mul]
      _ = (π (FreeGroup.mk c.pre))⁻¹ * π w * π (FreeGroup.mk c.pre) := by
        rw [map_inv, ← hw]
  have hreplace := replacement_preserves_presented_word
      (R := R) (w := FreeGroup.mk (c.suf ++ c.pre)) hredex
  have hreplace' : π (replaceRedex c.redex) =
      (π (FreeGroup.mk c.pre))⁻¹ * π w * π (FreeGroup.mk c.pre) :=
    hreplace.symm.trans hconj
  constructor
  · intro h
    have hconjOne :
        (π (FreeGroup.mk c.pre))⁻¹ * π w * π (FreeGroup.mk c.pre) = 1 := by
      rw [← hreplace']
      exact h
    exact (conjugate_eq_one_iff (π (FreeGroup.mk c.pre)) (π w)).mp hconjOne
  · intro h
    have hconjOne :=
      (conjugate_eq_one_iff (π (FreeGroup.mk c.pre)) (π w)).mpr h
    rw [← hreplace'] at hconjOne
    exact hconjOne

/-- A Greendlinger shell may meet the basepoint of the boundary circuit. This
property states the conclusion in a cyclic rotation, matching the standard
diagrammatic form of the lemma. -/
def CyclicGreendlingerProperty (R : List (FreeGroup α)) : Prop :=
  ∀ w : FreeGroup α,
    PresentedGroup.mk (relationSet R) w = 1 → w ≠ 1 →
      ∃ c, IsCyclicRedex R w c

/-- Cyclic Dehn reduction with fuel equal to the original reduced length. Each
step decreases length after rotating to the representative containing the
shell. -/
def cyclicDehnReduceFuel (R : List (FreeGroup α)) : Nat → FreeGroup α → FreeGroup α
  | 0, w => w
  | n + 1, w =>
      match findCyclicRedex? R w with
      | none => w
      | some c => cyclicDehnReduceFuel R n (replaceRedex c.1.redex)

/-- The executable cyclic Dehn reducer. -/
def cyclicDehnReduce (R : List (FreeGroup α)) (w : FreeGroup α) : FreeGroup α :=
  cyclicDehnReduceFuel R w.norm w

theorem cyclicReplacement_decreases_norm {R : List (FreeGroup α)}
    {w : FreeGroup α} {c : CyclicRedex α} (hc : IsCyclicRedex R w c) :
    (replaceRedex c.redex).norm < w.norm := by
  rcases hc with ⟨hsplit, hredex⟩
  have hdecrease := replacement_decreases_norm hredex
  have hrotateNorm : (FreeGroup.mk (c.suf ++ c.pre)).norm ≤ w.norm := by
    calc
      (FreeGroup.mk (c.suf ++ c.pre)).norm ≤ (c.suf ++ c.pre).length :=
        FreeGroup.norm_mk_le
      _ = w.toWord.length := by
        rw [hsplit]
        simp only [List.length_append]
        omega
      _ = w.norm := rfl
  omega

theorem cyclicDehnReduceFuel_preserves_identity {R : List (FreeGroup α)} :
    ∀ (n : Nat) (w : FreeGroup α),
      PresentedGroup.mk (relationSet R) (cyclicDehnReduceFuel R n w) = 1 ↔
        PresentedGroup.mk (relationSet R) w = 1 := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
      intro w
      unfold cyclicDehnReduceFuel
      cases hfind : findCyclicRedex? R w with
      | none => rfl
      | some c =>
          exact (ih (replaceRedex c.1.redex)).trans
            (cyclicReplacement_identity_iff (findCyclicRedex?_sound hfind))

theorem cyclicDehnReduceFuel_noCyclicRedex {R : List (FreeGroup α)} :
    ∀ (n : Nat) (w : FreeGroup α), w.norm ≤ n →
      ¬ ∃ c, IsCyclicRedex R (cyclicDehnReduceFuel R n w) c := by
  intro n
  induction n with
  | zero =>
      intro w hw hredex
      rcases hredex with ⟨c, hc⟩
      have hdecrease := cyclicReplacement_decreases_norm hc
      unfold cyclicDehnReduceFuel at hdecrease
      have hwzero : w.norm = 0 := Nat.eq_zero_of_le_zero hw
      omega
  | succ n ih =>
      intro w hw
      unfold cyclicDehnReduceFuel
      cases hfind : findCyclicRedex? R w with
      | none =>
          exact (findCyclicRedex?_none_iff (R := R) (w := w)).mp hfind
      | some c =>
          apply ih (replaceRedex c.1.redex)
          have hc := findCyclicRedex?_sound hfind
          have hdecrease := cyclicReplacement_decreases_norm hc
          omega

theorem cyclicDehnReduce_preserves_identity {R : List (FreeGroup α)}
    (w : FreeGroup α) :
    PresentedGroup.mk (relationSet R) (cyclicDehnReduce R w) = 1 ↔
      PresentedGroup.mk (relationSet R) w = 1 := by
  simpa [cyclicDehnReduce] using
    cyclicDehnReduceFuel_preserves_identity (R := R) w.norm w

theorem cyclicDehnReduce_has_no_cyclicRedex {R : List (FreeGroup α)}
    (w : FreeGroup α) :
    ¬ ∃ c, IsCyclicRedex R (cyclicDehnReduce R w) c := by
  simpa [cyclicDehnReduce] using
    cyclicDehnReduceFuel_noCyclicRedex (R := R) w.norm w (le_rfl : w.norm ≤ w.norm)

/-- The cyclic Dehn algorithm decides the word problem whenever the cyclic
Greendlinger property holds. -/
def cyclicDehnWordProblem (R : List (FreeGroup α)) (w : FreeGroup α) : Bool :=
  decide (cyclicDehnReduce R w = 1)

theorem cyclicDehnWordProblem_correct_of_greendlinger
    {R : List (FreeGroup α)} (hgreen : CyclicGreendlingerProperty R)
    (w : FreeGroup α) :
    cyclicDehnWordProblem R w = true ↔
      PresentedGroup.mk (relationSet R) w = 1 := by
  simp only [cyclicDehnWordProblem, decide_eq_true_eq]
  constructor
  · intro h
    rw [← cyclicDehnReduce_preserves_identity (R := R) w, h]
    rfl
  · intro h
    by_contra hne
    have hterminal : PresentedGroup.mk (relationSet R) (cyclicDehnReduce R w) = 1 :=
      (cyclicDehnReduce_preserves_identity (R := R) w).2 h
    obtain ⟨c, hc⟩ := hgreen (cyclicDehnReduce R w) hterminal hne
    exact (cyclicDehnReduce_has_no_cyclicRedex (R := R) w) ⟨c, hc⟩

end GreendlingerDehn
