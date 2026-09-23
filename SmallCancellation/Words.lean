import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup

namespace GreendlingerDehn

abbrev Letter (α : Type*) := α × Bool
abbrev Word (α : Type*) := List (Letter α)

/-- Every cut of a finite word, represented by its prefix and suffix. -/
def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun p => (x :: p.1, p.2))

@[simp]
theorem mem_splits_iff {α : Type*} {w pre suf : List α} :
    (pre, suf) ∈ splits w ↔ w = pre ++ suf := by
  induction w generalizing pre with
  | nil => simp [splits]
  | cons x xs ih =>
      cases pre with
      | nil => simp [splits, eq_comm]
      | cons y ys => simp [splits, ih, List.cons_append, and_comm, eq_comm]

/-- All cyclic rotations of a word, tagged by their distinct start positions.
The full-length split is omitted because it is the same cyclic position as zero. -/
def cyclicShifts {α : Type*} (w : Word α) : List (Nat × Word α) :=
  ((splits w).filter fun p => decide (p.1.length < w.length)).map
    fun p => (p.1.length, p.2 ++ p.1)

theorem mem_cyclicShifts_iff {α : Type*} {w : Word α} {i : Nat} {v : Word α} :
    (i, v) ∈ cyclicShifts w ↔
      ∃ pre suf, w = pre ++ suf ∧ pre.length < w.length ∧
        i = pre.length ∧ v = suf ++ pre := by
  constructor
  · intro h
    unfold cyclicShifts at h
    rcases List.mem_map.mp h with ⟨p, hp, hpair⟩
    rcases List.mem_filter.mp hp with ⟨hsplit, hlt⟩
    have hlt' : p.1.length < w.length := by simpa using hlt
    have hword := mem_splits_iff.mp hsplit
    cases p with
    | mk pre suf =>
        simp only [Prod.mk.injEq] at hpair
        rcases hpair with ⟨hi, hv⟩
        exact ⟨pre, suf, hword, hlt', hi.symm, hv.symm⟩
  · rintro ⟨pre, suf, hsplit, hlt, rfl, rfl⟩
    unfold cyclicShifts
    apply List.mem_map.mpr
    refine ⟨(pre, suf), ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨mem_splits_iff.mpr hsplit, by simp [hlt]⟩

/-- A nonempty common prefix of two distinct symmetrized relators, or of two
different cyclic positions in one relator, is a piece. The second clause is
essential for proper powers, where distinct cyclic positions can spell the same
word and would be lost by deduplicating the symmetrized relator list. -/
def IsPiece {α : Type*} [DecidableEq α] (R : List (FreeGroup α)) (u : Word α) : Prop :=
  u ≠ [] ∧
    ((∃ r ∈ R, ∃ s ∈ R, r ≠ s ∧
        ∃ rTail sTail, r.toWord = u ++ rTail ∧ s.toWord = u ++ sTail) ∨
      ∃ r ∈ R, ∃ i j rShift sShift rTail sTail,
        i ≠ j ∧
        (i, rShift) ∈ cyclicShifts r.toWord ∧
        (j, sShift) ∈ cyclicShifts r.toWord ∧
        rShift = u ++ rTail ∧ sShift = u ++ sTail)

/-- The metric small cancellation condition (C'(1/6)), for a symmetrized finite
set of cyclically reduced relators. -/
def CPrimeSix {α : Type*} [DecidableEq α] (R : List (FreeGroup α)) : Prop :=
  ∀ {u r}, IsPiece R u → r ∈ R →
    (∃ tail, r.toWord = u ++ tail) → 6 * u.length < r.toWord.length

/-- Relator data for a finite symmetrized presentation. Rotating a relator means
moving its first letter to the end of its canonical reduced word. -/
structure SymmetrizedPresentation (α : Type*) [Fintype α] [DecidableEq α] where
  relators : List (FreeGroup α)
  relatorsNodup : relators.Nodup
  nontrivial : ∀ r ∈ relators, r ≠ 1
  cyclicallyReduced : ∀ r ∈ relators, ∀ first rest,
    r.toWord = first :: rest → rest.getLast? ≠ some (first.1, !first.2)
  inverseClosed : ∀ r ∈ relators, r⁻¹ ∈ relators
  rotationClosed : ∀ r ∈ relators, ∀ first rest,
    r.toWord = first :: rest → FreeGroup.mk (rest ++ [first]) ∈ relators

/-- A candidate replacement in Dehn's algorithm. -/
structure Redex (α : Type*) where
  before : Word α
  long : Word α
  after : Word α
  relator : FreeGroup α
  short : Word α
  deriving DecidableEq

/-- The candidate occurs in the current reduced word and is more than half of
its relator. -/
@[reducible] def IsRedex {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : Word α) (c : Redex α) : Prop :=
  w = c.before ++ c.long ++ c.after ∧
  c.relator ∈ R ∧
  c.relator.toWord = c.long ++ c.short ∧
  c.long.length > c.short.length

/-- Enumerate every possible occurrence and every relator cut. -/
def redexCandidates {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : Word α) : List (Redex α) :=
  (splits w).flatMap fun p =>
    (splits p.2).flatMap fun q =>
      R.flatMap fun r =>
        (splits r.toWord).map fun t =>
          ⟨p.1, q.1, q.2, r, t.2⟩

/-- Return the first valid Dehn replacement candidate in a finite search. -/
def findRedexAux {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : Word α) :
    List (Redex α) → Option {c : Redex α // IsRedex R w c}
  | [] => none
  | c :: cs => if h : IsRedex R w c then some ⟨c, h⟩ else findRedexAux R w cs

/-- The deterministic, executable search for a Dehn replacement. -/
def findRedex? {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : Word α) :=
  findRedexAux R w (redexCandidates R w)

/-- Replace a long relator segment by the inverse of the complementary segment. -/
def replaceRedex {α : Type*} (c : Redex α) : FreeGroup α :=
  FreeGroup.mk (c.before ++ FreeGroup.invRev c.short ++ c.after)

/-- The Greendlinger property of a finite presentation: each nontrivial null word
has a reducible relator segment longer than half the relator. -/
def HasGreendlingerProperty {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) : Prop :=
  ∀ w : FreeGroup α,
    PresentedGroup.mk {r | r ∈ R} w = 1 → w ≠ 1 →
      ∃ c, IsRedex R w.toWord c

/-- Dehn reduction with a fuel bound. Each rewrite decreases free-word length,
so the input length bounds the number of iterations. -/
def dehnReduceFuel {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) : Nat → FreeGroup α → FreeGroup α
  | 0, w => w
  | n + 1, w =>
      match findRedex? R w.toWord with
      | none => w
      | some c => dehnReduceFuel R n (replaceRedex c.1)

/-- The executable Dehn algorithm, run with the initial reduced length as fuel. -/
def dehnReduce {α : Type*} [DecidableEq α]
    (R : List (FreeGroup α)) (w : FreeGroup α) : FreeGroup α :=
  dehnReduceFuel R w.norm w

end GreendlingerDehn
