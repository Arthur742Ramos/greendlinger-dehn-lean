import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace GreendlingerDehn

/-- The local type of a face in the angle proof of the shell lemma. -/
inductive CurvatureFaceKind where
  | internal
  | external
  | shell (internalArcs : Nat)
  deriving DecidableEq

/-- Finite local data used in the standard C'(1/6) angle count. Angles are
measured in units of π. The `angleCap` field records the bounds 1/2 at exterior
corners and 2/3 at interior corners; the remaining fields are the local
incidence facts supplied by an arc-reduced disk diagram. -/
structure CurvatureFace where
  kind : CurvatureFaceKind
  sides : Nat
  exteriorCorners : Nat
  angleSum : ℚ
  exteriorCorners_le_sides : exteriorCorners ≤ sides
  angleCap : angleSum ≤
    (exteriorCorners : ℚ) * (1 / 2 : ℚ) +
      ((sides - exteriorCorners : Nat) : ℚ) * (2 / 3 : ℚ)
  internal_sides : kind = .internal → 7 ≤ sides
  internal_exteriorCorners : kind = .internal → exteriorCorners = 0
  external_sides : kind = .external → 4 ≤ sides
  external_small_exteriorCorners : kind = .external → sides ≤ 5 →
    4 ≤ exteriorCorners
  external_large_exteriorCorners : kind = .external → 6 ≤ sides →
    1 ≤ exteriorCorners
  shell_sides : ∀ i, kind = .shell i → sides = i + 1
  shell_exteriorCorners : ∀ i, kind = .shell i → exteriorCorners = 2

/-- Combinatorial curvature of one face, in units of π. -/
def CurvatureFace.curvature (f : CurvatureFace) : ℚ :=
  f.angleSum - ((f.sides : ℚ) - 2)

/-- A shell with at most three internal arcs is the desired Greendlinger face. -/
def CurvatureFace.IsSmallShell (f : CurvatureFace) : Prop :=
  ∃ i, f.kind = .shell i ∧ i ≤ 3

theorem CurvatureFace.curvature_le_local_bound (f : CurvatureFace) :
    f.curvature ≤ 2 - (f.sides : ℚ) / 3 -
      (f.exteriorCorners : ℚ) / 6 := by
  have hsub : ((f.sides - f.exteriorCorners : Nat) : ℚ) =
      (f.sides : ℚ) - (f.exteriorCorners : ℚ) := by
    exact_mod_cast Nat.cast_sub f.exteriorCorners_le_sides
  have hcap : f.angleSum ≤
      (f.exteriorCorners : ℚ) * (1 / 2 : ℚ) +
        ((f.sides : ℚ) - (f.exteriorCorners : ℚ)) * (2 / 3 : ℚ) := by
    simpa [hsub] using f.angleCap
  dsimp [CurvatureFace.curvature]
  nlinarith [hcap]

theorem CurvatureFace.curvature_nonpos_of_not_smallShell (f : CurvatureFace)
    (hsmall : ¬ f.IsSmallShell) : f.curvature ≤ 0 := by
  cases hk : f.kind with
  | internal =>
      have hsides := f.internal_sides hk
      have hcorners := f.internal_exteriorCorners hk
      have hbound := f.curvature_le_local_bound
      rw [hcorners] at hbound
      have hsidesQ : (7 : ℚ) ≤ (f.sides : ℚ) := by exact_mod_cast hsides
      nlinarith
  | external =>
      have hsides := f.external_sides hk
      have hbound := f.curvature_le_local_bound
      by_cases hsmallSides : f.sides ≤ 5
      · have hc := f.external_small_exteriorCorners hk hsmallSides
        have hsidesQ : (4 : ℚ) ≤ (f.sides : ℚ) := by exact_mod_cast hsides
        have hcQ : (4 : ℚ) ≤ (f.exteriorCorners : ℚ) := by exact_mod_cast hc
        nlinarith
      · have hsidesLarge : 6 ≤ f.sides :=
          Nat.succ_le_of_lt (not_le.mp hsmallSides)
        have hc := f.external_large_exteriorCorners hk hsidesLarge
        have hsidesQ : (6 : ℚ) ≤ (f.sides : ℚ) := by exact_mod_cast hsidesLarge
        have hcQ : (1 : ℚ) ≤ (f.exteriorCorners : ℚ) := by exact_mod_cast hc
        nlinarith
  | shell i =>
      have hlarge : 4 ≤ i := by
        by_contra h
        apply hsmall
        have hiLt : i < 4 := not_le.mp h
        exact ⟨i, hk, Nat.le_of_lt_succ (by simpa using hiLt)⟩
      have hsides := f.shell_sides i hk
      have hcorners := f.shell_exteriorCorners i hk
      have hbound := f.curvature_le_local_bound
      rw [hsides, hcorners] at hbound
      have hiQ : (4 : ℚ) ≤ (i : ℚ) := by exact_mod_cast hlarge
      norm_num [Nat.cast_add] at hbound
      nlinarith [hbound]

/-- The local curvature estimates force a small shell whenever the total
curvature is positive. For disk diagrams, the total-curvature identity is the
Euler characteristic calculation; the diagram-to-local-data construction is a
separate theorem. -/
theorem positive_curvature_forces_small_shell {F : Type*} [Fintype F]
    (faces : F → CurvatureFace)
    (htotal : ∑ f : F, (faces f).curvature = 2) :
    ∃ f : F, (faces f).IsSmallShell := by
  by_contra hnone
  have hnonpos : ∀ f : F, (faces f).curvature ≤ 0 := by
    intro f
    apply CurvatureFace.curvature_nonpos_of_not_smallShell
    intro hsmall
    exact hnone ⟨f, hsmall⟩
  have hsum : (∑ f : F, (faces f).curvature) ≤ 0 := by
    calc
      (∑ f : F, (faces f).curvature) ≤ ∑ _f : F, (0 : ℚ) :=
        Finset.sum_le_sum (fun f _ => hnonpos f)
      _ = 0 := by simp
  rw [htotal] at hsum
  norm_num at hsum

/-- Summing strict one-sixth bounds over a nonempty finite arc family gives a
strict total bound. -/
theorem six_mul_sum_lt_length_mul {pieces : List Nat} {perimeter : Nat}
    (hne : pieces ≠ []) (hpiece : ∀ p ∈ pieces, 6 * p < perimeter) :
    6 * pieces.sum < pieces.length * perimeter := by
  induction pieces with
  | nil => simp at hne
  | cons a rest ih =>
      have hhead : 6 * a < perimeter := hpiece a (by simp)
      have htail : ∀ p ∈ rest, 6 * p < perimeter := by
        intro p hp
        exact hpiece p (by simp [hp])
      by_cases hrest : rest = []
      · subst rest
        simpa using hhead
      · have htailBound := ih hrest htail
        simp only [List.sum_cons, List.length_cons]
        nlinarith [hhead, htailBound]

/-- In a shell with at most three internal arcs, strict C'(1/6) bounds make
the complementary exterior arc longer than all internal arcs combined. -/
theorem shell_exterior_longer_than_interior
    {perimeter exterior : Nat} {pieces : List Nat}
    (hperimeter : perimeter = exterior + pieces.sum)
    (hperimeter_pos : 0 < perimeter)
    (hcount : pieces.length ≤ 3)
    (hpieces : ∀ p ∈ pieces, 6 * p < perimeter) :
    pieces.sum < exterior := by
  by_cases hnil : pieces = []
  · subst pieces
    simp only [List.sum_nil, Nat.add_zero] at hperimeter
    rw [hperimeter] at hperimeter_pos
    simpa using hperimeter_pos
  · have hsum := six_mul_sum_lt_length_mul hnil hpieces
    have hlen : pieces.length * perimeter ≤ 3 * perimeter :=
      Nat.mul_le_mul_right perimeter hcount
    have hbound : 6 * pieces.sum < 3 * perimeter := lt_of_lt_of_le hsum hlen
    rw [hperimeter] at hbound
    omega

/-- Consequently, the exterior shell arc occupies more than half of the
relator boundary. -/
theorem shell_exterior_longer_than_half
    {perimeter exterior : Nat} {pieces : List Nat}
    (hperimeter : perimeter = exterior + pieces.sum)
    (hperimeter_pos : 0 < perimeter)
    (hcount : pieces.length ≤ 3)
    (hpieces : ∀ p ∈ pieces, 6 * p < perimeter) :
    perimeter < 2 * exterior := by
  have hlong := shell_exterior_longer_than_interior hperimeter hperimeter_pos
    hcount hpieces
  rw [hperimeter]
  omega

end GreendlingerDehn
