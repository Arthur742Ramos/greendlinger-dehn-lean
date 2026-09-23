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

end GreendlingerDehn
