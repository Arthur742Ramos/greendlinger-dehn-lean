import Mathlib.Algebra.BigOperators.Group.List.Basic
import SmallCancellation.Dehn

namespace GreendlingerDehn

universe u

variable {α : Type u}

/-- A finite algebraic certificate that a word lies in the normal closure of the relators.
The conjugate constructor corresponds to attaching one relator cell along a conjugating path;
the product and inverse constructors combine such cells. -/
inductive RelatorCertificate (R : List (FreeGroup α)) : FreeGroup α → Type (u + 1) where
  | one : RelatorCertificate R 1
  | relator (r : FreeGroup α) (hr : r ∈ R) : RelatorCertificate R r
  | mul {x y : FreeGroup α} : RelatorCertificate R x → RelatorCertificate R y →
      RelatorCertificate R (x * y)
  | inv {x : FreeGroup α} : RelatorCertificate R x → RelatorCertificate R x⁻¹
  | conjugate (g r : FreeGroup α) (hr : r ∈ R) :
      RelatorCertificate R (g * r * g⁻¹)

/-- Number of relator-cell leaves in an algebraic certificate. -/
def RelatorCertificate.area {R : List (FreeGroup α)} {w : FreeGroup α}
    (c : RelatorCertificate R w) : Nat :=
  match c with
  | .one => 0
  | .relator _ _ => 1
  | .mul c₁ c₂ => c₁.area + c₂.area
  | .inv c => c.area
  | .conjugate _ _ _ => 1

/-- Flatten a certificate into the finite sequence of relator factors it uses. -/
def RelatorCertificate.factors {R : List (FreeGroup α)} {w : FreeGroup α}
    (c : RelatorCertificate R w) : List (FreeGroup α) :=
  match c with
  | .one => []
  | .relator r _ => [r]
  | .mul c₁ c₂ => c₁.factors ++ c₂.factors
  | .inv c => (c.factors.map fun r => r⁻¹).reverse
  | .conjugate g r _ => [g * r * g⁻¹]

theorem RelatorCertificate.factors_prod {R : List (FreeGroup α)}
    {w : FreeGroup α} (c : RelatorCertificate R w) : c.factors.prod = w := by
  induction c with
  | one => simp [RelatorCertificate.factors]
  | relator r hr => simp [RelatorCertificate.factors]
  | mul c₁ c₂ ih₁ ih₂ =>
    simp [RelatorCertificate.factors, List.prod_append, ih₁, ih₂]
  | inv c ih =>
    simp only [RelatorCertificate.factors]
    rw [← List.prod_inv_reverse, ih]
  | conjugate g r hr => simp [RelatorCertificate.factors]

theorem RelatorCertificate.factors_length {R : List (FreeGroup α)}
    {w : FreeGroup α} (c : RelatorCertificate R w) : c.factors.length = c.area := by
  induction c with
  | one => simp [RelatorCertificate.factors, RelatorCertificate.area]
  | relator r hr => simp [RelatorCertificate.factors, RelatorCertificate.area]
  | mul c₁ c₂ ih₁ ih₂ =>
    simp [RelatorCertificate.factors, RelatorCertificate.area, List.length_append,
      ih₁, ih₂]
  | inv c ih =>
    simp [RelatorCertificate.factors, RelatorCertificate.area, ih]
  | conjugate g r hr => simp [RelatorCertificate.factors, RelatorCertificate.area]

/-- A factor in a relator certificate is a conjugate of a defining relator. -/
def IsRelatorConjugate (R : List (FreeGroup α)) (x : FreeGroup α) : Prop :=
  ∃ g r, r ∈ R ∧ x = g * r * g⁻¹

theorem RelatorCertificate.factors_are_conjugates {R : List (FreeGroup α)}
    (hinv : ∀ r ∈ R, r⁻¹ ∈ R) {w : FreeGroup α}
    (c : RelatorCertificate R w) :
    ∀ x ∈ c.factors, IsRelatorConjugate R x := by
  induction c with
  | one => simp [RelatorCertificate.factors]
  | relator r hr =>
    intro x hx
    simp only [RelatorCertificate.factors, List.mem_singleton] at hx
    subst x
    exact ⟨1, r, hr, by simp⟩
  | mul c₁ c₂ ih₁ ih₂ =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih₁ x hx
    · exact ih₂ x hx
  | inv c ih =>
    intro x hx
    simp only [RelatorCertificate.factors, List.mem_reverse, List.mem_map] at hx
    rcases hx with ⟨y, hy, hxy⟩
    subst x
    obtain ⟨g, r, hr, hEq⟩ := ih y hy
    refine ⟨g, r⁻¹, hinv r hr, ?_⟩
    rw [hEq]
    simp [mul_assoc]
  | conjugate g r hr =>
    intro x hx
    simp only [RelatorCertificate.factors, List.mem_singleton] at hx
    subst x
    exact ⟨g, r, hr, rfl⟩

theorem RelatorCertificate.eq_one_of_area_eq_zero {R : List (FreeGroup α)}
    {w : FreeGroup α} (c : RelatorCertificate R w) (h : c.area = 0) : w = 1 := by
  induction c with
  | one => rfl
  | relator r hr => simp [RelatorCertificate.area] at h
  | mul c₁ c₂ ih₁ ih₂ =>
    simp only [RelatorCertificate.area] at h
    have h₁ : c₁.area = 0 := by omega
    have h₂ : c₂.area = 0 := by omega
    rw [ih₁ h₁, ih₂ h₂]
    simp
  | inv c ih =>
    simp only [RelatorCertificate.area] at h
    rw [ih h]
    simp
  | conjugate g r hr => simp [RelatorCertificate.area] at h

theorem RelatorCertificate.area_pos_of_ne_one {R : List (FreeGroup α)}
    {w : FreeGroup α} (c : RelatorCertificate R w) (hw : w ≠ 1) :
    0 < c.area := by
  by_contra hpos
  have hzero : c.area = 0 := Nat.eq_zero_of_not_pos hpos
  exact hw (c.eq_one_of_area_eq_zero hzero)

theorem RelatorCertificate.mem_normalClosure {R : List (FreeGroup α)} {w : FreeGroup α}
    (h : RelatorCertificate R w) : w ∈ Subgroup.normalClosure (relationSet R) := by
  induction h with
  | one => exact one_mem _
  | relator r hr => exact Subgroup.subset_normalClosure hr
  | mul _ _ hx hy => exact mul_mem hx hy
  | inv _ hx => exact inv_mem hx
  | conjugate g r hr =>
    have hr' : r ∈ Subgroup.normalClosure (relationSet R) :=
      Subgroup.subset_normalClosure hr
    exact Subgroup.Normal.conj_mem Subgroup.normalClosure_normal r hr' g

theorem RelatorCertificate.nonempty_of_mem_normalClosure {R : List (FreeGroup α)}
    {w : FreeGroup α} (h : w ∈ Subgroup.normalClosure (relationSet R)) :
    Nonempty (RelatorCertificate R w) := by
  change w ∈ Subgroup.closure (Group.conjugatesOfSet (relationSet R)) at h
  apply Subgroup.closure_induction
    (p := fun x _ => Nonempty (RelatorCertificate R x))
  · intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨r, hr, hconj⟩
    rcases isConj_iff.mp hconj with ⟨g, hg⟩
    have hr' : r ∈ R := hr
    rw [← hg]
    exact ⟨RelatorCertificate.conjugate g r hr'⟩
  · exact ⟨RelatorCertificate.one⟩
  · intro x y hx hy ihx ihy
    exact ⟨RelatorCertificate.mul ihx.some ihy.some⟩
  · intro x hx ihx
    exact ⟨RelatorCertificate.inv ihx.some⟩
  · exact h

theorem RelatorCertificate.exists_minimum_area {R : List (FreeGroup α)}
    {w : FreeGroup α} (h : Nonempty (RelatorCertificate R w)) :
    ∃ c : RelatorCertificate R w, ∀ d : RelatorCertificate R w, c.area ≤ d.area := by
  classical
  rcases h with ⟨c₀⟩
  let p : Nat → Prop := fun n => ∃ c : RelatorCertificate R w, c.area = n
  have hp : ∃ n, p n := ⟨c₀.area, c₀, rfl⟩
  let n := Nat.find hp
  obtain ⟨c, hc⟩ := Nat.find_spec hp
  refine ⟨c, fun d => ?_⟩
  rw [hc]
  exact Nat.find_min' hp ⟨d, rfl⟩

theorem relatorCertificate_iff_quotient_eq_one {R : List (FreeGroup α)}
    {w : FreeGroup α} :
    Nonempty (RelatorCertificate R w) ↔ PresentedGroup.mk (relationSet R) w = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  exact ⟨fun h => h.elim RelatorCertificate.mem_normalClosure,
    RelatorCertificate.nonempty_of_mem_normalClosure⟩

end GreendlingerDehn
