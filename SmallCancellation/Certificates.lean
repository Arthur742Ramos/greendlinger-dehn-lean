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
