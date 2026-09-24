import SmallCancellation.Curvature
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp

namespace GreendlingerDehn

/-- The three local link shapes in a planar van Kampen map after arc
reduction: a circle at an interior vertex, one interval at an ordinary
boundary vertex, or a disconnected union of intervals and circles at a
semi-exterior vertex. -/
inductive VertexLinkKind where
  | circle
  | interval
  | disconnected
  deriving DecidableEq

/-- Numerical data for a finite vertex link. `darts` counts edge germs and
`corners` counts incident relator-face corners. A circle has equal counts, an
interval has one more dart, and a disconnected link has Euler characteristic
at least two. -/
structure VertexLinkProfile where
  kind : VertexLinkKind
  corners : Nat
  darts : Nat
  circle_darts : kind = .circle → darts = corners
  circle_min_corners : kind = .circle → 3 ≤ corners
  interval_darts : kind = .interval → darts = corners + 1
  interval_min_corners : kind = .interval → 2 ≤ corners
  disconnected_euler : kind = .disconnected → corners + 2 ≤ darts

namespace VertexLinkProfile

/-- The Euler characteristic of the link, encoded as `darts - corners`. -/
def eulerDefect (p : VertexLinkProfile) : Nat := p.darts - p.corners

theorem corners_le_darts (p : VertexLinkProfile) : p.corners ≤ p.darts := by
  cases hk : p.kind with
  | circle => have h := p.circle_darts hk; omega
  | interval => have h := p.interval_darts hk; omega
  | disconnected => have h := p.disconnected_euler hk; omega

/-- The angle assigned to a corner at this vertex. Semi-exterior corners are
assigned angle zero, which is below both local caps and gives a nonpositive
vertex contribution. -/
def cornerAngle (p : VertexLinkProfile) (_i : Fin p.corners) : ℚ :=
  match p.kind with
  | .circle => 2 / (p.corners : ℚ)
  | .interval => 1 / (p.corners : ℚ)
  | .disconnected => 0

/-- The total prescribed angle around one link. -/
def angleSum (p : VertexLinkProfile) : ℚ :=
  match p.kind with
  | .circle => 2
  | .interval => 1
  | .disconnected => 0

/-- Package a link corner with the corresponding local angle cap used by the
face curvature argument. -/
def cornerDatum (p : VertexLinkProfile) (_i : Fin p.corners) : FaceCorner :=
  if h : p.kind = .circle then
    .interior (2 / (p.corners : ℚ)) (by
      have hcount := p.circle_min_corners h
      have hpos : (0 : ℚ) < (p.corners : ℚ) := by
        exact_mod_cast (show 0 < p.corners by omega)
      have hcountQ : (3 : ℚ) ≤ (p.corners : ℚ) := by exact_mod_cast hcount
      rw [div_le_iff₀ hpos]
      nlinarith [hcountQ])
  else if h : p.kind = .interval then
    .exterior (1 / (p.corners : ℚ)) (by
      have hcount := p.interval_min_corners h
      have hpos : (0 : ℚ) < (p.corners : ℚ) := by
        exact_mod_cast (show 0 < p.corners by omega)
      have hcountQ : (2 : ℚ) ≤ (p.corners : ℚ) := by exact_mod_cast hcount
      rw [div_le_iff₀ hpos]
      nlinarith [hcountQ])
  else .exterior 0 (by norm_num)

@[simp]
theorem cornerDatum_angle (p : VertexLinkProfile) (i : Fin p.corners) :
    (p.cornerDatum i).angle = p.cornerAngle i := by
  cases hk : p.kind <;> simp [cornerDatum, cornerAngle, FaceCorner.angle, hk]

/-- The angles around one vertex sum to 2 on a circle link, 1 on an interval
link, and 0 on a disconnected link. -/
theorem sum_cornerAngle (p : VertexLinkProfile) :
    (∑ i : Fin p.corners, p.cornerAngle i) = p.angleSum := by
  cases hk : p.kind with
  | circle =>
      have hcount := p.circle_min_corners hk
      have hpos : (p.corners : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (show 0 < p.corners by omega))
      simp only [cornerAngle, hk, angleSum, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]
      field_simp
  | interval =>
      have hcount := p.interval_min_corners hk
      have hpos : (p.corners : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (show 0 < p.corners by omega))
      simp only [cornerAngle, hk, angleSum, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]
      field_simp
  | disconnected => simp [cornerAngle, angleSum, hk]

/-- The angle sum plus link Euler characteristic is at least 2 at every
vertex. Disconnected links satisfy the inequality because their Euler
characteristic is at least 2. -/
theorem sum_cornerAngle_add_eulerDefect_ge_two (p : VertexLinkProfile) :
    (2 : ℚ) ≤ (∑ i : Fin p.corners, p.cornerAngle i) + p.eulerDefect := by
  cases hk : p.kind with
  | circle =>
      have hdarts := p.circle_darts hk
      have hdefect : p.eulerDefect = 0 := by
        simp [eulerDefect, hdarts]
      rw [p.sum_cornerAngle, hdefect]
      simp [angleSum, hk]
  | interval =>
      have hdarts := p.interval_darts hk
      have hdefect : p.eulerDefect = 1 := by
        simp [eulerDefect, hdarts]
      rw [p.sum_cornerAngle, hdefect]
      norm_num [angleSum, hk]
  | disconnected =>
      have h := p.disconnected_euler hk
      have hdefect : 2 ≤ p.eulerDefect := by
        dsimp [eulerDefect]
        omega
      rw [p.sum_cornerAngle]
      simp [angleSum, hk]
      exact_mod_cast hdefect

end VertexLinkProfile

theorem FaceCorner.angleSum_map {β : Type*} (f : β → FaceCorner) (xs : List β) :
    FaceCorner.angleSum (xs.map f) =
      (xs.map fun x => (f x).angle).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [FaceCorner.angleSum, ih]

/-- A corner occurrence indexed by its vertex and its position in the link. -/
abbrev LinkCorner {V : Type*} (link : V → VertexLinkProfile) :=
  Σ v : V, Fin (link v).corners

/-- Incidence data for a finite planar cell map that permits cut vertices.
Each face's corner list is tied to the corners in its vertex links. The
`darts_total` field counts the two ends of every edge; Euler characteristic
and the local link shapes then derive the generalized curvature ledger. -/
structure LinkCornerMapData (V E F : Type*) [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq F] where
  link : V → VertexLinkProfile
  cornerFace : LinkCorner link → F
  faces : F → CurvatureFace
  faceCorners : ∀ f, (faces f).corners =
    ((Finset.univ.filter fun c : LinkCorner link => cornerFace c = f).toList).map
      (fun c => (link c.1).cornerDatum c.2)
  euler : Fintype.card V + Fintype.card F = Fintype.card E + 1
  darts_total : (∑ v : V, (link v).darts) = 2 * Fintype.card E

namespace LinkCornerMapData

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq F] (D : LinkCornerMapData V E F)

abbrev Corner := LinkCorner D.link

def faceCornerSet (f : F) : Finset D.Corner :=
  Finset.univ.filter (fun c => D.cornerFace c = f)

def cornerDatum (c : D.Corner) : FaceCorner := (D.link c.1).cornerDatum c.2

def cornerAngle (c : D.Corner) : ℚ := (D.cornerDatum c).angle

def linkEuler : Nat := ∑ v : V, (D.link v).eulerDefect

theorem face_sides_eq (f : F) :
    (D.faces f).sides = (D.faceCornerSet f).card := by
  change (D.faces f).corners.length = (D.faceCornerSet f).card
  rw [D.faceCorners]
  simp [faceCornerSet]

theorem face_angleSum_eq (f : F) :
    (D.faces f).angleSum = ∑ c ∈ D.faceCornerSet f, D.cornerAngle c := by
  classical
  calc
    (D.faces f).angleSum = FaceCorner.angleSum (D.faces f).corners := rfl
    _ = FaceCorner.angleSum
        ((D.faceCornerSet f).toList.map D.cornerDatum) := by
      rw [D.faceCorners]
      rfl
    _ = ((D.faceCornerSet f).toList.map D.cornerAngle).sum := by
      rw [FaceCorner.angleSum_map]
      rfl
    _ = ∑ c ∈ D.faceCornerSet f, D.cornerAngle c := by
      symm
      rw [← List.sum_toFinset D.cornerAngle
        (Finset.nodup_toList (D.faceCornerSet f))]
      simp

theorem sum_face_sides_eq_corner_card :
    (∑ f : F, (D.faces f).sides) = Fintype.card D.Corner := by
  classical
  calc
    (∑ f : F, (D.faces f).sides) =
        ∑ f : F, (D.faceCornerSet f).card := by
      apply Finset.sum_congr rfl
      intro f hf
      exact D.face_sides_eq f
    _ = Fintype.card D.Corner := by
      have hcard := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset D.Corner))
        (t := (Finset.univ : Finset F)) (f := D.cornerFace)
        (by intro c hc; simp)
      simpa [faceCornerSet] using hcard.symm

theorem sum_face_angles_eq_corner_angles :
    (∑ f : F, (D.faces f).angleSum) = ∑ c : D.Corner, D.cornerAngle c := by
  classical
  calc
    (∑ f : F, (D.faces f).angleSum) =
        ∑ f : F, ∑ c ∈ D.faceCornerSet f, D.cornerAngle c := by
      apply Finset.sum_congr rfl
      intro f hf
      exact D.face_angleSum_eq f
    _ = ∑ c : D.Corner, D.cornerAngle c := by
      have h := Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset D.Corner) (Finset.univ : Finset F)
        (fun c : D.Corner => D.cornerFace c) D.cornerAngle
      simpa [faceCornerSet, Finset.sum_filter] using h

theorem vertex_angle_link_lower :
    (2 : ℚ) * Fintype.card V ≤
      (∑ c : D.Corner, D.cornerAngle c) + (D.linkEuler : ℚ) := by
  classical
  have hlocal : (2 : ℚ) * Fintype.card V ≤
      ∑ v : V,
        ((∑ i : Fin (D.link v).corners,
            (D.link v).cornerAngle i) + (D.link v).eulerDefect) := by
    calc
      (2 : ℚ) * Fintype.card V = ∑ _v : V, (2 : ℚ) := by simp [mul_comm]
      _ ≤ ∑ v : V,
          ((∑ i : Fin (D.link v).corners,
              (D.link v).cornerAngle i) + (D.link v).eulerDefect) := by
        apply Finset.sum_le_sum
        intro v hv
        exact D.link v |>.sum_cornerAngle_add_eulerDefect_ge_two
  have hlocal' : (2 : ℚ) * Fintype.card V ≤
      (∑ v : V, ∑ i : Fin (D.link v).corners,
        (D.link v).cornerAngle i) +
        ∑ v : V, ((D.link v).eulerDefect : ℚ) := by
    simpa only [Finset.sum_add_distrib] using hlocal
  have hcorner :
      (∑ c : D.Corner, D.cornerAngle c) =
        ∑ v : V, ∑ i : Fin (D.link v).corners,
          (D.link v).cornerAngle i := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro i hi
    exact (D.link v).cornerDatum_angle i
  have hlinkEulerCast : (D.linkEuler : ℚ) =
      ∑ v : V, ((D.link v).eulerDefect : ℚ) := by
    change (↑(∑ v : V, (D.link v).eulerDefect) : ℚ) =
      ∑ v : V, ((D.link v).eulerDefect : ℚ)
    exact Nat.cast_sum (R := ℚ) (s := (Finset.univ : Finset V))
      (f := fun v => (D.link v).eulerDefect)
  rw [← hcorner, ← hlinkEulerCast] at hlocal'
  exact hlocal'

theorem nat_side_link_eq_two_edges :
    (∑ f : F, (D.faces f).sides) + D.linkEuler =
      2 * Fintype.card E := by
  classical
  have hcard : Fintype.card D.Corner =
      ∑ v : V, (D.link v).corners := by simp [Corner, LinkCorner]
  calc
    (∑ f : F, (D.faces f).sides) + D.linkEuler =
        (∑ v : V, (D.link v).corners) +
          ∑ v : V, (D.link v).eulerDefect := by
      rw [D.sum_face_sides_eq_corner_card, hcard]
      rfl
    _ = ∑ v : V,
          ((D.link v).corners + (D.link v).eulerDefect) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ v : V, (D.link v).darts := by
      apply Finset.sum_congr rfl
      intro v hv
      have hle := (D.link v).corners_le_darts
      simp [VertexLinkProfile.eulerDefect, Nat.add_sub_of_le hle]
    _ = 2 * Fintype.card E := D.darts_total

/-- Actual link data produces the generalized Gauss--Bonnet accounting used
by the shell proof. This formulation includes disconnected vertex links. -/
def toLinkCurvatureAccounting : LinkCurvatureAccounting D.faces where
  vertices := Fintype.card V
  edges := Fintype.card E
  linkEuler := D.linkEuler
  euler := D.euler
  angle_count_lower := by
    rw [D.sum_face_angles_eq_corner_angles]
    exact D.vertex_angle_link_lower
  side_count := by
    have hnat := D.nat_side_link_eq_two_edges
    have hcast := congrArg (fun n : Nat => (n : ℚ)) hnat
    simpa only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using hcast

end LinkCornerMapData

end GreendlingerDehn
