import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GreendlingerDehn

/-- The local type of a face in the angle proof of the shell lemma. -/
inductive CurvatureFaceKind where
  | internal
  | external
  | shell (internalArcs : Nat)
  deriving DecidableEq

/-- A corner carries its actual angle (normalized by π) together with the
local angle bound supplied by the diagram geometry. -/
inductive FaceCorner where
  | exterior (angle : ℚ) (angle_le : angle ≤ 1 / 2)
  | interior (angle : ℚ) (angle_le : angle ≤ 2 / 3)
  deriving DecidableEq

/-- Angle value carried by one diagram corner. -/
def FaceCorner.angle : FaceCorner → ℚ
  | .exterior a _ => a
  | .interior a _ => a

/-- Number of exterior corners in a finite cyclic list of corners. -/
def FaceCorner.exteriorCount : List FaceCorner → Nat
  | [] => 0
  | .exterior _ _ :: cs => FaceCorner.exteriorCount cs + 1
  | .interior _ _ :: cs => FaceCorner.exteriorCount cs

/-- Number of interior corners in a finite cyclic list of corners. -/
def FaceCorner.interiorCount : List FaceCorner → Nat
  | [] => 0
  | .exterior _ _ :: cs => FaceCorner.interiorCount cs
  | .interior _ _ :: cs => FaceCorner.interiorCount cs + 1

/-- Sum of the actual normalized corner angles around one face. -/
def FaceCorner.angleSum : List FaceCorner → ℚ
  | [] => 0
  | c :: cs => FaceCorner.angle c + FaceCorner.angleSum cs

/-- Sum of the local angle caps around one face. -/
def FaceCorner.capSum : List FaceCorner → ℚ
  | [] => 0
  | .exterior _ _ :: cs => 1 / 2 + FaceCorner.capSum cs
  | .interior _ _ :: cs => 2 / 3 + FaceCorner.capSum cs

theorem FaceCorner.counts_eq_length (cs : List FaceCorner) :
    FaceCorner.exteriorCount cs + FaceCorner.interiorCount cs = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      cases c with
      | exterior a h => simp [FaceCorner.exteriorCount, FaceCorner.interiorCount]; omega
      | interior a h => simp [FaceCorner.exteriorCount, FaceCorner.interiorCount]; omega

theorem FaceCorner.angleSum_le_capSum (cs : List FaceCorner) :
    FaceCorner.angleSum cs ≤ FaceCorner.capSum cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      cases c with
      | exterior a h =>
          simp only [FaceCorner.angleSum, FaceCorner.angle, FaceCorner.capSum]
          exact add_le_add h ih
      | interior a h =>
          simp only [FaceCorner.angleSum, FaceCorner.angle, FaceCorner.capSum]
          exact add_le_add h ih

theorem FaceCorner.capSum_eq_counts (cs : List FaceCorner) :
    FaceCorner.capSum cs = (FaceCorner.exteriorCount cs : ℚ) * (1 / 2 : ℚ) +
      (FaceCorner.interiorCount cs : ℚ) * (2 / 3 : ℚ) := by
  induction cs with
  | nil => norm_num [FaceCorner.capSum, FaceCorner.exteriorCount,
      FaceCorner.interiorCount]
  | cons c cs ih =>
      cases c with
      | exterior a h =>
          simp [FaceCorner.capSum, FaceCorner.exteriorCount,
            FaceCorner.interiorCount, ih]; ring
      | interior a h =>
          simp [FaceCorner.capSum, FaceCorner.exteriorCount,
            FaceCorner.interiorCount, ih]; ring
/-- Finite local data used in the standard C'(1/6) angle count. Angles are
measured in units of π. The actual corner angles and their local caps determine
the face angle sum; the remaining fields record incidence facts supplied by an
arc-reduced disk diagram. -/
structure CurvatureFace where
  kind : CurvatureFaceKind
  corners : List FaceCorner
  internal_sides : kind = .internal → 7 ≤ corners.length
  internal_exteriorCorners : kind = .internal → FaceCorner.exteriorCount corners = 0
  external_sides : kind = .external → 4 ≤ corners.length
  external_small_exteriorCorners : kind = .external → corners.length ≤ 5 →
    4 ≤ FaceCorner.exteriorCount corners
  external_large_exteriorCorners : kind = .external → 6 ≤ corners.length →
    1 ≤ FaceCorner.exteriorCount corners
  shell_sides : ∀ i, kind = .shell i → corners.length = i + 1
  shell_exteriorCorners : ∀ i, kind = .shell i → FaceCorner.exteriorCount corners = 2

def CurvatureFace.sides (f : CurvatureFace) : Nat := f.corners.length

def CurvatureFace.exteriorCorners (f : CurvatureFace) : Nat :=
  FaceCorner.exteriorCount f.corners

def CurvatureFace.angleSum (f : CurvatureFace) : ℚ :=
  FaceCorner.angleSum f.corners

theorem CurvatureFace.exteriorCorners_le_sides (f : CurvatureFace) :
    f.exteriorCorners ≤ f.sides := by
  change FaceCorner.exteriorCount f.corners ≤ f.corners.length
  rw [← FaceCorner.counts_eq_length f.corners]
  exact Nat.le_add_right _ _

theorem CurvatureFace.angleCap (f : CurvatureFace) :
    f.angleSum ≤ (f.exteriorCorners : ℚ) * (1 / 2 : ℚ) +
      ((f.sides - f.exteriorCorners : Nat) : ℚ) * (2 / 3 : ℚ) := by
  have hcounts := FaceCorner.counts_eq_length f.corners
  have hsub : f.corners.length - FaceCorner.exteriorCount f.corners =
      FaceCorner.interiorCount f.corners := by omega
  change FaceCorner.angleSum f.corners ≤
    (FaceCorner.exteriorCount f.corners : ℚ) * (1 / 2 : ℚ) +
      (((f.corners.length - FaceCorner.exteriorCount f.corners : Nat) : ℚ)) *
        (2 / 3 : ℚ)
  calc
    FaceCorner.angleSum f.corners ≤ FaceCorner.capSum f.corners :=
      FaceCorner.angleSum_le_capSum f.corners
    _ = (FaceCorner.exteriorCount f.corners : ℚ) * (1 / 2 : ℚ) +
        (FaceCorner.interiorCount f.corners : ℚ) * (2 / 3 : ℚ) :=
      FaceCorner.capSum_eq_counts f.corners
    _ = _ := by rw [hsub]

/-- Combinatorial curvature of one face, in units of π. -/
def CurvatureFace.curvature (f : CurvatureFace) : ℚ :=
  f.angleSum - ((f.sides : ℚ) - 2)

/-- Finite accounting data for the combinatorial Gauss--Bonnet calculation on a
disk decomposition. `angle_count` says interior vertices contribute angle sum
2 and boundary vertices 1; `side_count` says interior edges have two incident
face sides and boundary edges one. The diagram development must establish these
identities and Euler's formula from its actual incidence structure. -/
structure DiskCurvatureAccounting {F : Type*} [Fintype F]
    (faces : F → CurvatureFace) where
  vertices : Nat
  edges : Nat
  boundary : Nat
  euler : vertices + Fintype.card F = edges + 1
  angle_count : (∑ f : F, (faces f).angleSum) + boundary =
    (2 : ℚ) * vertices
  side_count : (∑ f : F, ((faces f).sides : ℚ)) + boundary =
    (2 : ℚ) * edges

/-- The local vertex and edge counts together with disk Euler characteristic
give total face curvature 2. -/
theorem DiskCurvatureAccounting.total_curvature_eq_two
    {F : Type*} [Fintype F] {faces : F → CurvatureFace}
    (a : DiskCurvatureAccounting faces) :
    ∑ f : F, (faces f).curvature = 2 := by
  classical
  simp only [CurvatureFace.curvature, Finset.sum_sub_distrib]
  have hangle : (∑ f : F, (faces f).angleSum) =
      (2 : ℚ) * a.vertices - a.boundary := by
    linarith [a.angle_count]
  have hside : (∑ f : F, ((faces f).sides : ℚ)) =
      (2 : ℚ) * a.edges - a.boundary := by
    linarith [a.side_count]
  have hconst : (∑ _f : F, (2 : ℚ)) = (Fintype.card F : ℚ) * 2 := by
    simp
  have heuler : (a.vertices : ℚ) + (Fintype.card F : ℚ) =
      (a.edges : ℚ) + 1 := by
    exact_mod_cast a.euler
  rw [hangle, hside, hconst]
  nlinarith [heuler]

/-- Curvature accounting for a planar cell map with cut vertices and
semi-exterior vertices. `linkEuler` is the sum of the Euler characteristics
of the finite vertex links. For links that are disjoint unions of paths and
cycles it is nonnegative; a disconnected link contributes at least 2. The
two incidence equations below are the link-count identities
`Σ χ(link(v)) = 2E - Σ sides`. The angle inequality allows a semi-exterior
vertex to contribute angle sum 0, which is at least `2 - χ(link(v))`. -/
structure LinkCurvatureAccounting {F : Type*} [Fintype F]
    (faces : F → CurvatureFace) where
  vertices : Nat
  edges : Nat
  linkEuler : Nat
  /-- The finite complex has Euler characteristic at least one. Extra
  spherical components increase this lower bound and do not hurt curvature. -/
  euler : edges + 1 ≤ vertices + Fintype.card F
  angle_count_lower :
    (2 : ℚ) * vertices ≤ (∑ f : F, (faces f).angleSum) + linkEuler
  side_count :
    (∑ f : F, ((faces f).sides : ℚ)) + linkEuler = (2 : ℚ) * edges

/-- Ordinary disk accounting is the special case where every vertex link is
one circle or one interval, so the total link Euler characteristic is the
boundary vertex count. -/
def DiskCurvatureAccounting.toLinkCurvatureAccounting
    {F : Type*} [Fintype F] {faces : F → CurvatureFace}
    (a : DiskCurvatureAccounting faces) : LinkCurvatureAccounting faces where
  vertices := a.vertices
  edges := a.edges
  linkEuler := a.boundary
  euler := a.euler.symm.le
  angle_count_lower := by linarith [a.angle_count]
  side_count := a.side_count

/-- The generalized link accounting gives total face curvature at least 2;
semi-exterior vertices can only increase this lower bound. -/
theorem LinkCurvatureAccounting.total_curvature_ge_two
    {F : Type*} [Fintype F] {faces : F → CurvatureFace}
    (a : LinkCurvatureAccounting faces) :
    (2 : ℚ) ≤ ∑ f : F, (faces f).curvature := by
  classical
  simp only [CurvatureFace.curvature, Finset.sum_sub_distrib]
  have heuler : (a.edges : ℚ) + 1 ≤
      (a.vertices : ℚ) + (Fintype.card F : ℚ) := by
    exact_mod_cast a.euler
  have hangle : (2 : ℚ) * a.vertices ≤
      (∑ f : F, (faces f).angleSum) + a.linkEuler := a.angle_count_lower
  have hside : (∑ f : F, ((faces f).sides : ℚ)) + a.linkEuler =
      (2 : ℚ) * a.edges := a.side_count
  have hconst : (∑ _f : F, (2 : ℚ)) = (Fintype.card F : ℚ) * 2 := by simp
  rw [hconst]
  linarith [hangle, hside, heuler]

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
      simp only [CurvatureFace.sides, CurvatureFace.exteriorCorners] at hbound
      rw [hcorners] at hbound
      have hsidesQ : (7 : ℚ) ≤ (f.corners.length : ℚ) := by exact_mod_cast hsides
      nlinarith
  | external =>
      have hsides := f.external_sides hk
      have hbound := f.curvature_le_local_bound
      simp only [CurvatureFace.sides, CurvatureFace.exteriorCorners] at hbound
      by_cases hsmallSides : f.sides ≤ 5
      · have hc := f.external_small_exteriorCorners hk hsmallSides
        have hsidesQ : (4 : ℚ) ≤ (f.corners.length : ℚ) := by exact_mod_cast hsides
        have hcQ : (4 : ℚ) ≤ (FaceCorner.exteriorCount f.corners : ℚ) := by
          exact_mod_cast hc
        nlinarith
      · have hsidesLarge : 6 ≤ f.sides :=
          Nat.succ_le_of_lt (not_le.mp hsmallSides)
        have hc := f.external_large_exteriorCorners hk hsidesLarge
        have hsidesQ : (6 : ℚ) ≤ (f.corners.length : ℚ) := by
          exact_mod_cast hsidesLarge
        have hcQ : (1 : ℚ) ≤ (FaceCorner.exteriorCount f.corners : ℚ) := by
          exact_mod_cast hc
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
      simp only [CurvatureFace.sides, CurvatureFace.exteriorCorners] at hbound
      have hsides' : f.corners.length = i + 1 := hsides
      have hcorners' : FaceCorner.exteriorCount f.corners = 2 := hcorners
      rw [hsides', hcorners'] at hbound
      have hiQ : (4 : ℚ) ≤ (i : ℚ) := by exact_mod_cast hlarge
      norm_num [Nat.cast_add] at hbound
      nlinarith [hbound]

/-- If all faces outside the designated shell cases have nonpositive
curvature, positive total curvature forces a small shell. -/
theorem positive_curvature_forces_small_shell_of_nonpos {F : Type*} [Fintype F]
    (faces : F → CurvatureFace)
    (htotal : ∑ f : F, (faces f).curvature = 2)
    (hface_nonpos : ∀ f, ¬ (faces f).IsSmallShell → (faces f).curvature ≤ 0) :
    ∃ f : F, (faces f).IsSmallShell := by
  by_contra hnone
  have hnonpos_all : ∀ f : F, (faces f).curvature ≤ 0 := by
    intro f
    apply hface_nonpos
    intro hsmall
    exact hnone ⟨f, hsmall⟩
  have hsum : (∑ f : F, (faces f).curvature) ≤ 0 := by
    calc
      (∑ f : F, (faces f).curvature) ≤ ∑ _f : F, (0 : ℚ) :=
        Finset.sum_le_sum (fun f _ => hnonpos_all f)
      _ = 0 := by simp
  rw [htotal] at hsum
  norm_num at hsum

/-- The local curvature estimates force a small shell whenever the total
curvature is positive. For disk diagrams, the total-curvature identity is the
Euler characteristic calculation; the diagram-to-local-data construction is a
separate theorem. -/
theorem positive_curvature_forces_small_shell {F : Type*} [Fintype F]
    (faces : F → CurvatureFace)
    (htotal : ∑ f : F, (faces f).curvature = 2) :
    ∃ f : F, (faces f).IsSmallShell := by
  apply positive_curvature_forces_small_shell_of_nonpos faces htotal
  intro f hsmall
  exact (faces f).curvature_nonpos_of_not_smallShell hsmall

/-- Any total curvature at least 2 forces a small shell when every other face
has nonpositive curvature. -/
theorem positive_curvature_forces_small_shell_of_ge_two
    {F : Type*} [Fintype F] (faces : F → CurvatureFace)
    (htotal : (2 : ℚ) ≤ ∑ f : F, (faces f).curvature)
    (hface_nonpos : ∀ f, ¬ (faces f).IsSmallShell →
      (faces f).curvature ≤ 0) :
    ∃ f : F, (faces f).IsSmallShell := by
  by_contra hnone
  have hnonpos_all : ∀ f : F, (faces f).curvature ≤ 0 := by
    intro f
    apply hface_nonpos
    intro hsmall
    exact hnone ⟨f, hsmall⟩
  have hsum : (∑ f : F, (faces f).curvature) ≤ 0 := by
    calc
      (∑ f : F, (faces f).curvature) ≤ ∑ _f : F, (0 : ℚ) :=
        Finset.sum_le_sum (fun f _ => hnonpos_all f)
      _ = 0 := by simp
  linarith

/-- Combining the finite Gauss--Bonnet accounting with the local angle bounds
forces a face with at most three internal arcs. -/
theorem positive_curvature_forces_small_shell_of_accounting
    {F : Type*} [Fintype F] (faces : F → CurvatureFace)
    (a : DiskCurvatureAccounting faces) :
    ∃ f : F, (faces f).IsSmallShell :=
  positive_curvature_forces_small_shell faces a.total_curvature_eq_two

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
