import SmallCancellation.Curvature
import SmallCancellation.Shell
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace GreendlingerDehn

/-- Finite incidence data intended to describe a polygonal disk map. Corners
are indexed by vertices and their local positions. Edge incidence, local
vertex degree, boundary counts, and the disk Euler equation are explicit;
the aggregate angle and side ledgers are derived below from these data. This
record does not yet certify cyclic orders/planarity or construct the incidence
data from a nullity certificate. -/
structure DiskMapData (V E F : Type*) [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F] where
  degree : V → Nat
  cornerFace : (Σ v : V, Fin (degree v)) → F
  sideEdge : (Σ v : V, Fin (degree v)) → E
  boundaryVertex : V → Bool
  boundaryEdge : E → Bool
  degree_pos : ∀ v, 0 < degree v
  interior_degree : ∀ v, boundaryVertex v = false → 3 ≤ degree v
  boundary_degree : ∀ v, boundaryVertex v = true → 2 ≤ degree v
  edge_side_count : ∀ e,
    (Finset.univ.filter (fun c : Σ v : V, Fin (degree v) =>
      sideEdge c = e)).card = if boundaryEdge e then 1 else 2
  boundary_counts :
    (Finset.univ.filter (fun v : V => boundaryVertex v = true)).card =
      (Finset.univ.filter (fun e : E => boundaryEdge e = true)).card
  euler : Fintype.card V + Fintype.card F = Fintype.card E + 1

namespace DiskMapData

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq F] (D : DiskMapData V E F)

abbrev Corner := Σ v : V, Fin (D.degree v)

def cornerAngle (c : D.Corner) : ℚ :=
  if D.boundaryVertex c.1 = true then 1 / (D.degree c.1 : ℚ)
  else 2 / (D.degree c.1 : ℚ)

def cornerDatum (c : D.Corner) : FaceCorner := by
  by_cases hb : D.boundaryVertex c.1 = true
  · have hdegree : (2 : ℚ) ≤ (D.degree c.1 : ℚ) := by
      exact_mod_cast D.boundary_degree c.1 hb
    have hpos : (0 : ℚ) < (D.degree c.1 : ℚ) := by positivity
    have hangle : 1 / (D.degree c.1 : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hpos]
      nlinarith
    exact .exterior (D.cornerAngle c) (by simpa [cornerAngle, hb] using hangle)
  · have hdegree : (3 : ℚ) ≤ (D.degree c.1 : ℚ) := by
      exact_mod_cast D.interior_degree c.1 (by simpa using hb)
    have hpos : (0 : ℚ) < (D.degree c.1 : ℚ) := by positivity
    have hangle : 2 / (D.degree c.1 : ℚ) ≤ 2 / 3 := by
      rw [div_le_iff₀ hpos]
      nlinarith
    exact .interior (D.cornerAngle c) (by simpa [cornerAngle, hb] using hangle)

@[simp] theorem cornerDatum_angle (c : D.Corner) :
    (D.cornerDatum c).angle = D.cornerAngle c := by
  unfold cornerDatum
  split <;> rfl

theorem cornerList_angleSum (cs : List D.Corner) :
    FaceCorner.angleSum (cs.map D.cornerDatum) =
      (cs.map D.cornerAngle).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [FaceCorner.angleSum, ih]

def faceCornerSet (f : F) : Finset D.Corner :=
  Finset.univ.filter (fun c => D.cornerFace c = f)

def edgeSideSet (e : E) : Finset D.Corner :=
  Finset.univ.filter (fun c => D.sideEdge c = e)

def faceAngleSum (f : F) : ℚ :=
  ∑ c ∈ D.faceCornerSet f, D.cornerAngle c

def faceSideCount (f : F) : Nat := (D.faceCornerSet f).card

def boundaryVertexCount : Nat :=
  (Finset.univ.filter fun v : V => D.boundaryVertex v = true).card

def boundaryEdgeCount : Nat :=
  (Finset.univ.filter fun e : E => D.boundaryEdge e = true).card

theorem angle_sum_at_vertex (v : V) :
    (∑ i : Fin (D.degree v), D.cornerAngle ⟨v, i⟩) =
      if D.boundaryVertex v = true then 1 else 2 := by
  classical
  have hdegree_pos : (D.degree v : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (D.degree_pos v))
  have hconst : ∀ i : Fin (D.degree v),
      D.cornerAngle ⟨v, i⟩ =
        if D.boundaryVertex v = true then 1 / (D.degree v : ℚ)
        else 2 / (D.degree v : ℚ) := by
    intro i
    simp [cornerAngle]
  calc
    (∑ i : Fin (D.degree v), D.cornerAngle ⟨v, i⟩) =
        ∑ _i : Fin (D.degree v),
          (if D.boundaryVertex v = true then 1 / (D.degree v : ℚ)
          else 2 / (D.degree v : ℚ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hconst i
    _ = (D.degree v : ℚ) *
          (if D.boundaryVertex v = true then 1 / (D.degree v : ℚ)
          else 2 / (D.degree v : ℚ)) := by simp
    _ = if D.boundaryVertex v = true then 1 else 2 := by
      by_cases hb : D.boundaryVertex v = true
      · simp only [if_pos hb]
        field_simp
      · simp only [if_neg hb]
        field_simp

theorem sum_corner_angles_eq_two_vertices_sub_boundary :
    (∑ c : D.Corner, D.cornerAngle c) + D.boundaryVertexCount =
      2 * Fintype.card V := by
  classical
  have hboundary : (D.boundaryVertexCount : ℚ) =
      ∑ v : V, if D.boundaryVertex v = true then 1 else 0 := by
    have hNat : D.boundaryVertexCount =
        ∑ v : V, if D.boundaryVertex v = true then 1 else 0 := by
      unfold boundaryVertexCount
      exact Finset.card_filter (fun v : V => D.boundaryVertex v = true) Finset.univ
    have hcast := congrArg (fun n : Nat => (n : ℚ)) hNat
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hcast
  calc
    (∑ c : D.Corner, D.cornerAngle c) + D.boundaryVertexCount =
        (∑ v : V, if D.boundaryVertex v = true then 1 else 2) +
          (∑ v : V, if D.boundaryVertex v = true then 1 else 0) := by
      rw [Fintype.sum_sigma]
      simp_rw [angle_sum_at_vertex]
      rw [hboundary]
    _ = ∑ v : V,
          ((if D.boundaryVertex v = true then 1 else 2) +
            (if D.boundaryVertex v = true then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ _v : V, (2 : ℚ) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hb : D.boundaryVertex v = true <;> norm_num [hb]
    _ = 2 * Fintype.card V := by simp; ring

theorem sum_face_sides_eq_corner_count :
    (∑ f : F, D.faceSideCount f) = Fintype.card D.Corner := by
  classical
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset D.Corner)) (t := (Finset.univ : Finset F))
    (f := D.cornerFace) (by intro c hc; simp)
  simpa [faceSideCount, faceCornerSet] using hcard.symm

theorem sum_face_angles_eq_corner_angles :
    (∑ f : F, D.faceAngleSum f) = ∑ c : D.Corner, D.cornerAngle c := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset D.Corner) (Finset.univ : Finset F)
      (fun c : D.Corner => D.cornerFace c) (fun c => D.cornerAngle c)
  simpa [faceAngleSum, faceCornerSet, Finset.sum_filter] using h

theorem corner_count_eq_edge_side_sum :
    Fintype.card D.Corner = ∑ e : E, (D.edgeSideSet e).card := by
  classical
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset D.Corner)) (t := (Finset.univ : Finset E))
    (f := D.sideEdge) (by intro c hc; simp)
  simpa [edgeSideSet] using hcard

theorem sum_face_sides_add_boundary_edges_eq_two_edges :
    (∑ f : F, D.faceSideCount f) + D.boundaryEdgeCount =
      2 * Fintype.card E := by
  classical
  rw [D.sum_face_sides_eq_corner_count, D.corner_count_eq_edge_side_sum]
  simp only [boundaryEdgeCount]
  have hsum : (∑ e : E, (D.edgeSideSet e).card) =
      ∑ e : E, if D.boundaryEdge e = true then 1 else 2 := by
    apply Finset.sum_congr rfl
    intro e he
    rw [edgeSideSet, D.edge_side_count]
  rw [hsum]
  have hboundary : D.boundaryEdgeCount =
      ∑ e : E, if D.boundaryEdge e = true then 1 else 0 := by
    unfold boundaryEdgeCount
    exact (Finset.card_filter
      (fun e : E => D.boundaryEdge e = true) Finset.univ)
  calc
    (∑ e : E, if D.boundaryEdge e = true then 1 else 2) +
        D.boundaryEdgeCount =
      (∑ e : E, if D.boundaryEdge e = true then 1 else 2) +
        (∑ e : E, if D.boundaryEdge e = true then 1 else 0) := by rw [hboundary]
    _ = ∑ e : E,
          ((if D.boundaryEdge e = true then 1 else 2) +
            (if D.boundaryEdge e = true then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ _e : E, (2 : Nat) := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hb : D.boundaryEdge e = true <;> norm_num [hb]
    _ = 2 * Fintype.card E := by simp; omega

theorem boundary_counts_cast :
    (D.boundaryVertexCount : ℚ) = (D.boundaryEdgeCount : ℚ) := by
  exact_mod_cast D.boundary_counts

noncomputable def faceCornerList (f : F) : List FaceCorner :=
  (D.faceCornerSet f).toList.map D.cornerDatum

theorem faceCornerList_length (f : F) :
    (D.faceCornerList f).length = D.faceSideCount f := by
  simp [faceCornerList, faceSideCount]

theorem faceCornerList_angleSum (f : F) :
    FaceCorner.angleSum (D.faceCornerList f) = D.faceAngleSum f := by
  classical
  calc
    FaceCorner.angleSum (D.faceCornerList f) =
        ((D.faceCornerSet f).toList.map D.cornerAngle).sum := by
      exact D.cornerList_angleSum (D.faceCornerSet f).toList
    _ = D.faceAngleSum f := by
      symm
      rw [← List.sum_toFinset D.cornerAngle
        (Finset.nodup_toList (D.faceCornerSet f))]
      simp [faceAngleSum]

/-- Local classification facts for the relator faces of a disk map. These are
the face-by-face obligations (piece bounds and exterior-corner topology) that
remain after the map has supplied its actual corner incidences. -/
structure FaceClassification where
  kind : F → CurvatureFaceKind
  internal_sides : ∀ f, kind f = .internal → 7 ≤ D.faceSideCount f
  internal_exteriorCorners : ∀ f, kind f = .internal →
    FaceCorner.exteriorCount (D.faceCornerList f) = 0
  external_sides : ∀ f, kind f = .external → 4 ≤ D.faceSideCount f
  external_small_exteriorCorners : ∀ f, kind f = .external →
    D.faceSideCount f ≤ 5 → 4 ≤ FaceCorner.exteriorCount (D.faceCornerList f)
  external_large_exteriorCorners : ∀ f, kind f = .external →
    6 ≤ D.faceSideCount f → 1 ≤ FaceCorner.exteriorCount (D.faceCornerList f)
  shell_sides : ∀ f i, kind f = .shell i → D.faceSideCount f = i + 1
  shell_exteriorCorners : ∀ f i, kind f = .shell i →
    FaceCorner.exteriorCount (D.faceCornerList f) = 2

noncomputable def FaceClassification.curvatureFace (C : D.FaceClassification) (f : F) :
    CurvatureFace where
  kind := C.kind f
  corners := D.faceCornerList f
  internal_sides := by
    intro h
    rw [D.faceCornerList_length]
    exact C.internal_sides f h
  internal_exteriorCorners := by
    intro h
    exact C.internal_exteriorCorners f h
  external_sides := by
    intro h
    rw [D.faceCornerList_length]
    exact C.external_sides f h
  external_small_exteriorCorners := by
    intro h hsmall
    apply C.external_small_exteriorCorners f h
    simpa [D.faceCornerList_length] using hsmall
  external_large_exteriorCorners := by
    intro h hlarge
    apply C.external_large_exteriorCorners f h
    simpa [D.faceCornerList_length] using hlarge
  shell_sides := by
    intro i h
    rw [D.faceCornerList_length]
    exact C.shell_sides f i h
  shell_exteriorCorners := by
    intro i h
    exact C.shell_exteriorCorners f i h

noncomputable def FaceClassification.to_diskCurvatureAccounting
    (C : D.FaceClassification) :
    DiskCurvatureAccounting (fun f => FaceClassification.curvatureFace (D := D) C f) := by
  classical
  refine ⟨Fintype.card V, Fintype.card E, D.boundaryVertexCount, D.euler,
    ?_, ?_⟩
  · calc
      (∑ f : F, (FaceClassification.curvatureFace (D := D) C f).angleSum) +
          D.boundaryVertexCount =
          (∑ f : F, D.faceAngleSum f) + D.boundaryVertexCount := by
        congr 1
        apply Finset.sum_congr rfl
        intro f hf
        exact D.faceCornerList_angleSum f
      _ = (∑ c : D.Corner, D.cornerAngle c) + D.boundaryVertexCount := by
        rw [D.sum_face_angles_eq_corner_angles]
      _ = 2 * Fintype.card V := D.sum_corner_angles_eq_two_vertices_sub_boundary
  · have hside := D.sum_face_sides_add_boundary_edges_eq_two_edges
    have hsideQ := congrArg (fun n : Nat => (n : ℚ)) hside
    simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hsideQ
    have hboundary := D.boundary_counts_cast
    have hfaces :
        (∑ f : F, ((FaceClassification.curvatureFace (D := D) C f).sides : ℚ)) =
          ∑ f : F, (D.faceSideCount f : ℚ) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact_mod_cast D.faceCornerList_length f
    calc
      (∑ f : F, ((FaceClassification.curvatureFace (D := D) C f).sides : ℚ)) +
          (D.boundaryVertexCount : ℚ) =
          (∑ f : F, (D.faceSideCount f : ℚ)) +
            (D.boundaryEdgeCount : ℚ) := by
        rw [hfaces, hboundary]
      _ = 2 * Fintype.card E := by
        exact hsideQ

/-- With the local face data fixed, an incidence ledger supplies the
Gauss--Bonnet accounting needed by the shell argument. The missing theorem is
still existence of this incidence data and its local face classification for
every nontrivial null word. -/
theorem positive_curvature_forces_cyclicRedex_of_incidenceData
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (hc : CPrimeSix P.relators)
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (D : DiskMapData V E F) (C : D.FaceClassification)
    (w : FreeGroup α)
    (internalData : ∀ f,
      (FaceClassification.curvatureFace (D := D) C f).kind = .internal →
        InternalFacePieceData P (FaceClassification.curvatureFace (D := D) C f))
    (shellData : ∀ f,
      (FaceClassification.curvatureFace (D := D) C f).IsSmallShell →
        ShellRedexData P w (FaceClassification.curvatureFace (D := D) C f)) :
    ∃ c, IsCyclicRedex P.relators w c := by
  exact positive_curvature_forces_cyclicRedex_of_curvature_and_shell_data
    P hc w (fun f => FaceClassification.curvatureFace (D := D) C f)
    (FaceClassification.to_diskCurvatureAccounting (D := D) C)
    internalData shellData

end DiskMapData

end GreendlingerDehn
