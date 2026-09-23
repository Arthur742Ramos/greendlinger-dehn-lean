import SmallCancellation.Curvature
import SmallCancellation.CyclicDehn

namespace GreendlingerDehn

universe u

variable {α : Type u} [DecidableEq α]

/-- Local boundary data for an internal relator face of an arc-reduced disk
diagram. Each boundary arc is listed as a word, together with the cyclic
position at which it occurs on the relator. -/
structure InternalFacePieceData {α : Type u} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (f : CurvatureFace) where
  relator : FreeGroup α
  relator_mem : relator ∈ P.relators
  arcs : List (Word α)
  sides_eq : f.sides = arcs.length
  perimeter_eq : relator.toWord.length = (arcs.map List.length).sum
  perimeter_pos : 0 < relator.toWord.length
  pieces : ∀ u ∈ arcs, IsPiece P.relators u
  cyclicPieces : ∀ u ∈ arcs, ∃ arcPre arcSuf tail,
    relator.toWord = arcPre ++ arcSuf ∧ arcSuf ++ arcPre = u ++ tail

/-- A C'(1/6) piece on a relator boundary has length strictly below one sixth
of that relator, directly from the finite piece predicate. -/
theorem cPrimeSix_piece_lt_perimeter {R : List (FreeGroup α)}
    (hc : CPrimeSix R) {u : Word α} (hpiece : IsPiece R u)
    {perimeter : Nat}
    (hprefix : ∃ r ∈ R, ∃ tail, r.toWord = u ++ tail ∧
      r.toWord.length = perimeter) :
    6 * u.length < perimeter := by
  obtain ⟨r, hr, tail, hword, hlength⟩ := hprefix
  have h := hc hpiece hr ⟨tail, hword⟩
  rw [hlength] at h
  exact h

/-- A complete partition of a nonempty relator boundary into C'(1/6) pieces
has at least seven arcs. This is the interior-face side-count used by the
curvature argument once a disk diagram supplies its arc decomposition. -/
theorem cPrimeSix_fullBoundary_has_seven_arcs
    {R : List (FreeGroup α)} (hc : CPrimeSix R)
    {arcs : List (Word α)} {perimeter : Nat}
    (hperimeter : perimeter = (arcs.map List.length).sum)
    (hperimeter_pos : 0 < perimeter)
    (hpieces : ∀ u ∈ arcs, IsPiece R u)
    (hprefix : ∀ u ∈ arcs, ∃ r ∈ R, ∃ tail,
      r.toWord = u ++ tail ∧ r.toWord.length = perimeter) :
    7 ≤ arcs.length := by
  have hnonempty : (arcs.map List.length) ≠ [] := by
    intro hnil
    simp [hnil] at hperimeter
    omega
  have hpiecebounds : ∀ p ∈ arcs.map List.length, 6 * p < perimeter := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨u, hu, rfl⟩
    exact cPrimeSix_piece_lt_perimeter hc (hpieces u hu) (hprefix u hu)
  have hsum := six_mul_sum_lt_length_mul hnonempty hpiecebounds
  rw [← hperimeter] at hsum
  simp only [List.length_map] at hsum
  have hlength : 6 < arcs.length := by
    by_contra hnot
    have hle : arcs.length ≤ 6 := Nat.le_of_not_gt hnot
    have hmul : arcs.length * perimeter ≤ 6 * perimeter :=
      Nat.mul_le_mul_right perimeter hle
    omega
  exact Nat.succ_le_of_lt hlength

/-- The internal face data and C'(1/6) derive the side-count field used by the
curvature model. -/
theorem InternalFacePieceData.seven_sides
    {α : Type u} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {f : CurvatureFace}
    (d : InternalFacePieceData P f) (hc : CPrimeSix P.relators) :
    7 ≤ f.sides := by
  have hprefix : ∀ u ∈ d.arcs, ∃ r ∈ P.relators, ∃ tail,
      r.toWord = u ++ tail ∧ r.toWord.length = d.relator.toWord.length := by
    intro u hu
    obtain ⟨arcPre, arcSuf, tail, hcut, hocc⟩ := d.cyclicPieces u hu
    obtain ⟨r, hr, hrot⟩ := P.rotateRelator d.relator_mem hcut
    refine ⟨r, hr, tail, hrot.trans hocc, ?_⟩
    rw [hrot, hcut]
    simp [List.length_append, Nat.add_comm]
  have hseven := cPrimeSix_fullBoundary_has_seven_arcs hc d.perimeter_eq
    d.perimeter_pos d.pieces hprefix
  rw [d.sides_eq]
  exact hseven

/-- C'(1/6) piece arcs covering an internal relator face force at least seven
sides, and the angle cap then makes that face's curvature nonpositive. -/
theorem CurvatureFace.curvature_nonpos_of_cPrimeSix_pieceBoundary
    {α : Type u} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α)
    (hc : CPrimeSix P.relators)
    (f : CurvatureFace)
    (hkind : f.kind = .internal)
    {relator : FreeGroup α} (hrelator : relator ∈ P.relators)
    {arcs : List (Word α)}
    (hsides : f.sides = arcs.length)
    (hperimeter : relator.toWord.length = (arcs.map List.length).sum)
    (hperimeter_pos : 0 < relator.toWord.length)
    (hpieces : ∀ u ∈ arcs, IsPiece P.relators u)
    (hcyclicPieces : ∀ u ∈ arcs, ∃ arcPre arcSuf tail,
      relator.toWord = arcPre ++ arcSuf ∧ arcSuf ++ arcPre = u ++ tail) :
    f.curvature ≤ 0 := by
  have hprefix : ∀ u ∈ arcs, ∃ r ∈ P.relators, ∃ tail,
      r.toWord = u ++ tail ∧ r.toWord.length = relator.toWord.length := by
    intro u hu
    obtain ⟨arcPre, arcSuf, tail, hcut, hocc⟩ := hcyclicPieces u hu
    obtain ⟨r, hr, hrot⟩ := P.rotateRelator hrelator hcut
    refine ⟨r, hr, tail, hrot.trans hocc, ?_⟩
    rw [hrot, hcut]
    simp [List.length_append, Nat.add_comm]
  have hseven := cPrimeSix_fullBoundary_has_seven_arcs hc hperimeter
    hperimeter_pos hpieces hprefix
  have hfaceSides : 7 ≤ f.sides := by rw [hsides]; exact hseven
  have hcorners := f.internal_exteriorCorners hkind
  have hbound := f.curvature_le_local_bound
  simp only [CurvatureFace.exteriorCorners] at hbound
  rw [hcorners] at hbound
  have hsidesQ : (7 : ℚ) ≤ (f.sides : ℚ) := by exact_mod_cast hfaceSides
  nlinarith [hbound]

/-- For a finite face family with Gauss--Bonnet accounting, actual C'(1/6)
piece data on every internal face discharges the internal side-count premise
and forces a small shell. External-face incidence bounds and the disk
accounting identities remain explicit fields of the curvature model. -/
theorem positive_curvature_forces_small_shell_of_pieceData
    {α : Type u} [Fintype α] [DecidableEq α]
    {F : Type*} [Fintype F]
    (P : SymmetrizedPresentation α)
    (hc : CPrimeSix P.relators)
    (faces : F → CurvatureFace)
    (accounting : DiskCurvatureAccounting faces)
    (internalData : ∀ f, (faces f).kind = .internal →
      InternalFacePieceData P (faces f)) :
    ∃ f : F, (faces f).IsSmallShell := by
  let adjustedFaces : F → CurvatureFace := fun f =>
    { faces f with
      internal_sides := fun hkind => (internalData f hkind).seven_sides hc }
  have hcurvature : ∀ f, (adjustedFaces f).curvature = (faces f).curvature := by
    intro f
    rfl
  have htotal : ∑ f : F, (adjustedFaces f).curvature = 2 := by
    calc
      (∑ f : F, (adjustedFaces f).curvature) =
          ∑ f : F, (faces f).curvature :=
        Finset.sum_congr rfl (fun f _ => hcurvature f)
      _ = 2 := accounting.total_curvature_eq_two
  obtain ⟨f, hsmall⟩ := positive_curvature_forces_small_shell adjustedFaces htotal
  refine ⟨f, ?_⟩
  simpa [adjustedFaces] using hsmall

/-- If the internal arcs of a shell are pieces and each occurs as a prefix of
a relator of the shell's perimeter, C'(1/6) and the three-arc bound force the
exterior arc to exceed half the relator boundary. -/
theorem cPrimeSix_shell_exterior_longer_than_half
    {R : List (FreeGroup α)} (hc : CPrimeSix R)
    {arcs : List (Word α)} {perimeter exterior : Nat}
    (hperimeter : perimeter = exterior + (arcs.map List.length).sum)
    (hperimeter_pos : 0 < perimeter)
    (hcount : arcs.length ≤ 3)
    (hpieces : ∀ u ∈ arcs, IsPiece R u)
    (hprefix : ∀ u ∈ arcs, ∃ r ∈ R, ∃ tail,
      r.toWord = u ++ tail ∧ r.toWord.length = perimeter) :
    perimeter < 2 * exterior := by
  apply shell_exterior_longer_than_half hperimeter hperimeter_pos ?_ ?_
  · simpa using hcount
  · intro p hp
    rcases List.mem_map.mp hp with ⟨u, hu, rfl⟩
    exact cPrimeSix_piece_lt_perimeter hc (hpieces u hu) (hprefix u hu)

/-- A shell decomposition into an exterior arc and at most three C'(1/6)
internal pieces supplies the exact cyclic redex searched for by the executable
Dehn procedure. The diagrammatic theorem still has to construct such a shell. -/
theorem cPrimeSix_shell_gives_cyclicRedex
    {R : List (FreeGroup α)} (hc : CPrimeSix R)
    {w : FreeGroup α} {pre suf : Word α}
    {relator : FreeGroup α} {exterior : Word α}
    {arcs : List (Word α)}
    (hsplit : w.toWord = pre ++ suf)
    (hrotation : (FreeGroup.mk (suf ++ pre)).toWord =
      exterior ++ arcs.flatten)
    (hrelator : relator ∈ R)
    (hboundary : relator.toWord = exterior ++ arcs.flatten)
    (hperimeter_pos : 0 < relator.toWord.length)
    (hcount : arcs.length ≤ 3)
    (hpieces : ∀ u ∈ arcs, IsPiece R u)
    (hprefix : ∀ u ∈ arcs, ∃ r ∈ R, ∃ tail,
      r.toWord = u ++ tail ∧ r.toWord.length = relator.toWord.length) :
    ∃ c, IsCyclicRedex R w c := by
  have hperimeter : relator.toWord.length = exterior.length +
      (arcs.map List.length).sum := by
    rw [hboundary]
    simp
  have hlong : relator.toWord.length < 2 * exterior.length :=
    cPrimeSix_shell_exterior_longer_than_half hc hperimeter hperimeter_pos
      hcount hpieces hprefix
  refine ⟨⟨pre, suf, ⟨[], exterior, arcs.flatten, relator, arcs.flatten⟩⟩,
    ?_⟩
  refine ⟨hsplit, ?_⟩
  refine ⟨?_, hrelator, hboundary, ?_⟩
  · simpa using hrotation
  · change exterior.length > (arcs.flatten).length
    rw [hboundary, List.length_append] at hlong
    rw [List.length_flatten] at hlong
    rw [List.length_flatten]
    omega

/-- In a `SymmetrizedPresentation`, the piece-side prefix bounds needed by the
shell estimate follow from the shell face's cyclic boundary positions and
iterated relator-rotation closure. -/
theorem cPrimeSix_shell_gives_cyclicRedex_of_cyclicPieces
    {α : Type u} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α)
    (hc : CPrimeSix P.relators)
    {w : FreeGroup α} {pre suf : Word α}
    {relator : FreeGroup α} {exterior : Word α}
    {arcs : List (Word α)}
    (hsplit : w.toWord = pre ++ suf)
    (hrotation : (FreeGroup.mk (suf ++ pre)).toWord =
      exterior ++ arcs.flatten)
    (hrelator : relator ∈ P.relators)
    (hboundary : relator.toWord = exterior ++ arcs.flatten)
    (hperimeter_pos : 0 < relator.toWord.length)
    (hcount : arcs.length ≤ 3)
    (hpieces : ∀ u ∈ arcs, IsPiece P.relators u)
    (hcyclicPieces : ∀ u ∈ arcs, ∃ arcPre arcSuf tail,
      relator.toWord = arcPre ++ arcSuf ∧ arcSuf ++ arcPre = u ++ tail) :
    ∃ c, IsCyclicRedex P.relators w c := by
  have hprefix : ∀ u ∈ arcs, ∃ r ∈ P.relators, ∃ tail,
      r.toWord = u ++ tail ∧ r.toWord.length = relator.toWord.length := by
    intro u hu
    obtain ⟨arcPre, arcSuf, tail, hcut, hocc⟩ := hcyclicPieces u hu
    obtain ⟨r, hr, hrot⟩ := P.rotateRelator hrelator hcut
    refine ⟨r, hr, tail, hrot.trans hocc, ?_⟩
    rw [hrot, hcut]
    simp [List.length_append, Nat.add_comm]
  exact cPrimeSix_shell_gives_cyclicRedex hc hsplit hrotation hrelator
    hboundary hperimeter_pos hcount hpieces hprefix

/-- The boundary information associated with a shell face in a curvature
profile. The arc count is tied to the face's shell index; all word and piece
data needed for the executable reducer is explicit. -/
structure ShellRedexData {α : Type u} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) (w : FreeGroup α) (f : CurvatureFace) where
  pre : Word α
  suf : Word α
  relator : FreeGroup α
  exterior : Word α
  arcs : List (Word α)
  boundarySplit : w.toWord = pre ++ suf
  rotatedBoundary : (FreeGroup.mk (suf ++ pre)).toWord = exterior ++ arcs.flatten
  relator_mem : relator ∈ P.relators
  relatorBoundary : relator.toWord = exterior ++ arcs.flatten
  perimeter_pos : 0 < relator.toWord.length
  arcCount : ∀ i, f.kind = .shell i → arcs.length = i
  pieces : ∀ u ∈ arcs, IsPiece P.relators u
  cyclicPieces : ∀ u ∈ arcs, ∃ arcPre arcSuf tail,
    relator.toWord = arcPre ++ arcSuf ∧ arcSuf ++ arcPre = u ++ tail

/-- A small-shell boundary profile yields the cyclic redex used by the Dehn
reducer. -/
theorem ShellRedexData.cyclic_redex
    {α : Type u} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α} {f : CurvatureFace}
    (d : ShellRedexData P w f)
    (hc : CPrimeSix P.relators)
    (hsmall : f.IsSmallShell) :
    ∃ c, IsCyclicRedex P.relators w c := by
  obtain ⟨i, hkind, hi⟩ := hsmall
  have hcount : d.arcs.length ≤ 3 := by
    rw [d.arcCount i hkind]
    exact hi
  exact cPrimeSix_shell_gives_cyclicRedex_of_cyclicPieces P hc
    d.boundarySplit d.rotatedBoundary d.relator_mem d.relatorBoundary
    d.perimeter_pos hcount d.pieces d.cyclicPieces

/-- The finite curvature and face-boundary profile implies a Dehn redex. This
is the composed local Greendlinger argument; constructing this profile from a
nullity certificate is the remaining van Kampen diagram theorem. -/
theorem positive_curvature_forces_cyclicRedex_of_curvature_and_shell_data
    {α : Type u} [Fintype α] [DecidableEq α]
    {F : Type*} [Fintype F]
    (P : SymmetrizedPresentation α)
    (hc : CPrimeSix P.relators)
    (w : FreeGroup α)
    (faces : F → CurvatureFace)
    (accounting : DiskCurvatureAccounting faces)
    (internalData : ∀ f, (faces f).kind = .internal →
      InternalFacePieceData P (faces f))
    (shellData : ∀ f, (faces f).IsSmallShell →
      ShellRedexData P w (faces f)) :
    ∃ c, IsCyclicRedex P.relators w c := by
  obtain ⟨f, hsmall⟩ := positive_curvature_forces_small_shell_of_pieceData
    P hc faces accounting internalData
  exact (shellData f hsmall).cyclic_redex hc hsmall

end GreendlingerDehn
