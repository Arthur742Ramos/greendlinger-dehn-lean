import SmallCancellation.Curvature
import SmallCancellation.CyclicDehn

namespace GreendlingerDehn

universe u

variable {α : Type u} [DecidableEq α]

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
  omega

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

end GreendlingerDehn
