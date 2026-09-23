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

end GreendlingerDehn
