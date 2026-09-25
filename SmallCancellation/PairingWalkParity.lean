import SmallCancellation.PairingComponents

/-!
# Parity in the union of two occurrence pairings

Edges in the stem/cancellation occurrence graph come in two colors. A simple
path alternates colors: an occurrence cannot have two different partners in
the same partial pairing. This file isolates that fact so orientation parity
can be used when building the local incidence structure of a folded diagram.
-/

namespace GreendlingerDehn

universe u

variable {V : Type u} [DecidableEq V]

/-- The color of an edge in the union graph: `true` means the left pairing.
If both pairings contain the same edge, the left pairing is chosen. -/
def pairingEdgeColor (P Q : PartialOccurrencePairing V) {v w : V}
    (_h : (twoPairingGraph P Q).Adj v w) : Bool :=
  decide (P.partner v = some w)

/-- Read the left/right colors along a walk in the union of two pairings. -/
def pairingWalkColors (P Q : PartialOccurrencePairing V) :
    {v w : V} → (twoPairingGraph P Q).Walk v w → List Bool
  | _, _, .nil => []
  | _, _, @SimpleGraph.Walk.cons _ _ v _x w h tail =>
      pairingEdgeColor P Q h :: pairingWalkColors P Q tail

/-- A color word is alternating when each consecutive pair differs. -/
def PairingColorsAlternate : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≠ b ∧ PairingColorsAlternate (b :: rest)

theorem PairingColorsAlternate.length_mod_two
    {colors : List Bool} (halt : PairingColorsAlternate colors)
    {first last : Bool} (hfirst : colors.head? = some first)
    (hlast : colors.getLast? = some last) :
    colors.length % 2 = if first = last then 1 else 0 := by
  induction colors generalizing first last with
  | nil => simp at hfirst
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hfirst hlast
          subst first
          subst last
          simp
      | cons b tail =>
          simp only [PairingColorsAlternate] at halt
          have hfirst' : first = a := by simpa using hfirst.symm
          have hlast' : (b :: tail).getLast? = some last := by
            simpa using hlast
          have htail := ih halt.2 rfl hlast'
          have hlength : (a :: b :: tail).length = (b :: tail).length + 1 := by
            simp
          rw [hlength, Nat.add_mod, htail, hfirst']
          cases a <;> cases b <;> cases last <;> simp_all

theorem PairingColorsAlternate.odd_of_false_ends
    {colors : List Bool} (halt : PairingColorsAlternate colors)
    (hfirst : colors.head? = some false)
    (hlast : colors.getLast? = some false) :
    Odd colors.length := by
  have hmod := halt.length_mod_two hfirst hlast
  rw [Nat.odd_iff]
  simpa using hmod

theorem PairingColorsAlternate.even_of_different_ends
    {colors : List Bool} (halt : PairingColorsAlternate colors)
    (hfirst : colors.head? = some false)
    (hlast : colors.getLast? = some true) :
    Even colors.length := by
  have hmod := halt.length_mod_two hfirst hlast
  have hzero : colors.length % 2 = 0 := by simpa using hmod
  exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hzero)

theorem PairingColorsAlternate.odd_of_true_ends
    {colors : List Bool} (halt : PairingColorsAlternate colors)
    (hfirst : colors.head? = some true)
    (hlast : colors.getLast? = some true) :
    Odd colors.length := by
  have hmod := halt.length_mod_two hfirst hlast
  have hone : colors.length % 2 = 1 := by simpa using hmod
  exact Nat.odd_iff.mpr hone

theorem PairingColorsAlternate.even_of_true_false_ends
    {colors : List Bool} (halt : PairingColorsAlternate colors)
    (hfirst : colors.head? = some true)
    (hlast : colors.getLast? = some false) :
    Even colors.length := by
  have hmod := halt.length_mod_two hfirst hlast
  have hzero : colors.length % 2 = 0 := by simpa using hmod
  exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hzero)

private theorem pairingEdgeColor_true_iff (P Q : PartialOccurrencePairing V)
    {v w : V} (_h : (twoPairingGraph P Q).Adj v w) :
    pairingEdgeColor P Q _h = true ↔ P.partner v = some w := by
  simp [pairingEdgeColor]

private theorem pairingEdgeColor_false_iff (P Q : PartialOccurrencePairing V)
    {v w : V} (h : (twoPairingGraph P Q).Adj v w) :
    pairingEdgeColor P Q h = false ↔
      P.partner v ≠ some w ∧ Q.partner v = some w := by
  constructor
  · intro hcolor
    have hnot : P.partner v ≠ some w := by
      intro hp
      have := (pairingEdgeColor_true_iff P Q h).2 hp
      rw [hcolor] at this
      contradiction
    rcases h with hp | hq
    · exact (hnot hp).elim
    · exact ⟨hnot, hq⟩
  · rintro ⟨hp, hq⟩
    simp [pairingEdgeColor, hp]

private theorem pairingEdgeColor_symm (P Q : PartialOccurrencePairing V)
    {v w : V} (h : (twoPairingGraph P Q).Adj v w) :
    pairingEdgeColor P Q h = pairingEdgeColor P Q h.symm := by
  unfold pairingEdgeColor
  by_cases hp : P.partner v = some w
  · have hp' : P.partner w = some v := P.partner_symm hp
    simp [hp, hp']
  · have hp' : P.partner w ≠ some v := by
      intro h'
      exact hp (P.partner_symm h')
    simp [hp, hp']

theorem pairingWalkColors_length (P Q : PartialOccurrencePairing V)
    {v w : V} (p : (twoPairingGraph P Q).Walk v w) :
    (pairingWalkColors P Q p).length = p.length := by
  induction p with
  | nil => rfl
  | @cons v x w h tail ih => simp [pairingWalkColors, ih]

theorem pairingWalkColors_append (P Q : PartialOccurrencePairing V)
    {u v w : V} (p : (twoPairingGraph P Q).Walk u v)
    (q : (twoPairingGraph P Q).Walk v w) :
    pairingWalkColors P Q (p.append q) =
      pairingWalkColors P Q p ++ pairingWalkColors P Q q := by
  induction p with
  | nil => rfl
  | @cons u v' mid h p ih => simp [pairingWalkColors, ih]

theorem pairingWalkColors_reverse (P Q : PartialOccurrencePairing V)
    {u v : V} (p : (twoPairingGraph P Q).Walk u v) :
    pairingWalkColors P Q p.reverse = (pairingWalkColors P Q p).reverse := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.reverse_cons, pairingWalkColors_append, ih]
      simp only [pairingWalkColors, List.reverse_cons]
      rw [← pairingEdgeColor_symm P Q h]

theorem pairingWalkColors_alternate_of_isPath
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w) (hp : p.IsPath) :
    PairingColorsAlternate (pairingWalkColors P Q p) := by
  induction p with
  | nil => trivial
  | @cons v x w h tail ih =>
      cases tail with
      | nil => trivial
      | @cons x y w h₂ rest =>
          have htailPath : (SimpleGraph.Walk.cons h₂ rest).IsPath :=
            SimpleGraph.Walk.IsPath.of_cons hp
          have huNot : v ∉ (SimpleGraph.Walk.cons h₂ rest).support := by
            have hn := hp.support_nodup
            simp only [SimpleGraph.Walk.support_cons] at hn
            exact (List.nodup_cons.mp hn).1
          have hvy : v ≠ y := by
            intro heq
            have hymem : y ∈ (SimpleGraph.Walk.cons h₂ rest).support := by
              cases rest <;> simp [SimpleGraph.Walk.support]
            exact huNot (heq ▸ hymem)
          have hcolors_ne : pairingEdgeColor P Q h ≠ pairingEdgeColor P Q h₂ := by
            by_cases hc : pairingEdgeColor P Q h = true
            · have hleft₁ : P.partner v = some x :=
                (pairingEdgeColor_true_iff P Q h).1 hc
              have hleft₁' : P.partner x = some v := P.partner_symm hleft₁
              by_cases hc₂ : pairingEdgeColor P Q h₂ = true
              · have hleft₂ : P.partner x = some y :=
                  (pairingEdgeColor_true_iff P Q h₂).1 hc₂
                have : y = v := Option.some.inj (hleft₂.symm.trans hleft₁')
                intro _
                exact (hvy this.symm).elim
              · intro heq
                exact hc₂ (heq ▸ hc)
            · by_cases hc₂ : pairingEdgeColor P Q h₂ = true
              · intro heq
                exact hc (heq.symm ▸ hc₂)
              · have hright₁ : Q.partner v = some x :=
                  ((pairingEdgeColor_false_iff P Q h).1 (by
                    cases hcolor : pairingEdgeColor P Q h with
                    | false => rfl
                    | true => exact (hc hcolor).elim)).2
                have hright₁' : Q.partner x = some v := Q.partner_symm hright₁
                have hright₂ : Q.partner x = some y :=
                  ((pairingEdgeColor_false_iff P Q h₂).1 (by
                    cases hcolor : pairingEdgeColor P Q h₂ with
                    | false => rfl
                    | true => exact (hc₂ hcolor).elim)).2
                have : y = v := Option.some.inj (hright₂.symm.trans hright₁')
                intro _
                exact (hvy this.symm).elim
          have htail := ih htailPath
          change pairingEdgeColor P Q h ≠ pairingEdgeColor P Q h₂ ∧
            PairingColorsAlternate
              (pairingEdgeColor P Q h₂ :: pairingWalkColors P Q rest)
          exact ⟨hcolors_ne, htail⟩

theorem pairingWalkColors_head_false_of_leftUnpaired
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w)
    (hstart : P.partner v = none) (hnonempty : 0 < p.length) :
    (pairingWalkColors P Q p).head? = some false := by
  cases p with
  | nil => simp at hnonempty
  | @cons v x w h tail =>
      have hleft : P.partner v ≠ some x := by
        intro hx
        rw [hstart] at hx
        cases hx
      have hright : Q.partner v = some x := by
        rcases h with hp | hq
        · exact (hleft hp).elim
        · exact hq
      have hcolor : pairingEdgeColor P Q h = false :=
        (pairingEdgeColor_false_iff P Q h).2 ⟨hleft, hright⟩
      simp [pairingWalkColors, hcolor]

theorem pairingWalkColors_head_true_of_rightUnpaired
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w)
    (hstart : Q.partner v = none) (hnonempty : 0 < p.length) :
    (pairingWalkColors P Q p).head? = some true := by
  cases p with
  | nil => simp at hnonempty
  | @cons v x w h tail =>
      have hright : Q.partner v ≠ some x := by
        intro hx
        rw [hstart] at hx
        cases hx
      have hleft : P.partner v = some x := by
        rcases h with hp | hq
        · exact hp
        · exact (hright hq).elim
      have hcolor : pairingEdgeColor P Q h = true :=
        (pairingEdgeColor_true_iff P Q h).2 hleft
      simp [pairingWalkColors, hcolor]

theorem pairingWalkColors_last_false_of_leftUnpaired
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w)
    (hend : P.partner w = none) (hnonempty : 0 < p.length) :
    (pairingWalkColors P Q p).getLast? = some false := by
  have hrev := pairingWalkColors_head_false_of_leftUnpaired P Q p.reverse
    hend (by simpa using hnonempty)
  rw [pairingWalkColors_reverse] at hrev
  simpa using hrev

theorem pairingWalkColors_last_true_of_rightUnpaired
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w)
    (hend : Q.partner w = none) (hnonempty : 0 < p.length) :
    (pairingWalkColors P Q p).getLast? = some true := by
  have hrev := pairingWalkColors_head_true_of_rightUnpaired P Q p.reverse
    hend (by simpa using hnonempty)
  rw [pairingWalkColors_reverse] at hrev
  simpa using hrev

theorem pairingWalk_length_odd_of_leftUnpaired_endpoints
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w) (hp : p.IsPath) (hvw : v ≠ w)
    (hstart : P.partner v = none) (hend : P.partner w = none) :
    Odd p.length := by
  have hlen : 0 < p.length := by
    by_contra h
    have hz : p.length = 0 := Nat.eq_zero_of_not_pos h
    exact hvw (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hfirst := pairingWalkColors_head_false_of_leftUnpaired P Q p hstart hlen
  have hlast := pairingWalkColors_last_false_of_leftUnpaired P Q p hend hlen
  have hodd := (pairingWalkColors_alternate_of_isPath P Q p hp).odd_of_false_ends
    hfirst hlast
  rw [pairingWalkColors_length P Q p] at hodd
  exact hodd

theorem pairingWalk_length_odd_of_rightUnpaired_endpoints
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w) (hp : p.IsPath) (hvw : v ≠ w)
    (hstart : Q.partner v = none) (hend : Q.partner w = none) :
    Odd p.length := by
  have hlen : 0 < p.length := by
    by_contra h
    have hz : p.length = 0 := Nat.eq_zero_of_not_pos h
    exact hvw (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hfirst := pairingWalkColors_head_true_of_rightUnpaired P Q p hstart hlen
  have hlast := pairingWalkColors_last_true_of_rightUnpaired P Q p hend hlen
  have hodd := (pairingWalkColors_alternate_of_isPath P Q p hp).odd_of_true_ends
    hfirst hlast
  rw [pairingWalkColors_length P Q p] at hodd
  exact hodd

theorem pairingWalk_length_even_of_leftRightUnpaired_endpoints
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w) (hp : p.IsPath) (hvw : v ≠ w)
    (hstart : P.partner v = none) (hend : Q.partner w = none) :
    Even p.length := by
  have hlen : 0 < p.length := by
    by_contra h
    have hz : p.length = 0 := Nat.eq_zero_of_not_pos h
    exact hvw (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hfirst := pairingWalkColors_head_false_of_leftUnpaired P Q p hstart hlen
  have hlast := pairingWalkColors_last_true_of_rightUnpaired P Q p hend hlen
  have heven := (pairingWalkColors_alternate_of_isPath P Q p hp).even_of_different_ends
    hfirst hlast
  rw [pairingWalkColors_length P Q p] at heven
  exact heven

theorem pairingWalk_length_even_of_rightLeftUnpaired_endpoints
    (P Q : PartialOccurrencePairing V) {v w : V}
    (p : (twoPairingGraph P Q).Walk v w) (hp : p.IsPath) (hvw : v ≠ w)
    (hstart : Q.partner v = none) (hend : P.partner w = none) :
    Even p.length := by
  have hlen : 0 < p.length := by
    by_contra h
    have hz : p.length = 0 := Nat.eq_zero_of_not_pos h
    exact hvw (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hfirst := pairingWalkColors_head_true_of_rightUnpaired P Q p hstart hlen
  have hlast := pairingWalkColors_last_false_of_leftUnpaired P Q p hend hlen
  have halt := pairingWalkColors_alternate_of_isPath P Q p hp
  have heven := halt.even_of_true_false_ends hfirst hlast
  rw [pairingWalkColors_length P Q p] at heven
  exact heven

end GreendlingerDehn
