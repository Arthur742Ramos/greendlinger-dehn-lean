import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Tactic.Group
import SmallCancellation.Words
import SmallCancellation.Certificates
import SmallCancellation.Cancellation
import SmallCancellation.CertificateCancellation

namespace GreendlingerDehn

theorem exists_append_singleton_of_ne_nil {α : Type*} {xs : List α}
    (h : xs ≠ []) : ∃ pre x, xs = pre ++ [x] := by
  induction xs using List.reverseRecOn with
  | nil => simp at h
  | append_singleton pre x ih => exact ⟨pre, x, rfl⟩

theorem mk_singleton_inverseLetter {α : Type*} (a : Letter α) :
    FreeGroup.mk [inverseLetter a] = (FreeGroup.mk [a])⁻¹ := by
  simp [FreeGroup.inv_mk, FreeGroup.invRev, inverseLetter]

theorem reduced_prefix_of_append_singleton {α : Type*} [DecidableEq α]
    {pre : Word α} {x : Letter α}
    (h : FreeGroup.IsReduced (pre ++ [x])) : FreeGroup.IsReduced pre := by
  exact h.left_of_append

theorem toWord_mk_reduced {α : Type*} [DecidableEq α]
    {xs : Word α} (h : FreeGroup.IsReduced xs) :
    (FreeGroup.mk xs).toWord = xs := h.reduce_eq

theorem RelatorConjugateWitness.rawWord_length_eq {α : Type*} [DecidableEq α]
    {R : List (FreeGroup α)} {factor : FreeGroup α}
    (d : RelatorConjugateWitness R factor) :
    d.rawWord.length = 2 * d.conjugator.toWord.length + d.relator.toWord.length := by
  simp [RelatorConjugateWitness.rawWord, FreeGroup.toWord_inv,
    FreeGroup.invRev_length, List.length_append]
  omega

theorem reducedAdjacent_of_ne_inverse {α : Type*} {x y : Letter α}
    (h : x ≠ inverseLetter y) : x.1 = y.1 → x.2 = y.2 := by
  intro hgen
  by_contra hsign
  apply h
  cases x with
  | mk xgen xsign =>
    cases y with
    | mk ygen ysign =>
      simp_all [inverseLetter]

@[simp]
theorem inverseLetter_inverseLetter {α : Type*} (x : Letter α) :
    inverseLetter (inverseLetter x) = x := by
  cases x
  simp [inverseLetter]

@[simp]
theorem head?_invRev_word {α : Type*} (xs : Word α) :
    (FreeGroup.invRev xs).head? = xs.getLast?.map inverseLetter := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre a ih =>
    rw [FreeGroup.invRev_append]
    simp [FreeGroup.invRev, inverseLetter,
      List.getLast?_append_of_ne_nil pre (by simp : ([a] : List (Letter α)) ≠ [])]

theorem RelatorConjugateWitness.shorten_of_leftJoinCancellation
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {factor : FreeGroup α}
    (d : RelatorConjugateWitness P.relators factor)
    {pre : Word α} {x a : Letter α} {tail : Word α}
    (hconj : d.conjugator.toWord = pre ++ [x])
    (hrel : d.relator.toWord = a :: tail)
    (hcancels : x = inverseLetter a) :
    ∃ d' : RelatorConjugateWitness P.relators factor,
      d'.conjugator.toWord.length < d.conjugator.toWord.length := by
  obtain ⟨r', hr', hrot⟩ := P.rotateRelator d.relator_mem (pre := [a])
    (suf := tail) (by simpa using hrel)
  let g₀ : FreeGroup α := FreeGroup.mk pre
  let a₀ : FreeGroup α := FreeGroup.mk [a]
  let x₀ : FreeGroup α := FreeGroup.mk [x]
  let t₀ : FreeGroup α := FreeGroup.mk tail
  have hx₀ : x₀ = a₀⁻¹ := by
    dsimp [x₀, a₀]
    rw [hcancels]
    exact mk_singleton_inverseLetter a
  have hrel₀ : d.relator = a₀ * t₀ := by
    calc
      d.relator = FreeGroup.mk d.relator.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (a :: tail) := by rw [hrel]
      _ = a₀ * t₀ := by dsimp [a₀, t₀]
  have hrot₀ : r' = t₀ * a₀ := by
    calc
      r' = FreeGroup.mk r'.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (tail ++ [a]) := by rw [hrot]
      _ = t₀ * a₀ := by dsimp [a₀, t₀]
  have hg₀ : d.conjugator = g₀ * x₀ := by
    calc
      d.conjugator = FreeGroup.mk d.conjugator.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (pre ++ [x]) := by rw [hconj]
      _ = g₀ * x₀ := by dsimp [g₀, x₀]
  have hrotate : x₀ * d.relator * x₀⁻¹ = r' := by
    calc
      x₀ * d.relator * x₀⁻¹ = a₀⁻¹ * (a₀ * t₀) * a₀ := by
        rw [hx₀, hrel₀]
        simp
      _ = t₀ * a₀ := by group
      _ = r' := hrot₀.symm
  have hfactor : factor = g₀ * r' * g₀⁻¹ := by
    calc
      factor = d.conjugator * d.relator * d.conjugator⁻¹ := d.factor_eq
      _ = (g₀ * x₀) * d.relator * (g₀ * x₀)⁻¹ := by rw [hg₀]
      _ = g₀ * (x₀ * d.relator * x₀⁻¹) * g₀⁻¹ := by group
      _ = g₀ * r' * g₀⁻¹ := by rw [hrotate]
  have hpreReduced : FreeGroup.IsReduced pre := by
    apply reduced_prefix_of_append_singleton
    rw [← hconj]
    exact FreeGroup.isReduced_toWord
  have hshort : (FreeGroup.mk pre).toWord.length < d.conjugator.toWord.length := by
    rw [toWord_mk_reduced hpreReduced, hconj]
    simp
  exact ⟨⟨g₀, r', hr', hfactor⟩, by simpa [g₀] using hshort⟩

theorem RelatorConjugateWitness.shorten_of_rightJoinCancellation
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {factor : FreeGroup α}
    (d : RelatorConjugateWitness P.relators factor)
    {pre : Word α} {x a : Letter α} {tail : Word α}
    (hconj : d.conjugator.toWord = pre ++ [x])
    (hrel : d.relator.toWord = tail ++ [a])
    (hcancels : a = x) :
    ∃ d' : RelatorConjugateWitness P.relators factor,
      d'.conjugator.toWord.length < d.conjugator.toWord.length := by
  obtain ⟨r', hr', hrot⟩ := P.rotateRelator d.relator_mem (pre := tail)
    (suf := [a]) (by simpa using hrel)
  let g₀ : FreeGroup α := FreeGroup.mk pre
  let a₀ : FreeGroup α := FreeGroup.mk [a]
  let x₀ : FreeGroup α := FreeGroup.mk [x]
  let t₀ : FreeGroup α := FreeGroup.mk tail
  have hxa₀ : x₀ = a₀ := by
    dsimp [x₀, a₀]
    rw [hcancels]
  have hrel₀ : d.relator = t₀ * a₀ := by
    calc
      d.relator = FreeGroup.mk d.relator.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (tail ++ [a]) := by rw [hrel]
      _ = t₀ * a₀ := by dsimp [a₀, t₀]
  have hrot₀ : r' = a₀ * t₀ := by
    calc
      r' = FreeGroup.mk r'.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk ([a] ++ tail) := by rw [hrot]
      _ = a₀ * t₀ := by dsimp [a₀, t₀]
  have hg₀ : d.conjugator = g₀ * x₀ := by
    calc
      d.conjugator = FreeGroup.mk d.conjugator.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (pre ++ [x]) := by rw [hconj]
      _ = g₀ * x₀ := by dsimp [g₀, x₀]
  have hrotate : x₀ * d.relator * x₀⁻¹ = r' := by
    calc
      x₀ * d.relator * x₀⁻¹ = a₀ * (t₀ * a₀) * a₀⁻¹ := by
        rw [hxa₀, hrel₀]
      _ = a₀ * t₀ := by group
      _ = r' := hrot₀.symm
  have hfactor : factor = g₀ * r' * g₀⁻¹ := by
    calc
      factor = d.conjugator * d.relator * d.conjugator⁻¹ := d.factor_eq
      _ = (g₀ * x₀) * d.relator * (g₀ * x₀)⁻¹ := by rw [hg₀]
      _ = g₀ * (x₀ * d.relator * x₀⁻¹) * g₀⁻¹ := by group
      _ = g₀ * r' * g₀⁻¹ := by rw [hrotate]
  have hpreReduced : FreeGroup.IsReduced pre := by
    apply reduced_prefix_of_append_singleton
    rw [← hconj]
    exact FreeGroup.isReduced_toWord
  have hshort : (FreeGroup.mk pre).toWord.length < d.conjugator.toWord.length := by
    rw [toWord_mk_reduced hpreReduced, hconj]
    simp
  exact ⟨⟨g₀, r', hr', hfactor⟩, by simpa [g₀] using hshort⟩

theorem exists_reducedRelatorConjugateWitness
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) {factor : FreeGroup α}
    (h : IsRelatorConjugate P.relators factor) :
    ∃ d : RelatorConjugateWitness P.relators factor,
      FreeGroup.IsReduced d.rawWord ∧ d.rawWord = factor.toWord ∧
        ∀ e : RelatorConjugateWitness P.relators factor,
          d.conjugator.toWord.length ≤ e.conjugator.toWord.length := by
  classical
  let lengthWitness : Nat → Prop := fun n =>
    ∃ d : RelatorConjugateWitness P.relators factor,
      d.conjugator.toWord.length = n
  have hlengthWitness : ∃ n, lengthWitness n := by
    rcases h with ⟨g, r, hr, hfactor⟩
    exact ⟨(⟨g, r, hr, hfactor⟩ :
      RelatorConjugateWitness P.relators factor).conjugator.toWord.length,
      ⟨⟨g, r, hr, hfactor⟩, rfl⟩⟩
  let minLength := Nat.find hlengthWitness
  obtain ⟨d, hdLength⟩ := Nat.find_spec hlengthWitness
  have hminimum (e : RelatorConjugateWitness P.relators factor) :
      minLength ≤ e.conjugator.toWord.length := by
    exact Nat.find_min' hlengthWitness ⟨e, rfl⟩
  have hleftNoShorter : ∀ pre x a tail,
      d.conjugator.toWord = pre ++ [x] →
      d.relator.toWord = a :: tail → x ≠ inverseLetter a := by
    intro pre x a tail hconj hrel hcancels
    obtain ⟨e, hshort⟩ := d.shorten_of_leftJoinCancellation
      hconj hrel hcancels
    have hle := hminimum e
    omega
  have hrightNoShorter : ∀ tail a x,
      d.relator.toWord = tail ++ [a] →
      x ∈ d.conjugator.toWord.getLast? → a ≠ x := by
    intro tail a x hrel hx hcancels
    have hconj : d.conjugator.toWord = d.conjugator.toWord.dropLast ++ [x] :=
      (List.dropLast_append_getLast? x hx).symm
    obtain ⟨e, hshort⟩ := d.shorten_of_rightJoinCancellation
      hconj hrel hcancels
    have hle := hminimum e
    omega
  have hGR : FreeGroup.IsReduced
      (d.conjugator.toWord ++ d.relator.toWord) := by
    apply List.IsChain.append
    · exact FreeGroup.isReduced_toWord
    · exact FreeGroup.isReduced_toWord
    · intro x hx a ha hgen
      have hne : x ≠ inverseLetter a := by
        intro hcancel
        have hconj : d.conjugator.toWord = d.conjugator.toWord.dropLast ++ [x] :=
            (List.dropLast_append_getLast? x hx).symm
        cases hrelword : d.relator.toWord with
        | nil => simp [hrelword] at ha
        | cons first tail =>
          have ha' : first = a := by simpa [hrelword] using ha
          subst a
          exact hleftNoShorter (d.conjugator.toWord.dropLast) x first tail
            hconj hrelword hcancel
      exact reducedAdjacent_of_ne_inverse hne hgen
  have hRI : FreeGroup.IsReduced
      (d.relator.toWord ++ FreeGroup.invRev d.conjugator.toWord) := by
    apply List.IsChain.append
    · exact FreeGroup.isReduced_toWord
    · have hInv : FreeGroup.IsReduced (FreeGroup.invRev d.conjugator.toWord) := by
        rw [← FreeGroup.toWord_inv]
        exact FreeGroup.isReduced_toWord
      exact hInv
    · intro a ha y hy hgen
      have hne : a ≠ inverseLetter y := by
        intro hcancel
        rw [head?_invRev_word] at hy
        cases hlast : d.conjugator.toWord.getLast? with
        | none => simp [hlast] at hy
        | some x =>
          have hx : x ∈ d.conjugator.toWord.getLast? := by
            rw [hlast]
            simp
          have hy' : y = inverseLetter x := by
            have h' : inverseLetter x = y := by simpa [hlast] using hy
            exact h'.symm
          have hrel : d.relator.toWord.dropLast ++ [a] = d.relator.toWord :=
            List.dropLast_append_getLast? a ha
          have heq : a = x := by simpa [hy'] using hcancel
          exact hrightNoShorter _ _ _ hrel.symm hx heq
      exact reducedAdjacent_of_ne_inverse hne hgen
  have hrNonempty : d.relator.toWord ≠ [] := by
    intro hrnil
    have hrOne : d.relator = 1 := by
      apply FreeGroup.toWord_injective
      rw [hrnil, FreeGroup.toWord_one]
    exact P.nontrivial d.relator d.relator_mem hrOne
  have hrawReduced : FreeGroup.IsReduced d.rawWord := by
    have hcombined := FreeGroup.IsReduced.append_overlap hGR hRI hrNonempty
    simpa [RelatorConjugateWitness.rawWord, FreeGroup.toWord_inv] using hcombined
  have hmk : FreeGroup.mk d.rawWord = FreeGroup.mk factor.toWord := by
    rw [d.mk_rawWord, FreeGroup.mk_toWord]
  have hreduce := FreeGroup.reduce.sound hmk
  have hraw : FreeGroup.reduce d.rawWord = d.rawWord := hrawReduced.reduce_eq
  have hnormal : FreeGroup.reduce factor.toWord = factor.toWord := by
    exact FreeGroup.isReduced_toWord.reduce_eq
  have hrawEq : d.rawWord = factor.toWord := by
    calc
      d.rawWord = FreeGroup.reduce d.rawWord := hraw.symm
      _ = FreeGroup.reduce factor.toWord := hreduce
      _ = factor.toWord := hnormal
  exact ⟨d, hrawReduced, hrawEq, fun e => by
    calc
      d.conjugator.toWord.length = minLength := hdLength
      _ ≤ e.conjugator.toWord.length := hminimum e⟩

/-- A relator-conjugate factor equipped with a cancellation-free literal
lollipop boundary. The label retains the actual relator and conjugator. -/
structure ReducedRelatorBalloonData {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) where
  factor : FreeGroup α
  label : RelatorConjugateWitness P.relators factor
  boundary_reduced : FreeGroup.IsReduced label.rawWord
  boundary_eq_factorWord : label.rawWord = factor.toWord
  conjugator_minimal : ∀ e : RelatorConjugateWitness P.relators factor,
    label.conjugator.toWord.length ≤ e.conjugator.toWord.length

theorem ReducedRelatorBalloonData.factorWord_length_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P) :
    b.factor.toWord.length =
      2 * b.label.conjugator.toWord.length + b.label.relator.toWord.length := by
  rw [← b.boundary_eq_factorWord]
  exact b.label.rawWord_length_eq

noncomputable def ReducedRelatorBalloonData.of_isRelatorConjugate
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) {factor : FreeGroup α}
    (h : IsRelatorConjugate P.relators factor) :
    ReducedRelatorBalloonData P := by
  let hn := exists_reducedRelatorConjugateWitness P h
  exact ⟨factor, Classical.choose hn,
    (Classical.choose_spec hn).1, (Classical.choose_spec hn).2.1,
    (Classical.choose_spec hn).2.2⟩

@[simp]
theorem ReducedRelatorBalloonData.of_isRelatorConjugate_factor
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : SymmetrizedPresentation α) {factor : FreeGroup α}
    (h : IsRelatorConjugate P.relators factor) :
    (ReducedRelatorBalloonData.of_isRelatorConjugate P h).factor = factor := rfl

noncomputable def RelatorFactorBoundarySeed.reducedBalloons
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed P.relators w) : List (ReducedRelatorBalloonData P) :=
  seed.factors.attach.map fun x =>
    ReducedRelatorBalloonData.of_isRelatorConjugate P
      (seed.factor_labels x.1 x.2)

theorem RelatorFactorBoundarySeed.reducedBalloonFactors
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed P.relators w) :
    (seed.reducedBalloons).map ReducedRelatorBalloonData.factor = seed.factors := by
  unfold RelatorFactorBoundarySeed.reducedBalloons
  rw [List.map_map]
  change (seed.factors.attach.map fun x =>
    (ReducedRelatorBalloonData.of_isRelatorConjugate P
      (seed.factor_labels x.1 x.2)).factor) = seed.factors
  simp only [ReducedRelatorBalloonData.of_isRelatorConjugate_factor]
  simp

noncomputable def RelatorFactorBoundarySeed.reducedLiteralBoundary
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed P.relators w) : Word α :=
  ((seed.reducedBalloons).map fun b => b.label.rawWord).flatten

theorem RelatorFactorBoundarySeed.reducedLiteralBoundary_eq_rawProductWord
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed P.relators w) :
    seed.reducedLiteralBoundary = rawProductWord seed.factors := by
  unfold RelatorFactorBoundarySeed.reducedLiteralBoundary rawProductWord
  have hwordMap :
      (seed.reducedBalloons).map (fun b => b.label.rawWord) =
        (seed.reducedBalloons).map (fun b => b.factor.toWord) := by
    apply List.map_congr_left
    intro b hb
    exact b.boundary_eq_factorWord
  have hfactorWordMap :
      (seed.reducedBalloons).map (fun b => b.factor.toWord) =
        seed.factors.map FreeGroup.toWord := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map FreeGroup.toWord) seed.reducedBalloonFactors
  rw [hwordMap, hfactorWordMap]

noncomputable def RelatorFactorBoundarySeed.reducedLiteralBoundaryShape
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed P.relators w) :
    FreeReductionShape seed.reducedLiteralBoundary w.toWord := by
  have hshape := seed.cancellation
  rw [← seed.reducedLiteralBoundary_eq_rawProductWord] at hshape
  exact hshape

theorem RelatorFactorBoundarySeed.reducedLiteralBoundary_length_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : RelatorFactorBoundarySeed P.relators w) :
    seed.reducedLiteralBoundary.length =
      w.toWord.length + 2 * seed.cancellation.cancellationCount := by
  calc
    seed.reducedLiteralBoundary.length = (rawProductWord seed.factors).length :=
      congrArg List.length seed.reducedLiteralBoundary_eq_rawProductWord
    _ = w.toWord.length + 2 * seed.cancellation.cancellationCount :=
      seed.cancellation.length_eq_cancellationCount

end GreendlingerDehn
