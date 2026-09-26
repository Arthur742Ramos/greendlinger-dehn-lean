import SmallCancellation.Words

namespace GreendlingerDehn

universe u

variable {α : Type u}

/-- The inverse of one signed generator letter. -/
def inverseLetter (a : Letter α) : Letter α := (a.1, !a.2)

/-- A parse tree witnessing that a raw word freely reduces to a reduced word.
`bracket` records a noncrossing cancellation pair around an inner null word. -/
inductive FreeReductionShape : Word α → Word α → Type u where
  | empty : FreeReductionShape [] []
  | letter (a : Letter α) : FreeReductionShape [a] [a]
  | append {u u' v v' : Word α} :
      FreeReductionShape u u' → FreeReductionShape v v' →
      FreeReductionShape (u ++ v) (u' ++ v')
  | bracket (a : Letter α) {inner suffix result : Word α} :
      FreeReductionShape inner [] → FreeReductionShape suffix result →
      FreeReductionShape ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix) result

theorem FreeReductionShape.sound {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    FreeGroup.mk raw = FreeGroup.mk reduced := by
  induction h with
  | empty => rfl
  | letter a => rfl
  | append hu hv ihu ihv =>
      simpa only [← FreeGroup.mul_mk] using congrArg₂ (· * ·) ihu ihv
  | bracket a hinner hsuffix ihinner ihsuffix =>
      have hcancel : FreeGroup.mk [a] *
          FreeGroup.mk [inverseLetter a] = 1 := by
        calc
          FreeGroup.mk [a] * FreeGroup.mk [inverseLetter a] =
              FreeGroup.mk ([a] ++ [inverseLetter a]) := FreeGroup.mul_mk
          _ = FreeGroup.mk [] := by
            apply Quot.sound
            change FreeGroup.Red.Step (a :: inverseLetter a :: []) []
            exact FreeGroup.Red.Step.cons_not
          _ = 1 := rfl
      simp only [← FreeGroup.mul_mk, ihinner, ihsuffix,
        ← FreeGroup.one_eq_mk, hcancel, one_mul, mul_one]
structure FreeReductionHead (raw reduced : Word α) (a : Letter α) (out : Word α) where
  pre : Word α
  post : Word α
  word_eq : raw = pre ++ [a] ++ post
  preShape : FreeReductionShape pre []
  postShape : FreeReductionShape post out

noncomputable def FreeReductionShape.extractHead {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    ∀ (a : Letter α) (out : Word α), reduced = a :: out →
      FreeReductionHead raw reduced a out := by
  induction h with
  | empty =>
      intro a out heq
      cases heq
  | letter b =>
      intro a out heq
      injection heq with hba hout
      subst a
      subst out
      exact ⟨[], [], by simp, .empty, .empty⟩
  | append hu hv ihu ihv =>
      rename_i u u' v v'
      intro a out heq
      cases u' with
      | nil =>
          simp only [List.nil_append] at heq
          obtain ⟨pre, post, hvword, hpre, hpost⟩ := ihv a out heq
          refine ⟨u ++ pre, post, ?_, ?_, hpost⟩
          · rw [hvword]
            simp [List.append_assoc]
          · simpa using FreeReductionShape.append hu hpre
      | cons b rest =>
          simp only [List.cons_append] at heq
          injection heq with hba hout
          cases hba
          obtain ⟨pre, post, huword, hpre, hmid⟩ := ihu a rest rfl
          have hpost : FreeReductionShape (post ++ v) out := by
            simpa [hout] using FreeReductionShape.append hmid hv
          refine ⟨pre, post ++ v, ?_, hpre, hpost⟩
          rw [huword]
          simp [List.append_assoc]
  | bracket a hinner hsuffix ihinner ihsuffix =>
      rename_i inner suffix result
      intro b out heq
      obtain ⟨pre, post, hsuffixWord, hpre, hpost⟩ := ihsuffix b out heq
      refine ⟨(([a] ++ inner) ++ [inverseLetter a]) ++ pre, post,
        ?_, ?_, hpost⟩
      · rw [hsuffixWord]
        simp [List.append_assoc]
      · exact FreeReductionShape.bracket a hinner hpre
noncomputable def FreeReductionShape.of_reduce [DecidableEq α] (w : Word α) :
    FreeReductionShape w (FreeGroup.reduce w) := by
  induction w with
  | nil => exact .empty
  | cons a tail ih =>
      cases hred : FreeGroup.reduce tail with
      | nil =>
          have htail : FreeReductionShape tail [] := by
            simpa [hred] using ih
          have hhead : FreeGroup.reduce (a :: tail) = [a] := by
            rw [FreeGroup.reduce.cons, hred]

          rw [hhead]
          simpa using
            (FreeReductionShape.append (FreeReductionShape.letter a) htail)
      | cons b rest =>
          have htail : FreeReductionShape tail (b :: rest) := by
            simpa [hred] using ih
          by_cases hmatch : a.1 = b.1 ∧ a.2 = !b.2
          · obtain ⟨pre, post, hword, hpre, hpost⟩ :=
              htail.extractHead b rest rfl
            have hinverse : b = inverseLetter a := by
              cases a with
              | mk x s =>
                  cases b with
                  | mk y t =>
                      rcases hmatch with ⟨hxy, hsign⟩
                      have hxy' : x = y := by simpa using hxy
                      subst y
                      cases s <;> cases t <;> simp [inverseLetter] at hsign ⊢
            have hhead : FreeGroup.reduce (a :: tail) = rest := by
              rw [FreeGroup.reduce.cons, hred]
              simp [hmatch]
            rw [hhead, hword, hinverse]
            simpa [List.append_assoc] using
              (FreeReductionShape.bracket a hpre hpost)
          · have hhead : FreeGroup.reduce (a :: tail) = a :: b :: rest := by
              rw [FreeGroup.reduce.cons, hred]
              simp [hmatch]
            rw [hhead]
            simpa using
              (FreeReductionShape.append (FreeReductionShape.letter a) htail)
noncomputable def FreeReductionShape.of_mk_eq_one [DecidableEq α] {w : Word α}
    (h : FreeGroup.mk w = 1) : FreeReductionShape w [] := by
  have hword : FreeGroup.mk w = FreeGroup.mk [] := by
    rw [← FreeGroup.one_eq_mk]
    exact h
  have hred : FreeGroup.reduce w = [] := by
    have hnormal := FreeGroup.reduce.sound hword
    simpa using hnormal
  rw [← hred]
  exact FreeReductionShape.of_reduce w

theorem FreeReductionShape.exists_iff_mk_eq_one [DecidableEq α]
    {w : Word α} :
    Nonempty (FreeReductionShape w []) ↔ FreeGroup.mk w = 1 := by
  constructor
  · rintro ⟨h⟩
    exact h.sound.trans rfl
  · exact fun h => ⟨FreeReductionShape.of_mk_eq_one h⟩

/-- One elementary free cancellation in an arbitrary word context. -/
inductive FreeCancellationStep : Word α → Word α → Type u where
  | cancel (pre post : Word α) (a : Letter α) :
      FreeCancellationStep
        (pre ++ [a] ++ [inverseLetter a] ++ post) (pre ++ post)

/-- Transport a cancellation step across equalities of its source and target
words. -/
def FreeCancellationStep.castWords {w₁ w₁' w₂ w₂' : Word α}
    (h₁ : w₁ = w₁') (h₂ : w₂ = w₂')
    (step : FreeCancellationStep w₁ w₂) : FreeCancellationStep w₁' w₂' :=
  h₂ ▸ h₁ ▸ step

/-- A finite sequence of adjacent inverse-letter cancellations. -/
inductive FreeCancellationSequence : Word α → Word α → Type u where
  | refl (w : Word α) : FreeCancellationSequence w w
  | cons {w₁ w₂ w₃ : Word α} : FreeCancellationStep w₁ w₂ →
      FreeCancellationSequence w₂ w₃ → FreeCancellationSequence w₁ w₃

/-- Transport a cancellation sequence across equalities of its endpoint
words. -/
def FreeCancellationSequence.castWords {w₁ w₁' w₂ w₂' : Word α}
    (h₁ : w₁ = w₁') (h₂ : w₂ = w₂')
    (steps : FreeCancellationSequence w₁ w₂) :
    FreeCancellationSequence w₁' w₂' :=
  h₂ ▸ h₁ ▸ steps

@[simp] theorem FreeCancellationSequence.castWords_rfl
    {w₁ w₂ : Word α} (steps : FreeCancellationSequence w₁ w₂) :
    FreeCancellationSequence.castWords rfl rfl steps = steps := rfl


/-- The identity reduction tree for a word. -/
def FreeReductionShape.identity : (w : Word α) → FreeReductionShape w w
  | [] => .empty
  | a :: tail => .append (.letter a) (FreeReductionShape.identity tail)

def FreeCancellationStep.to_shape {w₁ w₂ : Word α}
    (h : FreeCancellationStep w₁ w₂) : FreeReductionShape w₁ w₂ := by
  cases h with
  | cancel pre post a =>
      simpa [List.append_assoc] using
        FreeReductionShape.append (FreeReductionShape.identity pre)
          (FreeReductionShape.append
            (FreeReductionShape.bracket a .empty .empty)
            (FreeReductionShape.identity post))

theorem FreeCancellationStep.sound {w₁ w₂ : Word α}
    (h : FreeCancellationStep w₁ w₂) : FreeGroup.mk w₁ = FreeGroup.mk w₂ :=
  h.to_shape.sound

theorem FreeCancellationStep.length_difference {w₁ w₂ : Word α}
    (h : FreeCancellationStep w₁ w₂) : w₁.length = w₂.length + 2 := by
  cases h with
  | cancel pre post a => simp [List.length_append]; omega

theorem FreeCancellationSequence.sound {w₁ w₂ : Word α}
    (h : FreeCancellationSequence w₁ w₂) : FreeGroup.mk w₁ = FreeGroup.mk w₂ := by
  induction h with
  | refl _ => rfl
  | cons step rest ih => exact step.sound.trans ih

theorem FreeCancellationSequence.length_decomposition {w₁ w₂ : Word α}
    (h : FreeCancellationSequence w₁ w₂) :
    ∃ n, w₁.length = w₂.length + 2 * n := by
  induction h with
  | refl _ => exact ⟨0, by simp⟩
  | cons step rest ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      have hs := step.length_difference
      omega

def FreeCancellationStep.appendRight {w₁ w₂ : Word α}
    (h : FreeCancellationStep w₁ w₂) (suffix : Word α) :
    FreeCancellationStep (w₁ ++ suffix) (w₂ ++ suffix) := by
  cases h with
  | cancel pre post a =>
      have hsource :
          pre ++ [a] ++ [inverseLetter a] ++ (post ++ suffix) =
            (pre ++ [a] ++ [inverseLetter a] ++ post) ++ suffix := by
        simp [List.append_assoc]
      have htarget : pre ++ (post ++ suffix) = (pre ++ post) ++ suffix :=
        (List.append_assoc pre post suffix).symm
      exact FreeCancellationStep.castWords hsource htarget
        (FreeCancellationStep.cancel pre (post ++ suffix) a)

def FreeCancellationStep.appendLeft {w₁ w₂ : Word α}
    (h : FreeCancellationStep w₁ w₂) (preContext : Word α) :
    FreeCancellationStep (preContext ++ w₁) (preContext ++ w₂) := by
  cases h with
  | cancel pre post a =>
      have hsource :
          (preContext ++ pre) ++ [a] ++ [inverseLetter a] ++ post =
            preContext ++ (pre ++ [a] ++ [inverseLetter a] ++ post) := by
        simp [List.append_assoc]
      have htarget : (preContext ++ pre) ++ post = preContext ++ (pre ++ post) :=
        List.append_assoc preContext pre post
      exact FreeCancellationStep.castWords hsource htarget
        (FreeCancellationStep.cancel (preContext ++ pre) post a)

noncomputable def FreeCancellationSequence.appendRight {w₁ w₂ : Word α}
    (h : FreeCancellationSequence w₁ w₂) (suffix : Word α) :
    FreeCancellationSequence (w₁ ++ suffix) (w₂ ++ suffix) := by
  induction h with
  | refl w => exact .refl (w ++ suffix)
  | cons step rest ih => exact .cons (step.appendRight suffix) ih

noncomputable def FreeCancellationSequence.appendLeft {w₁ w₂ : Word α}
    (h : FreeCancellationSequence w₁ w₂) (preContext : Word α) :
    FreeCancellationSequence (preContext ++ w₁) (preContext ++ w₂) := by
  induction h with
  | refl w => exact .refl (preContext ++ w)
  | cons step rest ih => exact .cons (step.appendLeft preContext) ih

noncomputable def FreeCancellationSequence.trans {w₁ w₂ w₃ : Word α}
    (h₁ : FreeCancellationSequence w₁ w₂)
    (h₂ : FreeCancellationSequence w₂ w₃) :
    FreeCancellationSequence w₁ w₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | cons step rest ih => exact .cons step (ih h₂)

/-- Transporting the endpoints of a composed cancellation sequence is the
same as transporting the first source and last target separately. -/
@[simp] theorem FreeCancellationSequence.castWords_trans
    {w₁ w₁' w₂ w₃ w₃' : Word α}
    (h₁ : w₁ = w₁') (h₃ : w₃ = w₃')
    (first : FreeCancellationSequence w₁ w₂)
    (second : FreeCancellationSequence w₂ w₃) :
    FreeCancellationSequence.castWords h₁ h₃ (first.trans second) =
      (FreeCancellationSequence.castWords h₁ rfl first).trans
        (FreeCancellationSequence.castWords rfl h₃ second) := by
  cases h₁
  cases h₃
  rfl

/-- The nested cancellation tree can be replayed as a concrete sequence of
adjacent free cancellations. -/
noncomputable def FreeReductionShape.to_cancellationSequence {raw reduced : Word α}
    (h : FreeReductionShape raw reduced) :
    FreeCancellationSequence raw reduced := by
  induction h with
  | empty => exact .refl []
  | letter a => exact .refl [a]
  | append hu hv ihu ihv =>
      exact (ihu.appendRight _).trans (ihv.appendLeft _)
  | @bracket a inner suffix result hinner hsuffix ihinner ihsuffix =>
      let contextSuffix := [inverseLetter a] ++ suffix
      have hraw :
          ([a] ++ inner) ++ contextSuffix =
            ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix) := by
        simp [contextSuffix, List.append_assoc]
      have hmid :
          ([a] ++ []) ++ contextSuffix =
            ((([a] ++ []) ++ [inverseLetter a]) ++ suffix) := by
        simp [contextSuffix, List.append_assoc]
      have hinnerContext :
          FreeCancellationSequence
            ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)
            ((([a] ++ []) ++ [inverseLetter a]) ++ suffix) := by
        exact FreeCancellationSequence.castWords hraw hmid
          ((ihinner.appendLeft [a]).appendRight contextSuffix)
      have hcancel :
          FreeCancellationStep
            ((([a] ++ []) ++ [inverseLetter a]) ++ suffix) suffix := by
        simpa [List.append_assoc] using
          FreeCancellationStep.cancel [] suffix a
      exact hinnerContext.trans
        (.cons hcancel (.refl suffix)) |>.trans ihsuffix

/-- Number of inverse-letter pairs recorded by a nested cancellation tree. -/
noncomputable def FreeReductionShape.cancellationCount
    {raw reduced : Word α} : FreeReductionShape raw reduced → Nat
  | .empty => 0
  | .letter _ => 0
  | .append hleft hright =>
      hleft.cancellationCount + hright.cancellationCount
  | .bracket _ hinner hsuffix =>
      hinner.cancellationCount + hsuffix.cancellationCount + 1

/-- The tree's pair count exactly accounts for the length removed by free
reduction. -/
theorem FreeReductionShape.length_eq_cancellationCount
    {raw reduced : Word α} (h : FreeReductionShape raw reduced) :
    raw.length = reduced.length + 2 * h.cancellationCount := by
  induction h with
  | empty => rfl
  | letter a => rfl
  | append hleft hright ihleft ihright =>
      simp only [List.length_append, cancellationCount]
      omega
  | bracket a hinner hsuffix ihinner ihsuffix =>
      simp only [List.length_append, List.length_cons, List.length_nil,
        cancellationCount] at ihinner ihsuffix ⊢
      omega

/-- Free reductions can be combined componentwise over a concatenated list of
words. This is the factorwise gluing lemma for relator-conjugate boundaries. -/
noncomputable def FreeReductionShape.flatten_map {β : Type*} (xs : List β)
    (raw reduced : β → Word α)
    (h : ∀ x ∈ xs, FreeReductionShape (raw x) (reduced x)) :
    FreeReductionShape (List.flatten (xs.map raw))
      (List.flatten (xs.map reduced)) := by
  induction xs with
  | nil => exact .empty
  | cons x xs ih =>
      have hx : FreeReductionShape (raw x) (reduced x) := h x (by simp)
      have htail : ∀ y ∈ xs, FreeReductionShape (raw y) (reduced y) := by
        intro y hy
        exact h y (by simp [hy])
      have hrest := ih htail
      change FreeReductionShape
        (raw x ++ List.flatten (xs.map raw))
        (reduced x ++ List.flatten (xs.map reduced))
      exact .append hx hrest
end GreendlingerDehn
