import SmallCancellation.PlanarCancellation

namespace GreendlingerDehn

private theorem pairwise_lt_idxOf_succ {l : List Nat}
    (h : List.Pairwise (fun a b : Nat => a < b) l) {x : Nat}
    (hx : x ∈ l) (hx1 : x + 1 ∈ l) :
    l.idxOf (x + 1) = l.idxOf x + 1 := by
  have hxi : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hxi1 : l.idxOf (x + 1) < l.length := List.idxOf_lt_length_of_mem hx1
  have hval? : l[l.idxOf x]? = some x := List.getElem?_idxOf hx
  have hval1? : l[l.idxOf (x + 1)]? = some (x + 1) := List.getElem?_idxOf hx1
  have hval : l.get ⟨l.idxOf x, hxi⟩ = x := by
    rw [List.get_eq_getElem?]
    simp [hval?]
  have hval1 : l.get ⟨l.idxOf (x + 1), hxi1⟩ = x + 1 := by
    rw [List.get_eq_getElem?]
    simp [hval1?]
  have hne : l.idxOf x ≠ l.idxOf (x + 1) := by
    intro heq
    have hv : x = x + 1 := by
      calc
        x = l.get ⟨l.idxOf x, hxi⟩ := hval.symm
        _ = l.get ⟨l.idxOf (x + 1), hxi1⟩ := by simp [heq]
        _ = x + 1 := hval1
    omega
  have hlt : l.idxOf x < l.idxOf (x + 1) := by
    by_contra hnot
    have hback : l.idxOf (x + 1) < l.idxOf x := by omega
    have hbackFin :
        (⟨l.idxOf (x + 1), hxi1⟩ : Fin l.length) <
          ⟨l.idxOf x, hxi⟩ := Fin.mk_lt_mk.mpr hback
    have hlt' := h.rel_get_of_lt hbackFin
    change l.get ⟨l.idxOf (x + 1), hxi1⟩ < l.get ⟨l.idxOf x, hxi⟩ at hlt'
    rw [hval1, hval] at hlt'
    omega
  by_contra hnot
  have hgap : l.idxOf x + 2 ≤ l.idxOf (x + 1) := by omega
  let k := l.idxOf x + 1
  have hk : k < l.length := by omega
  have hfirst : l.idxOf x < k := by omega
  have hsecond : k < l.idxOf (x + 1) := by omega
  have hfirstFin :
      (⟨l.idxOf x, hxi⟩ : Fin l.length) < ⟨k, hk⟩ := Fin.mk_lt_mk.mpr hfirst
  have hsecondFin :
      (⟨k, hk⟩ : Fin l.length) < ⟨l.idxOf (x + 1), hxi1⟩ := Fin.mk_lt_mk.mpr hsecond
  have hleft := h.rel_get_of_lt hfirstFin
  have hright := h.rel_get_of_lt hsecondFin
  have hvalK : l.get ⟨k, hk⟩ = l[k] := by
    rw [List.get_eq_getElem?]
    simp
  change l.get ⟨l.idxOf x, hxi⟩ < l.get ⟨k, hk⟩ at hleft
  change l.get ⟨k, hk⟩ < l.get ⟨l.idxOf (x + 1), hxi1⟩ at hright
  rw [hval, hvalK] at hleft
  rw [hval1, hvalK] at hright
  omega

/-- If every source position in an interval survives a boundary reduction,
then its letters still form one contiguous interval in the reduced word. -/
theorem IndexedBoundaryTrace.contiguous_source_interval_of_survivors
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) (start len : Nat)
    (hsurv : ∀ j, j < len → start + j ∈ trace.survivorOccurrences.map Prod.fst) :
    ∃ pre post : Word α,
      reduced = pre ++ (raw.drop start).take len ++ post := by
  by_cases hlen : len = 0
  · subst len
    refine ⟨[], reduced, ?_⟩
    simp
  · have hlenPos : 0 < len := Nat.pos_of_ne_zero hlen
    let positions := trace.survivorOccurrences.map Prod.fst
    have hstrict : List.Pairwise (fun i j : Nat => i < j) positions := by
      simpa [positions] using trace.survivorPositions_strict
    have hpositionsLength : positions.length = reduced.length := by
      simp [positions, trace.survivors_length]
    have hstart : start ∈ positions := by
      simpa [positions] using hsurv 0 hlenPos
    have hidxShift : ∀ j, j < len →
        positions.idxOf (start + j) = positions.idxOf start + j := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
          have hjlt : j < len := by omega
          have hprev := hsurv j hjlt
          have hnext := hsurv (j + 1) (by omega)
          have hstep : positions.idxOf ((start + j) + 1) =
              positions.idxOf (start + j) + 1 :=
            pairwise_lt_idxOf_succ hstrict (by simpa [positions, Nat.add_assoc] using hprev)
              (by simpa [positions, Nat.add_assoc] using hnext)
          calc
            positions.idxOf (start + (j + 1)) = positions.idxOf ((start + j) + 1) := by
              rfl
            _ = positions.idxOf (start + j) + 1 := hstep
            _ = (positions.idxOf start + j) + 1 := by rw [ih hjlt]
            _ = positions.idxOf start + (j + 1) := by omega
    have hsourcelt : ∀ j, j < len → start + j < raw.length := by
      intro j hj
      rcases List.mem_map.mp (hsurv j hj) with ⟨o, ho, hpos⟩
      have hb := trace.survivors_inBounds o ho
      simpa [hpos] using hb
    have hlastSourceBound : start + (len - 1) < raw.length := hsourcelt (len - 1) (by omega)
    have hdropLen : len ≤ (raw.drop start).length := by
      simp only [List.length_drop]
      omega
    let first := positions.idxOf start
    have hlastMem : start + (len - 1) ∈ positions := by
      simpa [positions] using hsurv (len - 1) (by omega)
    have hlastIdxBound : positions.idxOf (start + (len - 1)) < positions.length :=
      List.idxOf_lt_length_of_mem hlastMem
    have hfirstPlusLen : first + len ≤ reduced.length := by
      rw [← hpositionsLength]
      have hlastShift := hidxShift (len - 1) (by omega)
      omega
    let middle := (reduced.drop first).take len
    have hmiddleLength : middle.length = len := by
      dsimp [middle]
      simp only [List.length_take, List.length_drop]
      omega
    have hmiddleLetters : ∀ j (hj : j < len),
        middle[j]'(by simpa [hmiddleLength] using hj) =
          raw[start + j]'(hsourcelt j hj) := by
      intro j hj
      have hmem : start + j ∈ positions := by
        simpa [positions] using hsurv j hj
      have hidxBound : positions.idxOf (start + j) < positions.length :=
        List.idxOf_lt_length_of_mem hmem
      have hidx : positions.idxOf (start + j) = first + j := hidxShift j hj
      let i := positions.idxOf (start + j)
      have hi : i < trace.survivorOccurrences.length := by
        simpa [i, positions] using hidxBound
      let occurrence := trace.survivorOccurrences[i]
      have hocc : occurrence ∈ trace.survivorOccurrences := by
        dsimp [occurrence]
        exact List.getElem_mem hi
      have hposGet : positions[positions.idxOf (start + j)] = start + j :=
        List.getElem_idxOf hidxBound
      have hposMapped :
          (trace.survivorOccurrences.map Prod.fst)[positions.idxOf (start + j)] =
            start + j := by
        simpa only [positions] using hposGet
      have hposOccurrence : occurrence.1 = start + j := by
        dsimp [occurrence, i]
        simpa only [List.getElem_map] using hposMapped
      have hlabelMap := congrArg (fun xs : List (Letter α) => xs[i]?)
        trace.survivors_labels
      have hredBound : i < reduced.length := by
        rw [← hpositionsLength]
        exact hidxBound
      have hlabelMap' : (trace.survivorOccurrences[i]?).map Prod.snd =
          some reduced[i] := by
        simpa [hredBound] using hlabelMap
      have hocc? : trace.survivorOccurrences[i]? = some occurrence := by
        simp [occurrence, hi]
      have hlabel : occurrence.2 = reduced[i] := by
        rw [hocc?] at hlabelMap'
        exact Option.some.inj hlabelMap'
      have hsource := trace.survivors_are_sourceLetters occurrence hocc
      have hsource' : raw[start + j]? = some (reduced[i]) := by
        simpa [hposOccurrence, hlabel] using hsource
      have hsourceElem : raw[start + j]'(hsourcelt j hj) = reduced[i] :=
        (List.getElem?_eq_some_iff.mp hsource').2
      have hsourceElem' : raw[start + j]'(hsourcelt j hj) = reduced[first + j] := by
        simpa [i, hidx] using hsourceElem
      have hmiddleElem : middle[j]'(by simpa [hmiddleLength] using hj) =
          reduced[first + j] := by
        dsimp [middle]
        simp [List.getElem_take, List.getElem_drop, first]
      rw [hmiddleElem, hsourceElem']
    let sourceSegment := (raw.drop start).take len
    have hsourceSegmentLength : sourceSegment.length = len := by
      simp only [sourceSegment, List.length_take, List.length_drop]
      omega
    have hmiddleEq : middle = sourceSegment := by
      apply List.ext_getElem?'
      intro j hjmax
      have hj : j < len := by simpa [hmiddleLength, hsourceSegmentLength] using hjmax
      have hjMiddle : j < middle.length := by simpa [hmiddleLength] using hj
      have hjSource : j < sourceSegment.length := by simpa [hsourceSegmentLength] using hj
      rw [List.getElem?_eq_getElem hjMiddle, List.getElem?_eq_getElem hjSource]
      rw [hmiddleLetters j hj]
      simp [sourceSegment, List.getElem_take, List.getElem_drop]
    have hdecomp : reduced = reduced.take first ++ middle ++ reduced.drop (first + len) := by
      calc
        reduced = reduced.take first ++ reduced.drop first :=
          (List.take_append_drop first reduced).symm
        _ = reduced.take first ++ ((reduced.drop first).take len ++
              (reduced.drop first).drop len) := by
          congr 1
          exact (List.take_append_drop len (reduced.drop first)).symm
        _ = reduced.take first ++ middle ++ reduced.drop (first + len) := by
          simp [middle, List.drop_drop]
    rw [hmiddleEq] at hdecomp
    exact ⟨reduced.take first, reduced.drop (first + len), hdecomp⟩

end GreendlingerDehn
