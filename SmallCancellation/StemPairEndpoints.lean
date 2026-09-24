import SmallCancellation.LollipopFolds
import SmallCancellation.PairingComponents
import SmallCancellation.PlanarBoundarySeed

/-!
# Distinct occurrences in the balloon stem pairing

The occurrence pairs used to fold conjugator stems must form a matching before
they can be combined with the boundary-cancellation matching. This file proves
the basic lollipop case directly from the disjoint outward-stem and return-stem
positions in its literal boundary word.
-/

namespace GreendlingerDehn

/-- The occurrence list represented by a list of labeled dart pairs. -/
def labelledDartPairEndpoints {α : Type*} {G : LabelledDartGraph α}
    (pairs : List (LabelledDartPair G)) : List G.toDartGraph.Dart :=
  pairs.flatMap fun pair => [pair.first, pair.second]

theorem labelledDartPairEndpoints_map {α : Type*} {G H : LabelledDartGraph α}
    (f : LabelledGraphHom G H) (pairs : List (LabelledDartPair G)) :
    labelledDartPairEndpoints (pairs.map (LabelledDartPair.map f)) =
      (labelledDartPairEndpoints pairs).map f.mapDart := by
  simp [labelledDartPairEndpoints, LabelledDartPair.map,
    List.flatMap_map, List.map_flatMap]

theorem labelledDartPairEndpoints_append {α : Type*}
    {G : LabelledDartGraph α} (left right : List (LabelledDartPair G)) :
    labelledDartPairEndpoints (left ++ right) =
      labelledDartPairEndpoints left ++ labelledDartPairEndpoints right := by
  simp [labelledDartPairEndpoints]

private theorem wordPathPrefixHom_mapDart_injective {α : Type*}
    (pre suf : Word α) :
    Function.Injective (wordPathPrefixHom pre suf).mapDart := by
  intro d e h
  cases d with
  | mk di db =>
      cases e with
      | mk ei eb =>
          have hidx : di.val = ei.val := by
            simpa [wordPathPrefixHom] using congrArg (fun x => x.1.val) h
          have hdir : db = eb := by
            simpa [wordPathPrefixHom] using congrArg (fun x => x.2) h
          exact Prod.ext (Fin.ext hidx) hdir

private theorem wordPathSuffixHom_mapDart_injective {α : Type*}
    (pre suf : Word α) :
    Function.Injective (wordPathSuffixHom pre suf).mapDart := by
  intro d e h
  cases d with
  | mk di db =>
      cases e with
      | mk ei eb =>
          have hidx : di.val = ei.val := by
            have hval := congrArg (fun x => x.1.val) h
            simpa [wordPathSuffixHom] using Nat.add_left_cancel hval
          have hdir : db = eb := by
            simpa [wordPathSuffixHom] using congrArg (fun x => x.2) h
          exact Prod.ext (Fin.ext hidx) hdir

private theorem wordPathPrefixHom_mapDart_index_lt {α : Type*}
    (pre suf : Word α) (d : (wordPathGraph pre).toDartGraph.Dart) :
    ((wordPathPrefixHom pre suf).mapDart d).1.val < pre.length := by
  simp [wordPathPrefixHom]

private theorem wordPathSuffixHom_mapDart_index_ge {α : Type*}
    (pre suf : Word α) (d : (wordPathGraph suf).toDartGraph.Dart) :
    pre.length ≤ ((wordPathSuffixHom pre suf).mapDart d).1.val := by
  simp [wordPathSuffixHom]

private def lollipopStemEndpointIndices {α : Type*} (stem relator : Word α) :
    List (Fin (lollipopBoundaryWord stem relator).length) :=
  (List.finRange stem.length).flatMap fun i =>
    [lollipopStemFirstIndex stem relator i, lollipopStemMateIndex stem relator i]

/-- The outward and return positions of all stem folds in one lollipop are
pairwise distinct. -/
theorem lollipopStemEndpointIndices_nodup {α : Type*}
    (stem relator : Word α) :
    (lollipopStemEndpointIndices stem relator).Nodup := by
  classical
  unfold lollipopStemEndpointIndices
  rw [List.nodup_flatMap]
  constructor
  · intro i hi
    rw [List.nodup_cons]
    constructor
    · simp only [List.mem_singleton]
      intro heq
      have hval : i.val =
          stem.length + relator.length + (stem.length - (i.val + 1)) := by
        simpa [lollipopStemFirstIndex, lollipopStemMateIndex,
          lollipopBoundaryWord] using congrArg Fin.val heq
      omega
    · exact List.nodup_singleton _
  · rw [List.pairwise_iff_forall_sublist]
    intro i j hij
    have hpairNodup : ([i, j] : List (Fin stem.length)).Nodup :=
      (List.nodup_finRange stem.length).sublist hij
    have hne : i ≠ j := by
      intro heq
      have hnot : i ∉ [j] := (List.nodup_cons.mp hpairNodup).1
      exact hnot (List.mem_singleton.mpr heq)
    have hmate_lb (k : Fin stem.length) :
        stem.length + relator.length ≤ (lollipopStemMateIndex stem relator k).val := by
      simp
    apply List.disjoint_left.mpr
    intro x hxi hxj
    change x ∈ [lollipopStemFirstIndex stem relator i,
      lollipopStemMateIndex stem relator i] at hxi
    change x ∈ [lollipopStemFirstIndex stem relator j,
      lollipopStemMateIndex stem relator j] at hxj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxi hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · have hval := congrArg Fin.val (hxi.symm.trans hxj)
      have hval' : i.val = j.val := by
        simpa [lollipopStemFirstIndex] using hval
      exact hne (Fin.ext hval')
    · have hval := congrArg Fin.val (hxi.symm.trans hxj)
      have hi := i.isLt
      have hj := hmate_lb j
      have hval' : i.val =
          stem.length + relator.length + (stem.length - (j.val + 1)) := by
        simpa [lollipopStemFirstIndex, lollipopStemMateIndex,
          lollipopBoundaryWord] using hval
      omega
    · have hval := congrArg Fin.val (hxi.symm.trans hxj)
      have hj := j.isLt
      have hi := hmate_lb i
      have hval' : stem.length + relator.length +
          (stem.length - (i.val + 1)) = j.val := by
        simpa [lollipopStemFirstIndex, lollipopStemMateIndex,
          lollipopBoundaryWord] using hval
      omega
    · have hval := congrArg Fin.val (hxi.symm.trans hxj)
      have hi := i.isLt
      have hj := j.isLt
      have hval' : stem.length + relator.length +
          (stem.length - (i.val + 1)) = stem.length + relator.length +
            (stem.length - (j.val + 1)) := by
        simpa [lollipopStemMateIndex, lollipopBoundaryWord] using hval
      have hijval : i.val = j.val := by omega
      exact hne (Fin.ext hijval)

private def lollipopStemIndexToDart {α : Type*} (stem relator : Word α)
    (i : Fin (lollipopBoundaryWord stem relator).length) :
    (wordPathGraph (lollipopBoundaryWord stem relator)).toDartGraph.Dart :=
  (i, false)

private theorem lollipopStemEndpointIndices_map_nodup {α : Type*}
    (stem relator : Word α) :
    ((lollipopStemEndpointIndices stem relator).map
      (lollipopStemIndexToDart stem relator)).Nodup := by
  apply (lollipopStemEndpointIndices_nodup stem relator).map
  intro i j h
  exact congrArg Prod.fst h

/-- In one lollipop, the outward and return dart occurrences of all stem
folds are pairwise distinct. -/
theorem lollipopStemPairs_endpointList_nodup {α : Type*}
    (stem relator : Word α) :
    ((lollipopStemPairs stem relator).flatMap fun pair =>
      [pair.first, pair.second]).Nodup := by
  simpa [lollipopStemPairs, lollipopStemEndpointIndices,
    List.flatMap_map, List.map_flatMap, lollipopStemPair,
    lollipopStemIndexToDart] using
    (lollipopStemEndpointIndices_map_nodup stem relator)

/-- In a single lollipop, a stem-paired occurrence lies before or after the
relator segment. -/
theorem lollipopStemPairs_endpoint_mem_stem_region {α : Type*}
    (stem relator : Word α)
    {d : (wordPathGraph (lollipopBoundaryWord stem relator)).toDartGraph.Dart}
    (hd : d ∈ (lollipopStemPairs stem relator).flatMap fun pair =>
      [pair.first, pair.second]) :
    d.1.val < stem.length ∨ stem.length + relator.length ≤ d.1.val := by
  have hd' : d ∈ (List.finRange stem.length).flatMap (fun i =>
      [(lollipopStemPair stem relator i).first,
       (lollipopStemPair stem relator i).second]) := by
    simpa only [lollipopStemPairs, List.flatMap_map] using hd
  rcases List.mem_flatMap.mp hd' with ⟨i, _, hmem⟩
  cases d with
  | mk dindex ddirection =>
      change (dindex, ddirection) ∈
        [(lollipopStemFirstIndex stem relator i, false),
          (lollipopStemMateIndex stem relator i, false)] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hfirst | hmate
      · have hval : dindex.val = i.val := by
          have hv := congrArg (fun x : Fin _ × Bool => x.1.val) hfirst
          simpa [lollipopStemFirstIndex] using hv
        exact Or.inl (hval ▸ i.isLt)
      · have hval : dindex.val =
            stem.length + relator.length + (stem.length - (i.val + 1)) := by
          have hv := congrArg (fun x : Fin _ × Bool => x.1.val) hmate
          simpa [lollipopStemMateIndex, lollipopBoundaryWord] using hv
        apply Or.inr
        rw [hval]
        exact Nat.le_add_right _ _

/-- Every position in the outward or return conjugator segment occurs as an
endpoint of one of the lollipop's stem pairs. -/
theorem lollipopStemPosition_mem_endpoint_of_region {α : Type*}
    (stem relator : Word α)
    (i : Fin (lollipopBoundaryWord stem relator).length)
    (hregion : i.val < stem.length ∨
      stem.length + relator.length ≤ i.val) :
    (i, false) ∈ labelledDartPairEndpoints (lollipopStemPairs stem relator) := by
  classical
  unfold labelledDartPairEndpoints lollipopStemPairs
  simp only [List.flatMap_map]
  rcases hregion with hfirst | hreturn
  · let k : Fin stem.length := ⟨i.val, hfirst⟩
    have hpos : (lollipopStemPair stem relator k).first = (i, false) := by
      apply Prod.ext
      · apply Fin.ext
        simp [lollipopStemPair, lollipopStemFirstIndex, k]
      · rfl
    apply List.mem_flatMap.mpr
    refine ⟨k, by simp, ?_⟩
    change (i, false) ∈
      [(lollipopStemPair stem relator k).first,
        (lollipopStemPair stem relator k).second]
    rw [← hpos]
    exact List.mem_cons_self
  · have hupper : i.val < 2 * stem.length + relator.length := by
      have hi := i.isLt
      simp [lollipopBoundaryWord, FreeGroup.invRev_length] at hi
      omega
    let k : Fin stem.length :=
      ⟨stem.length - 1 - (i.val - (stem.length + relator.length)), by omega⟩
    have hpos : (lollipopStemPair stem relator k).second = (i, false) := by
      apply Prod.ext
      · apply Fin.ext
        simp [lollipopStemPair, lollipopStemMateIndex, k]
        omega
      · rfl
    apply List.mem_flatMap.mpr
    refine ⟨k, by simp, ?_⟩
    change (i, false) ∈
      [(lollipopStemPair stem relator k).first,
        (lollipopStemPair stem relator k).second]
    rw [← hpos]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- Casting a balloon's lollipop boundary to its stored raw-word presentation
preserves distinct stem occurrences. -/
theorem ReducedRelatorBalloonData.stemPairs_endpointList_nodup
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P) :
    (b.stemPairs.flatMap fun pair => [pair.first, pair.second]).Nodup := by
  classical
  let h := b.label.lollipopBoundary_eq_rawWord
  let castDart := fun d :
      (wordPathGraph (lollipopBoundaryWord b.label.conjugator.toWord
        b.label.relator.toWord)).toDartGraph.Dart =>
    (Fin.cast (congrArg List.length h) d.1, d.2)
  have hcast : Function.Injective castDart := by
    intro d e hde
    have hfirst := congrArg Prod.fst hde
    have hsecond := congrArg Prod.snd hde
    exact Prod.ext
      (Fin.cast_injective (congrArg List.length h) hfirst) hsecond
  have hlocal := lollipopStemPairs_endpointList_nodup
    b.label.conjugator.toWord b.label.relator.toWord
  have hmap := hlocal.map hcast
  have hmap' := hmap
  rw [List.map_flatMap] at hmap'
  unfold ReducedRelatorBalloonData.stemPairs
  rw [List.flatMap_map]
  simpa [h, castDart, LabelledDartPair.castWordPath,
    wordPathGraph] using hmap'

/-- Every endpoint in a balloon's stored stem pairing lies outside its
relator-side interval. -/
theorem ReducedRelatorBalloonData.stemPairs_endpoint_mem_stem_region
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    {d : (wordPathGraph b.label.rawWord).toDartGraph.Dart}
    (hd : d ∈ labelledDartPairEndpoints b.stemPairs) :
    d.1.val < b.label.conjugator.toWord.length ∨
      b.label.conjugator.toWord.length + b.label.relator.toWord.length ≤ d.1.val := by
  cases d with
  | mk dindex ddirection =>
      unfold ReducedRelatorBalloonData.stemPairs labelledDartPairEndpoints at hd
      rw [List.flatMap_map] at hd
      rcases List.mem_flatMap.mp hd with ⟨pair, hpair, hmem⟩
      rcases List.mem_map.mp hpair with ⟨i, hindex, hpair⟩
      rw [← hpair] at hmem
      change (dindex, ddirection) ∈
        [(Fin.cast (congrArg List.length b.label.lollipopBoundary_eq_rawWord
            ) (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).first.1,
            (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).first.2),
          (Fin.cast (congrArg List.length b.label.lollipopBoundary_eq_rawWord
            ) (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).second.1,
            (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).second.2)] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hfirst | hsecond
      · have hlocal : (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).first ∈
            (lollipopStemPairs b.label.conjugator.toWord
              b.label.relator.toWord).flatMap fun p => [p.first, p.second] := by
          apply List.mem_flatMap.mpr
          exact ⟨lollipopStemPair b.label.conjugator.toWord
            b.label.relator.toWord i,
            List.mem_map.mpr ⟨i, hindex, rfl⟩, by simp⟩
        have hregion := lollipopStemPairs_endpoint_mem_stem_region
          b.label.conjugator.toWord b.label.relator.toWord hlocal
        have hval : dindex.val =
            (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).first.1.val := by
          have hv := congrArg (fun x : Fin _ × Bool => x.1.val) hfirst
          simpa [Fin.cast] using hv
        rw [hval]
        exact hregion
      · have hlocal : (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).second ∈
            (lollipopStemPairs b.label.conjugator.toWord
              b.label.relator.toWord).flatMap fun p => [p.first, p.second] := by
          apply List.mem_flatMap.mpr
          exact ⟨lollipopStemPair b.label.conjugator.toWord
            b.label.relator.toWord i,
            List.mem_map.mpr ⟨i, hindex, rfl⟩, by simp⟩
        have hregion := lollipopStemPairs_endpoint_mem_stem_region
          b.label.conjugator.toWord b.label.relator.toWord hlocal
        have hval : dindex.val =
            (lollipopStemPair b.label.conjugator.toWord
              b.label.relator.toWord i).second.1.val := by
          have hv := congrArg (fun x : Fin _ × Bool => x.1.val) hsecond
          simpa [Fin.cast] using hv
        rw [hval]
        exact hregion

/-- Every stored raw-word position outside the relator interval is represented
by the balloon's stem pairing. -/
theorem ReducedRelatorBalloonData.stemPosition_mem_endpoint_of_region
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (p : Fin b.label.rawWord.length)
    (hregion : p.val < b.label.conjugator.toWord.length ∨
      b.label.conjugator.toWord.length + b.label.relator.toWord.length ≤ p.val) :
    (p, false) ∈ labelledDartPairEndpoints b.stemPairs := by
  let sourceWord := lollipopBoundaryWord b.label.conjugator.toWord
    b.label.relator.toWord
  let hraw := b.label.lollipopBoundary_eq_rawWord
  let pLocal : Fin sourceWord.length :=
    ⟨p.val, by simpa [sourceWord, hraw] using p.isLt⟩
  have hregionLocal : pLocal.val < b.label.conjugator.toWord.length ∨
      b.label.conjugator.toWord.length + b.label.relator.toWord.length ≤ pLocal.val :=
    hregion
  have hmemLocal := lollipopStemPosition_mem_endpoint_of_region
    b.label.conjugator.toWord b.label.relator.toWord pLocal hregionLocal
  have hmemLocal' :
      (pLocal, false) ∈ labelledDartPairEndpoints
        (lollipopStemPairs b.label.conjugator.toWord b.label.relator.toWord) := by
    simpa [sourceWord] using hmemLocal
  unfold labelledDartPairEndpoints at hmemLocal'
  obtain ⟨localPair, hlocalPair, hlocalEndpoint⟩ :=
    List.mem_flatMap.mp hmemLocal'
  have hendpoint :
      (pLocal, false) = localPair.first ∨
        (pLocal, false) = localPair.second := by
    rcases List.mem_cons.mp hlocalEndpoint with hfirst | htail
    · exact Or.inl hfirst
    · exact Or.inr (List.mem_singleton.mp htail)
  let rawPair := LabelledDartPair.castWordPath hraw localPair
  have hrawPair : rawPair ∈ b.stemPairs := by
    change rawPair ∈ (lollipopStemPairs b.label.conjugator.toWord
      b.label.relator.toWord).map (LabelledDartPair.castWordPath hraw)
    exact List.mem_map.mpr ⟨localPair, hlocalPair, rfl⟩
  have hcastPos :
      Fin.cast (congrArg List.length hraw) pLocal = p := by
    apply Fin.ext
    rfl
  let castDart := fun d : Fin sourceWord.length × Bool =>
    (Fin.cast (congrArg List.length hraw) d.1, d.2)
  have hcastDartPos : castDart (pLocal, false) = (p, false) := by
    apply Prod.ext
    · exact hcastPos
    · rfl
  unfold labelledDartPairEndpoints
  apply List.mem_flatMap.mpr
  refine ⟨rawPair, hrawPair, ?_⟩
  change (p, false) ∈ [rawPair.first, rawPair.second]
  rcases hendpoint with hfirst | hsecond
  · have hrawFirst : (p, false) = rawPair.first := by
      have hcast := Eq.trans hcastDartPos.symm (congrArg castDart hfirst)
      simpa [castDart, rawPair, LabelledDartPair.castWordPath] using hcast
    rw [hrawFirst]
    change rawPair.first ∈ rawPair.first :: [rawPair.second]
    simp
  · have hrawSecond : (p, false) = rawPair.second := by
      have hcast := Eq.trans hcastDartPos.symm (congrArg castDart hsecond)
      simpa [castDart, rawPair, LabelledDartPair.castWordPath] using hcast
    rw [hrawSecond]
    change rawPair.second ∈ rawPair.first :: [rawPair.second]
    simp

/-- The forward dart for one side of a balloon's relator boundary, transported
to the stored raw-word path. -/
private theorem list_get_cast_eq {α : Type*} {u v : List α} (h : u = v)
    (i : Fin u.length) :
    v[Fin.cast (congrArg List.length h) i] = u[i] := by
  cases h
  rfl

def ReducedRelatorBalloonData.relatorSideDart
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
    (wordPathGraph b.label.rawWord).toDartGraph.Dart := by
  let localIndex : Fin (lollipopBoundaryWord b.label.conjugator.toWord
      b.label.relator.toWord).length :=
    ⟨b.label.conjugator.toWord.length + j.val, by
      simp [lollipopBoundaryWord, FreeGroup.invRev_length]
      omega⟩
  exact (Fin.cast (congrArg List.length b.label.lollipopBoundary_eq_rawWord
    ) localIndex, false)

@[simp] theorem ReducedRelatorBalloonData.relatorSideDart_index
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
    (b.relatorSideDart j).1.val =
      b.label.conjugator.toWord.length + j.val := by
  simp [ReducedRelatorBalloonData.relatorSideDart]

@[simp] theorem ReducedRelatorBalloonData.relatorSideDart_direction
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
    (b.relatorSideDart j).2 = false := rfl

/-- The transported face-side occurrence retains the corresponding literal
relator letter. -/
@[simp] theorem ReducedRelatorBalloonData.relatorSideDart_label
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
  (wordPathGraph b.label.rawWord).label (b.relatorSideDart j) =
      b.label.relator.toWord[j] := by
  unfold ReducedRelatorBalloonData.relatorSideDart
  simp only [wordPathGraph, Bool.false_eq_true, ↓reduceIte]
  let localIndex : Fin (lollipopBoundaryWord b.label.conjugator.toWord
      b.label.relator.toWord).length :=
    ⟨b.label.conjugator.toWord.length + j.val, by
      simp [lollipopBoundaryWord, FreeGroup.invRev_length]
      omega⟩
  change b.label.rawWord[
      Fin.cast (congrArg List.length b.label.lollipopBoundary_eq_rawWord)
        localIndex] = b.label.relator.toWord[j]
  rw [list_get_cast_eq b.label.lollipopBoundary_eq_rawWord localIndex]
  simp [localIndex, lollipopBoundaryWord]

/-- Relator-side occurrences are disjoint from the local balloon stem
matching. -/
theorem ReducedRelatorBalloonData.relatorSideDart_not_stemEndpoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (j : Fin b.label.relator.toWord.length) :
    b.relatorSideDart j ∉ labelledDartPairEndpoints b.stemPairs := by
  intro hmem
  have hregion := b.stemPairs_endpoint_mem_stem_region hmem
  have hval : (b.relatorSideDart j).1.val =
      b.label.conjugator.toWord.length + j.val := by
    simp [ReducedRelatorBalloonData.relatorSideDart]
  rcases hregion with hlow | hhigh
  · omega
  · omega

private theorem reducedBalloonOccurrencePathEmbedding_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P)
    (tail : List (ReducedRelatorBalloonData P)) :
    reducedBalloonOccurrencePathEmbedding (b :: tail) 0 =
      wordPathPrefixHom b.label.rawWord
        ((tail.map fun x => x.label.rawWord).flatten) := by
  rfl

private theorem reducedBalloonOccurrencePathEmbedding_succ
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P)
    (tail : List (ReducedRelatorBalloonData P))
    (i : Fin tail.length) :
    reducedBalloonOccurrencePathEmbedding (b :: tail) i.succ =
      LabelledGraphHom.comp
        (wordPathSuffixHom b.label.rawWord
          ((tail.map fun x => x.label.rawWord).flatten))
      (reducedBalloonOccurrencePathEmbedding tail i) := by
  rfl

/-- Every balloon boundary embeds injectively in the flattened boundary word.
The prefix and suffix path maps are injective on dart occurrences, so the
inductive concatenation embedding is as well. -/
theorem reducedBalloonOccurrencePathEmbedding_mapDart_injective {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (i : Fin balloons.length),
      Function.Injective (reducedBalloonOccurrencePathEmbedding balloons i).mapDart := by
  intro balloons
  induction balloons with
  | nil => intro i; exact Fin.elim0 i
  | cons b tail ih =>
      intro i
      cases i using Fin.cases with
      | zero =>
          rw [reducedBalloonOccurrencePathEmbedding_zero]
          exact wordPathPrefixHom_mapDart_injective b.label.rawWord
            ((tail.map fun x => x.label.rawWord).flatten)
      | succ i =>
          rw [reducedBalloonOccurrencePathEmbedding_succ]
          intro d e h
          have hinner :
              (reducedBalloonOccurrencePathEmbedding tail i).mapDart d =
                (reducedBalloonOccurrencePathEmbedding tail i).mapDart e := by
            apply wordPathSuffixHom_mapDart_injective b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten)
            simpa [LabelledGraphHom.comp, Function.comp_apply] using h
          have hinner' :
              (reducedBalloonOccurrencePathEmbedding tail i).mapDart d =
                (reducedBalloonOccurrencePathEmbedding tail i).mapDart e := by
            simpa only [List.get_cons_succ'] using hinner
          exact ih i hinner'

/-- Balloon occurrence embeddings preserve the forward/reverse direction bit
of each source dart. -/
theorem reducedBalloonOccurrencePathEmbedding_direction {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (i : Fin balloons.length)
      (d : (wordPathGraph (balloons.get i).label.rawWord).toDartGraph.Dart),
      ((reducedBalloonOccurrencePathEmbedding balloons i).mapDart d).2 = d.2 := by
  intro balloons
  induction balloons with
  | nil => intro i; exact Fin.elim0 i
  | cons b tail ih =>
      intro i d
      cases i using Fin.cases with
      | zero =>
          rw [reducedBalloonOccurrencePathEmbedding_zero]
          simp [wordPathPrefixHom]
      | succ i =>
          rw [reducedBalloonOccurrencePathEmbedding_succ]
          let d' : (wordPathGraph (tail.get i).label.rawWord).toDartGraph.Dart := by
            simpa only [List.get_cons_succ'] using d
          have hinner := ih i d'
          calc
            (((wordPathSuffixHom b.label.rawWord
                ((tail.map fun x => x.label.rawWord).flatten)).comp
                (reducedBalloonOccurrencePathEmbedding tail i)).mapDart d).2 =
                ((reducedBalloonOccurrencePathEmbedding tail i).mapDart d).2 := rfl
            _ = d.2 := by simpa only [List.get_cons_succ'] using hinner

/-- Every edge position in the flattened balloon boundary belongs to one
indexed balloon occurrence. This is the position-surjectivity companion to
the occurrence embeddings' injectivity. -/
theorem reducedBalloonOccurrencePathEmbedding_position_surjective
    {α : Type*} [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (p : Fin ((balloons.map fun b => b.label.rawWord).flatten).length),
      ∃ i : Fin balloons.length,
        ∃ j : Fin (balloons.get i).label.rawWord.length,
          (((reducedBalloonOccurrencePathEmbedding balloons i).mapDart
            (j, false)).1).val = p.val := by
  intro balloons
  induction balloons with
  | nil =>
      intro p
      exact Fin.elim0 p
  | cons b tail ih =>
      intro p
      let tailWord := (tail.map fun x => x.label.rawWord).flatten
      have hlength :
          ((b :: tail).map fun x => x.label.rawWord).flatten.length =
            b.label.rawWord.length + tailWord.length := by
        simp [tailWord]
      by_cases hp : p.val < b.label.rawWord.length
      · let j : Fin b.label.rawWord.length := ⟨p.val, hp⟩
        refine ⟨0, j, ?_⟩
        rw [reducedBalloonOccurrencePathEmbedding_zero]
        simp [j, wordPathPrefixHom]
      · have htail : p.val - b.label.rawWord.length < tailWord.length := by
          have hpbound : p.val < b.label.rawWord.length + tailWord.length := by
            simpa [tailWord] using p.isLt
          omega
        let pTail : Fin tailWord.length := ⟨p.val - b.label.rawWord.length, htail⟩
        obtain ⟨i, j, hpos⟩ := ih pTail
        refine ⟨i.succ, j, ?_⟩
        rw [reducedBalloonOccurrencePathEmbedding_succ]
        change b.label.rawWord.length +
          ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
            (j, false)).1.val = p.val
        dsimp [pTail] at hpos
        omega

/-- A stem pair belonging to a particular balloon occurrence remains in the
flattened pairing at that same indexed occurrence. Using the index avoids
confusing duplicate balloon values. -/
theorem reducedBalloonOccurrencePathEmbedding_stemPair_mem
    {α : Type*} [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (i : Fin balloons.length)
      (pair : LabelledDartPair (wordPathGraph (balloons.get i).label.rawWord)),
      pair ∈ (balloons.get i).stemPairs →
        LabelledDartPair.map
          (reducedBalloonOccurrencePathEmbedding balloons i) pair ∈
          reducedBalloonStemPairs balloons := by
  intro balloons
  induction balloons with
  | nil =>
      intro i
      exact Fin.elim0 i
  | cons b tail ih =>
      intro i pair hpair
      cases i using Fin.cases with
      | zero =>
          rw [reducedBalloonOccurrencePathEmbedding_zero,
            reducedBalloonStemPairs_cons]
          apply List.mem_append.mpr
          left
          exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
      | succ i =>
          rw [reducedBalloonOccurrencePathEmbedding_succ,
            reducedBalloonStemPairs_cons]
          apply List.mem_append.mpr
          right
          apply List.mem_map.mpr
          refine ⟨LabelledDartPair.map
            (reducedBalloonOccurrencePathEmbedding tail i) pair,
            ih i pair (by simpa using hpair), ?_⟩
          simp

/-- Relator-side occurrences from the entire flattened balloon list have
distinct source positions. This is the global form of the per-balloon
injectivity statement below. -/
theorem reducedBalloonRelatorSidePosition_injective {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P)),
      Function.Injective (fun side : Σ i : Fin balloons.length,
          Fin ((balloons.get i).label.relator.toWord.length) =>
        ((reducedBalloonOccurrencePathEmbedding balloons side.1).mapDart
          ((balloons.get side.1).relatorSideDart side.2)).1) := by
  intro balloons
  induction balloons with
  | nil =>
      intro side
      exact Fin.elim0 side.1
  | cons b tail ih =>
      intro side₁ side₂ hpos
      rcases side₁ with ⟨i, j⟩
      rcases side₂ with ⟨k, l⟩
      cases i using Fin.cases with
      | zero =>
          cases k using Fin.cases with
          | zero =>
              dsimp only at hpos
              simp only [List.get_cons_zero] at hpos
              have hdart : b.relatorSideDart j = b.relatorSideDart l := by
                apply wordPathPrefixHom_mapDart_injective b.label.rawWord
                  ((tail.map fun x => x.label.rawWord).flatten)
                apply Prod.ext
                · simpa [reducedBalloonOccurrencePathEmbedding_zero,
                    wordPathPrefixHom] using hpos
                · rfl
              have hjl : j = l := by
                apply Fin.ext
                have hval := congrArg (fun d : Fin _ × Bool => d.1.val) hdart
                simpa [ReducedRelatorBalloonData.relatorSideDart, Fin.cast] using hval
              subst l
              rfl
          | succ k =>
              dsimp only at hpos
              simp only [List.get_cons_zero, List.get_cons_succ'] at hpos
              rw [reducedBalloonOccurrencePathEmbedding_zero,
                reducedBalloonOccurrencePathEmbedding_succ] at hpos
              have hlow := wordPathPrefixHom_mapDart_index_lt
                b.label.rawWord ((tail.map fun x => x.label.rawWord).flatten)
                (b.relatorSideDart j)
              have hhigh := wordPathSuffixHom_mapDart_index_ge
                b.label.rawWord ((tail.map fun x => x.label.rawWord).flatten)
                ((reducedBalloonOccurrencePathEmbedding tail k).mapDart
                  ((tail.get k).relatorSideDart l))
              have hEq := congrArg Fin.val hpos
              change ((wordPathPrefixHom b.label.rawWord
                  ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                    (b.relatorSideDart j)).1.val =
                ((wordPathSuffixHom b.label.rawWord
                  ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                    ((reducedBalloonOccurrencePathEmbedding tail k).mapDart
                      ((tail.get k).relatorSideDart l))).1.val at hEq
              omega
      | succ i =>
          cases k using Fin.cases with
          | zero =>
              dsimp only at hpos
              simp only [List.get_cons_zero, List.get_cons_succ'] at hpos
              rw [reducedBalloonOccurrencePathEmbedding_succ,
                reducedBalloonOccurrencePathEmbedding_zero] at hpos
              have hhigh := wordPathSuffixHom_mapDart_index_ge
                b.label.rawWord ((tail.map fun x => x.label.rawWord).flatten)
                ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                  ((tail.get i).relatorSideDart j))
              have hlow := wordPathPrefixHom_mapDart_index_lt
                b.label.rawWord ((tail.map fun x => x.label.rawWord).flatten)
                (b.relatorSideDart l)
              have hEq := congrArg Fin.val hpos
              change ((wordPathSuffixHom b.label.rawWord
                  ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                    ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                      ((tail.get i).relatorSideDart j))).1.val =
                ((wordPathPrefixHom b.label.rawWord
                  ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                    (b.relatorSideDart l)).1.val at hEq
              omega
          | succ k =>
              dsimp only at hpos
              simp only [List.get_cons_succ'] at hpos
              rw [reducedBalloonOccurrencePathEmbedding_succ,
                reducedBalloonOccurrencePathEmbedding_succ] at hpos
              have htail :
                  ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                    ((tail.get i).relatorSideDart j)).1 =
                  ((reducedBalloonOccurrencePathEmbedding tail k).mapDart
                    ((tail.get k).relatorSideDart l)).1 := by
                have hDart :
                    (wordPathSuffixHom b.label.rawWord
                      ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                        ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                          ((tail.get i).relatorSideDart j)) =
                    (wordPathSuffixHom b.label.rawWord
                      ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                        ((reducedBalloonOccurrencePathEmbedding tail k).mapDart
                          ((tail.get k).relatorSideDart l)) := by
                  apply Prod.ext
                  · exact hpos
                  · calc
                      ((wordPathSuffixHom b.label.rawWord
                        ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                          ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                            ((tail.get i).relatorSideDart j))).2 =
                          ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                            ((tail.get i).relatorSideDart j)).2 := rfl
                      _ = ((tail.get i).relatorSideDart j).2 :=
                        reducedBalloonOccurrencePathEmbedding_direction tail i
                          ((tail.get i).relatorSideDart j)
                      _ = ((tail.get k).relatorSideDart l).2 := by
                        simp [ReducedRelatorBalloonData.relatorSideDart]
                      _ = ((reducedBalloonOccurrencePathEmbedding tail k).mapDart
                            ((tail.get k).relatorSideDart l)).2 :=
                        (reducedBalloonOccurrencePathEmbedding_direction tail k
                          ((tail.get k).relatorSideDart l)).symm
                      _ = ((wordPathSuffixHom b.label.rawWord
                        ((tail.map fun x => x.label.rawWord).flatten)).mapDart
                          ((reducedBalloonOccurrencePathEmbedding tail k).mapDart
                            ((tail.get k).relatorSideDart l))).2 := rfl
                have hinner := wordPathSuffixHom_mapDart_injective
                  b.label.rawWord ((tail.map fun x => x.label.rawWord).flatten)
                  hDart
                exact congrArg Prod.fst hinner
              have hside :
                  (⟨i, j⟩ : Σ x : Fin tail.length,
                    Fin ((tail.get x).label.relator.toWord.length)) = ⟨k, l⟩ := by
                apply ih
                exact htail
              cases hside
              rfl

/-- A relator-side occurrence from any indexed balloon remains outside the
stem matching after all balloon boundaries are flattened together. -/
theorem reducedBalloonRelatorSideDart_not_stemEndpoint {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (i : Fin balloons.length)
      (j : Fin (balloons.get i).label.relator.toWord.length),
      (reducedBalloonOccurrencePathEmbedding balloons i).mapDart
        ((balloons.get i).relatorSideDart j) ∉
          labelledDartPairEndpoints (reducedBalloonStemPairs balloons) := by
  intro balloons
  induction balloons with
  | nil => intro i; exact Fin.elim0 i
  | cons b tail ih =>
      intro i j
      cases i using Fin.cases with
      | zero =>
          simp only [List.get_cons_zero]
          rw [reducedBalloonOccurrencePathEmbedding_zero,
            reducedBalloonStemPairs_cons, labelledDartPairEndpoints_append,
            labelledDartPairEndpoints_map, labelledDartPairEndpoints_map]
          intro hmem
          rw [List.mem_append] at hmem
          rcases hmem with hhead | htail
          · rcases List.mem_map.mp hhead with ⟨d, hd, heq⟩
            have hsource := wordPathPrefixHom_mapDart_injective
              b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten) heq
            exact b.relatorSideDart_not_stemEndpoint j (hsource ▸ hd)
          · rcases List.mem_map.mp htail with ⟨d, _, heq⟩
            have hlow := wordPathPrefixHom_mapDart_index_lt
              b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten)
              (b.relatorSideDart j)
            have hhigh := wordPathSuffixHom_mapDart_index_ge
              b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten) d
            rw [← heq] at hlow
            omega
      | succ i =>
          rw [reducedBalloonOccurrencePathEmbedding_succ,
            reducedBalloonStemPairs_cons, labelledDartPairEndpoints_append,
            labelledDartPairEndpoints_map, labelledDartPairEndpoints_map]
          simp only [List.get_cons_succ']
          intro hmem
          rw [List.mem_append] at hmem
          rcases hmem with hhead | htail
          · rcases List.mem_map.mp hhead with ⟨d, _, heq⟩
            have hlow := wordPathPrefixHom_mapDart_index_lt
              b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten) d
            have hhigh := wordPathSuffixHom_mapDart_index_ge
              b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten)
              ((reducedBalloonOccurrencePathEmbedding tail i).mapDart
                ((tail.get i).relatorSideDart j))
            have hhigh' : b.label.rawWord.length ≤
                (((LabelledGraphHom.comp
                  (wordPathSuffixHom b.label.rawWord
                    ((tail.map fun x : ReducedRelatorBalloonData P =>
                      x.label.rawWord).flatten))
                  (reducedBalloonOccurrencePathEmbedding tail i)).mapDart
                    ((tail.get i).relatorSideDart j)).1.val) := by
              simpa [LabelledGraphHom.comp] using hhigh
            rw [heq] at hlow
            omega
          · rcases List.mem_map.mp htail with ⟨d, hd, heq⟩
            have hsame := wordPathSuffixHom_mapDart_injective
              b.label.rawWord
              ((tail.map fun x => x.label.rawWord).flatten) heq
            apply ih i j
            rw [← hsame]
            exact hd

/-- The stem pairs for an entire list of relator balloons are a matching on
the flattened literal boundary. The prefix and suffix images of each cons
split occupy disjoint source-position intervals. -/
theorem reducedBalloonStemPairs_endpointList_nodup {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P)),
      (labelledDartPairEndpoints (reducedBalloonStemPairs balloons)).Nodup := by
  intro balloons
  induction balloons with
  | nil => simp [reducedBalloonStemPairs, labelledDartPairEndpoints]
  | cons b tail ih =>
      let tailWord := (tail.map
        (fun x : ReducedRelatorBalloonData P => x.label.rawWord)).flatten
      let prefixHom := wordPathPrefixHom b.label.rawWord tailWord
      let suffix := wordPathSuffixHom b.label.rawWord tailWord
      rw [reducedBalloonStemPairs_cons, labelledDartPairEndpoints_append,
        labelledDartPairEndpoints_map, labelledDartPairEndpoints_map]
      have hhead :
          (labelledDartPairEndpoints b.stemPairs).map prefixHom.mapDart |>.Nodup :=
        (b.stemPairs_endpointList_nodup).map
          (wordPathPrefixHom_mapDart_injective b.label.rawWord tailWord)
      have htail :
          (labelledDartPairEndpoints (reducedBalloonStemPairs tail)).map
              suffix.mapDart |>.Nodup :=
        ih.map (wordPathSuffixHom_mapDart_injective b.label.rawWord tailWord)
      apply List.nodup_append.mpr
      refine ⟨hhead, htail, ?_⟩
      intro d hd e he hde
      have hd' : d.1.val < b.label.rawWord.length := by
        rcases List.mem_map.mp hd with ⟨d₀, _, rfl⟩
        exact wordPathPrefixHom_mapDart_index_lt
          b.label.rawWord tailWord d₀
      have he' : b.label.rawWord.length ≤ e.1.val := by
        rcases List.mem_map.mp he with ⟨d₀, _, rfl⟩
        exact wordPathSuffixHom_mapDart_index_ge
          b.label.rawWord tailWord d₀
      rw [hde] at hd'
      omega

/-- Every local balloon stem occurrence is taken in the forward orientation
of the original word path. -/
theorem ReducedRelatorBalloonData.stemPairs_forward
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (pair : LabelledDartPair (wordPathGraph b.label.rawWord))
    (hpair : pair ∈ b.stemPairs) :
    pair.first.2 = false ∧ pair.second.2 = false := by
  unfold ReducedRelatorBalloonData.stemPairs at hpair
  rcases List.mem_map.mp hpair with ⟨sourcePair, hsource, hpair⟩
  have hsourceOrient : sourcePair.first.2 = false ∧ sourcePair.second.2 = false := by
    change sourcePair ∈
      (List.finRange b.label.conjugator.toWord.length).map
        (lollipopStemPair b.label.conjugator.toWord b.label.relator.toWord) at hsource
    rcases List.mem_map.mp hsource with ⟨i, _, hi⟩
    rw [← hi]
    simp [lollipopStemPair]
  rw [← hpair]
  simpa [LabelledDartPair.castWordPath] using hsourceOrient

/-- All stem pairs in the flattened balloon list retain their forward
orientation. -/
theorem reducedBalloonStemPairs_forward {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P)) (pair),
      pair ∈ reducedBalloonStemPairs balloons →
      pair.first.2 = false ∧ pair.second.2 = false := by
  intro balloons
  induction balloons with
  | nil => simp [reducedBalloonStemPairs]
  | cons b tail ih =>
      intro pair hpair
      rw [reducedBalloonStemPairs_cons] at hpair
      rcases List.mem_append.mp hpair with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨sourcePair, hsource, rfl⟩
        simpa [LabelledDartPair.map, wordPathPrefixHom] using
          b.stemPairs_forward sourcePair hsource
      · rcases List.mem_map.mp htail with ⟨sourcePair, hsource, rfl⟩
        simpa [LabelledDartPair.map, wordPathSuffixHom] using
          ih sourcePair hsource

/-- Every dart endpoint in the flattened stem list keeps the forward
orientation. -/
theorem reducedBalloonStemEndpoints_forward {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P)) (d),
      d ∈ labelledDartPairEndpoints (reducedBalloonStemPairs balloons) →
      d.2 = false := by
  intro balloons d hd
  rcases List.mem_flatMap.mp hd with ⟨pair, hp, hd⟩
  have hpair := reducedBalloonStemPairs_forward balloons pair hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd
  · simpa [hd] using hpair.1
  · simpa [hd] using hpair.2

/-- At the seed boundary, discard the fixed forward orientation and retain
the finite source positions of its balloon stem pairs. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairs
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    List (Fin seed.boundary.reducedLiteralBoundary.length ×
      Fin seed.boundary.reducedLiteralBoundary.length) :=
  seed.balloonStemPairs.map fun pair =>
    (pair.first.1, pair.second.1)

theorem MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairs_endpoints_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    occurrencePairEndpoints seed.balloonStemOccurrencePairs =
      (labelledDartPairEndpoints seed.balloonStemPairs).map
        (fun d => d.1) := by
  simp [MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairs,
    occurrencePairEndpoints, labelledDartPairEndpoints,
    List.flatMap_map, List.map_flatMap]

/-- Every flattened relator-side occurrence is unmatched by the stem pairing
on the seed's literal boundary positions. -/
theorem MinimalAreaRelatorBoundarySeed.relatorSidePosition_unmatched_by_stem
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)) :
    ((reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
      ((seed.boundary.reducedBalloons.get i).relatorSideDart j)).1 ∉
        occurrencePairEndpoints seed.balloonStemOccurrencePairs := by
  let sideDart := (reducedBalloonOccurrencePathEmbedding
    seed.boundary.reducedBalloons i).mapDart
      ((seed.boundary.reducedBalloons.get i).relatorSideDart j)
  have hnotDart := reducedBalloonRelatorSideDart_not_stemEndpoint
    seed.boundary.reducedBalloons i j
  have hsideDirection : sideDart.2 = false := by
    dsimp [sideDart]
    rw [reducedBalloonOccurrencePathEmbedding_direction]
    simp [ReducedRelatorBalloonData.relatorSideDart]
  intro hmem
  rw [seed.balloonStemOccurrencePairs_endpoints_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨d, hd, hpos⟩
  have hdirection := reducedBalloonStemEndpoints_forward
    seed.boundary.reducedBalloons d hd
  have hdartEq : d = sideDart :=
    Prod.ext hpos (hdirection.trans hsideDirection.symm)
  have hsideDartMem : sideDart ∈
      labelledDartPairEndpoints (reducedBalloonStemPairs
        seed.boundary.reducedBalloons) := by
    rw [← hdartEq]
    exact hd
  exact hnotDart hsideDartMem

private theorem ReducedRelatorBalloonData.relatorSideDart_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P) :
    Function.Injective b.relatorSideDart := by
  intro j k h
  apply Fin.ext
  have hval := congrArg (fun d => d.1.val) h
  have hval' : b.label.conjugator.toWord.length + j.val =
      b.label.conjugator.toWord.length + k.val := by
    simpa [ReducedRelatorBalloonData.relatorSideDart, Fin.cast] using hval
  omega

/-- Relator-side positions of a fixed balloon remain distinct after its path
is embedded in the full literal boundary. -/
theorem MinimalAreaRelatorBoundarySeed.relatorSidePosition_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length) :
    Function.Injective (fun j : Fin
        (seed.boundary.reducedBalloons.get i).label.relator.toWord.length =>
      ((reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
        ((seed.boundary.reducedBalloons.get i).relatorSideDart j)).1) := by
  intro j k hpos
  have hdarts :
      (reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
          ((seed.boundary.reducedBalloons.get i).relatorSideDart j) =
        (reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
          ((seed.boundary.reducedBalloons.get i).relatorSideDart k) := by
    apply Prod.ext
    · exact hpos
    · have hj := reducedBalloonOccurrencePathEmbedding_direction
        seed.boundary.reducedBalloons i
        ((seed.boundary.reducedBalloons.get i).relatorSideDart j)
      have hk := reducedBalloonOccurrencePathEmbedding_direction
        seed.boundary.reducedBalloons i
        ((seed.boundary.reducedBalloons.get i).relatorSideDart k)
      exact hj.trans hk.symm
  have hlocal :=
    (reducedBalloonOccurrencePathEmbedding_mapDart_injective
      seed.boundary.reducedBalloons i) hdarts
  exact ReducedRelatorBalloonData.relatorSideDart_injective
    (seed.boundary.reducedBalloons.get i) hlocal

theorem MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairs_endpoints_nodup
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    (occurrencePairEndpoints seed.balloonStemOccurrencePairs).Nodup := by
  classical
  have hDarts :
      (labelledDartPairEndpoints seed.balloonStemPairs).Nodup := by
    unfold MinimalAreaRelatorBoundarySeed.balloonStemPairs
    exact reducedBalloonStemPairs_endpointList_nodup
      seed.boundary.reducedBalloons
  have hforward : ∀ d ∈ labelledDartPairEndpoints seed.balloonStemPairs,
      d.2 = false := reducedBalloonStemEndpoints_forward
        seed.boundary.reducedBalloons
  have hpos :
      ((labelledDartPairEndpoints seed.balloonStemPairs).map
        fun d => d.1).Nodup := by
    apply hDarts.map_on
    intro d hd e he hde
    have hd2 := hforward d hd
    have he2 := hforward e he
    exact Prod.ext hde (hd2.trans he2.symm)
  rw [seed.balloonStemOccurrencePairs_endpoints_eq]
  exact hpos

/-- Endpoint uniqueness of a pair list rules out self-pairs. -/
theorem occurrencePair_noLoop_of_endpoints_nodup {V : Type*}
    {pairs : List (V × V)}
    (hnodup : (occurrencePairEndpoints pairs).Nodup) :
    ∀ p ∈ pairs, p.1 ≠ p.2 := by
  intro p hp
  have hflat : (pairs.flatMap fun q => [q.1, q.2]).Nodup := by
    simpa [occurrencePairEndpoints] using hnodup
  have hlocal := (List.nodup_flatMap.mp hflat).1 p hp
  simpa using hlocal

/-- The balloon stem occurrences form a partial pairing of positions in the
seed's literal reduced-balloon boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairing
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    PartialOccurrencePairing (Fin seed.boundary.reducedLiteralBoundary.length) :=
  occurrencePairListToPairing seed.balloonStemOccurrencePairs
    seed.balloonStemOccurrencePairs_endpoints_nodup
    (occurrencePair_noLoop_of_endpoints_nodup
      seed.balloonStemOccurrencePairs_endpoints_nodup)

theorem MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairing_spec
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i j : Fin seed.boundary.reducedLiteralBoundary.length) :
    seed.balloonStemOccurrencePairing.partner i = some j ↔
      occurrencePairRel seed.balloonStemOccurrencePairs i j := by
  exact occurrencePairListToPairing_spec _
    seed.balloonStemOccurrencePairs_endpoints_nodup
    (occurrencePair_noLoop_of_endpoints_nodup
      seed.balloonStemOccurrencePairs_endpoints_nodup) i j

theorem MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedLiteralBoundary.length) :
    seed.balloonStemOccurrencePairing.partner i = none ↔
      i ∉ occurrencePairEndpoints seed.balloonStemOccurrencePairs := by
  exact occurrencePairListToPairing_partner_eq_none_iff_not_mem_endpoints
    seed.balloonStemOccurrencePairs
    seed.balloonStemOccurrencePairs_endpoints_nodup
    (occurrencePair_noLoop_of_endpoints_nodup
      seed.balloonStemOccurrencePairs_endpoints_nodup) i

/-- Turn the absolute cancellation positions of an indexed boundary trace into
inverse-labeled forward-dart pairs on the word occurrence path. -/
noncomputable def IndexedBoundaryTrace.cancellationOccurrenceDartPairs
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    List (LabelledDartPair (wordPathGraph raw)) :=
  trace.cancellationPairs.attach.map fun entry =>
    let p := entry.1
    let hp := entry.2
    let bounds := trace.pairs_inBounds p hp
    let first : Fin raw.length := ⟨p.1, by omega⟩
    let second : Fin raw.length := ⟨p.2, bounds.2⟩
    {
      first := (first, false)
      second := (second, false)
      inverse_labels := by
        rcases trace.pairs_are_inverseLetters p hp with ⟨a, hfirst, hsecond⟩
        have hfirst' : raw.get first = a := by
          change raw[p.1]? = some a at hfirst
          rw [List.getElem?_eq_getElem first.isLt] at hfirst
          exact Option.some.inj hfirst
        have hsecond' : raw.get second = inverseLetter a := by
          change raw[p.2]? = some (inverseLetter a) at hsecond
          rw [List.getElem?_eq_getElem second.isLt] at hsecond
          exact Option.some.inj hsecond
        change raw.get first = inverseLetter (raw.get second)
        rw [hfirst', hsecond']
        simp
    }

theorem IndexedBoundaryTrace.cancellationOccurrenceDartPairs_positions
    {α : Type*} {raw reduced : Word α}
    (trace : IndexedBoundaryTrace raw reduced) :
    trace.cancellationOccurrenceDartPairs.map
      (fun pair => (pair.first.1, pair.second.1)) =
        trace.cancellationOccurrencePairs := by
  simp [IndexedBoundaryTrace.cancellationOccurrenceDartPairs,
    IndexedBoundaryTrace.cancellationOccurrencePairs]

/-- Boundary cancellations are the second partial pairing on the same finite
set of literal source positions. -/
noncomputable def MinimalAreaRelatorBoundarySeed.boundaryCancellationPairing
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairing

/-- The cancellation matching, now with its source positions represented as
forward darts on the same literal boundary graph as the stem folds. -/
noncomputable def MinimalAreaRelatorBoundarySeed.boundaryCancellationDartPairs
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    List (LabelledDartPair
      seed.balloonBoundaryGraph) :=
  seed.reducedLollipopBoundaryTrace.cancellationOccurrenceDartPairs.map
    (LabelledDartPair.map seed.balloonBoundaryHom)

theorem MinimalAreaRelatorBoundarySeed.boundaryCancellationDartPairs_positions
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
  seed.boundaryCancellationDartPairs.map
      (fun pair => (pair.first.1, pair.second.1)) =
        seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs := by
  simpa [MinimalAreaRelatorBoundarySeed.boundaryCancellationDartPairs,
    LabelledDartPair.map, MinimalAreaRelatorBoundarySeed.balloonBoundaryHom,
    wordPathBoundaryHomWithJoins, Function.comp_def] using
    seed.reducedLollipopBoundaryTrace.cancellationOccurrenceDartPairs_positions

/-- Fold both families of occurrence pairs directly on the same literal
boundary graph. This explicit quotient presents the edge identifications
whose connected components are tracked by the occurrence pairing graph. -/
noncomputable def MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  WalkFoldResult.foldPairs
    (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)
    seed.balloonBoundaryLoop

theorem MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold_stem_reverse
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (pair : LabelledDartPair
      seed.balloonBoundaryGraph)
    (hpair : pair ∈ seed.boundaryBalloonStemPairs) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart pair.second =
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart pair.first) := by
  exact WalkFoldResult.foldPairs_pair_reverse
    (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)
    seed.balloonBoundaryLoop pair (List.mem_append_left _ hpair)

theorem MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold_cancellation_reverse
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (pair : LabelledDartPair
      seed.balloonBoundaryGraph)
    (hpair : pair ∈ seed.boundaryCancellationDartPairs) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart pair.second =
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart pair.first) := by
  exact WalkFoldResult.foldPairs_pair_reverse
    (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)
    seed.balloonBoundaryLoop pair (List.mem_append_right _ hpair)

theorem MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs_positions
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    seed.boundaryBalloonStemPairs.map
      (fun pair => (pair.first.1, pair.second.1)) =
        seed.balloonStemOccurrencePairs := by
  simp [MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs,
    MinimalAreaRelatorBoundarySeed.balloonStemOccurrencePairs,
    LabelledDartPair.map, MinimalAreaRelatorBoundarySeed.balloonBoundaryHom,
    wordPathBoundaryHomWithJoins, Function.comp_def]

theorem MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold_positions
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs).map
        (fun pair => (pair.first.1, pair.second.1)) =
      seed.balloonStemOccurrencePairs ++
        seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs := by
  rw [List.map_append, seed.boundaryBalloonStemPairs_positions,
    seed.boundaryCancellationDartPairs_positions]

theorem MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold_forward
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (pair : LabelledDartPair seed.balloonBoundaryGraph)
    (hpair : pair ∈
      seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs) :
    pair.first.2 = false ∧ pair.second.2 = false := by
  rw [List.mem_append] at hpair
  rcases hpair with hstem | hcancel
  · unfold MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs at hstem
    rcases List.mem_map.mp hstem with ⟨sourcePair, hsource, rfl⟩
    have hforward := reducedBalloonStemPairs_forward
      seed.boundary.reducedBalloons sourcePair hsource
    simpa [LabelledDartPair.map,
      MinimalAreaRelatorBoundarySeed.balloonBoundaryHom,
      wordPathBoundaryHomWithJoins] using hforward
  · unfold MinimalAreaRelatorBoundarySeed.boundaryCancellationDartPairs at hcancel
    rcases List.mem_map.mp hcancel with ⟨sourcePair, hsource, rfl⟩
    unfold IndexedBoundaryTrace.cancellationOccurrenceDartPairs at hsource
    rcases List.mem_map.mp hsource with ⟨entry, hentry, rfl⟩
    constructor <;>
      simpa [LabelledDartPair.map,
        MinimalAreaRelatorBoundarySeed.balloonBoundaryHom,
        wordPathBoundaryHomWithJoins]

/-- Any edge of the alternating occurrence graph is sent to a single
unoriented dart class by the explicit pair-fold quotient. -/
theorem MinimalAreaRelatorBoundarySeed.edgeClass_eq_of_occurrencePairRel
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hrel : occurrencePairRel
      (seed.balloonStemOccurrencePairs ++
        seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs) v x) :
    let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
    (Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
      UnorientedDartClass G) =
    Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
  classical
  let pairs := seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs
  have hpositions := seed.boundaryOccurrenceDartPairFold_positions
  rw [← hpositions] at hrel
  rcases hrel with ⟨p, hp, hpvx | hpwx⟩
  · rcases List.mem_map.mp hp with ⟨pair, hpair, hpos⟩
    have hfirstDirection := seed.boundaryOccurrenceDartPairFold_forward pair hpair |>.1
    have hsecondDirection := seed.boundaryOccurrenceDartPairFold_forward pair hpair |>.2
    have hfold := WalkFoldResult.foldPairs_pair_unorientedClass_eq
      pairs seed.balloonBoundaryLoop pair hpair
    have hfirst : pair.first = (v, false) :=
      Prod.ext ((congrArg Prod.fst hpos).trans hpvx.1) hfirstDirection
    have hsecond : pair.second = (x, false) :=
      Prod.ext ((congrArg Prod.snd hpos).trans hpvx.2) hsecondDirection
    dsimp [pairs, MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold]
      at hfold ⊢
    simpa [hfirst, hsecond] using hfold.symm
  · rcases List.mem_map.mp hp with ⟨pair, hpair, hpos⟩
    have hfirstDirection := seed.boundaryOccurrenceDartPairFold_forward pair hpair |>.1
    have hsecondDirection := seed.boundaryOccurrenceDartPairFold_forward pair hpair |>.2
    have hfold := WalkFoldResult.foldPairs_pair_unorientedClass_eq
      pairs seed.balloonBoundaryLoop pair hpair
    have hfirst : pair.first = (x, false) :=
      Prod.ext ((congrArg Prod.fst hpos).trans hpwx.1) hfirstDirection
    have hsecond : pair.second = (v, false) :=
      Prod.ext ((congrArg Prod.snd hpos).trans hpwx.2) hsecondDirection
    dsimp [pairs, MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold]
      at hfold ⊢
    simpa [hfirst, hsecond] using hfold

theorem MinimalAreaRelatorBoundarySeed.edgeClass_eq_of_pairingGraph_adj
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hadj : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Adj v x) :
    let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
    (Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
      UnorientedDartClass G) =
    Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
  have hadj' : seed.balloonStemOccurrencePairing.partner v = some x ∨
      seed.boundaryCancellationPairing.partner v = some x := by
    exact hadj
  have hrel : occurrencePairRel
      (seed.balloonStemOccurrencePairs ++
        seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs) v x := by
    rw [occurrencePairRel_append_iff]
    rcases hadj' with hstem | hcancel
    · exact Or.inl (seed.balloonStemOccurrencePairing_spec v x |>.1 hstem)
    · exact Or.inr
        (seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairing_spec
          v x |>.1 hcancel)
  exact seed.edgeClass_eq_of_occurrencePairRel v x hrel

/-- The explicit fold map is constant, up to orientation, on every connected
component of the two occurrence-pairing graph. -/
theorem MinimalAreaRelatorBoundarySeed.unorientedEdgeClass_eq_in_component
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (v x : C.supp) :
    let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
    (Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v.1, false)) :
      UnorientedDartClass G) =
    Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x.1, false)) := by
  let graph := twoPairingGraph seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing
  have hcomponent : graph.connectedComponentMk v.1 = graph.connectedComponentMk x.1 :=
    v.2.trans x.2.symm
  have hreachable : graph.Reachable v.1 x.1 :=
    SimpleGraph.ConnectedComponent.eq.mp hcomponent
  exact hreachable.map_eq_of_adj
    (fun i => Quotient.mk
      (UnorientedDartSetoid seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)))
    (by
      intro a b hab
      exact seed.edgeClass_eq_of_pairingGraph_adj a b hab)

/-- The exact fold-setoid relation preserves connected components of the
alternating occurrence-pairing graph, regardless of dart orientation. -/
theorem MinimalAreaRelatorBoundarySeed.boundaryPairFoldSetoid_component_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (vDirection xDirection : Bool)
    (h : (LabelledDartPairFoldSetoid
      (seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs)).r
      (v, vDirection) (x, xDirection)) :
    (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).connectedComponentMk v =
    (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).connectedComponentMk x := by
  classical
  let pairs := seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs
  let graph := twoPairingGraph seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing
  have hpair_adj : ∀ pair ∈ pairs, graph.Adj pair.first.1 pair.second.1 := by
    intro pair hpair
    have hmem : (pair.first.1, pair.second.1) ∈
        pairs.map (fun p => (p.first.1, p.second.1)) :=
      List.mem_map.mpr ⟨pair, hpair, rfl⟩
    have hocc : occurrencePairRel
        (seed.balloonStemOccurrencePairs ++
          seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs)
        pair.first.1 pair.second.1 := by
      rw [← seed.boundaryOccurrenceDartPairFold_positions]
      exact ⟨(pair.first.1, pair.second.1), hmem, Or.inl ⟨rfl, rfl⟩⟩
    have hparts := (occurrencePairRel_append_iff
      seed.balloonStemOccurrencePairs
      seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs
      pair.first.1 pair.second.1).1 hocc
    change seed.balloonStemOccurrencePairing.partner pair.first.1 =
        some pair.second.1 ∨
      seed.boundaryCancellationPairing.partner pair.first.1 =
        some pair.second.1
    rcases hparts with hstem | hcancel
    · exact Or.inl ((seed.balloonStemOccurrencePairing_spec
        pair.first.1 pair.second.1).2 hstem)
    · exact Or.inr ((seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairing_spec
        pair.first.1 pair.second.1).2 hcancel)
  have hstep : ∀ a b,
      LabelledDartPairFoldGenerator pairs a b →
      graph.connectedComponentMk a.1 = graph.connectedComponentMk b.1 := by
    intro a b hgen
    rcases hgen with ⟨pair, hpair, hfold⟩
    have hadj := hpair_adj pair hpair
    have hfirstReverse :
        (seed.balloonBoundaryGraph.toDartGraph.reverse pair.first).1 =
          pair.first.1 := by
      simp [MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph,
        wordBoundaryGraphWithJoins, wordPathGraph]
    have hsecondReverse :
        (seed.balloonBoundaryGraph.toDartGraph.reverse pair.second).1 =
          pair.second.1 := by
      simp [MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph,
        wordBoundaryGraphWithJoins, wordPathGraph]
    rcases hfold with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hsecondReverse]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    · rw [hfirstReverse]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  change Relation.EqvGen (LabelledDartPairFoldGenerator pairs)
    (v, vDirection) (x, xDirection) at h
  have hmap : ∀ {a b}, Relation.EqvGen (LabelledDartPairFoldGenerator pairs) a b →
      graph.connectedComponentMk a.1 = graph.connectedComponentMk b.1 := by
    intro a b hab
    induction hab with
    | rel a b hgen => exact hstep a b hgen
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact hmap h

/-- Equal final unoriented dart classes come from the same alternating
occurrence-pairing component. Together with the forward theorem above, this
identifies the edge classes exactly. -/
theorem MinimalAreaRelatorBoundarySeed.component_eq_of_unorientedEdgeClass_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hclass :
      let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
      (Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
        UnorientedDartClass G) =
      Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false))) :
    (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).connectedComponentMk v =
    (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).connectedComponentMk x := by
  classical
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
  let pairs := seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs
  have hclass' :
      (Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
        UnorientedDartClass G) =
      Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := hclass
  rcases (unorientedDartClass_eq_iff
    (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false))
    (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false))).1 hclass' with
    heq | hreverse
  · have hsetoid : (LabelledDartPairFoldSetoid pairs).r
        (v, false) (x, false) := by
      apply (LabelledDartPairFoldResult.foldAll_mapDart_eq_iff_pairFoldSetoid
        (G := seed.balloonBoundaryGraph) pairs (v, false) (x, false)).1
      simpa [G, pairs,
        MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold,
        WalkFoldResult.foldPairs] using heq
    exact seed.boundaryPairFoldSetoid_component_eq v x false false hsetoid
  · have hmapReverse :
        seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, true) =
          G.reverse
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
      change seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.balloonBoundaryGraph.toDartGraph.reverse (x, false)) = _
      exact (seed.boundaryOccurrenceDartPairFold.hom.map_reverse (x, false)).symm
    have heq' :
        seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false) =
          seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, true) :=
      hreverse.trans hmapReverse.symm
    have hsetoid : (LabelledDartPairFoldSetoid pairs).r
        (v, false) (x, true) := by
      apply (LabelledDartPairFoldResult.foldAll_mapDart_eq_iff_pairFoldSetoid
        (G := seed.balloonBoundaryGraph) pairs (v, false) (x, true)).1
      simpa [G, pairs,
        MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold,
        WalkFoldResult.foldPairs] using heq'
    exact seed.boundaryPairFoldSetoid_component_eq v x false true hsetoid

/-- Exact correspondence between alternating occurrence components and
unoriented edges in the explicit pair-fold quotient. -/
theorem MinimalAreaRelatorBoundarySeed.unorientedEdgeClass_eq_iff_componentEq
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length) :
    (let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
     (Quotient.mk (UnorientedDartSetoid G)
       (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
       UnorientedDartClass G) =
     Quotient.mk (UnorientedDartSetoid G)
       (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false))) ↔
    (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).connectedComponentMk v =
    (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).connectedComponentMk x := by
  constructor
  · exact seed.component_eq_of_unorientedEdgeClass_eq v x
  · intro hcomponent
    let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
    let graph := twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing
    have hreachable : graph.Reachable v x :=
      SimpleGraph.ConnectedComponent.eq.mp hcomponent
    exact hreachable.map_eq_of_adj
      (fun i => Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)))
      (by
        intro a b hadj
        exact seed.edgeClass_eq_of_pairingGraph_adj a b hadj)

/-- In each connected component of the two occurrence pairings, at most two
positions can be unmatched by either the balloon-stem folds or the boundary
cancellations. This is the alternating-component endpoint bound for the
actual minimum-area boundary seed. -/
theorem MinimalAreaRelatorBoundarySeed.card_component_unmatched_by_either_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent) :
    Nat.card {v : C.supp //
      (componentLeftPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C).partner v = none ∨
      (componentRightPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C).partner v = none} ≤ 2 := by
  exact card_component_unpaired_either_le_two
    seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing C

/-- The two colors of unmatched positions in a connected component have total
cardinality zero or two. The endpoint colors record whether an end is a
relator side or a surviving target-boundary occurrence. -/
theorem MinimalAreaRelatorBoundarySeed.card_component_unmatched_slots_eq_zero_or_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent) :
    Nat.card
        ({v : C.supp //
          (componentLeftPairing seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C).partner v = none} ⊕
         {v : C.supp //
          (componentRightPairing seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C).partner v = none}) = 0 ∨
    Nat.card
        ({v : C.supp //
          (componentLeftPairing seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C).partner v = none} ⊕
         {v : C.supp //
          (componentRightPairing seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C).partner v = none}) = 2 := by
  exact card_component_unpaired_slots_eq_zero_or_two
    seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing C

/-- A relator face contributes at most two side occurrences to any component
of the alternating stem/cancellation pairing graph. Each side occurrence is
unmatched by the stem pairing, and the side positions of one balloon are
injective in the literal boundary. -/
theorem MinimalAreaRelatorBoundarySeed.card_balloonRelatorSides_in_component_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent) :
    Nat.card {j : Fin
        (seed.boundary.reducedBalloons.get i).label.relator.toWord.length //
      ((reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
        ((seed.boundary.reducedBalloons.get i).relatorSideDart j)).1 ∈ C.supp} ≤ 2 := by
  classical
  let sidePosition := fun j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length =>
    ((reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
      ((seed.boundary.reducedBalloons.get i).relatorSideDart j)).1
  let sidePositionsInComponent := {j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length //
    sidePosition j ∈ C.supp}
  let unmatchedLeft := {v : C.supp //
    (componentLeftPairing seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing C).partner v = none}
  let unmatchedEither := {v : C.supp //
    (componentLeftPairing seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing C).partner v = none ∨
    (componentRightPairing seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing C).partner v = none}
  have hglobalNone (j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length) :
      seed.balloonStemOccurrencePairing.partner (sidePosition j) = none := by
    exact (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint
      (sidePosition j)).2 (seed.relatorSidePosition_unmatched_by_stem i j)
  let toUnmatchedLeft : sidePositionsInComponent → unmatchedLeft := fun j =>
    ⟨⟨sidePosition j.1, j.2⟩, by
      change PartialOccurrencePairing.restrictedPartner
        seed.balloonStemOccurrencePairing C.supp
          ⟨sidePosition j.1, j.2⟩ = none
      cases hpartner : PartialOccurrencePairing.restrictedPartner
          seed.balloonStemOccurrencePairing C.supp
            ⟨sidePosition j.1, j.2⟩ with
      | none => rfl
      | some v =>
          have hglobal :=
            (PartialOccurrencePairing.restrictedPartner_eq_some_iff
              seed.balloonStemOccurrencePairing C.supp
              ⟨sidePosition j.1, j.2⟩ v).1 hpartner
          rw [hglobalNone j.1] at hglobal
          cases hglobal⟩
  have htoUnmatchedLeft : Function.Injective toUnmatchedLeft := by
    intro j k h
    apply Subtype.ext
    apply seed.relatorSidePosition_injective i
    exact congrArg (fun v : unmatchedLeft => v.1.1) h
  have hcardLeft : Fintype.card sidePositionsInComponent ≤
      Fintype.card unmatchedLeft :=
    Fintype.card_le_of_injective toUnmatchedLeft htoUnmatchedLeft
  have hcardMono : Fintype.card unmatchedLeft ≤ Fintype.card unmatchedEither :=
    Fintype.card_subtype_mono
      (fun v : C.supp =>
        (componentLeftPairing seed.balloonStemOccurrencePairing
          seed.boundaryCancellationPairing C).partner v = none)
      (fun v =>
        (componentLeftPairing seed.balloonStemOccurrencePairing
          seed.boundaryCancellationPairing C).partner v = none ∨
        (componentRightPairing seed.balloonStemOccurrencePairing
          seed.boundaryCancellationPairing C).partner v = none)
      (fun _ hv => Or.inl hv)
  have hcomponent := seed.card_component_unmatched_by_either_le_two C
  have hcomponent' : Fintype.card unmatchedEither ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, unmatchedEither] using hcomponent
  rw [Nat.card_eq_fintype_card]
  exact hcardLeft.trans (hcardMono.trans hcomponent')

/-- A fixed balloon has at most two side occurrences in any one unoriented
edge class of the explicit pair-fold quotient. -/
noncomputable def MinimalAreaRelatorBoundarySeed.relatorSidePosition
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length) :
    Fin seed.boundary.reducedLiteralBoundary.length :=
  ((reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons i).mapDart
    ((seed.boundary.reducedBalloons.get i).relatorSideDart j)).1

theorem MinimalAreaRelatorBoundarySeed.card_balloonRelatorSides_in_edgeClass_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j₀ : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length) :
    Nat.card {j : Fin
        (seed.boundary.reducedBalloons.get i).label.relator.toWord.length //
      (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSidePosition i j, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
       Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSidePosition i j₀, false))} ≤ 2 := by
  classical
  let sidePosition := seed.relatorSidePosition i
  let graph := twoPairingGraph seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing
  let C := graph.connectedComponentMk (sidePosition j₀)
  let S := {j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length //
    (Quotient.mk
      (UnorientedDartSetoid seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (sidePosition j, false)) :
      UnorientedDartClass
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (sidePosition j₀, false))}
  let T := {j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length //
    sidePosition j ∈ C.supp}
  have hproperty (j : Fin
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length) :
      (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (sidePosition j, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (sidePosition j₀, false)) ↔
      sidePosition j ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    change (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (sidePosition j, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (sidePosition j₀, false)) ↔
      graph.connectedComponentMk (sidePosition j) =
        graph.connectedComponentMk (sidePosition j₀)
    exact seed.unorientedEdgeClass_eq_iff_componentEq
      (sidePosition j) (sidePosition j₀)
  let e : S ≃ T :=
    { toFun := fun j => ⟨j.1, (hproperty j.1).mp j.2⟩
      invFun := fun j => ⟨j.1, (hproperty j.1).mpr j.2⟩
      left_inv := by intro j; apply Subtype.ext; rfl
      right_inv := by intro j; apply Subtype.ext; rfl }
  calc
    Nat.card {j : Fin
        (seed.boundary.reducedBalloons.get i).label.relator.toWord.length //
      (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (sidePosition j, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (sidePosition j₀, false))} = Nat.card T := Nat.card_congr e
    _ ≤ 2 := seed.card_balloonRelatorSides_in_component_le_two i C

/-- The finite type of all relator-side occurrences across the minimum-area
seed's full list of reduced balloons. -/
abbrev MinimalAreaRelatorBoundarySeed.RelatorSideOccurrence
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  Σ i : Fin seed.boundary.reducedBalloons.length,
    Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length)

/-- The source boundary position occupied by an indexed relator-side
occurrence after the balloon boundaries are flattened. -/
noncomputable def MinimalAreaRelatorBoundarySeed.relatorSideOccurrencePosition
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    Fin seed.boundary.reducedLiteralBoundary.length :=
  ((reducedBalloonOccurrencePathEmbedding seed.boundary.reducedBalloons side.1).mapDart
    ((seed.boundary.reducedBalloons.get side.1).relatorSideDart side.2)).1

theorem MinimalAreaRelatorBoundarySeed.relatorSideOccurrencePosition_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    Function.Injective seed.relatorSideOccurrencePosition := by
  exact reducedBalloonRelatorSidePosition_injective seed.boundary.reducedBalloons

/-- Every occurrence left unmatched by the balloon-stem pairing is a literal
side of exactly one indexed relator boundary. -/
theorem MinimalAreaRelatorBoundarySeed.exists_relatorSide_of_unmatched_by_stem
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (p : Fin seed.boundary.reducedLiteralBoundary.length)
    (hp : seed.balloonStemOccurrencePairing.partner p = none) :
    ∃ side : seed.RelatorSideOccurrence,
      seed.relatorSideOccurrencePosition side = p := by
  have hnot : p ∉ occurrencePairEndpoints seed.balloonStemOccurrencePairs :=
    (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint p).mp hp
  obtain ⟨i, j, hposition⟩ :=
    reducedBalloonOccurrencePathEmbedding_position_surjective
      seed.boundary.reducedBalloons p
  let balloon := seed.boundary.reducedBalloons.get i
  let embedding := reducedBalloonOccurrencePathEmbedding
    seed.boundary.reducedBalloons i
  by_cases hstemRegion :
      j.val < balloon.label.conjugator.toWord.length ∨
        balloon.label.conjugator.toWord.length +
          balloon.label.relator.toWord.length ≤ j.val
  · have hlocal := balloon.stemPosition_mem_endpoint_of_region j hstemRegion
    unfold labelledDartPairEndpoints at hlocal
    obtain ⟨localPair, hlocalPair, hlocalEndpoint⟩ :=
      List.mem_flatMap.mp hlocal
    have hendpoint :
        (j, false) = localPair.first ∨ (j, false) = localPair.second := by
      rcases List.mem_cons.mp hlocalEndpoint with hfirst | htail
      · exact Or.inl hfirst
      · exact Or.inr (List.mem_singleton.mp htail)
    let globalPair := LabelledDartPair.map embedding localPair
    have hglobalPair : globalPair ∈ seed.balloonStemPairs := by
      change globalPair ∈ reducedBalloonStemPairs seed.boundary.reducedBalloons
      exact reducedBalloonOccurrencePathEmbedding_stemPair_mem
        seed.boundary.reducedBalloons i localPair hlocalPair
    have hglobalEndpoints :
        globalPair.first ∈ labelledDartPairEndpoints seed.balloonStemPairs := by
      unfold labelledDartPairEndpoints
      apply List.mem_flatMap.mpr
      refine ⟨globalPair, hglobalPair, ?_⟩
      change globalPair.first ∈ [globalPair.first, globalPair.second]
      exact List.mem_cons.mpr (Or.inl rfl)
    rcases hendpoint with hfirst | hsecond
    · have hfirstPos : globalPair.first.1 = p := by
        apply Fin.ext
        have hmap := congrArg
          (fun d => (embedding.mapDart d).1.val) hfirst.symm
        calc
          globalPair.first.1.val = (embedding.mapDart localPair.first).1.val := rfl
          _ = (embedding.mapDart (j, false)).1.val := hmap
          _ = p.val := hposition
      have hpGlobal :
          p ∈ (labelledDartPairEndpoints seed.balloonStemPairs).map
            (fun d => d.1) := by
        apply List.mem_map.mpr
        exact ⟨globalPair.first, hglobalEndpoints, hfirstPos⟩
      have hpContradiction :
          p ∈ occurrencePairEndpoints seed.balloonStemOccurrencePairs := by
        rw [seed.balloonStemOccurrencePairs_endpoints_eq]
        exact hpGlobal
      exact False.elim (hnot hpContradiction)
    · have hsecondPos : globalPair.second.1 = p := by
        apply Fin.ext
        have hmap := congrArg
          (fun d => (embedding.mapDart d).1.val) hsecond.symm
        calc
          globalPair.second.1.val = (embedding.mapDart localPair.second).1.val := rfl
          _ = (embedding.mapDart (j, false)).1.val := hmap
          _ = p.val := hposition
      have hglobalSecond :
          globalPair.second ∈ labelledDartPairEndpoints seed.balloonStemPairs := by
        unfold labelledDartPairEndpoints
        apply List.mem_flatMap.mpr
        refine ⟨globalPair, hglobalPair, ?_⟩
        change globalPair.second ∈ [globalPair.first, globalPair.second]
        exact List.mem_cons.mpr
          (Or.inr (List.mem_singleton.mpr rfl))
      have hpGlobal :
          p ∈ (labelledDartPairEndpoints seed.balloonStemPairs).map
            (fun d => d.1) := by
        apply List.mem_map.mpr
        exact ⟨globalPair.second, hglobalSecond, hsecondPos⟩
      have hpContradiction :
          p ∈ occurrencePairEndpoints seed.balloonStemOccurrencePairs := by
        rw [seed.balloonStemOccurrencePairs_endpoints_eq]
        exact hpGlobal
      exact False.elim (hnot hpContradiction)
  · have hbefore : balloon.label.conjugator.toWord.length ≤ j.val := by
      push_neg at hstemRegion
      omega
    have hafter : j.val < balloon.label.conjugator.toWord.length +
        balloon.label.relator.toWord.length := by
      push_neg at hstemRegion
      omega
    let sideIndex : Fin balloon.label.relator.toWord.length :=
      ⟨j.val - balloon.label.conjugator.toWord.length, by omega⟩
    have hsideDart : balloon.relatorSideDart sideIndex = (j, false) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [ReducedRelatorBalloonData.relatorSideDart_index]
        dsimp [sideIndex]
        omega
      · simp
    refine ⟨⟨i, sideIndex⟩, ?_⟩
    change ((embedding.mapDart
      (balloon.relatorSideDart sideIndex)).1) = p
    rw [hsideDart]
    apply Fin.ext
    exact hposition

/-- Across all balloons, a final unoriented edge class contains at most two
relator-side occurrences. Global flattened-position injectivity makes these
actual side occurrences distinct endpoints of the alternating pairing
component, rather than only a per-face bound. -/
theorem MinimalAreaRelatorBoundarySeed.card_relatorSideOccurrences_in_component_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent) :
    Nat.card {side : seed.RelatorSideOccurrence //
      seed.relatorSideOccurrencePosition side ∈ C.supp} ≤ 2 := by
  classical
  let sidePositionsInComponent := {side : seed.RelatorSideOccurrence //
    seed.relatorSideOccurrencePosition side ∈ C.supp}
  let unmatchedLeft := {v : C.supp //
    (componentLeftPairing seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing C).partner v = none}
  let unmatchedEither := {v : C.supp //
    (componentLeftPairing seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing C).partner v = none ∨
    (componentRightPairing seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing C).partner v = none}
  have hglobalNone (side : seed.RelatorSideOccurrence) :
      seed.balloonStemOccurrencePairing.partner
          (seed.relatorSideOccurrencePosition side) = none := by
    exact (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint
      (seed.relatorSideOccurrencePosition side)).2 (by
        exact seed.relatorSidePosition_unmatched_by_stem side.1 side.2)
  let toUnmatchedLeft : sidePositionsInComponent → unmatchedLeft := fun side =>
    ⟨⟨seed.relatorSideOccurrencePosition side.1, side.2⟩, by
      change PartialOccurrencePairing.restrictedPartner
        seed.balloonStemOccurrencePairing C.supp
          ⟨seed.relatorSideOccurrencePosition side.1, side.2⟩ = none
      cases hpartner : PartialOccurrencePairing.restrictedPartner
          seed.balloonStemOccurrencePairing C.supp
            ⟨seed.relatorSideOccurrencePosition side.1, side.2⟩ with
      | none => rfl
      | some v =>
          have hglobal :=
            (PartialOccurrencePairing.restrictedPartner_eq_some_iff
              seed.balloonStemOccurrencePairing C.supp
              ⟨seed.relatorSideOccurrencePosition side.1, side.2⟩ v).1 hpartner
          rw [hglobalNone side.1] at hglobal
          cases hglobal⟩
  have htoUnmatchedLeft : Function.Injective toUnmatchedLeft := by
    intro side₁ side₂ h
    apply Subtype.ext
    apply seed.relatorSideOccurrencePosition_injective
    exact congrArg (fun v : unmatchedLeft => v.1.1) h
  have hcardLeft : Fintype.card sidePositionsInComponent ≤
      Fintype.card unmatchedLeft :=
    Fintype.card_le_of_injective toUnmatchedLeft htoUnmatchedLeft
  have hcardMono : Fintype.card unmatchedLeft ≤ Fintype.card unmatchedEither :=
    Fintype.card_subtype_mono
      (fun v : C.supp =>
        (componentLeftPairing seed.balloonStemOccurrencePairing
          seed.boundaryCancellationPairing C).partner v = none)
      (fun v =>
        (componentLeftPairing seed.balloonStemOccurrencePairing
          seed.boundaryCancellationPairing C).partner v = none ∨
        (componentRightPairing seed.balloonStemOccurrencePairing
          seed.boundaryCancellationPairing C).partner v = none)
      (fun _ hv => Or.inl hv)
  have hcomponent := seed.card_component_unmatched_by_either_le_two C
  have hcomponent' : Fintype.card unmatchedEither ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, unmatchedEither] using hcomponent
  rw [Nat.card_eq_fintype_card]
  exact hcardLeft.trans (hcardMono.trans hcomponent')

/-- Counting each relator-side and surviving boundary occurrence separately,
the total number of incident ends in one alternating component is zero for a
cycle and exactly two for a path. The sum keeps a relator side that survives
on the boundary as two incidences at the same source position. -/
theorem MinimalAreaRelatorBoundarySeed.card_boundaryIncidences_in_component_eq_zero_or_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent) :
      Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0 ∨
    Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 2 := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  let leftPairing := componentLeftPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  let rightPairing := componentRightPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  let leftSlots := {v : C.supp // leftPairing.partner v = none}
  let rightSlots := {v : C.supp // rightPairing.partner v = none}
  let sideIncidences := {side : seed.RelatorSideOccurrence //
    seed.relatorSideOccurrencePosition side ∈ C.supp}
  let boundaryIncidences := {i : Fin seed.boundary.reducedLiteralBoundary.length //
    i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
    i ∈ C.supp}
  let incidenceSlots := leftSlots ⊕ rightSlots
  let toIncidenceSlots : sideIncidences ⊕ boundaryIncidences → incidenceSlots :=
    fun incidence =>
      match incidence with
      | Sum.inl side => Sum.inl ⟨⟨seed.relatorSideOccurrencePosition side.1,
          side.2⟩, by
            change PartialOccurrencePairing.restrictedPartner
              seed.balloonStemOccurrencePairing C.supp
                ⟨seed.relatorSideOccurrencePosition side.1, side.2⟩ = none
            have hnone := (seed.balloonStemOccurrencePairing_unpaired_iff_not_endpoint
              (seed.relatorSideOccurrencePosition side.1)).2
              (seed.relatorSidePosition_unmatched_by_stem side.1.1 side.1.2)
            cases hpartner : PartialOccurrencePairing.restrictedPartner
                seed.balloonStemOccurrencePairing C.supp
                  ⟨seed.relatorSideOccurrencePosition side.1, side.2⟩ with
            | none => rfl
            | some v =>
                have hglobal :=
                  (PartialOccurrencePairing.restrictedPartner_eq_some_iff
                    seed.balloonStemOccurrencePairing C.supp
                    ⟨seed.relatorSideOccurrencePosition side.1, side.2⟩ v).1 hpartner
                rw [hnone] at hglobal
                cases hglobal⟩
      | Sum.inr boundary => Sum.inr ⟨⟨boundary.1, boundary.2.2⟩, by
            change PartialOccurrencePairing.restrictedPartner
              seed.boundaryCancellationPairing C.supp
                ⟨boundary.1, boundary.2.2⟩ = none
            have hnone :=
              (IndexedBoundaryTrace.cancellationOccurrencePairing_unpaired_iff_survivor
                seed.reducedLollipopBoundaryTrace boundary.1).2 boundary.2.1
            cases hpartner : PartialOccurrencePairing.restrictedPartner
                seed.boundaryCancellationPairing C.supp
                  ⟨boundary.1, boundary.2.2⟩ with
            | none => rfl
            | some v =>
                have hglobal :=
                  (PartialOccurrencePairing.restrictedPartner_eq_some_iff
                    seed.boundaryCancellationPairing C.supp
                    ⟨boundary.1, boundary.2.2⟩ v).1 hpartner
                have hnone' : seed.boundaryCancellationPairing.partner boundary.1 = none := by
                  simpa [MinimalAreaRelatorBoundarySeed.boundaryCancellationPairing] using hnone
                rw [hnone'] at hglobal
                cases hglobal⟩
  have htoIncidenceSlots : Function.Injective toIncidenceSlots := by
    intro incidence₁ incidence₂ heq
    cases incidence₁ with
    | inl side₁ =>
        cases incidence₂ with
        | inl side₂ =>
            apply congrArg Sum.inl
            apply Subtype.ext
            apply seed.relatorSideOccurrencePosition_injective
            exact congrArg (fun v : leftSlots => v.1.1) (Sum.inl.inj heq)
        | inr boundary₂ => simp [toIncidenceSlots] at heq
    | inr boundary₁ =>
        cases incidence₂ with
        | inl side₂ => simp [toIncidenceSlots] at heq
        | inr boundary₂ =>
            apply congrArg Sum.inr
            apply Subtype.ext
            exact congrArg (fun v : rightSlots => v.1.1) (Sum.inr.inj heq)
  have htoIncidenceSlots_surjective : Function.Surjective toIncidenceSlots := by
    intro slot
    cases slot with
    | inl left =>
        have hglobalNone :=
          (componentLeftPairing_partner_none_iff
            seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C left.1).mp left.2
        obtain ⟨side, hside⟩ :=
          seed.exists_relatorSide_of_unmatched_by_stem left.1.1 hglobalNone
        have hsideC : seed.relatorSideOccurrencePosition side ∈ C.supp := by
          rw [hside]
          exact left.1.2
        refine ⟨Sum.inl ⟨side, hsideC⟩, ?_⟩
        simp only [toIncidenceSlots]
        apply congrArg Sum.inl
        apply Subtype.ext
        apply Subtype.ext
        exact hside
    | inr right =>
        have hglobalNone :=
          (componentRightPairing_partner_none_iff
            seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C right.1).mp right.2
        have hsurvivor :=
          (IndexedBoundaryTrace.cancellationOccurrencePairing_unpaired_iff_survivor
            seed.reducedLollipopBoundaryTrace right.1.1).mp hglobalNone
        let boundary : boundaryIncidences :=
          ⟨right.1.1, hsurvivor, right.1.2⟩
        refine ⟨Sum.inr boundary, ?_⟩
        simp only [toIncidenceSlots]
        apply congrArg Sum.inr
        apply Subtype.ext
        apply Subtype.ext
        rfl
  have hconn : (twoPairingGraph leftPairing rightPairing).Connected := by
    rw [twoPairingGraph_component_eq_induce
      seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing C]
    exact C.connected_toSimpleGraph
  let incidenceEquiv : sideIncidences ⊕ boundaryIncidences ≃ incidenceSlots :=
    Equiv.ofBijective toIncidenceSlots
      ⟨htoIncidenceSlots, htoIncidenceSlots_surjective⟩
  have hcard : Nat.card (sideIncidences ⊕ boundaryIncidences) =
      Nat.card incidenceSlots := Nat.card_congr incidenceEquiv
  rw [hcard]
  simpa only [incidenceSlots, leftSlots, rightSlots, leftPairing, rightPairing] using
    seed.card_component_unmatched_slots_eq_zero_or_two C

/-- The exact component incidence count implies the corresponding upper
bound, retained for edge-class corollaries. -/
theorem MinimalAreaRelatorBoundarySeed.card_boundaryIncidences_in_component_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent) :
    Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) ≤ 2 := by
  have h := seed.card_boundaryIncidences_in_component_eq_zero_or_two C
  rcases h with h | h <;> omega

/-- In the explicit pair-fold quotient, every edge class containing a
relator-side occurrence has exactly two incidences when relator sides and
surviving target-boundary occurrences are counted separately. A side that
survives on the target boundary contributes to both incidence families. -/
theorem MinimalAreaRelatorBoundarySeed.card_boundaryIncidences_in_edgeClass_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side₀ : seed.RelatorSideOccurrence) :
    Nat.card
      ({side : seed.RelatorSideOccurrence //
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
          Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side₀, false))} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
          Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side₀, false))}) = 2 := by
  classical
  let graph := twoPairingGraph seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing
  let C := graph.connectedComponentMk
    (seed.relatorSideOccurrencePosition side₀)
  let edgeClass := fun i : Fin seed.boundary.reducedLiteralBoundary.length =>
    (Quotient.mk
      (UnorientedDartSetoid
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)) :
      UnorientedDartClass seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
  let sourceSides := {side : seed.RelatorSideOccurrence //
    edgeClass (seed.relatorSideOccurrencePosition side) =
      edgeClass (seed.relatorSideOccurrencePosition side₀)}
  let targetSides := {side : seed.RelatorSideOccurrence //
    seed.relatorSideOccurrencePosition side ∈ C.supp}
  let sourceBoundary := {i : Fin seed.boundary.reducedLiteralBoundary.length //
    i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
    edgeClass i = edgeClass (seed.relatorSideOccurrencePosition side₀)}
  let targetBoundary := {i : Fin seed.boundary.reducedLiteralBoundary.length //
    i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
    i ∈ C.supp}
  have hproperty (i : Fin seed.boundary.reducedLiteralBoundary.length) :
      edgeClass i = edgeClass (seed.relatorSideOccurrencePosition side₀) ↔
        i ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    change edgeClass i = edgeClass (seed.relatorSideOccurrencePosition side₀) ↔
      graph.connectedComponentMk i =
        graph.connectedComponentMk (seed.relatorSideOccurrencePosition side₀)
    exact seed.unorientedEdgeClass_eq_iff_componentEq i
      (seed.relatorSideOccurrencePosition side₀)
  let sideEquiv : sourceSides ≃ targetSides :=
    { toFun := fun side => ⟨side.1,
        (hproperty (seed.relatorSideOccurrencePosition side.1)).mp side.2⟩
      invFun := fun side => ⟨side.1,
        (hproperty (seed.relatorSideOccurrencePosition side.1)).mpr side.2⟩
      left_inv := by intro side; apply Subtype.ext; rfl
      right_inv := by intro side; apply Subtype.ext; rfl }
  let boundaryEquiv : sourceBoundary ≃ targetBoundary :=
    { toFun := fun boundary => ⟨boundary.1, boundary.2.1,
        (hproperty boundary.1).mp boundary.2.2⟩
      invFun := fun boundary => ⟨boundary.1, boundary.2.1,
        (hproperty boundary.1).mpr boundary.2.2⟩
      left_inv := by intro boundary; apply Subtype.ext; rfl
      right_inv := by intro boundary; apply Subtype.ext; rfl }
  let incidenceEquiv : sourceSides ⊕ sourceBoundary ≃
      targetSides ⊕ targetBoundary := Equiv.sumCongr sideEquiv boundaryEquiv
  have hcomponent := seed.card_boundaryIncidences_in_component_eq_zero_or_two C
  have hcomponent' :
      Nat.card (targetSides ⊕ targetBoundary) = 0 ∨
        Nat.card (targetSides ⊕ targetBoundary) = 2 := by
    simpa [targetSides, targetBoundary] using hcomponent
  have hcard : Nat.card (sourceSides ⊕ sourceBoundary) =
      Nat.card (targetSides ⊕ targetBoundary) := Nat.card_congr incidenceEquiv
  have hpositive : 0 < Nat.card (sourceSides ⊕ sourceBoundary) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨Sum.inl ⟨side₀, rfl⟩⟩
  calc
    Nat.card (sourceSides ⊕ sourceBoundary) =
        Nat.card (targetSides ⊕ targetBoundary) := hcard
    _ = 2 := by
      rcases hcomponent' with hzero | htwo
      · rw [hcard, hzero] at hpositive
        omega
      · exact htwo

/-- The exact edge-class incidence count provides the upper bound used by
the boundary-edge corollary. -/
theorem MinimalAreaRelatorBoundarySeed.card_boundaryIncidences_in_edgeClass_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side₀ : seed.RelatorSideOccurrence) :
    Nat.card
      ({side : seed.RelatorSideOccurrence //
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
          Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side₀, false))} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
          Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side₀, false))}) ≤ 2 := by
  have h := seed.card_boundaryIncidences_in_edgeClass_eq_two side₀
  omega

/-- An edge class containing a surviving target-boundary occurrence has at
most one relator-side occurrence. This is the boundary-edge half of the
face/boundary incidence count in the pair-fold quotient. -/
theorem MinimalAreaRelatorBoundarySeed.card_relatorSideOccurrences_in_boundaryEdge_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side₀ : seed.RelatorSideOccurrence)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst)
    (hclass :
      (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side₀, false))) :
    Nat.card {side : seed.RelatorSideOccurrence //
      (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side₀, false))} ≤ 1 := by
  classical
  let edgeClass := fun j : Fin seed.boundary.reducedLiteralBoundary.length =>
    (Quotient.mk
      (UnorientedDartSetoid
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (j, false)) :
      UnorientedDartClass seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
  let sideIncidences := {side : seed.RelatorSideOccurrence //
    edgeClass (seed.relatorSideOccurrencePosition side) =
      edgeClass (seed.relatorSideOccurrencePosition side₀)}
  let boundaryIncidences := {j : Fin seed.boundary.reducedLiteralBoundary.length //
    j.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
    edgeClass j = edgeClass (seed.relatorSideOccurrencePosition side₀)}
  have hbound := seed.card_boundaryIncidences_in_edgeClass_le_two side₀
  have hsum : Fintype.card (sideIncidences ⊕ boundaryIncidences) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, edgeClass, sideIncidences,
      boundaryIncidences] using hbound
  have hboundary : 0 < Fintype.card boundaryIncidences :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi, hclass⟩⟩
  rw [Fintype.card_sum] at hsum
  have hside : Fintype.card sideIncidences ≤ 1 := by omega
  rw [Nat.card_eq_fintype_card]
  exact hside

/-- In the explicit quotient, an unoriented edge class contains at most two
relator-side occurrences across the whole minimum-area seed. -/
theorem MinimalAreaRelatorBoundarySeed.card_relatorSideOccurrences_in_edgeClass_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side₀ : seed.RelatorSideOccurrence) :
    Nat.card {side : seed.RelatorSideOccurrence //
      (Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side, false)) :
        UnorientedDartClass
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
      Quotient.mk
        (UnorientedDartSetoid
          seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart
          (seed.relatorSideOccurrencePosition side₀, false))} ≤ 2 := by
  classical
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
  let edgeClass := fun side : seed.RelatorSideOccurrence =>
    (Quotient.mk (UnorientedDartSetoid G)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart
        (seed.relatorSideOccurrencePosition side, false)) : UnorientedDartClass G)
  let graph := twoPairingGraph seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing
  let C := graph.connectedComponentMk
    (seed.relatorSideOccurrencePosition side₀)
  let S := {side : seed.RelatorSideOccurrence // edgeClass side = edgeClass side₀}
  let T := {side : seed.RelatorSideOccurrence //
    seed.relatorSideOccurrencePosition side ∈ C.supp}
  have hproperty (side : seed.RelatorSideOccurrence) :
      edgeClass side = edgeClass side₀ ↔
        seed.relatorSideOccurrencePosition side ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    change edgeClass side = edgeClass side₀ ↔
      graph.connectedComponentMk (seed.relatorSideOccurrencePosition side) =
        graph.connectedComponentMk (seed.relatorSideOccurrencePosition side₀)
    exact seed.unorientedEdgeClass_eq_iff_componentEq
      (seed.relatorSideOccurrencePosition side)
      (seed.relatorSideOccurrencePosition side₀)
  let e : S ≃ T :=
    { toFun := fun side => ⟨side.1, (hproperty side.1).mp side.2⟩
      invFun := fun side => ⟨side.1, (hproperty side.1).mpr side.2⟩
      left_inv := by intro side; apply Subtype.ext; rfl
      right_inv := by intro side; apply Subtype.ext; rfl }
  calc
    Nat.card {side : seed.RelatorSideOccurrence //
      edgeClass side = edgeClass side₀} = Nat.card T := Nat.card_congr e
    _ ≤ 2 := seed.card_relatorSideOccurrences_in_component_le_two C

/-- A source position that survives the boundary cancellation trace is
unmatched by its pairing. -/
theorem MinimalAreaRelatorBoundarySeed.boundaryCancellationPairing_unpaired_iff_survivor
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedLiteralBoundary.length) :
    seed.boundaryCancellationPairing.partner i = none ↔
      i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst := by
  exact IndexedBoundaryTrace.cancellationOccurrencePairing_unpaired_iff_survivor
    seed.reducedLollipopBoundaryTrace i

end GreendlingerDehn
