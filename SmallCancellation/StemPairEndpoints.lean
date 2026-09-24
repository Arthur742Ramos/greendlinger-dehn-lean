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

/-- The forward dart for one side of a balloon's relator boundary, transported
to the stored raw-word path. -/
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
            _ = d.2 := by
              simpa only [List.get_cons_succ'] using hinner

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
