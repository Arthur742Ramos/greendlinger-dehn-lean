import SmallCancellation.LollipopFolds
import SmallCancellation.FiniteFoldEuler
import SmallCancellation.PairingComponents
import SmallCancellation.PairingWalkParity
import SmallCancellation.PlanarBoundarySeed
import SmallCancellation.FoldedTraceReduction
import SmallCancellation.SurvivingIntervals

/-!
# Distinct occurrences in the balloon stem pairing

The occurrence pairs used to fold conjugator stems must form a matching before
they can be combined with the boundary-cancellation matching. This file proves
the basic lollipop case directly from the disjoint outward-stem and return-stem
positions in its literal boundary word.
-/

namespace GreendlingerDehn

private theorem finRange_successor_chain (n : Nat) :
    List.IsChain (fun i j : Fin n => i.val + 1 = j.val) (List.finRange n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      cases n with
      | zero => simp [List.finRange_zero]
      | succ n =>
          have htail : List.IsChain
              (fun i j : Fin (Nat.succ (Nat.succ n)) => i.val + 1 = j.val)
              (List.map Fin.succ (List.finRange (Nat.succ n))) := by
            apply List.isChain_map_of_isChain Fin.succ
            · intro i j hij
              simpa using hij
            · exact ih
          apply List.IsChain.cons htail
          intro j hj
          have hj' : j = Fin.succ 0 := by
            simpa [List.finRange_succ] using hj.symm
          subst j
          simp

/-- Consecutive doubled stem pairs meet at both ends in their literal
lollipop boundary path. -/
theorem lollipopStemPairs_isChain {α : Type*} (stem relator : Word α) :
    List.IsChain
      (LabelledDartPairChainStep
        (G := wordPathGraph (lollipopBoundaryWord stem relator)))
      (lollipopStemPairs stem relator) := by
  unfold lollipopStemPairs
  apply List.isChain_map_of_isChain (lollipopStemPair stem relator)
  · intro i j hij
    constructor <;>
      simp [LabelledDartPairChainStep, lollipopStemPair, wordPathGraph,
        lollipopStemFirstIndex, lollipopStemMateIndex] <;> omega
  · apply (finRange_successor_chain stem.length).imp
    intro i j hij
    exact hij.symm

private theorem castWordPath_refl {α : Type*} {u : Word α}
    (pair : LabelledDartPair (wordPathGraph u)) :
    LabelledDartPair.castWordPath rfl pair = pair := by
  cases pair
  rfl

private theorem pairChain_castWordPath {α : Type*} {u v : Word α} (h : u = v)
    {pairs : List (LabelledDartPair (wordPathGraph u))}
    (hchain : List.IsChain
      (LabelledDartPairChainStep (G := wordPathGraph u)) pairs) :
      List.IsChain (LabelledDartPairChainStep (G := wordPathGraph v))
      (pairs.map (LabelledDartPair.castWordPath h)) := by
  cases h
  have hmap : pairs.map (LabelledDartPair.castWordPath rfl) = pairs := by
    calc
      pairs.map (LabelledDartPair.castWordPath rfl) = pairs.map id := by
        apply List.map_congr_left
        intro pair hp
        exact castWordPath_refl pair
      _ = pairs := by simp
  rw [hmap]
  exact hchain

/-- The balloon's cast stem pairs retain the consecutive endpoint relations
of the lollipop positions. -/
theorem ReducedRelatorBalloonData.stemPairs_isChain {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P) :
    List.IsChain
      (LabelledDartPairChainStep (G := wordPathGraph b.label.rawWord))
      b.stemPairs := by
  unfold ReducedRelatorBalloonData.stemPairs
  exact pairChain_castWordPath b.label.lollipopBoundary_eq_rawWord
    (lollipopStemPairs_isChain
      b.label.conjugator.toWord b.label.relator.toWord)

private theorem castWordPath_eq_map {α : Type*} {u v : Word α} (h : u = v)
    (pair : LabelledDartPair (wordPathGraph u)) :
    LabelledDartPair.castWordPath h pair =
      LabelledDartPair.map (wordPathCastHom h) pair := by
  cases h
  cases pair
  rfl

/-- A lollipop's stem pairs are fold-adjacent after mapping its two outer
boundary endpoints to the same vertex. -/
theorem lollipopStemPairs_foldAdjacency {α : Type*}
    (stem relator : Word α) {H : LabelledDartGraph α}
    (f : LabelledGraphHom (wordPathGraph (lollipopBoundaryWord stem relator)) H)
    (hends : f.mapVertex (0 : Nat) =
      f.mapVertex (lollipopBoundaryWord stem relator).length) :
    LabelledDartPairFoldAdjacency H
      ((lollipopStemPairs stem relator).map (LabelledDartPair.map f)) := by
  apply LabelledDartPairFoldAdjacency.of_isChain
    (lollipopStemPairs_isChain stem relator) f
  intro pair hhead
  by_cases hzero : stem.length = 0
  · have hnil : lollipopStemPairs stem relator = [] := by
      simp [lollipopStemPairs, hzero]
    simp [hnil] at hhead
  · have hpos : 0 < stem.length := Nat.pos_of_ne_zero hzero
    let first := lollipopStemPair stem relator ⟨0, hpos⟩
    have hfinhead : (List.finRange stem.length).head? = some ⟨0, hpos⟩ := by
      rw [List.finRange_eq_pmap_range]
      simp [List.head?_range, hpos.ne']
    have hhead0 : (lollipopStemPairs stem relator).head? = some first := by
      change ((List.finRange stem.length).map
        (lollipopStemPair stem relator)).head? = some first
      rw [List.head?_map, hfinhead]
      rfl
    have hpair : pair = first :=
      Option.some.inj (hhead0.symm.trans hhead).symm
    subst pair
    right
    have hsource :
        (wordPathGraph (lollipopBoundaryWord stem relator)).toDartGraph.source
            first.first = (0 : Nat) := by
      simp [first, lollipopStemPair, lollipopStemFirstIndex, wordPathGraph]
    have htarget :
        (wordPathGraph (lollipopBoundaryWord stem relator)).toDartGraph.target
            first.second = (lollipopBoundaryWord stem relator).length := by
      simp [first, lollipopStemPair, lollipopStemMateIndex,
        lollipopBoundaryWord, wordPathGraph]
      omega
    calc
      H.toDartGraph.source (f.mapDart first.first) =
          f.mapVertex
            ((wordPathGraph (lollipopBoundaryWord stem relator)).toDartGraph.source
              first.first) := f.map_source _
      _ = f.mapVertex (0 : Nat) := congrArg f.mapVertex hsource
      _ = f.mapVertex (lollipopBoundaryWord stem relator).length := hends
      _ = f.mapVertex
          ((wordPathGraph (lollipopBoundaryWord stem relator)).toDartGraph.target
            first.second) := congrArg f.mapVertex htarget.symm
      _ = H.toDartGraph.target (f.mapDart first.second) := (f.map_target _).symm

/-- The cast stem pairs of a relator balloon can be folded sequentially in
any target graph that closes the raw balloon boundary. -/
theorem ReducedRelatorBalloonData.stemPairs_foldAdjacency {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P) {H : LabelledDartGraph α}
    (f : LabelledGraphHom (wordPathGraph b.label.rawWord) H)
    (hends : f.mapVertex (0 : Nat) = f.mapVertex b.label.rawWord.length) :
    LabelledDartPairFoldAdjacency H
      (b.stemPairs.map (LabelledDartPair.map f)) := by
  let h := b.label.lollipopBoundary_eq_rawWord
  let castHom := wordPathCastHom h
  let composedHom := LabelledGraphHom.comp f castHom
  have hlength : (lollipopBoundaryWord b.label.conjugator.toWord
      b.label.relator.toWord).length = b.label.rawWord.length :=
    congrArg List.length h
  have hends' : composedHom.mapVertex (0 : Nat) =
      composedHom.mapVertex
        (lollipopBoundaryWord b.label.conjugator.toWord b.label.relator.toWord).length := by
    change f.mapVertex (0 : Nat) = f.mapVertex
      (lollipopBoundaryWord b.label.conjugator.toWord b.label.relator.toWord).length
    exact hends.trans (congrArg f.mapVertex hlength.symm)
  have hlist :
      (lollipopStemPairs b.label.conjugator.toWord b.label.relator.toWord).map
          (LabelledDartPair.map composedHom) =
        b.stemPairs.map (LabelledDartPair.map f) := by
    unfold ReducedRelatorBalloonData.stemPairs
    simp only [List.map_map]
    apply List.map_congr_left
    intro pair hmem
    change LabelledDartPair.map composedHom pair =
      LabelledDartPair.map f (LabelledDartPair.castWordPath h pair)
    rw [castWordPath_eq_map h pair]
    simpa [composedHom, castHom] using
      (LabelledDartPairFoldAdjacency.mappedPair_comp f castHom pair).symm
  rw [← hlist]
  exact lollipopStemPairs_foldAdjacency
    b.label.conjugator.toWord b.label.relator.toWord composedHom hends'

/-- Stem folds for a list of relator balloons are adjacent when each balloon's
two outer endpoints are joined in the target graph. -/
theorem reducedBalloonStemPairs_foldAdjacency {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      {H : LabelledDartGraph α}
      (f : LabelledGraphHom
        (wordPathGraph ((balloons.map fun b => b.label.rawWord).flatten)) H),
      (∀ pair, pair ∈ reducedBalloonEndpointPairs balloons →
        f.mapVertex pair.1 = f.mapVertex pair.2) →
      LabelledDartPairFoldAdjacency H
        ((reducedBalloonStemPairs balloons).map (LabelledDartPair.map f)) := by
  intro balloons
  induction balloons with
  | nil =>
      intro H f hjoins
      exact .nil H
  | cons head tail ih =>
      intro H f hjoins
      let tailWord := (tail.map fun b => b.label.rawWord).flatten
      let prefixEmbedding := wordPathPrefixHom head.label.rawWord tailWord
      let suffix := wordPathSuffixHom head.label.rawWord tailWord
      let fHead := LabelledGraphHom.comp f prefixEmbedding
      let fTail := LabelledGraphHom.comp f suffix
      have hheadMem :
          (0, head.label.rawWord.length) ∈
            reducedBalloonEndpointPairs (head :: tail) := by
        rw [reducedBalloonEndpointPairs]
        exact List.Mem.head _
      have hheadEnds : fHead.mapVertex (0 : Nat) =
          fHead.mapVertex head.label.rawWord.length := by
        change f.mapVertex (prefixEmbedding.mapVertex (0 : Nat)) =
          f.mapVertex (prefixEmbedding.mapVertex head.label.rawWord.length)
        simpa [prefixEmbedding, wordPathPrefixHom, id] using hjoins
          (0, head.label.rawWord.length) hheadMem
      have htailJoins : ∀ pair,
          pair ∈ reducedBalloonEndpointPairs tail →
            fTail.mapVertex pair.1 = fTail.mapVertex pair.2 := by
        intro pair hpair
        have hpair' :
            (suffix.mapVertex pair.1, suffix.mapVertex pair.2) ∈
              reducedBalloonEndpointPairs (head :: tail) := by
          rw [reducedBalloonEndpointPairs]
          apply List.mem_cons.mpr
          right
          exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
        change f.mapVertex (suffix.mapVertex pair.1) =
          f.mapVertex (suffix.mapVertex pair.2)
        exact hjoins _ hpair'
      have hfirst := head.stemPairs_foldAdjacency fHead hheadEnds
      have hsecond := ih fTail htailJoins
      have hlist :
          (reducedBalloonStemPairs (head :: tail)).map
              (LabelledDartPair.map f) =
            (head.stemPairs.map (LabelledDartPair.map fHead)) ++
              ((reducedBalloonStemPairs tail).map (LabelledDartPair.map fTail)) := by
        rw [reducedBalloonStemPairs_cons, List.map_append]
        congr 1
        · rw [List.map_map]
          apply List.map_congr_left
          intro pair hp
          change LabelledDartPair.map f
              (LabelledDartPair.map prefixEmbedding pair) =
            LabelledDartPair.map fHead pair
          simpa [fHead, LabelledGraphHom.comp] using
            (LabelledDartPairFoldAdjacency.mappedPair_comp f prefixEmbedding pair)
        · rw [List.map_map]
          apply List.map_congr_left
          intro pair hp
          change LabelledDartPair.map f (LabelledDartPair.map suffix pair) =
            LabelledDartPair.map fTail pair
          simpa [fTail, LabelledGraphHom.comp] using
            (LabelledDartPairFoldAdjacency.mappedPair_comp f suffix pair)
      rw [hlist]
      exact LabelledDartPairFoldAdjacency.append hfirst hsecond

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

/-- Forget dart directions and retain the ordered source positions of a list
of occurrence pairs. -/
def wordPathDartPairPosition {α : Type*} (word : Word α)
    (pair : LabelledDartPair (wordPathGraph word)) : Nat × Nat :=
  let first : Fin word.length × Bool := pair.first
  let second : Fin word.length × Bool := pair.second
  (first.1.val, second.1.val)

def wordPathDartPairPositions {α : Type*} (word : Word α)
    (pairs : List (LabelledDartPair (wordPathGraph word))) : List (Nat × Nat) :=
  pairs.map (wordPathDartPairPosition word)

theorem wordPathDartPairPositions_append {α : Type*} (word : Word α)
    (left right : List (LabelledDartPair (wordPathGraph word))) :
    wordPathDartPairPositions word (left ++ right) =
      wordPathDartPairPositions word left ++ wordPathDartPairPositions word right := by
  simp [wordPathDartPairPositions]

private theorem wordPathDartPairPosition_map_prefix {α : Type*}
    (pre suf : Word α) (pair : LabelledDartPair (wordPathGraph pre)) :
    wordPathDartPairPosition (pre ++ suf)
        (LabelledDartPair.map (wordPathPrefixHom pre suf) pair) =
      wordPathDartPairPosition pre pair := by
  cases pair with
  | mk first second hinv =>
      simp [wordPathDartPairPosition, LabelledDartPair.map,
        wordPathPrefixHom, wordPathGraph]

private theorem wordPathDartPairPosition_map_suffix {α : Type*}
    (pre suf : Word α) (pair : LabelledDartPair (wordPathGraph suf)) :
    wordPathDartPairPosition (pre ++ suf)
        (LabelledDartPair.map (wordPathSuffixHom pre suf) pair) =
      (pre.length + (wordPathDartPairPosition suf pair).1,
        pre.length + (wordPathDartPairPosition suf pair).2) := by
  cases pair with
  | mk first second hinv =>
      simp [wordPathDartPairPosition, LabelledDartPair.map,
        wordPathSuffixHom, wordPathGraph]

private theorem wordPathDartPairPositions_map_prefix {α : Type*}
    (pre suf : Word α) (pairs : List (LabelledDartPair (wordPathGraph pre))) :
    wordPathDartPairPositions (pre ++ suf)
        (pairs.map (LabelledDartPair.map (wordPathPrefixHom pre suf))) =
      wordPathDartPairPositions pre pairs := by
  simp only [wordPathDartPairPositions, List.map_map]
  apply List.map_congr_left
  intro pair hp
  simpa only [Function.comp_def] using
    wordPathDartPairPosition_map_prefix pre suf pair

private theorem wordPathDartPairPositions_map_suffix {α : Type*}
    (pre suf : Word α) (pairs : List (LabelledDartPair (wordPathGraph suf))) :
    wordPathDartPairPositions (pre ++ suf)
        (pairs.map (LabelledDartPair.map (wordPathSuffixHom pre suf))) =
      (wordPathDartPairPositions suf pairs).map
        (fun p => (pre.length + p.1, pre.length + p.2)) := by
  simp only [wordPathDartPairPositions, List.map_map]
  apply List.map_congr_left
  intro pair hp
  simpa only [Function.comp_def] using
    wordPathDartPairPosition_map_suffix pre suf pair

private theorem wordPathDartPairPosition_cast {α : Type*}
    {u v : Word α} (h : u = v)
    (pair : LabelledDartPair (wordPathGraph u)) :
    wordPathDartPairPosition v (LabelledDartPair.castWordPath h pair) =
      wordPathDartPairPosition u pair := by
  simp [wordPathDartPairPosition, LabelledDartPair.castWordPath, Fin.cast]

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

private theorem lollipopStemPair_positions_compatible {α : Type*}
    (stem relator : Word α) (i j : Fin stem.length) :
    CancellationIntervalsCompatible
      ((lollipopStemFirstIndex stem relator i).val,
        (lollipopStemMateIndex stem relator i).val)
      ((lollipopStemFirstIndex stem relator j).val,
        (lollipopStemMateIndex stem relator j).val) := by
  unfold CancellationIntervalsCompatible
  by_cases hij : i.val ≤ j.val
  · by_cases heq : i.val = j.val
    · have heq' : i = j := Fin.ext heq
      subst j
      exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp⟩))
    · have hlt : i.val < j.val := by omega
      right
      right
      left
      constructor
      · simpa [lollipopStemFirstIndex] using hlt.le
      · simp only [lollipopStemMateIndex]
        omega
  · have hlt : j.val < i.val := by omega
    right
    right
    right
    constructor
    · simpa [lollipopStemFirstIndex] using hlt.le
    · simp only [lollipopStemMateIndex]
      omega

/-- The stem-fold intervals in a lollipop are nested: increasing the outward
stem position moves the return endpoint inward. -/
theorem lollipopStemPairs_positions_noncrossing {α : Type*}
    (stem relator : Word α) :
    CancellationPairsNoncrossing
      ((lollipopStemPairs stem relator).map fun pair =>
        (pair.first.1.val, pair.second.1.val)) := by
  intro p hp q hq
  rcases List.mem_map.mp hp with ⟨pairP, hpSource, rfl⟩
  rcases List.mem_map.mp hq with ⟨pairQ, hqSource, rfl⟩
  simp only [lollipopStemPairs, List.mem_map] at hpSource hqSource
  rcases hpSource with ⟨i, hi, hpairP⟩
  rcases hqSource with ⟨j, hj, hpairQ⟩
  have hpEq : pairP = lollipopStemPair stem relator i := hpairP.symm
  have hqEq : pairQ = lollipopStemPair stem relator j := hpairQ.symm
  subst pairP
  subst pairQ
  simpa [lollipopStemPair] using
    lollipopStemPair_positions_compatible stem relator i j

/-- Splitting a lollipop at a matched stem pair exposes the conjugate relator
word between the two stem occurrences. -/
theorem lollipopBoundaryWord_stemPair_decomposition {α : Type*}
    (stem relator : Word α) (i : Fin stem.length) :
    lollipopBoundaryWord stem relator =
      stem.take i.val ++ [stem.get i] ++
        (stem.drop (i.val + 1) ++ relator ++
          FreeGroup.invRev (stem.drop (i.val + 1))) ++
        [inverseLetter (stem.get i)] ++ FreeGroup.invRev (stem.take i.val) := by
  have hsplit : stem =
      stem.take i.val ++ [stem.get i] ++ stem.drop (i.val + 1) := by
    calc
      stem = stem.take (i.val + 1) ++ stem.drop (i.val + 1) :=
        (List.take_append_drop (i.val + 1) stem).symm
      _ = (stem.take i.val ++ [stem.get i]) ++ stem.drop (i.val + 1) := by
        rw [← List.take_concat_get' stem i.val i.isLt]
        simp only [List.get_eq_getElem]
  change stem ++ relator ++ FreeGroup.invRev stem = _
  conv_lhs => rw [hsplit]
  rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
  rw [show FreeGroup.invRev [stem.get i] =
      [inverseLetter (stem.get i)] by simp [FreeGroup.invRev, inverseLetter]]
  simp only [List.append_assoc]

/-- The interval inside a lollipop stem pair cannot represent the identity:
it is a conjugate of the nontrivial relator word. -/
theorem lollipopStemPair_interior_mk_ne_one {α : Type*}
    (stem relator : Word α) (i : Fin stem.length)
    (hrelator : FreeGroup.mk relator ≠ 1) :
    FreeGroup.mk
      (stem.drop (i.val + 1) ++ relator ++
        FreeGroup.invRev (stem.drop (i.val + 1))) ≠ 1 := by
  let tail := stem.drop (i.val + 1)
  have hconj : FreeGroup.mk (tail ++ relator ++ FreeGroup.invRev tail) =
      FreeGroup.mk tail * FreeGroup.mk relator * (FreeGroup.mk tail)⁻¹ := by
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  intro hnull
  have hconjNull :
      (FreeGroup.mk tail) * FreeGroup.mk relator * (FreeGroup.mk tail)⁻¹ = 1 :=
    hconj.symm.trans hnull
  have hrelatorNull : FreeGroup.mk relator = 1 :=
    (conjugate_eq_one_iff ((FreeGroup.mk tail)⁻¹)
      (FreeGroup.mk relator)).mp (by simpa using hconjNull)
  exact hrelator hrelatorNull

/-- Every local stem pair in a reduced balloon cuts out an interval whose
free-group value is a conjugate of that balloon's nontrivial relator. -/
theorem ReducedRelatorBalloonData.stemPair_interval_nontrivial
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (pair : LabelledDartPair (wordPathGraph b.label.rawWord))
    (hp : pair ∈ b.stemPairs) :
    ∃ (pre inner post : Word α) (a : Letter α),
      b.label.rawWord = pre ++ [a] ++ inner ++ [inverseLetter a] ++ post ∧
      (pair.first.1.val, pair.second.1.val) =
        (pre.length, pre.length + inner.length + 1) ∧
      FreeGroup.mk inner ≠ 1 := by
  let stem := b.label.conjugator.toWord
  let relator := b.label.relator.toWord
  have hp' : pair ∈
      ((List.finRange stem.length).map (lollipopStemPair stem relator)).map
        (LabelledDartPair.castWordPath b.label.lollipopBoundary_eq_rawWord) := by
    simpa [ReducedRelatorBalloonData.stemPairs, lollipopStemPairs, stem,
      relator] using hp
  rcases List.mem_map.mp hp' with ⟨localPair, hlocalPair, hpairMap⟩
  rcases List.mem_map.mp hlocalPair with ⟨i, hi, hlocal⟩
  have hpair : pair = LabelledDartPair.castWordPath
      b.label.lollipopBoundary_eq_rawWord (lollipopStemPair stem relator i) := by
    calc
      pair = LabelledDartPair.castWordPath
          b.label.lollipopBoundary_eq_rawWord localPair := hpairMap.symm
      _ = _ := congrArg
        (fun q => LabelledDartPair.castWordPath
          b.label.lollipopBoundary_eq_rawWord q) hlocal.symm
  have hfirst : pair.first.1.val = i.val := by
    rw [hpair]
    simp [LabelledDartPair.castWordPath, lollipopStemPair,
      lollipopStemFirstIndex]
  have hsecond : pair.second.1.val =
      stem.length + relator.length + (stem.length - (i.val + 1)) := by
    rw [hpair]
    simp [LabelledDartPair.castWordPath, lollipopStemPair,
      lollipopStemMateIndex, lollipopBoundaryWord]
  let pre := stem.take i.val
  let tail := stem.drop (i.val + 1)
  let inner := tail ++ relator ++ FreeGroup.invRev tail
  let post := FreeGroup.invRev pre
  have hword : b.label.rawWord =
      pre ++ [stem.get i] ++ inner ++
        [inverseLetter (stem.get i)] ++ post := by
    calc
      b.label.rawWord = lollipopBoundaryWord stem relator :=
        b.label.lollipopBoundary_eq_rawWord.symm
      _ = _ := lollipopBoundaryWord_stemPair_decomposition stem relator i
  have hpositions : (pair.first.1.val, pair.second.1.val) =
      (pre.length, pre.length + inner.length + 1) := by
    have hpre : pre.length = i.val := by simp [pre]
    have htail : tail.length = stem.length - (i.val + 1) := by simp [tail]
    have hinner : inner.length =
        tail.length + relator.length + tail.length := by
      simp [inner, List.length_append, FreeGroup.invRev_length]
      omega
    have hstem : stem.length = i.val + 1 + tail.length := by
      rw [htail]
      omega
    apply Prod.ext
    · rw [hfirst]
      exact hpre.symm
    · rw [hsecond, hpre, hinner, htail]
      omega
  have hrelator : FreeGroup.mk relator ≠ 1 := by
    intro h
    apply P.nontrivial b.label.relator b.label.relator_mem
    calc
      b.label.relator = FreeGroup.mk b.label.relator.toWord :=
        FreeGroup.mk_toWord.symm
      _ = 1 := h
  have hinner : FreeGroup.mk inner ≠ 1 := by
    simpa [inner, tail, stem, relator] using
      lollipopStemPair_interior_mk_ne_one stem relator i hrelator
  exact ⟨pre, inner, post, stem.get i, hword, hpositions, hinner⟩

/-- Stem folds in a concatenated minimum area boundary retain their local
nontrivial interval after the prefix or suffix embedding. -/
theorem reducedBalloonStemPair_interval_nontrivial
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (pair : LabelledDartPair
        (wordPathGraph ((balloons.map
          (fun b : ReducedRelatorBalloonData P => b.label.rawWord)).flatten))),
      pair ∈ reducedBalloonStemPairs balloons →
      ∃ (pre inner post : Word α) (a : Letter α),
        ((balloons.map
          (fun b : ReducedRelatorBalloonData P => b.label.rawWord)).flatten) =
          pre ++ [a] ++ inner ++ [inverseLetter a] ++ post ∧
        (pair.first.1.val, pair.second.1.val) =
          (pre.length, pre.length + inner.length + 1) ∧
        FreeGroup.mk inner ≠ 1 := by
  intro balloons
  induction balloons with
  | nil =>
      intro pair hpair
      simp [reducedBalloonStemPairs] at hpair
  | cons b tail ih =>
      intro pair hpair
      rw [reducedBalloonStemPairs_cons] at hpair
      rcases List.mem_append.mp hpair with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨sourcePair, hsource, hmap⟩
        obtain ⟨pre, inner, post, a, hword, hpositions, hnontrivial⟩ :=
          b.stemPair_interval_nontrivial sourcePair hsource
        let tailWord := (tail.map
          (fun x : ReducedRelatorBalloonData P => x.label.rawWord)).flatten
        have hfirst : pair.first.1.val = sourcePair.first.1.val := by
          rw [← hmap]
          simp [LabelledDartPair.map, wordPathPrefixHom]
        have hsecond : pair.second.1.val = sourcePair.second.1.val := by
          rw [← hmap]
          simp [LabelledDartPair.map, wordPathPrefixHom]
        refine ⟨pre, inner, post ++ tailWord, a, ?_, ?_, hnontrivial⟩
        · calc
            ((b :: tail).map
              (fun x : ReducedRelatorBalloonData P => x.label.rawWord)).flatten =
                b.label.rawWord ++ tailWord := rfl
            _ = (pre ++ [a] ++ inner ++ [inverseLetter a] ++ post) ++
                tailWord := by rw [hword]
            _ = pre ++ [a] ++ inner ++ [inverseLetter a] ++
                (post ++ tailWord) := by simp [List.append_assoc]
        · calc
            (pair.first.1.val, pair.second.1.val) =
                (sourcePair.first.1.val, sourcePair.second.1.val) :=
                  Prod.ext hfirst hsecond
            _ = (pre.length, pre.length + inner.length + 1) := hpositions
            _ = (pre.length, pre.length + inner.length + 1) := rfl
      · rcases List.mem_map.mp htail with ⟨sourcePair, hsource, hmap⟩
        obtain ⟨pre, inner, post, a, hword, hpositions, hnontrivial⟩ :=
          ih sourcePair hsource
        let tailWord := (tail.map
          (fun x : ReducedRelatorBalloonData P => x.label.rawWord)).flatten
        let pre' := b.label.rawWord ++ pre
        have hfirst : pair.first.1.val =
            b.label.rawWord.length + sourcePair.first.1.val := by
          rw [← hmap]
          simp [LabelledDartPair.map, wordPathSuffixHom]
        have hsecond : pair.second.1.val =
            b.label.rawWord.length + sourcePair.second.1.val := by
          rw [← hmap]
          simp [LabelledDartPair.map, wordPathSuffixHom]
        have hposFirst : sourcePair.first.1.val = pre.length :=
          congrArg Prod.fst hpositions
        have hposSecond : sourcePair.second.1.val =
            pre.length + inner.length + 1 := congrArg Prod.snd hpositions
        refine ⟨pre', inner, post, a, ?_, ?_, hnontrivial⟩
        · calc
            ((b :: tail).map
              (fun x : ReducedRelatorBalloonData P => x.label.rawWord)).flatten =
                b.label.rawWord ++ tailWord := rfl
            _ = b.label.rawWord ++
                (pre ++ [a] ++ inner ++ [inverseLetter a] ++ post) := by
                  simpa [tailWord] using
                    congrArg (fun x => b.label.rawWord ++ x) hword
            _ = pre' ++ [a] ++ inner ++ [inverseLetter a] ++ post := by
                  simp [pre', List.append_assoc]
        · apply Prod.ext
          · rw [hfirst, hposFirst]
            simp [pre', List.length_append]
          · rw [hsecond, hposSecond]
            simp only [pre', List.length_append]
            omega

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

/-- The vertex map of a balloon occurrence embedding shifts by the flattened
length of the balloons before that occurrence. -/
theorem reducedBalloonOccurrencePathEmbedding_vertex_formula
    {α : Type*} [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (i : Fin balloons.length) (v : Nat),
      (reducedBalloonOccurrencePathEmbedding balloons i).mapVertex v =
        ((balloons.take i.val).map
          (fun b => b.label.rawWord)).flatten.length + v := by
  intro balloons
  induction balloons with
  | nil => intro i; exact Fin.elim0 i
  | cons b tail ih =>
      intro i
      cases i using Fin.cases with
      | zero =>
          intro v
          rw [reducedBalloonOccurrencePathEmbedding_zero]
          simp [wordPathPrefixHom]
          rfl
      | succ i =>
          intro v
          rw [reducedBalloonOccurrencePathEmbedding_succ]
          change (wordPathSuffixHom b.label.rawWord
              ((tail.map fun b => b.label.rawWord).flatten)).mapVertex
              ((reducedBalloonOccurrencePathEmbedding tail i).mapVertex v) =
            ((b :: tail).take i.succ.val |>.map
              (fun b => b.label.rawWord)).flatten.length + v
          dsimp [wordPathSuffixHom]
          rw [ih i v]
          simp [id, List.map_cons, List.flatten_cons, Nat.add_assoc]
          rfl

/-- The source position of a forward dart in one balloon occurrence is its
local position shifted by the preceding balloon lengths. -/
theorem reducedBalloonOccurrencePathEmbedding_position_formula
    {α : Type*} [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α}
    (balloons : List (ReducedRelatorBalloonData P))
    (i : Fin balloons.length)
    (j : Fin (balloons.get i).label.rawWord.length) :
    (((reducedBalloonOccurrencePathEmbedding balloons i).mapDart
      (j, false)).1).val =
      ((balloons.take i.val).map
        (fun b => b.label.rawWord)).flatten.length + j.val := by
  let f := reducedBalloonOccurrencePathEmbedding balloons i
  have hsource := f.map_source (j, false)
  have hdirection :=
    reducedBalloonOccurrencePathEmbedding_direction balloons i (j, false)
  have hposition : (f.mapDart (j, false)).1.val = f.mapVertex j.val := by
    have hdirection' : (f.mapDart (j, false)).2 = false := by
      simpa using hdirection
    simpa [wordPathGraph, hdirection'] using hsource
  rw [hposition]
  exact reducedBalloonOccurrencePathEmbedding_vertex_formula balloons i j.val

/-- Splitting a flattened list of balloon words at one indexed balloon. -/
theorem reducedBalloonWords_flatten_split_at
    {α : Type*} [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α}
    (balloons : List (ReducedRelatorBalloonData P))
  (i : Fin balloons.length) :
    ((balloons.map fun b => b.label.rawWord).flatten) =
      ((balloons.take i.val).map fun b => b.label.rawWord).flatten ++
        (balloons.get i).label.rawWord ++
      ((balloons.drop (i.val + 1)).map fun b => b.label.rawWord).flatten := by
  let words := balloons.map fun b => b.label.rawWord
  have hi : i.val < words.length := by simpa [words] using i.isLt
  have hdrop : words.drop i.val = words[i.val] :: words.drop (i.val + 1) :=
    List.drop_eq_getElem_cons hi
  calc
    words.flatten = (words.take i.val ++ words.drop i.val).flatten := by
      rw [List.take_append_drop]
    _ = (words.take i.val).flatten ++ (words.drop i.val).flatten :=
      List.flatten_append
    _ = (words.take i.val).flatten ++
        words[i.val] ++ (words.drop (i.val + 1)).flatten := by
      rw [hdrop]
      simp only [List.flatten_cons]
      exact (List.append_assoc _ _ _).symm
    _ = _ := by
      simp [words, List.get_eq_getElem]

private theorem cancellationBracket_infix_of_bounds
    {α : Type*} {whole boundaryPrefix segment suffix pre inner post : Word α}
    {a : Letter α}
    (hwhole : whole = boundaryPrefix ++ segment ++ suffix)
    (hpair : whole = pre ++ [a] ++ inner ++ [inverseLetter a] ++ post)
    (hleft : boundaryPrefix.length ≤ pre.length)
    (hright : pre.length + inner.length + 1 <
      boundaryPrefix.length + segment.length) :
    ([a] ++ inner ++ [inverseLetter a]) <:+: segment := by
  have hprePrefix : pre.take boundaryPrefix.length = boundaryPrefix := by
    have ht := congrArg (fun x : Word α => x.take boundaryPrefix.length)
      (hwhole.symm.trans hpair)
    simpa [List.take_append_of_le_length hleft] using ht.symm
  have hpreSplit : pre = boundaryPrefix ++ pre.drop boundaryPrefix.length := by
    calc
      pre = pre.take boundaryPrefix.length ++ pre.drop boundaryPrefix.length :=
        (List.take_append_drop _ _).symm
      _ = boundaryPrefix ++ pre.drop boundaryPrefix.length := by rw [hprePrefix]
  have hwhole' : boundaryPrefix ++ (segment ++ suffix) =
      boundaryPrefix ++
        (pre.drop boundaryPrefix.length ++ [a] ++ inner ++
          [inverseLetter a] ++ post) := by
    calc
      boundaryPrefix ++ (segment ++ suffix) = whole := by
        rw [hwhole]
        simp [List.append_assoc]
      _ = pre ++ [a] ++ inner ++ [inverseLetter a] ++ post := hpair
      _ = boundaryPrefix ++
          (pre.drop boundaryPrefix.length ++ [a] ++ inner ++
            [inverseLetter a] ++ post) := by
        rw [hpreSplit]
        simp [List.append_assoc]
  have hrest : segment ++ suffix =
      pre.drop boundaryPrefix.length ++ [a] ++ inner ++
        [inverseLetter a] ++ post := List.append_cancel_left hwhole'
  let preSeg := pre.drop boundaryPrefix.length
  let core := preSeg ++ [a] ++ inner ++ [inverseLetter a]
  have hpreLength : pre.length = boundaryPrefix.length + preSeg.length := by
    have hdrop : preSeg.length = pre.length - boundaryPrefix.length := by
      simp [preSeg]
    omega
  have hright' : preSeg.length + inner.length + 1 < segment.length := by
    rw [hpreLength] at hright
    omega
  have hcoreLength : core.length = preSeg.length + inner.length + 2 := by
    simp [core, List.length_append, List.length_cons]
    omega
  have hcoreBound : core.length ≤ segment.length := by
    rw [hcoreLength]
    omega
  have hrestCore : segment ++ suffix = core ++ post := by
    simpa [core, preSeg, List.append_assoc] using hrest
  have htake : segment.take core.length = core := by
    have ht := congrArg (fun x : Word α => x.take core.length) hrestCore
    rw [List.take_append_of_le_length hcoreBound] at ht
    simpa using ht
  have hsegment : segment = core ++ segment.drop core.length := by
    calc
      segment = segment.take core.length ++ segment.drop core.length :=
        (List.take_append_drop _ _).symm
      _ = core ++ segment.drop core.length := by rw [htake]
  refine ⟨preSeg,
    segment.drop core.length, ?_⟩
  simpa [core, List.append_assoc] using hsegment.symm

/-- A null cancellation interior cannot have both endpoints inside one
freely reduced balloon boundary. -/
private theorem no_null_cancellation_interval_inside_reduced_segment
    {α : Type*} [DecidableEq α]
    {whole boundaryPrefix segment suffix pre inner post : Word α} {a : Letter α}
    (hwhole : whole = boundaryPrefix ++ segment ++ suffix)
    (hpair : whole = pre ++ [a] ++ inner ++ [inverseLetter a] ++ post)
    (hleft : boundaryPrefix.length ≤ pre.length)
    (hright : pre.length + inner.length + 1 <
      boundaryPrefix.length + segment.length)
    (hsegment : FreeGroup.IsReduced segment)
    (hnull : FreeGroup.mk inner = 1) : False := by
  have hbracket := cancellationBracket_infix_of_bounds
    hwhole hpair hleft hright
  have hinnerReduceNil : FreeGroup.reduce inner = [] := by
    have hword := congrArg FreeGroup.toWord hnull
    simpa only [FreeGroup.toWord_mk, FreeGroup.toWord_one] using hword
  have hinnerInBracket : inner <:+: ([a] ++ inner ++ [inverseLetter a]) := by
    refine ⟨[a], [inverseLetter a], ?_⟩
    simp [List.append_assoc]
  have hinnerInSegment := hinnerInBracket.trans hbracket
  have hinnerReduced : FreeGroup.IsReduced inner := hsegment.infix hinnerInSegment
  have hinnerNil : inner = [] := by
    calc
      inner = FreeGroup.reduce inner := hinnerReduced.reduce_eq.symm
      _ = [] := hinnerReduceNil
  have hpairInfix : ([a, inverseLetter a] : Word α) <:+: segment := by
    simpa [hinnerNil, List.append_assoc] using hbracket
  have hpairReduced := hsegment.infix hpairInfix
  have hcondition := (FreeGroup.isReduced_cons_cons.mp hpairReduced).1
  have hbits := hcondition rfl
  cases a with
  | mk generator sign => cases sign <;> simp [inverseLetter] at hbits

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

private theorem ReducedRelatorBalloonData.stemPairs_positions_noncrossing
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P) :
    CancellationPairsNoncrossing
      (wordPathDartPairPositions b.label.rawWord b.stemPairs) := by
  have hpositions : wordPathDartPairPositions b.label.rawWord b.stemPairs =
      wordPathDartPairPositions
        (lollipopBoundaryWord b.label.conjugator.toWord b.label.relator.toWord)
        (lollipopStemPairs b.label.conjugator.toWord b.label.relator.toWord) := by
    simp only [ReducedRelatorBalloonData.stemPairs,
      wordPathDartPairPositions, List.map_map]
    apply List.map_congr_left
    intro pair hp
    exact wordPathDartPairPosition_cast b.label.lollipopBoundary_eq_rawWord pair
  rw [hpositions]
  exact lollipopStemPairs_positions_noncrossing
    b.label.conjugator.toWord b.label.relator.toWord

/-- Stem-fold intervals remain noncrossing after the relator balloons are
flattened. Pairs within one balloon are nested; pairs from distinct balloons
are separated by their disjoint source-word intervals. -/
theorem reducedBalloonStemPairs_positions_noncrossing {α : Type*}
    [Fintype α] [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P)),
      CancellationPairsNoncrossing
        (wordPathDartPairPositions
          ((balloons.map fun b => b.label.rawWord).flatten)
          (reducedBalloonStemPairs balloons)) := by
  intro balloons
  induction balloons with
  | nil => simp [reducedBalloonStemPairs, wordPathDartPairPositions,
      CancellationPairsNoncrossing]
  | cons b tail ih =>
      change CancellationPairsNoncrossing
        (wordPathDartPairPositions
          (b.label.rawWord ++ (tail.map fun x => x.label.rawWord).flatten)
          (reducedBalloonStemPairs (b :: tail)))
      rw [reducedBalloonStemPairs_cons,
        wordPathDartPairPositions_append,
        wordPathDartPairPositions_map_prefix,
        wordPathDartPairPositions_map_suffix]
      have hhead : CancellationPairsNoncrossing
          (wordPathDartPairPositions b.label.rawWord b.stemPairs) :=
        b.stemPairs_positions_noncrossing
      have htail : CancellationPairsNoncrossing
          ((wordPathDartPairPositions
              ((tail.map fun x => x.label.rawWord).flatten)
              (reducedBalloonStemPairs tail)).map
            (fun p => (b.label.rawWord.length + p.1,
              b.label.rawWord.length + p.2))) := by
        intro p hp q hq
        rcases List.mem_map.mp hp with ⟨p₀, hp₀, rfl⟩
        rcases List.mem_map.mp hq with ⟨q₀, hq₀, rfl⟩
        exact (ih p₀ hp₀ q₀ hq₀).shift b.label.rawWord.length
      intro p hp q hq
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hq with hq | hq
        · exact hhead p hp q hq
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hpBound : p.2 < b.label.rawWord.length := by
            rcases List.mem_map.mp hp with ⟨pair, _, rfl⟩
            exact pair.second.1.isLt
          exact Or.inl (by omega)
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          have hqBound : q.2 < b.label.rawWord.length := by
            rcases List.mem_map.mp hq with ⟨pair, _, rfl⟩
            exact pair.second.1.isLt
          exact Or.inr (Or.inl (by omega))
        · exact htail p hp q hq

/-- The explicit minimum-area seed has the same nested stem intervals on its
complete literal boundary. -/
theorem MinimalAreaRelatorBoundarySeed.balloonStemIntervals_noncrossing
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    CancellationPairsNoncrossing
      (wordPathDartPairPositions seed.boundary.reducedLiteralBoundary
        seed.balloonStemPairs) := by
  simpa [MinimalAreaRelatorBoundarySeed.balloonStemPairs,
    RelatorFactorBoundarySeed.reducedLiteralBoundary] using
    reducedBalloonStemPairs_positions_noncrossing
      seed.boundary.reducedBalloons

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
      simp [LabelledDartPair.map,
        MinimalAreaRelatorBoundarySeed.balloonBoundaryHom,
        wordPathBoundaryHomWithJoins]

/-- Each source cancellation pair in the seed encloses a contiguous subword
whose free-group value is the identity. The decomposition is the word-level
form of the nested cancellation interval, and is available for later
comparison with consecutive factor blocks. -/
theorem MinimalAreaRelatorBoundarySeed.cancellationPair_has_null_interior
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (p : Nat × Nat)
    (hp : p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs) :
    ∃ (pre inner post : Word α) (a : Letter α),
      seed.boundary.reducedLiteralBoundary =
        pre ++ [a] ++ inner ++ [inverseLetter a] ++ post ∧
      p = (pre.length, pre.length + inner.length + 1) ∧
      FreeGroup.mk inner = 1 :=
  seed.boundary.reducedLiteralBoundaryShape.cancellationPair_interior_mk_eq_one p hp

/-- A source cancellation pair in a minimum area boundary cannot have both
endpoints in one reduced relator balloon. -/
theorem MinimalAreaRelatorBoundarySeed.cancellationPair_not_within_one_balloon
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (p : Nat × Nat)
    (hp : p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs)
    (i : Fin seed.boundary.reducedBalloons.length)
    (j k : Fin (seed.boundary.reducedBalloons.get i).label.rawWord.length)
    (hfirst :
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i).mapDart (j, false)).1).val = p.1)
    (hsecond :
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i).mapDart (k, false)).1).val = p.2) :
    False := by
  let balloons := seed.boundary.reducedBalloons
  let balloon := balloons.get i
  let prefixWord := ((balloons.take i.val).map
    fun b => b.label.rawWord).flatten
  let suffixWord := ((balloons.drop (i.val + 1)).map
    fun b => b.label.rawWord).flatten
  have hwhole : seed.boundary.reducedLiteralBoundary =
      prefixWord ++ balloon.label.rawWord ++ suffixWord := by
    dsimp [prefixWord, suffixWord, balloon, balloons,
      RelatorFactorBoundarySeed.reducedLiteralBoundary]
    exact reducedBalloonWords_flatten_split_at
      seed.boundary.reducedBalloons i
  have hfirstPosition := reducedBalloonOccurrencePathEmbedding_position_formula
    seed.boundary.reducedBalloons i j
  have hsecondPosition := reducedBalloonOccurrencePathEmbedding_position_formula
    seed.boundary.reducedBalloons i k
  have hleft : prefixWord.length ≤ p.1 := by
    rw [← hfirst, hfirstPosition]
    exact Nat.le_add_right _ _
  have hright : p.2 < prefixWord.length + balloon.label.rawWord.length := by
    rw [← hsecond, hsecondPosition]
    exact Nat.add_lt_add_left k.isLt _
  obtain ⟨pre, inner, post, a, hpair, hpositions, hnull⟩ :=
    seed.cancellationPair_has_null_interior p hp
  have hpositionFirst : p.1 = pre.length := congrArg Prod.fst hpositions
  have hpositionSecond : p.2 = pre.length + inner.length + 1 :=
    congrArg Prod.snd hpositions
  have hleft' : prefixWord.length ≤ pre.length := by omega
  have hright' : pre.length + inner.length + 1 <
      prefixWord.length + balloon.label.rawWord.length := by omega
  exact no_null_cancellation_interval_inside_reduced_segment
    hwhole hpair hleft' hright' balloon.boundary_reduced hnull

/-- Every cancellation pair in the flattened minimum area boundary joins
occurrences from distinct reduced relator balloons. -/
theorem MinimalAreaRelatorBoundarySeed.cancellationPair_spans_distinct_balloons
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (p : Nat × Nat)
    (hp : p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs) :
    ∃ (i₁ i₂ : Fin seed.boundary.reducedBalloons.length)
      (j₁ : Fin (seed.boundary.reducedBalloons.get i₁).label.rawWord.length)
      (j₂ : Fin (seed.boundary.reducedBalloons.get i₂).label.rawWord.length),
      i₁ ≠ i₂ ∧
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i₁).mapDart (j₁, false)).1).val = p.1 ∧
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i₂).mapDart (j₂, false)).1).val = p.2 := by
  obtain ⟨pre, inner, post, a, hpair, hpositions, _⟩ :=
    seed.cancellationPair_has_null_interior p hp
  have hpositionFirst : p.1 = pre.length := congrArg Prod.fst hpositions
  have hpositionSecond : p.2 = pre.length + inner.length + 1 :=
    congrArg Prod.snd hpositions
  have hfirstBound : p.1 < seed.boundary.reducedLiteralBoundary.length := by
    rw [hpositionFirst, hpair]
    simp only [List.length_append, List.length_cons]
    omega
  have hsecondBound : p.2 < seed.boundary.reducedLiteralBoundary.length := by
    rw [hpositionSecond, hpair]
    simp only [List.length_append, List.length_cons]
    omega
  let first : Fin (((seed.boundary.reducedBalloons.map
      fun b => b.label.rawWord).flatten).length) :=
    ⟨p.1, by simpa [RelatorFactorBoundarySeed.reducedLiteralBoundary] using hfirstBound⟩
  let second : Fin (((seed.boundary.reducedBalloons.map
      fun b => b.label.rawWord).flatten).length) :=
    ⟨p.2, by simpa [RelatorFactorBoundarySeed.reducedLiteralBoundary] using hsecondBound⟩
  obtain ⟨i₁, j₁, hmap₁⟩ :=
    reducedBalloonOccurrencePathEmbedding_position_surjective
      seed.boundary.reducedBalloons first
  obtain ⟨i₂, j₂, hmap₂⟩ :=
    reducedBalloonOccurrencePathEmbedding_position_surjective
      seed.boundary.reducedBalloons second
  have hposition₁ :
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i₁).mapDart (j₁, false)).1).val = p.1 := by
    simpa [first] using hmap₁
  have hposition₂ :
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i₂).mapDart (j₂, false)).1).val = p.2 := by
    simpa [second] using hmap₂
  have hdistinct : i₁ ≠ i₂ := by
    intro heq
    subst i₂
    exact seed.cancellationPair_not_within_one_balloon
      p hp i₁ j₁ j₂ hposition₁ hposition₂
  exact ⟨i₁, i₂, j₁, j₂, hdistinct, hposition₁, hposition₂⟩

private theorem reducedBalloonPrefix_ends_before_later_prefix
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α}
    (balloons : List (ReducedRelatorBalloonData P))
    (i j : Fin balloons.length) (hij : i.val < j.val) :
    ((balloons.take i.val).map fun b => b.label.rawWord).flatten.length +
        (balloons.get i).label.rawWord.length ≤
      ((balloons.take j.val).map fun b => b.label.rawWord).flatten.length := by
  induction balloons with
  | nil => exact Fin.elim0 i
  | cons b tail ih =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              have hget : (b :: tail).get (0 : Fin (b :: tail).length) = b := by
                rfl
              have hoffset :
                  (( (b :: tail).take (0 : Fin (b :: tail).length).val).map
                    (fun b => b.label.rawWord)).flatten.length = 0 := by
                rfl
              have htake : (b :: tail).take j.succ.val = b :: tail.take j.val := by
                simp
              rw [hoffset, Nat.zero_add, hget]
              change b.label.rawWord.length ≤
                (((b :: tail).take j.succ.val).map
                  (fun b => b.label.rawWord)).flatten.length
              rw [htake]
              simp only [List.map_cons, List.flatten_cons, List.length_append]
              exact Nat.le_add_right _ _
      | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              have hij' : i.val < j.val := by simpa using hij
              have htail := ih i j hij'
              simpa [List.take, List.map_cons, List.flatten_cons,
                List.get_cons_succ', Nat.add_assoc] using
                  (Nat.add_le_add_left htail b.label.rawWord.length)

/-- Cancellation endpoints occur in distinct balloons, and their balloon
indices increase in the same order as the source positions. -/
theorem MinimalAreaRelatorBoundarySeed.cancellationPair_balloonIndices_strictly_increase
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (p : Nat × Nat)
    (hp : p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs) :
    ∃ (i₁ i₂ : Fin seed.boundary.reducedBalloons.length)
      (j₁ : Fin (seed.boundary.reducedBalloons.get i₁).label.rawWord.length)
      (j₂ : Fin (seed.boundary.reducedBalloons.get i₂).label.rawWord.length),
      i₁.val < i₂.val ∧
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i₁).mapDart (j₁, false)).1).val = p.1 ∧
      (((reducedBalloonOccurrencePathEmbedding
        seed.boundary.reducedBalloons i₂).mapDart (j₂, false)).1).val = p.2 := by
  obtain ⟨i₁, i₂, j₁, j₂, hdistinct, hposition₁, hposition₂⟩ :=
    seed.cancellationPair_spans_distinct_balloons p hp
  obtain ⟨pre, inner, post, a, _hpair, hpositions, _hnull⟩ :=
    seed.cancellationPair_has_null_interior p hp
  have hsourceOrder : p.1 < p.2 := by
    have hfirst := congrArg Prod.fst hpositions
    have hsecond := congrArg Prod.snd hpositions
    omega
  have hindexOrder : i₁.val < i₂.val := by
    by_contra hnot
    have hreverse : i₂.val < i₁.val := by omega
    let balloons := seed.boundary.reducedBalloons
    have hoffset := reducedBalloonPrefix_ends_before_later_prefix
      balloons i₂ i₁ hreverse
    have hposition₂' : p.2 =
        ((balloons.take i₂.val).map fun b => b.label.rawWord).flatten.length + j₂.val := by
      rw [← hposition₂]
      exact reducedBalloonOccurrencePathEmbedding_position_formula balloons i₂ j₂
    have hposition₁' : p.1 =
        ((balloons.take i₁.val).map fun b => b.label.rawWord).flatten.length + j₁.val := by
      rw [← hposition₁]
      exact reducedBalloonOccurrencePathEmbedding_position_formula balloons i₁ j₁
    have hbefore : p.2 <
        ((balloons.take i₂.val).map fun b => b.label.rawWord).flatten.length +
          (balloons.get i₂).label.rawWord.length := by
      rw [hposition₂']
      exact Nat.add_lt_add_left j₂.isLt _
    have hafter :
        ((balloons.take i₁.val).map fun b => b.label.rawWord).flatten.length ≤ p.1 := by
      rw [hposition₁']
      omega
    omega
  exact ⟨i₁, i₂, j₁, j₂, hindexOrder, hposition₁, hposition₂⟩

/-- In the direct pair-fold quotient, each global free-cancellation pair is
already represented by opposite dart occurrences of the original boundary
walk. This lets us shorten the walk without making any further graph folds. -/
noncomputable def MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold_cancellationOppositeDarts
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {p : Nat × Nat}
    (hp : p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs) :
    seed.boundaryOccurrenceDartPairFold.walk.OppositeDartsAt p := by
  classical
  let trace := seed.reducedLollipopBoundaryTrace
  have hbounds := trace.pairs_inBounds p (by
    simpa [trace, MinimalAreaRelatorBoundarySeed.reducedLollipopBoundaryTrace,
      FreeReductionShape.toIndexedBoundaryTrace] using hp)
  let first : Fin seed.boundary.reducedLiteralBoundary.length :=
    ⟨p.1, by omega⟩
  let second : Fin seed.boundary.reducedLiteralBoundary.length :=
    ⟨p.2, hbounds.2⟩
  have htrace : (first, second) ∈ trace.cancellationOccurrencePairs := by
    simpa [first, second, trace] using
      trace.mem_cancellationOccurrencePairs (p := p) (by
        simpa [trace, MinimalAreaRelatorBoundarySeed.reducedLollipopBoundaryTrace,
          FreeReductionShape.toIndexedBoundaryTrace] using hp)
  have hposition : (first, second) ∈
      seed.boundaryCancellationDartPairs.map
        (fun pair => (pair.first.1, pair.second.1)) := by
    exact seed.boundaryCancellationDartPairs_positions.symm ▸ htrace
  let pair : LabelledDartPair seed.balloonBoundaryGraph :=
    Classical.choose (List.mem_map.mp hposition)
  have hpairFacts := Classical.choose_spec (List.mem_map.mp hposition)
  have hpair : pair ∈ seed.boundaryCancellationDartPairs := hpairFacts.1
  have hindices : (pair.first.1, pair.second.1) = (first, second) :=
    hpairFacts.2
  have hforward := seed.boundaryOccurrenceDartPairFold_forward pair
    (List.mem_append_right _ hpair)
  have hfirstIndex : pair.first.1 = first :=
    congrArg (fun x : Fin seed.boundary.reducedLiteralBoundary.length ×
      Fin seed.boundary.reducedLiteralBoundary.length => x.1) hindices
  have hsecondIndex : pair.second.1 = second :=
    congrArg (fun x : Fin seed.boundary.reducedLiteralBoundary.length ×
      Fin seed.boundary.reducedLiteralBoundary.length => x.2) hindices
  have hfirstPair : pair.first = (first, false) := by
    apply Prod.ext
    · exact hfirstIndex
    · exact hforward.1
  have hsecondPair : pair.second = (second, false) := by
    apply Prod.ext
    · exact hsecondIndex
    · exact hforward.2
  have hsourceFirst : seed.balloonBoundaryLoop.darts[p.1]? = some (first, false) := by
    change (wordBoundaryLoopWithJoins seed.boundary.reducedLiteralBoundary
      seed.balloonEndpointPairs).darts[p.1]? = some (first, false)
    exact wordBoundaryLoopWithJoins_darts_get
      seed.boundary.reducedLiteralBoundary seed.balloonEndpointPairs first
  have hsourceSecond : seed.balloonBoundaryLoop.darts[p.2]? = some (second, false) := by
    change (wordBoundaryLoopWithJoins seed.boundary.reducedLiteralBoundary
      seed.balloonEndpointPairs).darts[p.2]? = some (second, false)
    exact wordBoundaryLoopWithJoins_darts_get
      seed.boundary.reducedLiteralBoundary seed.balloonEndpointPairs second
  let folded := seed.boundaryOccurrenceDartPairFold
  have hmap := LabelledWalk.darts_map folded.hom seed.balloonBoundaryLoop
  have hfirstAt : folded.walk.darts[p.1]? =
      some (folded.hom.mapDart pair.first) := by
    change (seed.balloonBoundaryLoop.map folded.hom).darts[p.1]? = _
    have hindexed :
        (seed.balloonBoundaryLoop.map folded.hom).darts[p.1]? =
          (seed.balloonBoundaryLoop.darts[p.1]?).map folded.hom.mapDart := by
      have hlist := congrArg (fun ds : List _ => ds[p.1]?) hmap
      rw [List.getElem?_map] at hlist
      exact hlist
    calc
      (seed.balloonBoundaryLoop.map folded.hom).darts[p.1]? =
          (seed.balloonBoundaryLoop.darts[p.1]?).map folded.hom.mapDart := hindexed
      _ = some (folded.hom.mapDart pair.first) := by
        rw [hsourceFirst]
        rw [hfirstPair]
        rfl
  have hsecondAt : folded.walk.darts[p.2]? =
      some (folded.hom.mapDart pair.second) := by
    change (seed.balloonBoundaryLoop.map folded.hom).darts[p.2]? = _
    have hindexed :
        (seed.balloonBoundaryLoop.map folded.hom).darts[p.2]? =
          (seed.balloonBoundaryLoop.darts[p.2]?).map folded.hom.mapDart := by
      have hlist := congrArg (fun ds : List _ => ds[p.2]?) hmap
      rw [List.getElem?_map] at hlist
      exact hlist
    calc
      (seed.balloonBoundaryLoop.map folded.hom).darts[p.2]? =
          (seed.balloonBoundaryLoop.darts[p.2]?).map folded.hom.mapDart := hindexed
      _ = some (folded.hom.mapDart pair.second) := by
        rw [hsourceSecond]
        rw [hsecondPair]
        rfl
  change folded.walk.OppositeDartsAt p
  exact ⟨folded.hom.mapDart pair.first, folded.hom.mapDart pair.second,
    hfirstAt, hsecondAt,
    seed.boundaryOccurrenceDartPairFold_cancellation_reverse pair hpair⟩

/-- The direct pair-fold graph carries the boundary shortened by the recorded
global free-reduction trace, with no new edge identifications. -/
noncomputable def MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairReducedWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    WalkFoldResult
      (u₀ := Quotient.mk
        (BoundaryVertexJoinSetoid seed.boundary.reducedLiteralBoundary.length
          seed.balloonEndpointPairs) 0)
      (v₀ := Quotient.mk
        (BoundaryVertexJoinSetoid seed.boundary.reducedLiteralBoundary.length
          seed.balloonEndpointPairs) 0)
      seed.balloonBoundaryGraph w.toWord := by
  let folded := seed.boundaryOccurrenceDartPairFold
  refine ⟨folded.graph, folded.hom, ?_, folded.hom_surjective⟩
  exact seed.boundary.reducedLiteralBoundaryShape.reduceWalkByFoldedPairs
    folded.walk (fun p hp =>
      seed.boundaryOccurrenceDartPairFold_cancellationOppositeDarts
        (p := p) hp)

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
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
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

/-- Every step in the alternating occurrence graph reverses the orientation of
the corresponding folded dart. -/
theorem MinimalAreaRelatorBoundarySeed.mapDart_reverse_of_pairingGraph_adj
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hadj : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Adj v x) :
    let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      G.reverse (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) := by
  classical
  let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
  let pairs := seed.boundaryBalloonStemPairs ++ seed.boundaryCancellationDartPairs
  have hrel : occurrencePairRel
      (seed.balloonStemOccurrencePairs ++
        seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairs) v x := by
    rw [occurrencePairRel_append_iff]
    rcases hadj with hstem | hcancel
    · exact Or.inl (seed.balloonStemOccurrencePairing_spec v x |>.1 hstem)
    · exact Or.inr
        (seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairing_spec
          v x |>.1 hcancel)
  have hpositions := seed.boundaryOccurrenceDartPairFold_positions
  rw [← hpositions] at hrel
  rcases hrel with ⟨p, hp, hpvx | hpwx⟩
  · rcases List.mem_map.mp hp with ⟨pair, hpair, hpos⟩
    have hforward := seed.boundaryOccurrenceDartPairFold_forward pair hpair
    have hfold := WalkFoldResult.foldPairs_pair_reverse
      pairs seed.balloonBoundaryLoop pair hpair
    have hfirst : pair.first = (v, false) :=
      Prod.ext ((congrArg Prod.fst hpos).trans hpvx.1) hforward.1
    have hsecond : pair.second = (x, false) :=
      Prod.ext ((congrArg Prod.snd hpos).trans hpvx.2) hforward.2
    dsimp [pairs, MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold]
      at hfold ⊢
    simpa [hfirst, hsecond] using hfold
  · rcases List.mem_map.mp hp with ⟨pair, hpair, hpos⟩
    have hforward := seed.boundaryOccurrenceDartPairFold_forward pair hpair
    have hfold := WalkFoldResult.foldPairs_pair_reverse
      pairs seed.balloonBoundaryLoop pair hpair
    have hfirst : pair.first = (x, false) :=
      Prod.ext ((congrArg Prod.fst hpos).trans hpwx.1) hforward.1
    have hsecond : pair.second = (v, false) :=
      Prod.ext ((congrArg Prod.snd hpos).trans hpwx.2) hforward.2
    have hfold' :
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false) =
          G.reverse
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
      simpa [G, pairs, MinimalAreaRelatorBoundarySeed.boundaryOccurrenceDartPairFold,
        hfirst, hsecond] using hfold
    calc
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
          G.reverse (G.reverse
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false))) :=
        (G.reverse_involutive _).symm
      _ = G.reverse
          (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) := by
        rw [hfold'.symm]

private theorem MinimalAreaRelatorBoundarySeed.mapDart_orientation_of_pairingWalk_mod
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {v x : Fin seed.boundary.reducedLiteralBoundary.length}
    (path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x) :
    if path.length % 2 = 0 then
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
        seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)
    else
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
          (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) := by
  induction path with
  | nil => simp
  | @cons v y x hadj tail ih =>
      have hstep := seed.mapDart_reverse_of_pairingGraph_adj v y hadj
      let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
      change (if (tail.length + 1) % 2 = 0 then
        seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
          seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)
      else
        seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
          G.reverse (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)))
      by_cases htail : tail.length % 2 = 0
      · have htailEq :
            seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
              seed.boundaryOccurrenceDartPairFold.hom.mapDart (y, false) := by
          simpa [htail] using ih
        have hfull : (tail.length + 1) % 2 = 1 := by omega
        simp only [hfull]
        exact htailEq.trans hstep
      · have htailOne : tail.length % 2 = 1 := by omega
        have htailEq :
            seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
              G.reverse
                (seed.boundaryOccurrenceDartPairFold.hom.mapDart (y, false)) := by
          simpa [htailOne] using ih
        have hfull : (tail.length + 1) % 2 = 0 := by omega
        simp only [hfull]
        calc
          seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
              G.reverse
                (seed.boundaryOccurrenceDartPairFold.hom.mapDart (y, false)) := htailEq
          _ = G.reverse (G.reverse
                (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false))) := by
                rw [hstep]
          _ = seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false) :=
                G.reverse_involutive _

theorem MinimalAreaRelatorBoundarySeed.mapDart_eq_of_even_pairingWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {v x : Fin seed.boundary.reducedLiteralBoundary.length}
    (path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x)
    (heven : Even path.length) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false) := by
  have hmod : path.length % 2 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp (even_iff_two_dvd.mp heven)
  have h := seed.mapDart_orientation_of_pairingWalk_mod path
  simpa [hmod] using h

theorem MinimalAreaRelatorBoundarySeed.mapDart_reverse_of_odd_pairingWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    {v x : Fin seed.boundary.reducedLiteralBoundary.length}
    (path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x)
    (hodd : Odd path.length) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) := by
  have hmod : path.length % 2 = 1 := Nat.odd_iff.mp hodd
  have h := seed.mapDart_orientation_of_pairingWalk_mod path
  simpa [hmod] using h

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

private theorem MinimalAreaRelatorBoundarySeed.exists_simplePairingPath_of_edgeClass_eq
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
    ∃ path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x, path.IsPath := by
  have hcomponent :=
    (seed.unorientedEdgeClass_eq_iff_componentEq v x).mp hclass
  have hreachable :
      (twoPairingGraph seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing).Reachable v x :=
    SimpleGraph.ConnectedComponent.eq.mp hcomponent
  exact hreachable.exists_isPath

/-- Equal folded edges determine a simple alternating-pairing path. If both
ends are unmatched by the stem pairing, that path has odd length. -/
theorem MinimalAreaRelatorBoundarySeed.exists_odd_stemEndpointPath_of_edgeClass_eq
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
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)))
    (hne : v ≠ x)
    (hv : seed.balloonStemOccurrencePairing.partner v = none)
    (hx : seed.balloonStemOccurrencePairing.partner x = none) :
    ∃ path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x,
      path.IsPath ∧ Odd path.length := by
  obtain ⟨path, hpath⟩ := seed.exists_simplePairingPath_of_edgeClass_eq v x hclass
  exact ⟨path, hpath,
    pairingWalk_length_odd_of_leftUnpaired_endpoints
      seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing
      path hpath hne hv hx⟩

/-- If the two ends of a folded edge class are both unmatched by the boundary
cancellation pairing, their simple alternating path has odd length. -/
theorem MinimalAreaRelatorBoundarySeed.exists_odd_boundaryEndpointPath_of_edgeClass_eq
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
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)))
    (hne : v ≠ x)
    (hv : seed.boundaryCancellationPairing.partner v = none)
    (hx : seed.boundaryCancellationPairing.partner x = none) :
    ∃ path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x,
      path.IsPath ∧ Odd path.length := by
  obtain ⟨path, hpath⟩ := seed.exists_simplePairingPath_of_edgeClass_eq v x hclass
  exact ⟨path, hpath,
    pairingWalk_length_odd_of_rightUnpaired_endpoints
      seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing
      path hpath hne hv hx⟩

/-- A face-side endpoint and a surviving-boundary endpoint lie at even
distance in the alternating pairing graph. -/
theorem MinimalAreaRelatorBoundarySeed.exists_even_stemToBoundaryPath_of_edgeClass_eq
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
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)))
    (hne : v ≠ x)
    (hv : seed.balloonStemOccurrencePairing.partner v = none)
    (hx : seed.boundaryCancellationPairing.partner x = none) :
    ∃ path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x,
      path.IsPath ∧ Even path.length := by
  obtain ⟨path, hpath⟩ := seed.exists_simplePairingPath_of_edgeClass_eq v x hclass
  exact ⟨path, hpath,
    pairingWalk_length_even_of_leftRightUnpaired_endpoints
      seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing
      path hpath hne hv hx⟩

/-- The reverse endpoint order has the same even-distance property. -/
theorem MinimalAreaRelatorBoundarySeed.exists_even_boundaryToStemPath_of_edgeClass_eq
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
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)))
    (hne : v ≠ x)
    (hv : seed.boundaryCancellationPairing.partner v = none)
    (hx : seed.balloonStemOccurrencePairing.partner x = none) :
    ∃ path : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).Walk v x,
      path.IsPath ∧ Even path.length := by
  obtain ⟨path, hpath⟩ := seed.exists_simplePairingPath_of_edgeClass_eq v x hclass
  exact ⟨path, hpath,
    pairingWalk_length_even_of_rightLeftUnpaired_endpoints
      seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing
      path hpath hne hv hx⟩

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

private theorem MinimalAreaRelatorBoundarySeed.relatorSegment_slice
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length) :
    let balloons := seed.boundary.reducedBalloons
    let b := balloons.get i
    ((seed.boundary.reducedLiteralBoundary.drop
      ((((balloons.take i.val).map fun x => x.label.rawWord).flatten.length) +
        b.label.conjugator.toWord.length)).take b.label.relator.toWord.length) =
      b.label.relator.toWord := by
  dsimp
  let balloons := seed.boundary.reducedBalloons
  let b := balloons.get i
  let preWord := ((balloons.take i.val).map fun x => x.label.rawWord).flatten
  let suffix := ((balloons.drop (i.val + 1)).map fun x => x.label.rawWord).flatten
  let stem := b.label.conjugator.toWord
  let relator := b.label.relator.toWord
  have hsplit := reducedBalloonWords_flatten_split_at balloons i
  have hsplit' : seed.boundary.reducedLiteralBoundary =
      preWord ++ b.label.rawWord ++ suffix := by
    simpa [RelatorFactorBoundarySeed.reducedLiteralBoundary, balloons,
      preWord, suffix, b, List.append_assoc] using hsplit
  have hrawBalloon :
      b.label.rawWord = stem ++ relator ++ FreeGroup.invRev stem := by
    simp [RelatorConjugateWitness.rawWord, FreeGroup.toWord_inv, stem, relator]
  have hraw : seed.boundary.reducedLiteralBoundary =
      (preWord ++ stem) ++ relator ++ (FreeGroup.invRev stem ++ suffix) := by
    rw [hrawBalloon] at hsplit'
    simpa [List.append_assoc] using hsplit'
  have hleftLength :
      (preWord ++ stem).length = preWord.length + stem.length := List.length_append
  have hdropInner :
      (preWord ++ stem ++ relator).drop (preWord ++ stem).length = relator := by
    rw [List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  have hdrop :
      ((preWord ++ stem ++ relator) ++ (FreeGroup.invRev stem ++ suffix)).drop
          (preWord ++ stem).length = relator ++ (FreeGroup.invRev stem ++ suffix) := by
    rw [List.drop_append_of_le_length (by simp [List.length_append])]
    rw [hdropInner]
  have htake :
      (relator ++ (FreeGroup.invRev stem ++ suffix)).take relator.length = relator := by
    rw [List.take_append_of_le_length (Nat.le_refl _)]
    simp
  change ((seed.boundary.reducedLiteralBoundary.drop
      (preWord.length + stem.length)).take relator.length) = relator
  rw [hraw, ← hleftLength, hdrop, htake]

/-- If every letter on one relator side survives the global boundary
reduction, that full relator remains as a contiguous factor of the target
word and gives a valid cyclic Dehn redex. -/
theorem MinimalAreaRelatorBoundarySeed.cyclicRedex_of_relatorSides_survive
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length)
    (hsurvive : ∀ j : Fin
      ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length),
      (seed.relatorSideOccurrencePosition ⟨i, j⟩).val ∈
        seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst) :
    ∃ c, IsCyclicRedex P.relators w c := by
  let balloons := seed.boundary.reducedBalloons
  let b := balloons.get i
  let preWord := ((balloons.take i.val).map fun x => x.label.rawWord).flatten
  let stem := b.label.conjugator.toWord
  let relator := b.label.relator.toWord
  let start := preWord.length + stem.length
  have hposFormula (j : Fin relator.length) :
      (seed.relatorSideOccurrencePosition ⟨i, j⟩).val =
        preWord.length + stem.length + j.val := by
    change (((reducedBalloonOccurrencePathEmbedding balloons i).mapDart
      (b.relatorSideDart j)).1).val = _
    have h := reducedBalloonOccurrencePathEmbedding_position_formula
      balloons i (b.relatorSideDart j).1
    simpa [preWord, stem, b, balloons,
      ReducedRelatorBalloonData.relatorSideDart,
      ReducedRelatorBalloonData.relatorSideDart_index, Nat.add_assoc] using h
  have hsourceSurvives : ∀ k, k < relator.length →
      start + k ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst := by
    intro k hk
    let j : Fin relator.length := ⟨k, hk⟩
    have h := hsurvive j
    rw [hposFormula j] at h
    simpa [start, Nat.add_assoc] using h
  have hsegment :
      (seed.boundary.reducedLiteralBoundary.drop start).take relator.length = relator := by
    simpa [start, preWord, stem, relator, b, balloons] using
      seed.relatorSegment_slice i
  obtain ⟨pre, post, hword⟩ :=
    seed.reducedLollipopBoundaryTrace.contiguous_source_interval_of_survivors
      start relator.length hsourceSurvives
  have hword' : w.toWord = pre ++ relator ++ post := by
    simpa [hsegment] using hword
  have hrelatorNontrivial : b.label.relator ≠ 1 :=
    P.nontrivial b.label.relator b.label.relator_mem
  have hrelatorLength : 0 < relator.length := by
    by_contra hnot
    have hzero : relator.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hnil : relator = [] := List.length_eq_zero_iff.mp hzero
    have hone : b.label.relator = 1 := by
      apply FreeGroup.toWord_injective
      change relator = FreeGroup.toWord 1
      rw [hnil, FreeGroup.toWord_one]
    exact hrelatorNontrivial hone
  let redex : Redex α := ⟨pre, relator, post, b.label.relator, []⟩
  refine ⟨⟨w.toWord, [], redex⟩, ?_⟩
  refine ⟨by simp, ?_⟩
  change IsRedex P.relators (FreeGroup.mk w.toWord).toWord redex
  rw [FreeGroup.mk_toWord]
  refine ⟨?_, b.label.relator_mem, ?_, ?_⟩
  · exact hword'
  · simp [redex, relator]
  · simp [redex, relator]
    exact hrelatorLength

private theorem slice_after_prefix
    {α : Type*} (left stem relator right : List α) (offset len : Nat)
    (hbound : offset + len ≤ relator.length) :
    ((((left ++ stem) ++ relator) ++ right).drop
      ((left ++ stem).length + offset)).take len =
      (relator.drop offset).take len := by
  have hdropLeft :
      (left ++ (stem ++ (relator ++ right))).drop left.length =
        stem ++ (relator ++ right) := by
    rw [List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  have hdropStem :
      (stem ++ (relator ++ right)).drop stem.length = relator ++ right := by
    rw [List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  have hdrop :
      (left ++ (stem ++ (relator ++ right))).drop
          (left.length + (stem.length + offset)) = relator.drop offset ++ right := by
    calc
      _ = ((left ++ (stem ++ (relator ++ right))).drop left.length).drop
            (stem.length + offset) := by rw [← List.drop_drop]
      _ = (stem ++ (relator ++ right)).drop (stem.length + offset) := by
            rw [hdropLeft]
      _ = ((stem ++ (relator ++ right)).drop stem.length).drop offset := by
            rw [← List.drop_drop]
      _ = (relator ++ right).drop offset := by rw [hdropStem]
      _ = relator.drop offset ++ right :=
            List.drop_append_of_le_length (by omega)
  have hlen : len ≤ (relator.drop offset).length := by
    simp only [List.length_drop]
    omega
  have hdropTarget :
      (((left ++ stem) ++ relator) ++ right).drop
          ((left ++ stem).length + offset) = relator.drop offset ++ right := by
    simpa [List.append_assoc, List.length_append, Nat.add_assoc] using hdrop
  rw [hdropTarget, List.take_append_of_le_length hlen]

/-- A surviving relator-side arc longer than half its perimeter gives a
cyclic Dehn redex, even when the arc crosses the chosen cyclic start. -/
theorem MinimalAreaRelatorBoundarySeed.cyclicRedex_of_long_surviving_relator_arc
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length)
    (offset len : Nat)
    (hbound : offset + len ≤
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length)
    (hlong : 2 * len >
      (seed.boundary.reducedBalloons.get i).label.relator.toWord.length)
    (hsurvive : ∀ k (hk : k < len),
      (seed.relatorSideOccurrencePosition
        ⟨i, ⟨offset + k, by omega⟩⟩).val ∈
        seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst) :
    ∃ c, IsCyclicRedex P.relators w c := by
  let balloons := seed.boundary.reducedBalloons
  let b := balloons.get i
  let preWord := ((balloons.take i.val).map fun x => x.label.rawWord).flatten
  let suffix := ((balloons.drop (i.val + 1)).map fun x => x.label.rawWord).flatten
  let stem := b.label.conjugator.toWord
  let relator := b.label.relator.toWord
  let start := preWord.length + stem.length + offset
  have hboundLocal : offset + len ≤ relator.length := by
    simpa [relator, b, balloons] using hbound
  have hlongLocal : 2 * len > relator.length := by
    simpa [relator, b, balloons] using hlong
  have hposFormula (j : Fin relator.length) :
      (seed.relatorSideOccurrencePosition ⟨i, j⟩).val =
        preWord.length + stem.length + j.val := by
    change (((reducedBalloonOccurrencePathEmbedding balloons i).mapDart
      (b.relatorSideDart j)).1).val = _
    have h := reducedBalloonOccurrencePathEmbedding_position_formula
      balloons i (b.relatorSideDart j).1
    simpa [preWord, stem, b, balloons,
      ReducedRelatorBalloonData.relatorSideDart,
      ReducedRelatorBalloonData.relatorSideDart_index, Nat.add_assoc] using h
  have hsourceSurvives : ∀ k, k < len →
      start + k ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst := by
    intro k hk
    let j : Fin relator.length := ⟨offset + k, by omega⟩
    have h := hsurvive k hk
    rw [hposFormula j] at h
    simpa [start, Nat.add_assoc] using h
  have hsplit := reducedBalloonWords_flatten_split_at balloons i
  have hsplit' : seed.boundary.reducedLiteralBoundary =
      preWord ++ b.label.rawWord ++ suffix := by
    simpa [RelatorFactorBoundarySeed.reducedLiteralBoundary, balloons,
      preWord, suffix, b, List.append_assoc] using hsplit
  have hrawBalloon :
      b.label.rawWord = stem ++ relator ++ FreeGroup.invRev stem := by
    simp [RelatorConjugateWitness.rawWord, FreeGroup.toWord_inv, stem, relator]
  have hraw : seed.boundary.reducedLiteralBoundary =
      (preWord ++ stem) ++ relator ++ (FreeGroup.invRev stem ++ suffix) := by
    rw [hrawBalloon] at hsplit'
    simpa [List.append_assoc] using hsplit'
  let arc := (relator.drop offset).take len
  have hsegment :
      (seed.boundary.reducedLiteralBoundary.drop start).take len = arc := by
    have hslice := slice_after_prefix preWord stem relator
      (FreeGroup.invRev stem ++ suffix) offset len hboundLocal
    simpa [arc, start, hraw, List.length_append, Nat.add_assoc,
      List.append_assoc] using hslice
  obtain ⟨outPre, outPost, hword⟩ :=
    seed.reducedLollipopBoundaryTrace.contiguous_source_interval_of_survivors
      start len hsourceSurvives
  have hword' : w.toWord = outPre ++ arc ++ outPost := by
    simpa [hsegment] using hword
  let relatorPrefix := relator.take offset
  let relatorTail := relator.drop (offset + len)
  have hrelatorSplit : relator = relatorPrefix ++ (arc ++ relatorTail) := by
    calc
      relator = relator.take offset ++ relator.drop offset :=
        (List.take_append_drop offset relator).symm
      _ = relatorPrefix ++ (arc ++ relatorTail) := by
        dsimp [relatorPrefix, arc, relatorTail]
        rw [← List.take_append_drop len (relator.drop offset)]
        simp [List.drop_drop]
  have hrelatorSplit' :
      b.label.relator.toWord = relatorPrefix ++ (arc ++ relatorTail) := by
    simpa [relator, List.append_assoc] using hrelatorSplit
  obtain ⟨rotatedRelator, hrotatedMem, hrotatedWord⟩ :=
    P.rotateRelator b.label.relator_mem
      (pre := relatorPrefix) (suf := arc ++ relatorTail) hrelatorSplit'
  let short := relatorTail ++ relatorPrefix
  have hrotatedWord' : rotatedRelator.toWord = arc ++ short := by
    simpa [short, List.append_assoc] using hrotatedWord
  have hoffset : offset ≤ relator.length := by omega
  have hdropLengthNat : len ≤ relator.length - offset :=
    Nat.le_sub_of_add_le (by omega)
  have hdropLength : len ≤ (relator.drop offset).length := by
    simpa [List.length_drop, Nat.min_eq_right hoffset] using hdropLengthNat
  have hprefixLength : relatorPrefix.length = offset := by
    simp [relatorPrefix, List.length_take, Nat.min_eq_left hoffset]
  have harcLength : arc.length = len := by
    dsimp [arc]
    rw [List.length_take]
    exact Nat.min_eq_left hdropLength
  have hsplitLength :
      relator.length = relatorPrefix.length + arc.length + relatorTail.length := by
    rw [hrelatorSplit]
    simp [List.length_append, Nat.add_assoc]
  have hshortLength : short.length = relatorTail.length + offset := by
    simp [short, hprefixLength, List.length_append]
  have hrelatorLength : relator.length = arc.length + short.length := by
    rw [hsplitLength, hprefixLength, harcLength, hshortLength]
    omega
  have hlongRedex : arc.length > short.length := by
    rw [hrelatorLength, harcLength] at hlongLocal
    omega
  let redex : Redex α :=
    ⟨outPre, arc, outPost, rotatedRelator, short⟩
  refine ⟨⟨w.toWord, [], redex⟩, ?_⟩
  refine ⟨by simp, ?_⟩
  change IsRedex P.relators (FreeGroup.mk w.toWord).toWord redex
  rw [FreeGroup.mk_toWord]
  refine ⟨?_, hrotatedMem, ?_, ?_⟩
  · exact hword'
  · simpa [redex] using hrotatedWord'
  · simpa [redex] using hlongRedex

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

/-- Every occurrence in a zero-incidence component is paired by a boundary
cancellation. The only possible unpaired boundary occurrences are precisely
the surviving target-boundary letters, each of which contributes an
incidence. -/
theorem MinimalAreaRelatorBoundarySeed.boundaryCancellationPartner_of_zeroIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp) :
    ∃ j : Fin seed.boundary.reducedLiteralBoundary.length,
      j ∈ C.supp ∧ seed.boundaryCancellationPairing.partner i = some j := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  let v : C.supp := ⟨i, hi⟩
  let rightPairing := componentRightPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  have hright_ne : rightPairing.partner v ≠ none := by
    intro hnone
    have hglobalNone :=
      (componentRightPairing_partner_none_iff
        seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing C v).mp
        hnone
    have hsurvivor :=
      (IndexedBoundaryTrace.cancellationOccurrencePairing_unpaired_iff_survivor
        seed.reducedLollipopBoundaryTrace i).mp hglobalNone
    have hpositive : 0 < Nat.card
        ({side : seed.RelatorSideOccurrence //
            seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
         {i : Fin seed.boundary.reducedLiteralBoundary.length //
            i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
            i ∈ C.supp}) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr
        ⟨Sum.inr ⟨i, hsurvivor, hi⟩⟩
    omega
  cases hpartner : rightPairing.partner v with
  | none => exact False.elim (hright_ne hpartner)
  | some j =>
      have hglobal : seed.boundaryCancellationPairing.partner i = some j.1 :=
        (PartialOccurrencePairing.restrictedPartner_eq_some_iff
          seed.boundaryCancellationPairing C.supp v j).1 hpartner
      exact ⟨j.1, j.2, hglobal⟩

/-- Every occurrence in a zero-incidence component is also paired by its
balloon stem. An unmatched stem occurrence would be a relator-side incidence. -/
theorem MinimalAreaRelatorBoundarySeed.balloonStemPartner_of_zeroIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp) :
    ∃ j : Fin seed.boundary.reducedLiteralBoundary.length,
      j ∈ C.supp ∧ seed.balloonStemOccurrencePairing.partner i = some j := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  let v : C.supp := ⟨i, hi⟩
  let leftPairing := componentLeftPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  have hnoSide : ¬ ∃ side : seed.RelatorSideOccurrence,
      seed.relatorSideOccurrencePosition side = i := by
    intro hex
    obtain ⟨side, hposition⟩ := hex
    have hpositive : 0 < Nat.card
        ({side : seed.RelatorSideOccurrence //
            seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
         {i : Fin seed.boundary.reducedLiteralBoundary.length //
            i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
            i ∈ C.supp}) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr
        ⟨Sum.inl ⟨side, by rw [hposition]; exact hi⟩⟩
    omega
  have hleft_ne : leftPairing.partner v ≠ none := by
    intro hnone
    have hglobalNone :=
      (componentLeftPairing_partner_none_iff
        seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing C v).mp
        hnone
    obtain ⟨side, hposition⟩ :=
      seed.exists_relatorSide_of_unmatched_by_stem i hglobalNone
    exact hnoSide ⟨side, hposition⟩
  cases hpartner : leftPairing.partner v with
  | none => exact False.elim (hleft_ne hpartner)
  | some j =>
      have hglobal : seed.balloonStemOccurrencePairing.partner i = some j.1 :=
        (PartialOccurrencePairing.restrictedPartner_eq_some_iff
          seed.balloonStemOccurrencePairing C.supp v j).1 hpartner
      exact ⟨j.1, j.2, hglobal⟩

/-- In a zero-incidence component, each selected cancellation edge is backed
by a source cancellation pair, hence by a contiguous null subword of the
literal relator-factor boundary. -/
theorem MinimalAreaRelatorBoundarySeed.zeroIncidence_cancellation_has_null_interior
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp) :
    ∃ (j : Fin seed.boundary.reducedLiteralBoundary.length)
      (p : Nat × Nat) (pre inner post : Word α) (a : Letter α),
      j ∈ C.supp ∧
      seed.boundaryCancellationPairing.partner i = some j ∧
      p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs ∧
      (p = (i.val, j.val) ∨ p = (j.val, i.val)) ∧
      seed.boundary.reducedLiteralBoundary =
        pre ++ [a] ++ inner ++ [inverseLetter a] ++ post ∧
      p = (pre.length, pre.length + inner.length + 1) ∧
      FreeGroup.mk inner = 1 := by
  obtain ⟨j, hj, hpartner⟩ :=
    seed.boundaryCancellationPartner_of_zeroIncidence C hzero i hi
  obtain ⟨p, hp, hends⟩ :=
    seed.reducedLollipopBoundaryTrace.cancellationOccurrencePairing_source_pair
      i j hpartner
  have hp' : p ∈ seed.boundary.reducedLiteralBoundaryShape.cancellationPairs := by
    simpa [MinimalAreaRelatorBoundarySeed.reducedLollipopBoundaryTrace,
      FreeReductionShape.toIndexedBoundaryTrace] using hp
  obtain ⟨pre, inner, post, a, hword, hposition, hnull⟩ :=
    seed.cancellationPair_has_null_interior p hp'
  refine ⟨j, p, pre, inner, post, a, hj, hpartner, hp', ?_, hword,
    hposition, hnull⟩
  rcases hends with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩
  · exact Or.inl (Prod.ext hfirst hsecond)
  · exact Or.inr (Prod.ext hsecond hfirst)

/-- A stem-paired pair of boundary positions cuts out a nontrivial interval
in the complete literal boundary, including when its balloon follows a
nonempty prefix of earlier relators. -/
theorem MinimalAreaRelatorBoundarySeed.balloonStemPartner_has_nontrivial_interval
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i j : Fin seed.boundary.reducedLiteralBoundary.length)
    (hpartner : seed.balloonStemOccurrencePairing.partner i = some j) :
    ∃ (pre inner post : Word α) (a : Letter α),
      seed.boundary.reducedLiteralBoundary =
        pre ++ [a] ++ inner ++ [inverseLetter a] ++ post ∧
      ((i.val, j.val) = (pre.length, pre.length + inner.length + 1) ∨
        (j.val, i.val) = (pre.length, pre.length + inner.length + 1)) ∧
      FreeGroup.mk inner ≠ 1 := by
  have hrel := (seed.balloonStemOccurrencePairing_spec i j).1 hpartner
  rcases hrel with ⟨q, hq, hqorientation⟩
  rcases List.mem_map.mp hq with ⟨pair, hpair, hqeq⟩
  obtain ⟨pre, inner, post, a, hword, hpositions, hnontrivial⟩ :=
    reducedBalloonStemPair_interval_nontrivial
      seed.boundary.reducedBalloons pair hpair
  have hqfirst : pair.first.1 = q.1 := congrArg Prod.fst hqeq
  have hqsecond : pair.second.1 = q.2 := congrArg Prod.snd hqeq
  have hpairToQ :
      (pair.first.1.val, pair.second.1.val) = (q.1.val, q.2.val) :=
    Prod.ext (congrArg Fin.val hqfirst) (congrArg Fin.val hqsecond)
  rcases hqorientation with hleft | hright
  · have hqToIJ : (q.1.val, q.2.val) = (i.val, j.val) :=
      Prod.ext (congrArg Fin.val hleft.1) (congrArg Fin.val hleft.2)
    refine ⟨pre, inner, post, a, hword, Or.inl ?_, hnontrivial⟩
    exact (hpairToQ.trans hqToIJ).symm.trans hpositions
  · have hqToJI : (q.1.val, q.2.val) = (j.val, i.val) :=
      Prod.ext (congrArg Fin.val hright.1) (congrArg Fin.val hright.2)
    refine ⟨pre, inner, post, a, hword, Or.inr ?_, hnontrivial⟩
    exact (hpairToQ.trans hqToJI).symm.trans hpositions

/-- A zero-incidence component cannot use the same edge for a balloon stem
fold and a free-cancellation fold: the first encloses a nontrivial relator
interval, whereas the cancellation tree requires its interior to be null. -/
theorem MinimalAreaRelatorBoundarySeed.zeroIncidence_stem_and_cancellation_partners_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i j : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp)
    (hstem : seed.balloonStemOccurrencePairing.partner i = some j)
    (hcancel : seed.boundaryCancellationPairing.partner i = some j) : False := by
  obtain ⟨preS, innerS, postS, aS, hwordS, hendsS, hnontrivialS⟩ :=
    seed.balloonStemPartner_has_nontrivial_interval i j hstem
  obtain ⟨jC, p, preC, innerC, postC, aC, hjC, hpartnerC, hp, hendsC,
      hwordC, hpositionsC, hnullC⟩ :=
    seed.zeroIncidence_cancellation_has_null_interior C hzero i hi
  have hjEq : jC = j := Option.some.inj (hpartnerC.symm.trans hcancel)
  subst jC
  have hcancelLt : p.1 < p.2 := by
    rw [hpositionsC]
    omega
  have hstemLt : preS.length < preS.length + innerS.length + 1 := by
    omega
  have hpStem : p = (preS.length, preS.length + innerS.length + 1) := by
    rcases hendsS with hstemIJ | hstemJI
    · rcases hendsC with hcancelIJ | hcancelJI
      · exact hcancelIJ.trans hstemIJ
      · have hstemFirst := congrArg Prod.fst hstemIJ
        have hstemSecond := congrArg Prod.snd hstemIJ
        have hcancelFirst := congrArg Prod.fst hcancelJI
        have hcancelSecond := congrArg Prod.snd hcancelJI
        omega
    · rcases hendsC with hcancelIJ | hcancelJI
      · have hstemFirst := congrArg Prod.fst hstemJI
        have hstemSecond := congrArg Prod.snd hstemJI
        have hcancelFirst := congrArg Prod.fst hcancelIJ
        have hcancelSecond := congrArg Prod.snd hcancelIJ
        omega
      · exact hcancelJI.trans hstemJI
  exact seed.boundary.reducedLiteralBoundaryShape
    |>.cancellationPair_false_of_nontrivial_interval p hp
      ⟨preS, innerS, postS, aS, hwordS, hpStem, hnontrivialS⟩

/-- The distinct stem and cancellation partners force every zero-incidence
component to contain at least three boundary occurrences. -/
theorem MinimalAreaRelatorBoundarySeed.zeroIncidence_component_card_ge_three
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp) : 3 ≤ C.supp.ncard := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  obtain ⟨jS, hjS, hstem⟩ :=
    seed.balloonStemPartner_of_zeroIncidence C hzero i hi
  obtain ⟨jC, hjC, hcancel⟩ :=
    seed.boundaryCancellationPartner_of_zeroIncidence C hzero i hi
  have hiNeStem : i ≠ jS := by
    intro heq
    subst jS
    exact seed.balloonStemOccurrencePairing.partner_ne hstem
  have hiNeCancel : i ≠ jC := by
    intro heq
    subst jC
    exact seed.boundaryCancellationPairing.partner_ne hcancel
  have hjNe : jS ≠ jC := by
    intro heq
    subst jC
    exact seed.zeroIncidence_stem_and_cancellation_partners_ne
      C hzero i jS hi hstem hcancel
  let vertices : List C.supp := [⟨i, hi⟩, ⟨jS, hjS⟩, ⟨jC, hjC⟩]
  have hnodup : vertices.Nodup := by
    simp [vertices, hiNeStem, hiNeCancel, hjNe]
  have hcard := hnodup.length_le_card
  simpa [vertices] using hcard

/-- In fact the zero-incidence component cannot be a triangle: its two edge
families are matchings, so a closed alternating component has at least four
vertices. -/
theorem MinimalAreaRelatorBoundarySeed.zeroIncidence_component_card_ge_four
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp) : 4 ≤ C.supp.ncard := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  obtain ⟨jS, hjS, hstem⟩ :=
    seed.balloonStemPartner_of_zeroIncidence C hzero i hi
  obtain ⟨jC, hjC, hcancel⟩ :=
    seed.boundaryCancellationPartner_of_zeroIncidence C hzero i hi
  have hiNeStem : i ≠ jS := by
    intro heq
    subst jS
    exact seed.balloonStemOccurrencePairing.partner_ne hstem
  have hiNeCancel : i ≠ jC := by
    intro heq
    subst jC
    exact seed.boundaryCancellationPairing.partner_ne hcancel
  have hjNe : jS ≠ jC := by
    intro heq
    subst jC
    exact seed.zeroIncidence_stem_and_cancellation_partners_ne
      C hzero i jS hi hstem hcancel
  have hcard3 := seed.zeroIncidence_component_card_ge_three C hzero i hi
  by_contra hnotFour
  have hcardEq : C.supp.ncard = 3 := by omega
  have hsupport : ∀ x, x ∈ C.supp → x = i ∨ x = jS ∨ x = jC := by
    intro x hx
    by_contra hnot
    have hxi : x ≠ i := by
      intro heq
      exact hnot (Or.inl heq)
    have hxjS : x ≠ jS := by
      intro heq
      exact hnot (Or.inr (Or.inl heq))
    have hxjC : x ≠ jC := by
      intro heq
      exact hnot (Or.inr (Or.inr heq))
    let v₁ : C.supp := ⟨i, hi⟩
    let v₂ : C.supp := ⟨jS, hjS⟩
    let v₃ : C.supp := ⟨jC, hjC⟩
    let v₄ : C.supp := ⟨x, hx⟩
    have hv₄₁ : v₄ ≠ v₁ := by
      intro heq
      exact hxi (congrArg Subtype.val heq)
    have hv₄₂ : v₄ ≠ v₂ := by
      intro heq
      exact hxjS (congrArg Subtype.val heq)
    have hv₄₃ : v₄ ≠ v₃ := by
      intro heq
      exact hxjC (congrArg Subtype.val heq)
    have hv₁₂ : v₁ ≠ v₂ := by
      intro heq
      exact hiNeStem (congrArg Subtype.val heq)
    have hv₁₃ : v₁ ≠ v₃ := by
      intro heq
      exact hiNeCancel (congrArg Subtype.val heq)
    have hv₁₄ : v₁ ≠ v₄ := Ne.symm hv₄₁
    have hv₂₃ : v₂ ≠ v₃ := by
      intro heq
      exact hjNe (congrArg Subtype.val heq)
    have hv₂₄ : v₂ ≠ v₄ := Ne.symm hv₄₂
    have hv₃₄ : v₃ ≠ v₄ := Ne.symm hv₄₃
    let vertices : List C.supp := [v₁, v₂, v₃, v₄]
    have hnodup : vertices.Nodup := by
      simp [vertices, v₁, v₂, v₃, v₄, hv₁₂, hv₁₃, hv₁₄,
        hv₂₃, hv₂₄, hv₃₄]
    have hcardFour : 4 ≤ C.supp.ncard := by
      have hcard := hnodup.length_le_card
      simpa [vertices, v₁, v₂, v₃, v₄] using hcard
    omega
  obtain ⟨kC, hkC, hcancelS⟩ :=
    seed.boundaryCancellationPartner_of_zeroIncidence C hzero jS hjS
  have hstemBack : seed.balloonStemOccurrencePairing.partner jS = some i :=
    seed.balloonStemOccurrencePairing.partner_symm hstem
  have hiNeKC : i ≠ kC := by
    intro heq
    subst kC
    exact seed.zeroIncidence_stem_and_cancellation_partners_ne
      C hzero jS i hjS hstemBack hcancelS
  have hjSNeKC : kC ≠ jS := by
    intro heq
    subst kC
    exact seed.boundaryCancellationPairing.partner_ne hcancelS
  have hkCeq : kC = jC := by
    rcases hsupport kC hkC with h | h | h
    · exact False.elim (hiNeKC h.symm)
    · exact False.elim (hjSNeKC h)
    · exact h
  subst kC
  have hcancelBack : seed.boundaryCancellationPairing.partner jC = some jS :=
    seed.boundaryCancellationPairing.partner_symm hcancelS
  obtain ⟨kS, hkS, hstemC⟩ :=
    seed.balloonStemPartner_of_zeroIncidence C hzero jC hjC
  have hjSNeKS : kS ≠ jS := by
    intro heq
    subst kS
    exact seed.zeroIncidence_stem_and_cancellation_partners_ne
      C hzero jC jS hjC hstemC hcancelBack
  have hjCNeKS : kS ≠ jC := by
    intro heq
    subst kS
    exact seed.balloonStemOccurrencePairing.partner_ne hstemC
  have hkSeq : kS = i := by
    rcases hsupport kS hkS with h | h | h
    · exact h
    · exact False.elim (hjSNeKS h)
    · exact False.elim (hjCNeKS h)
  have hstemAround : seed.balloonStemOccurrencePairing.partner jC = some i := by
    rw [hkSeq] at hstemC
    exact hstemC
  have hstemBackAround := seed.balloonStemOccurrencePairing.partner_symm hstemAround
  have hpartners : some jS = some jC := hstem.symm.trans hstemBackAround
  exact hjNe (Option.some.inj hpartners)

/-- A zero-incidence component is a genuine alternating cycle: at each of
its occurrences both pairings are defined, and their partners are distinct.
This records the exact cycle structure needed by the remaining interval
argument. -/
theorem MinimalAreaRelatorBoundarySeed.zeroIncidence_component_isCycles
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0) :
    (twoPairingGraph
      (componentLeftPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C)
      (componentRightPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C)).IsCycles := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  letI : DecidableEq C.supp := Classical.decEq _
  let left := componentLeftPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  let right := componentRightPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  apply twoPairingGraph_isCycles_of_complete_distinct left right
  · intro v
    obtain ⟨j, hj, hpartner⟩ :=
      seed.balloonStemPartner_of_zeroIncidence C hzero v.1 v.2
    have hlocal : left.partner v = some ⟨j, hj⟩ := by
      exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
        seed.balloonStemOccurrencePairing C.supp v ⟨j, hj⟩).2 hpartner
    intro hnone
    rw [hnone] at hlocal
    cases hlocal
  · intro v
    obtain ⟨j, hj, hpartner⟩ :=
      seed.boundaryCancellationPartner_of_zeroIncidence C hzero v.1 v.2
    have hlocal : right.partner v = some ⟨j, hj⟩ := by
      exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
        seed.boundaryCancellationPairing C.supp v ⟨j, hj⟩).2 hpartner
    intro hnone
    rw [hnone] at hlocal
    cases hlocal
  · intro v heq
    obtain ⟨jS, hjS, hstem⟩ :=
      seed.balloonStemPartner_of_zeroIncidence C hzero v.1 v.2
    obtain ⟨jC, hjC, hcancel⟩ :=
      seed.boundaryCancellationPartner_of_zeroIncidence C hzero v.1 v.2
    have hstemLocal : left.partner v = some ⟨jS, hjS⟩ := by
      exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
        seed.balloonStemOccurrencePairing C.supp v ⟨jS, hjS⟩).2 hstem
    have hcancelLocal : right.partner v = some ⟨jC, hjC⟩ := by
      exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
        seed.boundaryCancellationPairing C.supp v ⟨jC, hjC⟩).2 hcancel
    have htargets : (⟨jS, hjS⟩ : C.supp) = ⟨jC, hjC⟩ :=
      Option.some.inj (hstemLocal.symm.trans (heq.trans hcancelLocal))
    have hvalues : jS = jC := congrArg Subtype.val htargets
    have hglobal :
        seed.balloonStemOccurrencePairing.partner v.1 =
          seed.boundaryCancellationPairing.partner v.1 := by
      rw [hstem, hcancel, hvalues]
    have hcancelSame :
        seed.boundaryCancellationPairing.partner v.1 = some jS :=
      hglobal.symm.trans hstem
    exact seed.zeroIncidence_stem_and_cancellation_partners_ne
      C hzero v.1 jS v.2 hstem hcancelSame

/-- Every occurrence in a zero-incidence component lies on a simple cycle of
the component graph. -/
theorem MinimalAreaRelatorBoundarySeed.zeroIncidence_component_cycle_through
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (C : (twoPairingGraph seed.balloonStemOccurrencePairing
      seed.boundaryCancellationPairing).ConnectedComponent)
    (hzero : Nat.card
      ({side : seed.RelatorSideOccurrence //
          seed.relatorSideOccurrencePosition side ∈ C.supp} ⊕
       {i : Fin seed.boundary.reducedLiteralBoundary.length //
          i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          i ∈ C.supp}) = 0)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i ∈ C.supp) :
    ∃ cycle : (twoPairingGraph
      (componentLeftPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C)
      (componentRightPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C)).Walk ⟨i, hi⟩ ⟨i, hi⟩,
      cycle.IsCycle ∧ cycle.toSubgraph.verts = Set.univ ∧
        PairingColorsAlternate (pairingWalkColors
          (componentLeftPairing seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C)
          (componentRightPairing seed.balloonStemOccurrencePairing
            seed.boundaryCancellationPairing C) cycle) := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite _
  let left := componentLeftPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  let right := componentRightPairing seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing C
  let graph := twoPairingGraph left right
  have hcycles : graph.IsCycles := by
    simpa [graph, left, right] using
      seed.zeroIncidence_component_isCycles C hzero
  have hdistinct : ∀ x : C.supp, left.partner x ≠ right.partner x := by
    intro x heq
    obtain ⟨jS, hjS, hstem⟩ :=
      seed.balloonStemPartner_of_zeroIncidence C hzero x.1 x.2
    obtain ⟨jC, hjC, hcancel⟩ :=
      seed.boundaryCancellationPartner_of_zeroIncidence C hzero x.1 x.2
    have hstemLocal : left.partner x = some ⟨jS, hjS⟩ := by
      exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
        seed.balloonStemOccurrencePairing C.supp x ⟨jS, hjS⟩).2 hstem
    have hcancelLocal : right.partner x = some ⟨jC, hjC⟩ := by
      exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
        seed.boundaryCancellationPairing C.supp x ⟨jC, hjC⟩).2 hcancel
    have htargets : (⟨jS, hjS⟩ : C.supp) = ⟨jC, hjC⟩ :=
      Option.some.inj (hstemLocal.symm.trans (heq.trans hcancelLocal))
    have hvalues : jS = jC := congrArg Subtype.val htargets
    have hglobal :
        seed.balloonStemOccurrencePairing.partner x.1 =
          seed.boundaryCancellationPairing.partner x.1 := by
      rw [hstem, hcancel, hvalues]
    have hcancelSame :
        seed.boundaryCancellationPairing.partner x.1 = some jS :=
      hglobal.symm.trans hstem
    exact seed.zeroIncidence_stem_and_cancellation_partners_ne
      C hzero x.1 jS x.2 hstem hcancelSame
  let v : C.supp := ⟨i, hi⟩
  obtain ⟨j, hj, hpartner⟩ :=
    seed.balloonStemPartner_of_zeroIncidence C hzero i hi
  let u : C.supp := ⟨j, hj⟩
  have hlocal : left.partner v = some u := by
    exact (PartialOccurrencePairing.restrictedPartner_eq_some_iff
      seed.balloonStemOccurrencePairing C.supp v u).2 hpartner
  have hadj : graph.Adj v u := Or.inl hlocal
  have hneighbors : (graph.neighborSet v).Nonempty :=
    ⟨u, by simpa only [SimpleGraph.mem_neighborSet] using hadj⟩
  have hconn : graph.Connected := by
    change (twoPairingGraph
      (componentLeftPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C)
      (componentRightPairing seed.balloonStemOccurrencePairing
        seed.boundaryCancellationPairing C)).Connected
    rw [twoPairingGraph_component_eq_induce
      seed.balloonStemOccurrencePairing seed.boundaryCancellationPairing C]
    exact C.connected_toSimpleGraph
  let component := graph.connectedComponentMk v
  have hv : v ∈ component.supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff component v).mpr rfl
  obtain ⟨cycle, hcycle, hverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hneighbors
  have hcomponent : component.supp = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff component x).mpr
      (SimpleGraph.ConnectedComponent.eq.mpr (hconn x v))
  have hcolors := pairingWalkColors_alternate_of_isCycle left right cycle hcycle
  exact ⟨cycle, hcycle, hverts.trans hcomponent, hcolors⟩

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

/-- A folded edge class represented by a surviving target-boundary occurrence
also has exactly two incidences when relator sides and surviving boundary
occurrences are counted separately. In particular this covers stem edges
that have no relator side. -/
theorem MinimalAreaRelatorBoundarySeed.card_boundaryIncidences_in_edgeClass_eq_two_of_survivor
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst) :
    Nat.card
      ({side : seed.RelatorSideOccurrence //
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart
              (seed.relatorSideOccurrencePosition side, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)} ⊕
       {j : Fin seed.boundary.reducedLiteralBoundary.length //
          j.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (j, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph) =
          (Quotient.mk
            (UnorientedDartSetoid
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
            (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false)) :
            UnorientedDartClass
              seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)}) = 2 := by
  classical
  let graph := twoPairingGraph seed.balloonStemOccurrencePairing
    seed.boundaryCancellationPairing
  let C := graph.connectedComponentMk i
  let edgeClass := fun p : Fin seed.boundary.reducedLiteralBoundary.length =>
    (Quotient.mk
      (UnorientedDartSetoid
        seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
      (seed.boundaryOccurrenceDartPairFold.hom.mapDart (p, false)) :
      UnorientedDartClass seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
  let sourceSides := {side : seed.RelatorSideOccurrence //
    edgeClass (seed.relatorSideOccurrencePosition side) = edgeClass i}
  let sourceBoundary := {j : Fin seed.boundary.reducedLiteralBoundary.length //
    j.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
      edgeClass j = edgeClass i}
  let targetSides := {side : seed.RelatorSideOccurrence //
    seed.relatorSideOccurrencePosition side ∈ C.supp}
  let targetBoundary := {j : Fin seed.boundary.reducedLiteralBoundary.length //
    j.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
      j ∈ C.supp}
  have hproperty (p : Fin seed.boundary.reducedLiteralBoundary.length) :
      edgeClass p = edgeClass i ↔ p ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    change edgeClass p = edgeClass i ↔
      graph.connectedComponentMk p = graph.connectedComponentMk i
    exact seed.unorientedEdgeClass_eq_iff_componentEq p i
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
    exact Fintype.card_pos_iff.mpr
      ⟨Sum.inr ⟨i, hi, rfl⟩⟩
  calc
    Nat.card (sourceSides ⊕ sourceBoundary) =
        Nat.card (targetSides ⊕ targetBoundary) := hcard
    _ = 2 := by
      rcases hcomponent' with hzero | htwo
      · rw [hcard, hzero] at hpositive
        omega
      · exact htwo

/-- An unoriented edge class in the quotient generated by the stem and
boundary-cancellation pairings. -/
abbrev MinimalAreaRelatorBoundarySeed.PairFoldEdgeClass
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  UnorientedDartClass seed.boundaryOccurrenceDartPairFold.graph.toDartGraph

/-- The folded unoriented edge containing a literal boundary occurrence. -/
noncomputable def MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedLiteralBoundary.length) :
    seed.PairFoldEdgeClass :=
  Quotient.mk (UnorientedDartSetoid
    seed.boundaryOccurrenceDartPairFold.graph.toDartGraph)
    (seed.boundaryOccurrenceDartPairFold.hom.mapDart (i, false))

/-- Equal edge classes with two distinct stem-unpaired positions have
opposite mapped orientations. -/
theorem MinimalAreaRelatorBoundarySeed.mapDart_reverse_of_edgeClass_eq_stemUnpaired
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hclass : seed.pairFoldEdgeClassAt v = seed.pairFoldEdgeClassAt x)
    (hne : v ≠ x)
    (hv : seed.balloonStemOccurrencePairing.partner v = none)
    (hx : seed.balloonStemOccurrencePairing.partner x = none) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) := by
  have hclass' :
      let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
      (Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
        UnorientedDartClass G) =
      Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
    simpa [MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt] using hclass
  obtain ⟨path, _hpath, hodd⟩ :=
    seed.exists_odd_stemEndpointPath_of_edgeClass_eq v x hclass' hne hv hx
  exact seed.mapDart_reverse_of_odd_pairingWalk path hodd

/-- Equal edge classes with two distinct cancellation-unpaired positions
have opposite mapped orientations. -/
theorem MinimalAreaRelatorBoundarySeed.mapDart_reverse_of_edgeClass_eq_boundaryUnpaired
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hclass : seed.pairFoldEdgeClassAt v = seed.pairFoldEdgeClassAt x)
    (hne : v ≠ x)
    (hv : seed.boundaryCancellationPairing.partner v = none)
    (hx : seed.boundaryCancellationPairing.partner x = none) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      seed.boundaryOccurrenceDartPairFold.graph.toDartGraph.reverse
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) := by
  have hclass' :
      let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
      (Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
        UnorientedDartClass G) =
      Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
    simpa [MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt] using hclass
  obtain ⟨path, _hpath, hodd⟩ :=
    seed.exists_odd_boundaryEndpointPath_of_edgeClass_eq v x hclass' hne hv hx
  exact seed.mapDart_reverse_of_odd_pairingWalk path hodd

/-- A stem-unpaired position and a cancellation-unpaired position in one
edge class have equal mapped orientations. -/
theorem MinimalAreaRelatorBoundarySeed.mapDart_eq_of_edgeClass_eq_stemToBoundary
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hclass : seed.pairFoldEdgeClassAt v = seed.pairFoldEdgeClassAt x)
    (hne : v ≠ x)
    (hv : seed.balloonStemOccurrencePairing.partner v = none)
    (hx : seed.boundaryCancellationPairing.partner x = none) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false) := by
  have hclass' :
      let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
      (Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
        UnorientedDartClass G) =
      Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
    simpa [MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt] using hclass
  obtain ⟨path, _hpath, heven⟩ :=
    seed.exists_even_stemToBoundaryPath_of_edgeClass_eq v x hclass' hne hv hx
  exact seed.mapDart_eq_of_even_pairingWalk path heven

/-- The reverse endpoint order also has equal mapped orientations. -/
theorem MinimalAreaRelatorBoundarySeed.mapDart_eq_of_edgeClass_eq_boundaryToStem
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (v x : Fin seed.boundary.reducedLiteralBoundary.length)
    (hclass : seed.pairFoldEdgeClassAt v = seed.pairFoldEdgeClassAt x)
    (hne : v ≠ x)
    (hv : seed.boundaryCancellationPairing.partner v = none)
    (hx : seed.balloonStemOccurrencePairing.partner x = none) :
    seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false) =
      seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false) := by
  have hclass' :
      let G := seed.boundaryOccurrenceDartPairFold.graph.toDartGraph
      (Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (v, false)) :
        UnorientedDartClass G) =
      Quotient.mk (UnorientedDartSetoid G)
        (seed.boundaryOccurrenceDartPairFold.hom.mapDart (x, false)) := by
    simpa [MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt] using hclass
  obtain ⟨path, _hpath, heven⟩ :=
    seed.exists_even_boundaryToStemPath_of_edgeClass_eq v x hclass' hne hv hx
  exact seed.mapDart_eq_of_even_pairingWalk path heven

/-- Relator-side occurrences represented by one folded unoriented edge. -/
def MinimalAreaRelatorBoundarySeed.pairFoldRelatorSideFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) : Type :=
  {side : seed.RelatorSideOccurrence //
    seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side) = e}

/-- Surviving reduced-boundary occurrences represented by one folded
unoriented edge. -/
def MinimalAreaRelatorBoundarySeed.pairFoldBoundaryFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) : Type :=
  {i : Fin seed.boundary.reducedLiteralBoundary.length //
    i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst ∧
      seed.pairFoldEdgeClassAt i = e}

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldRelatorSideFiberFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) :
    Fintype (seed.pairFoldRelatorSideFiber e) := by
  classical
  letI : Fintype seed.RelatorSideOccurrence := by
    change Fintype (Σ i : Fin seed.boundary.reducedBalloons.length,
      Fin ((seed.boundary.reducedBalloons.get i).label.relator.toWord.length))
    infer_instance
  letI : Finite (seed.pairFoldRelatorSideFiber e) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance MinimalAreaRelatorBoundarySeed.pairFoldBoundaryFiberFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (e : seed.PairFoldEdgeClass) :
    Fintype (seed.pairFoldBoundaryFiber e) := by
  classical
  letI : Finite (seed.pairFoldBoundaryFiber e) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Every edge class represented by a relator side has exactly two incidences
among relator-side and surviving-boundary occurrences. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceCount_eq_two_of_relatorSide
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    Nat.card (seed.pairFoldRelatorSideFiber
        (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) +
      Nat.card (seed.pairFoldBoundaryFiber
        (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) = 2 := by
  classical
  let e := seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side)
  have h := seed.card_boundaryIncidences_in_edgeClass_eq_two side
  have h' : Nat.card
      (seed.pairFoldRelatorSideFiber e ⊕ seed.pairFoldBoundaryFiber e) = 2 := by
    simpa [e, MinimalAreaRelatorBoundarySeed.pairFoldRelatorSideFiber,
      MinimalAreaRelatorBoundarySeed.pairFoldBoundaryFiber,
      MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt] using h
  simpa [Nat.card_sum] using h'

/-- The two incidences on an edge represented by a face side are either two
relator sides (an interior edge) or one relator side and one boundary
occurrence (a boundary edge). -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceShape_of_relatorSide
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (side : seed.RelatorSideOccurrence) :
    (Nat.card (seed.pairFoldRelatorSideFiber
        (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) = 2 ∧
      Nat.card (seed.pairFoldBoundaryFiber
        (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) = 0) ∨
    (Nat.card (seed.pairFoldRelatorSideFiber
        (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) = 1 ∧
      Nat.card (seed.pairFoldBoundaryFiber
        (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) = 1) := by
  have hsum := seed.pairFoldIncidenceCount_eq_two_of_relatorSide side
  letI : Fintype (seed.pairFoldRelatorSideFiber
      (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) :=
    Fintype.ofFinite _
  have hpos : 0 < Nat.card (seed.pairFoldRelatorSideFiber
      (seed.pairFoldEdgeClassAt (seed.relatorSideOccurrencePosition side))) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨side, rfl⟩
  omega

/-- Every edge class represented by a surviving target-boundary occurrence
has exactly two incidences among relator-side and surviving-boundary
occurrences. This also covers a stem edge with no incident relator side. -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceCount_eq_two_of_boundary
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst) :
    Nat.card (seed.pairFoldRelatorSideFiber (seed.pairFoldEdgeClassAt i)) +
      Nat.card (seed.pairFoldBoundaryFiber (seed.pairFoldEdgeClassAt i)) = 2 := by
  classical
  let e := seed.pairFoldEdgeClassAt i
  have h := seed.card_boundaryIncidences_in_edgeClass_eq_two_of_survivor i hi
  have h' : Nat.card
      (seed.pairFoldRelatorSideFiber e ⊕ seed.pairFoldBoundaryFiber e) = 2 := by
    simpa [e, MinimalAreaRelatorBoundarySeed.pairFoldRelatorSideFiber,
      MinimalAreaRelatorBoundarySeed.pairFoldBoundaryFiber,
      MinimalAreaRelatorBoundarySeed.pairFoldEdgeClassAt] using h
  simpa [Nat.card_sum] using h'

/-- On an edge represented by a surviving boundary occurrence, the two
incidences are either two boundary occurrences (a stem-only edge), or one of
each kind (a boundary edge incident to a relator face). -/
theorem MinimalAreaRelatorBoundarySeed.pairFoldIncidenceShape_of_boundary
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedLiteralBoundary.length)
    (hi : i.val ∈ seed.reducedLollipopBoundaryTrace.survivorOccurrences.map Prod.fst) :
    (Nat.card (seed.pairFoldRelatorSideFiber (seed.pairFoldEdgeClassAt i)) = 0 ∧
      Nat.card (seed.pairFoldBoundaryFiber (seed.pairFoldEdgeClassAt i)) = 2) ∨
    (Nat.card (seed.pairFoldRelatorSideFiber (seed.pairFoldEdgeClassAt i)) = 1 ∧
      Nat.card (seed.pairFoldBoundaryFiber (seed.pairFoldEdgeClassAt i)) = 1) := by
  have hsum := seed.pairFoldIncidenceCount_eq_two_of_boundary i hi
  letI : Fintype (seed.pairFoldBoundaryFiber (seed.pairFoldEdgeClassAt i)) :=
    Fintype.ofFinite _
  have hpos : 0 < Nat.card
      (seed.pairFoldBoundaryFiber (seed.pairFoldEdgeClassAt i)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨i, hi, rfl⟩
  omega

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
