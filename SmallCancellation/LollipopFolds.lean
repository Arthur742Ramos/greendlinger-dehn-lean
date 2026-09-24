import SmallCancellation.ReducedLollipop
import SmallCancellation.WordPath

namespace GreendlingerDehn

/-- The lollipop word is exactly the literal `g r g⁻¹` boundary stored in a
relator-conjugate witness. -/
theorem RelatorConjugateWitness.lollipopBoundary_eq_rawWord
    {α : Type*} [DecidableEq α] {R : List (FreeGroup α)}
    {factor : FreeGroup α} (d : RelatorConjugateWitness R factor) :
    lollipopBoundaryWord d.conjugator.toWord d.relator.toWord = d.rawWord := by
  simp [lollipopBoundaryWord, RelatorConjugateWitness.rawWord,
    FreeGroup.toWord_inv]

namespace LabelledDartPair

/-- Transport an occurrence pair along an equality of its underlying words. -/
def castWordPath {α : Type*} {u v : Word α} (h : u = v)
    (pair : LabelledDartPair (wordPathGraph u)) :
    LabelledDartPair (wordPathGraph v) where
  first := (Fin.cast (congrArg List.length h) pair.first.1, pair.first.2)
  second := (Fin.cast (congrArg List.length h) pair.second.1, pair.second.2)
  inverse_labels := by
    cases h
    exact pair.inverse_labels

end LabelledDartPair

/-- Transport a canonical occurrence walk along equality of its source word. -/
def castWordPathWalk {α : Type*} {u v : Word α} (h : u = v)
    {start finish : Nat} {word : Word α}
    (walk : LabelledWalk (wordPathGraph u) start finish word) :
    LabelledWalk (wordPathGraph v) start finish word := by
  cases h
  exact walk

/-- The canonical path across a relator segment inside a lollipop boundary. -/
noncomputable def wordPathRelatorSegmentWalk {α : Type*}
    (stem relator suffix : Word α) :
    LabelledWalk (wordPathGraph ((stem ++ relator) ++ suffix))
      stem.length (stem.length + relator.length) relator := by
  let suffixEmbedding := wordPathSuffixHom stem relator
  let prefixEmbedding := wordPathPrefixHom (stem ++ relator) suffix
  let embedding := LabelledGraphHom.comp prefixEmbedding suffixEmbedding
  let walk := (wordPathWalk relator).map embedding
  have hstart : embedding.mapVertex (0 : Nat) = stem.length := by
    change stem.length + 0 = stem.length
    simp
  have hend : embedding.mapVertex relator.length =
      stem.length + relator.length := by
    change stem.length + relator.length = stem.length + relator.length
    rfl
  exact hstart ▸ (hend ▸ walk)

/-- The innermost doubled stem pair, next to the relator boundary. -/
def lollipopInnermostStemPair {α : Type*} (stem relator : Word α)
    (hstem : stem.length ≠ 0) :
    LabelledDartPair (wordPathGraph (lollipopBoundaryWord stem relator)) :=
  let i : Fin stem.length := ⟨stem.length - 1, by omega⟩
  lollipopStemPair stem relator i

/-- The innermost stem occurrence is included in the list of stem folds. -/
theorem lollipopInnermostStemPair_mem {α : Type*} (stem relator : Word α)
    (hstem : stem.length ≠ 0) :
    lollipopInnermostStemPair stem relator hstem ∈
      lollipopStemPairs stem relator := by
  unfold lollipopInnermostStemPair lollipopStemPairs
  apply List.mem_map.mpr
  refine ⟨⟨stem.length - 1, by omega⟩, ?_, rfl⟩
  simp

/-- Fold the doubled conjugator edges on a lollipop's polygonal boundary. -/
noncomputable def lollipopStemFold {α : Type*} (stem relator : Word α) :=
  let boundaryWord := lollipopBoundaryWord stem relator
  let boundaryHom := wordPathBoundaryHom boundaryWord
  let stemFolds := (lollipopStemPairs stem relator).map
    (LabelledDartPair.map boundaryHom)
  WalkFoldResult.foldPairs stemFolds (wordBoundaryLoop boundaryWord)

/-- A lollipop's relator boundary closes after its doubled conjugator edges
are folded. This constructs an actual relator-labeled loop in the quotient
1-skeleton, based at the relator vertex. -/
noncomputable def lollipopFoldedRelatorLoop {α : Type*}
    (stem relator : Word α) :
    Σ vertex : (lollipopStemFold stem relator).graph.toDartGraph.Vertex,
      LabelledWalk (lollipopStemFold stem relator).graph vertex vertex relator := by
  let boundaryWord := lollipopBoundaryWord stem relator
  let boundaryHom := wordPathBoundaryHom boundaryWord
  let folded := lollipopStemFold stem relator
  let segment := (wordPathRelatorSegmentWalk stem relator
    (FreeGroup.invRev stem)).map boundaryHom
  by_cases hstem : stem.length = 0
  · have hnil : stem = [] := by
      cases stem with
      | nil => rfl
      | cons head tail => simp at hstem
    subst stem
    have hboundarylen : boundaryWord.length = relator.length := by
      simp [boundaryWord]
    have hbase :
        (Quotient.mk (BoundaryVertexSetoid boundaryWord.length) 0 :
          WordBoundaryVertex boundaryWord) =
          Quotient.mk (BoundaryVertexSetoid boundaryWord.length) boundaryWord.length :=
      wordBoundary_endpoints_eq boundaryWord
    have hloop := congrArg folded.hom.mapVertex hbase
    have hendpoint :
        (Quotient.mk (BoundaryVertexSetoid boundaryWord.length) relator.length :
          WordBoundaryVertex boundaryWord) =
          Quotient.mk (BoundaryVertexSetoid boundaryWord.length) boundaryWord.length := by
      congr 1
      exact hboundarylen.symm
    have hloop' := hloop.trans (congrArg folded.hom.mapVertex hendpoint.symm)
    refine ⟨folded.hom.mapVertex (boundaryHom.mapVertex (0 : Nat)), ?_⟩
    have hwalk : LabelledWalk folded.graph
        (folded.hom.mapVertex (boundaryHom.mapVertex (0 : Nat)))
        (folded.hom.mapVertex (boundaryHom.mapVertex relator.length)) relator := by
      simpa [boundaryHom, wordPathBoundaryHom, boundaryWord] using
        segment.map folded.hom
    exact Eq.mp (congrArg
      (fun endpoint => LabelledWalk folded.graph
        (folded.hom.mapVertex (boundaryHom.mapVertex (0 : Nat))) endpoint relator)
      hloop'.symm) hwalk
  · let rawPair := lollipopInnermostStemPair stem relator hstem
    let pair := LabelledDartPair.map boundaryHom rawPair
    let folds := (lollipopStemPairs stem relator).map
      (LabelledDartPair.map boundaryHom)
    have hpairMem : pair ∈ folds := by
      apply List.mem_map.mpr
      exact ⟨rawPair, lollipopInnermostStemPair_mem stem relator hstem, rfl⟩
    have hpairFolded := WalkFoldResult.foldPairs_pair_reverse
      folds (wordBoundaryLoop boundaryWord) pair hpairMem
    have hendpoints := LabelledGraphHom.mapVertex_source_second_eq_target_first
      folded.hom pair hpairFolded
    have hpositive : 0 < stem.length := Nat.pos_of_ne_zero hstem
    have hsourcePath :
        (wordPathGraph boundaryWord).toDartGraph.source rawPair.second =
          stem.length + relator.length := by
      simp [rawPair, lollipopInnermostStemPair, lollipopStemPair,
        lollipopStemMateIndex, wordPathGraph, boundaryWord,
        lollipopBoundaryWord]
      omega
    have htargetPath :
        (wordPathGraph boundaryWord).toDartGraph.target rawPair.first =
          stem.length := by
      simp [rawPair, lollipopInnermostStemPair, lollipopStemPair,
        lollipopStemFirstIndex, wordPathGraph, boundaryWord,
        lollipopBoundaryWord]
      omega
    have hsource :
        (wordBoundaryGraph boundaryWord).toDartGraph.source pair.second =
          Quotient.mk (BoundaryVertexSetoid boundaryWord.length)
            (stem.length + relator.length) := by
      calc
        _ = boundaryHom.mapVertex
              ((wordPathGraph boundaryWord).toDartGraph.source rawPair.second) :=
          by simpa [pair, LabelledDartPair.map] using boundaryHom.map_source rawPair.second
        _ = _ := by
          rw [hsourcePath]
          rfl
    have htarget :
        (wordBoundaryGraph boundaryWord).toDartGraph.target pair.first =
          Quotient.mk (BoundaryVertexSetoid boundaryWord.length) stem.length := by
      calc
        _ = boundaryHom.mapVertex
              ((wordPathGraph boundaryWord).toDartGraph.target rawPair.first) :=
          by simpa [pair, LabelledDartPair.map] using boundaryHom.map_target rawPair.first
        _ = _ := by
          rw [htargetPath]
          rfl
    have hloop :
        folded.hom.mapVertex
            (Quotient.mk (BoundaryVertexSetoid boundaryWord.length) stem.length) =
          folded.hom.mapVertex
            (Quotient.mk (BoundaryVertexSetoid boundaryWord.length)
              (stem.length + relator.length)) := by
      calc
        _ = folded.hom.mapVertex
              ((wordBoundaryGraph boundaryWord).toDartGraph.target pair.first) :=
          congrArg folded.hom.mapVertex htarget.symm
        _ = folded.hom.mapVertex
              ((wordBoundaryGraph boundaryWord).toDartGraph.source pair.second) :=
          hendpoints.symm
        _ = _ := congrArg folded.hom.mapVertex hsource
    refine ⟨folded.hom.mapVertex
      (Quotient.mk (BoundaryVertexSetoid boundaryWord.length) stem.length), ?_⟩
    have hwalk : LabelledWalk folded.graph
        (folded.hom.mapVertex
          (Quotient.mk (BoundaryVertexSetoid boundaryWord.length) stem.length))
        (folded.hom.mapVertex
          (Quotient.mk (BoundaryVertexSetoid boundaryWord.length)
            (stem.length + relator.length))) relator := by
      simpa [boundaryHom, wordPathBoundaryHom, boundaryWord] using
        segment.map folded.hom
    exact Eq.mp (congrArg
      (fun endpoint => LabelledWalk folded.graph
        (folded.hom.mapVertex
          (Quotient.mk (BoundaryVertexSetoid boundaryWord.length) stem.length))
        endpoint relator) hloop.symm) hwalk

/-- The conjugator stem pairs of an explicit relator balloon, expressed in
the occurrence path of its stored raw boundary word. -/
def ReducedRelatorBalloonData.stemPairs {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P) :
    List (LabelledDartPair (wordPathGraph b.label.rawWord)) := by
  let pairs := lollipopStemPairs b.label.conjugator.toWord b.label.relator.toWord
  exact pairs.map (LabelledDartPair.castWordPath
    b.label.lollipopBoundary_eq_rawWord)

/-- The last doubled stem pair of a balloon in its stored raw-word graph. -/
def ReducedRelatorBalloonData.innermostStemPair {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P)
    (hstem : b.label.conjugator.toWord.length ≠ 0) :
    LabelledDartPair (wordPathGraph b.label.rawWord) :=
  LabelledDartPair.castWordPath b.label.lollipopBoundary_eq_rawWord
    (lollipopInnermostStemPair b.label.conjugator.toWord
      b.label.relator.toWord hstem)

/-- The balloon's innermost stem pair occurs among its local stem pairs. -/
theorem ReducedRelatorBalloonData.innermostStemPair_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (hstem : b.label.conjugator.toWord.length ≠ 0) :
    b.innermostStemPair hstem ∈ b.stemPairs := by
  unfold ReducedRelatorBalloonData.innermostStemPair
    ReducedRelatorBalloonData.stemPairs
  apply List.mem_map.mpr
  exact ⟨lollipopInnermostStemPair b.label.conjugator.toWord
    b.label.relator.toWord hstem,
    lollipopInnermostStemPair_mem _ _ hstem, rfl⟩

theorem ReducedRelatorBalloonData.innermostStemPair_source_second
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (hstem : b.label.conjugator.toWord.length ≠ 0) :
    (wordPathGraph b.label.rawWord).toDartGraph.source
        (b.innermostStemPair hstem).second =
      b.label.conjugator.toWord.length + b.label.relator.toWord.length := by
  unfold ReducedRelatorBalloonData.innermostStemPair
  simp [LabelledDartPair.castWordPath, lollipopInnermostStemPair, lollipopStemPair,
    lollipopStemMateIndex, wordPathGraph]
  have hpositive : 0 < b.label.conjugator.toWord.length :=
    Nat.pos_of_ne_zero hstem
  omega

theorem ReducedRelatorBalloonData.innermostStemPair_target_first
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P)
    (hstem : b.label.conjugator.toWord.length ≠ 0) :
    (wordPathGraph b.label.rawWord).toDartGraph.target
        (b.innermostStemPair hstem).first =
      b.label.conjugator.toWord.length := by
  unfold ReducedRelatorBalloonData.innermostStemPair
  simp [LabelledDartPair.castWordPath, lollipopInnermostStemPair, lollipopStemPair,
    lollipopStemFirstIndex, wordPathGraph]
  have hpositive : 0 < b.label.conjugator.toWord.length :=
    Nat.pos_of_ne_zero hstem
  omega

/-- The reduced literal boundary of a balloon retains the canonical path along
its relator segment. -/
noncomputable def ReducedRelatorBalloonData.relatorSegmentWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} (b : ReducedRelatorBalloonData P) :
    LabelledWalk (wordPathGraph b.label.rawWord)
      b.label.conjugator.toWord.length
      (b.label.conjugator.toWord.length + b.label.relator.toWord.length)
      b.label.relator.toWord :=
  castWordPathWalk b.label.lollipopBoundary_eq_rawWord
    (wordPathRelatorSegmentWalk b.label.conjugator.toWord
      b.label.relator.toWord (FreeGroup.invRev b.label.conjugator.toWord))

/-- Every word position after a list prefix is carried into the flattened
occurrence path by the corresponding suffix embedding. -/
@[simp]
theorem LabelledDartPair.map_comp {α : Type*}
    {G H K : LabelledDartGraph α} (g : LabelledGraphHom H K)
    (f : LabelledGraphHom G H) (pair : LabelledDartPair G) :
    LabelledDartPair.map (LabelledGraphHom.comp g f) pair =
      LabelledDartPair.map g (LabelledDartPair.map f pair) := by
  cases pair
  rfl

/-- Recursively place every balloon's conjugator pairs into the occurrence
path of the concatenated literal boundary. Prefix and suffix embeddings retain
the source positions in the flattened word. -/
def reducedBalloonStemPairs {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} :
    (balloons : List (ReducedRelatorBalloonData P)) →
      List (LabelledDartPair
        (wordPathGraph ((balloons.map fun b => b.label.rawWord).flatten)))
  | [] => []
  | b :: tail => by
      let tailWord := (tail.map
        (fun (x : ReducedRelatorBalloonData P) => x.label.rawWord)).flatten
      have hhead : (b.label.rawWord ++ tailWord) =
          (((b :: tail).map fun x => x.label.rawWord).flatten) := rfl
      let firstPairs := b.stemPairs.map
        (LabelledDartPair.map (wordPathPrefixHom b.label.rawWord tailWord))
      let laterPairs := reducedBalloonStemPairs tail |>.map
        (LabelledDartPair.map (wordPathSuffixHom b.label.rawWord tailWord))
      simpa only [hhead] using (firstPairs ++ laterPairs)

@[simp]
theorem reducedBalloonStemPairs_cons {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α}
    (b : ReducedRelatorBalloonData P)
    (tail : List (ReducedRelatorBalloonData P)) :
    reducedBalloonStemPairs (b :: tail) =
      (b.stemPairs.map (LabelledDartPair.map
        (wordPathPrefixHom b.label.rawWord
          ((tail.map (fun (x : ReducedRelatorBalloonData P) =>
            x.label.rawWord)).flatten)))) ++
      ((reducedBalloonStemPairs tail).map (LabelledDartPair.map
        (wordPathSuffixHom b.label.rawWord
          ((tail.map (fun (x : ReducedRelatorBalloonData P) =>
            x.label.rawWord)).flatten)))) := by
  rfl

/-- A local stem pair from any balloon embeds as one of the original
occurrence pairs in the complete flattened boundary. -/
theorem reducedBalloonStemPairs_contains {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (b : ReducedRelatorBalloonData P), b ∈ balloons →
      ∀ (pair : LabelledDartPair (wordPathGraph b.label.rawWord)),
        pair ∈ b.stemPairs →
        ∃ f : LabelledGraphHom (wordPathGraph b.label.rawWord)
            (wordPathGraph ((balloons.map
              (fun (x : ReducedRelatorBalloonData P) => x.label.rawWord)).flatten)),
          LabelledDartPair.map f pair ∈ reducedBalloonStemPairs balloons := by
  intro balloons
  induction balloons with
  | nil =>
      intro b hb pair hp
      simp at hb
  | cons head tail ih =>
      intro b hb pair hp
      rcases List.mem_cons.mp hb with hhead | htail
      · subst b
        refine ⟨wordPathPrefixHom head.label.rawWord
          ((tail.map (fun (x : ReducedRelatorBalloonData P) =>
            x.label.rawWord)).flatten), ?_⟩
        rw [reducedBalloonStemPairs_cons]
        apply List.mem_append.mpr
        left
        exact List.mem_map.mpr ⟨pair, hp, rfl⟩
      · obtain ⟨f, hpair⟩ := ih b htail pair hp
        refine ⟨LabelledGraphHom.comp
          (wordPathSuffixHom head.label.rawWord
            ((tail.map (fun (x : ReducedRelatorBalloonData P) =>
              x.label.rawWord)).flatten)) f, ?_⟩
        rw [reducedBalloonStemPairs_cons]
        apply List.mem_append.mpr
        right
        apply List.mem_map.mpr
        refine ⟨LabelledDartPair.map f pair, hpair, ?_⟩
        rfl

/-- The start and end positions of every balloon boundary in the flattened
word, listed relative to that complete word. -/
def reducedBalloonEndpointPairs {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} :
    (balloons : List (ReducedRelatorBalloonData P)) → List (Nat × Nat)
  | [] => []
  | b :: tail =>
      (0, b.label.rawWord.length) ::
        (reducedBalloonEndpointPairs tail).map (fun pair =>
          ((wordPathSuffixHom b.label.rawWord
            ((tail.map (fun x => x.label.rawWord)).flatten)).mapVertex pair.1,
           (wordPathSuffixHom b.label.rawWord
            ((tail.map (fun x => x.label.rawWord)).flatten)).mapVertex pair.2))

/-- Each balloon occurrence has its own path embedding into the flattened
boundary. Indexing by `Fin` preserves duplicate balloon values as distinct face
occurrences. -/
theorem reducedBalloonOccurrencePathEmbedding {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α}
    (balloons : List (ReducedRelatorBalloonData P))
    (i : Fin balloons.length) :
    ∃ f : LabelledGraphHom
        (wordPathGraph (balloons.get i).label.rawWord)
        (wordPathGraph ((balloons.map
          (fun b => b.label.rawWord)).flatten)),
      (f.mapVertex (0 : Nat),
        f.mapVertex (balloons.get i).label.rawWord.length) ∈
        reducedBalloonEndpointPairs balloons := by
  induction balloons with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
    cases i using Fin.cases with
    | zero =>
      let f : LabelledGraphHom
          (wordPathGraph ((head :: tail).get 0).label.rawWord)
          (wordPathGraph (((head :: tail).map
            (fun b => b.label.rawWord)).flatten)) := by
        simpa only [List.get_cons_zero, List.map_cons, List.flatten_cons] using
          wordPathPrefixHom head.label.rawWord
            ((tail.map (fun b => b.label.rawWord)).flatten)
      refine ⟨f, ?_⟩
      change (0, head.label.rawWord.length) ∈
        reducedBalloonEndpointPairs (head :: tail)
      exact List.Mem.head _
    | succ i =>
      obtain ⟨tailEmbedding, htail⟩ := ih i
      let suffix := wordPathSuffixHom head.label.rawWord
        ((tail.map (fun b => b.label.rawWord)).flatten)
      let f : LabelledGraphHom
          (wordPathGraph ((head :: tail).get i.succ).label.rawWord)
          (wordPathGraph (((head :: tail).map
            (fun b => b.label.rawWord)).flatten)) := by
        simpa only [List.get_cons_succ', List.map_cons, List.flatten_cons] using
          LabelledGraphHom.comp suffix tailEmbedding
      refine ⟨f, ?_⟩
      change (suffix.mapVertex (tailEmbedding.mapVertex (0 : Nat)),
        suffix.mapVertex
          (tailEmbedding.mapVertex ((tail.get i).label.rawWord.length))) ∈
        reducedBalloonEndpointPairs (head :: tail)
      rw [reducedBalloonEndpointPairs]
      apply List.mem_cons.mpr
      right
      apply List.mem_map.mpr
      exact ⟨(tailEmbedding.mapVertex (0 : Nat),
        tailEmbedding.mapVertex ((tail.get i).label.rawWord.length)), htail, rfl⟩

/-- Each balloon boundary has a corresponding pair of endpoint positions in
the flattened occurrence path. -/
theorem reducedBalloonEndpointPairs_contains {α : Type*} [Fintype α]
    [DecidableEq α] {P : SymmetrizedPresentation α} :
    ∀ (balloons : List (ReducedRelatorBalloonData P))
      (b : ReducedRelatorBalloonData P), b ∈ balloons →
      ∃ f : LabelledGraphHom (wordPathGraph b.label.rawWord)
          (wordPathGraph ((balloons.map
            (fun (x : ReducedRelatorBalloonData P) => x.label.rawWord)).flatten)),
        (f.mapVertex (0 : Nat), f.mapVertex b.label.rawWord.length) ∈
          reducedBalloonEndpointPairs balloons := by
  intro balloons
  induction balloons with
  | nil =>
      intro b hb
      simp at hb
  | cons head tail ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hhead | htail
      · subst b
        refine ⟨wordPathPrefixHom head.label.rawWord
          ((tail.map (fun (x : ReducedRelatorBalloonData P) =>
            x.label.rawWord)).flatten), ?_⟩
        change (0, head.label.rawWord.length) ∈
          reducedBalloonEndpointPairs (head :: tail)
        exact List.Mem.head _
      · obtain ⟨f, hpair⟩ := ih b htail
        let suffixEmbedding := wordPathSuffixHom head.label.rawWord
          ((tail.map (fun (x : ReducedRelatorBalloonData P) =>
            x.label.rawWord)).flatten)
        let embedding := LabelledGraphHom.comp suffixEmbedding f
        refine ⟨embedding, ?_⟩
        have hpositions :
            (embedding.mapVertex (0 : Nat),
              embedding.mapVertex b.label.rawWord.length) =
            (suffixEmbedding.mapVertex (f.mapVertex (0 : Nat)),
              suffixEmbedding.mapVertex (f.mapVertex b.label.rawWord.length)) := by
          rfl
        rw [reducedBalloonEndpointPairs, hpositions]
        apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr
          ⟨(f.mapVertex (0 : Nat), f.mapVertex b.label.rawWord.length),
            hpair, rfl⟩

/-- All balloon stem folds for a minimum-area seed, transported to the
occurrence path of its complete lollipop boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonStemPairs
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    List (LabelledDartPair
      (wordPathGraph seed.boundary.reducedLiteralBoundary)) :=
  reducedBalloonStemPairs seed.boundary.reducedBalloons

/-- Endpoint positions for the lollipop loops in the concatenated boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonEndpointPairs
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) : List (Nat × Nat) :=
  reducedBalloonEndpointPairs seed.boundary.reducedBalloons

/-- The polygonal boundary with each lollipop's outer endpoints joined. This
is the wedge of the balloon circuits before the global free cancellations. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  wordBoundaryGraphWithJoins seed.boundary.reducedLiteralBoundary
    seed.balloonEndpointPairs

/-- The path-to-boundary map for the joined balloon boundary. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonBoundaryHom
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  wordPathBoundaryHomWithJoins seed.boundary.reducedLiteralBoundary
    seed.balloonEndpointPairs

/-- The concatenated lollipop boundary is a loop in the wedge of its balloons. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonBoundaryLoop
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  wordBoundaryLoopWithJoins seed.boundary.reducedLiteralBoundary
    seed.balloonEndpointPairs

/-- The stem pairs on the based polygonal boundary graph of the seed. -/
noncomputable def MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :
    List (LabelledDartPair
      seed.balloonBoundaryGraph) :=
  seed.balloonStemPairs.map
    (LabelledDartPair.map seed.balloonBoundaryHom)

/-- First fold every doubled conjugator stem, then replay the global
free-cancellation trace of the minimum-area seed. The result is a quotient
1-skeleton with a closed walk spelling the reduced boundary word. -/
noncomputable def MinimalAreaRelatorBoundarySeed.foldedBalloonBoundaryWalk
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w) :=
  WalkFoldResult.foldPairsThenReduce seed.boundaryBalloonStemPairs
    seed.boundary.reducedLiteralBoundaryShape.to_cancellationSequence
    seed.balloonBoundaryLoop

/-- Every relator occurrence in the minimum-area seed has a closed relator
walk in the final quotient 1-skeleton, after both stem folds and boundary
cancellations. -/
theorem MinimalAreaRelatorBoundarySeed.foldedBalloon_hasRelatorLoop
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (b : ReducedRelatorBalloonData P)
    (hb : b ∈ seed.boundary.reducedBalloons) :
    ∃ vertex : seed.foldedBalloonBoundaryWalk.graph.toDartGraph.Vertex,
      Nonempty (LabelledWalk seed.foldedBalloonBoundaryWalk.graph vertex vertex
        b.label.relator.toWord) := by
  by_cases hstem : b.label.conjugator.toWord.length = 0
  · obtain ⟨embedding, hends⟩ := reducedBalloonEndpointPairs_contains
      seed.boundary.reducedBalloons b hb
    let positions := (embedding.mapVertex (0 : Nat),
      embedding.mapVertex b.label.rawWord.length)
    have hpositions : positions ∈ seed.balloonEndpointPairs := by
      simpa [positions, MinimalAreaRelatorBoundarySeed.balloonEndpointPairs] using hends
    have hjoin := wordBoundary_join_eq seed.boundary.reducedLiteralBoundary
      seed.balloonEndpointPairs positions hpositions
    have hloop := congrArg seed.foldedBalloonBoundaryWalk.hom.mapVertex hjoin
    have hrawlen : b.label.rawWord.length = b.label.relator.toWord.length := by
      rw [b.label.rawWord_length_eq, hstem]
      simp
    let segment := (((b.relatorSegmentWalk.map embedding).map
      seed.balloonBoundaryHom).map seed.foldedBalloonBoundaryWalk.hom)
    refine ⟨seed.foldedBalloonBoundaryWalk.hom.mapVertex
      (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))), ?_⟩
    have hwalk : LabelledWalk seed.foldedBalloonBoundaryWalk.graph
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))))
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex b.label.rawWord.length)))
        b.label.relator.toWord := by
      simpa [segment, hstem, hrawlen] using segment
    refine ⟨Eq.mp (congrArg
        (fun endpoint => LabelledWalk seed.foldedBalloonBoundaryWalk.graph
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat))))
        endpoint b.label.relator.toWord) hloop.symm) hwalk⟩
  · let localPair := b.innermostStemPair hstem
    obtain ⟨embedding, hlocalPair⟩ := reducedBalloonStemPairs_contains
      seed.boundary.reducedBalloons b hb localPair
      (b.innermostStemPair_mem hstem)
    let boundaryHom := seed.balloonBoundaryHom
    let pair := LabelledDartPair.map boundaryHom
      (LabelledDartPair.map embedding localPair)
    have hpairMem : pair ∈ seed.boundaryBalloonStemPairs := by
      unfold MinimalAreaRelatorBoundarySeed.boundaryBalloonStemPairs
      exact List.mem_map.mpr ⟨LabelledDartPair.map embedding localPair,
        hlocalPair, rfl⟩
    have hpairFolded :
        seed.foldedBalloonBoundaryWalk.hom.mapDart pair.second =
          seed.foldedBalloonBoundaryWalk.graph.toDartGraph.reverse
            (seed.foldedBalloonBoundaryWalk.hom.mapDart pair.first) := by
      simpa [MinimalAreaRelatorBoundarySeed.foldedBalloonBoundaryWalk] using
        WalkFoldResult.foldPairsThenReduce_pair_reverse
          seed.boundaryBalloonStemPairs
          seed.boundary.reducedLiteralBoundaryShape.to_cancellationSequence
          seed.balloonBoundaryLoop pair hpairMem
    have hendpoints := LabelledGraphHom.mapVertex_source_second_eq_target_first
      seed.foldedBalloonBoundaryWalk.hom pair hpairFolded
    have hsource :
        seed.balloonBoundaryGraph.toDartGraph.source pair.second =
          boundaryHom.mapVertex
            (embedding.mapVertex
              (b.label.conjugator.toWord.length + b.label.relator.toWord.length)) := by
      calc
        _ = boundaryHom.mapVertex
              ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.source
                (embedding.mapDart localPair.second)) := by
          simpa [pair, LabelledDartPair.map,
            MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph] using
            boundaryHom.map_source (embedding.mapDart localPair.second)
        _ = boundaryHom.mapVertex
              (embedding.mapVertex
                ((wordPathGraph b.label.rawWord).toDartGraph.source localPair.second)) :=
          congrArg boundaryHom.mapVertex (embedding.map_source localPair.second)
        _ = _ := by rw [b.innermostStemPair_source_second hstem]
    have htarget :
        seed.balloonBoundaryGraph.toDartGraph.target pair.first =
          boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length) := by
      calc
        _ = boundaryHom.mapVertex
              ((wordPathGraph seed.boundary.reducedLiteralBoundary).toDartGraph.target
                (embedding.mapDart localPair.first)) := by
          simpa [pair, LabelledDartPair.map,
            MinimalAreaRelatorBoundarySeed.balloonBoundaryGraph] using
            boundaryHom.map_target (embedding.mapDart localPair.first)
        _ = boundaryHom.mapVertex
              (embedding.mapVertex
                ((wordPathGraph b.label.rawWord).toDartGraph.target localPair.first)) :=
          congrArg boundaryHom.mapVertex (embedding.map_target localPair.first)
        _ = _ := by rw [b.innermostStemPair_target_first hstem]
    have hloop :
        seed.foldedBalloonBoundaryWalk.hom.mapVertex
            (boundaryHom.mapVertex
              (embedding.mapVertex b.label.conjugator.toWord.length)) =
          seed.foldedBalloonBoundaryWalk.hom.mapVertex
            (boundaryHom.mapVertex
              (embedding.mapVertex
                (b.label.conjugator.toWord.length + b.label.relator.toWord.length))) := by
      calc
        _ = seed.foldedBalloonBoundaryWalk.hom.mapVertex
              (seed.balloonBoundaryGraph.toDartGraph.target pair.first) :=
            congrArg seed.foldedBalloonBoundaryWalk.hom.mapVertex htarget.symm
        _ = seed.foldedBalloonBoundaryWalk.hom.mapVertex
              (seed.balloonBoundaryGraph.toDartGraph.source pair.second) := hendpoints.symm
        _ = _ := congrArg seed.foldedBalloonBoundaryWalk.hom.mapVertex hsource
    let segment := (((b.relatorSegmentWalk).map embedding).map boundaryHom).map
      seed.foldedBalloonBoundaryWalk.hom
    refine ⟨seed.foldedBalloonBoundaryWalk.hom.mapVertex
      (boundaryHom.mapVertex
        (embedding.mapVertex b.label.conjugator.toWord.length)), ?_⟩
    have hwalk : LabelledWalk seed.foldedBalloonBoundaryWalk.graph
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length)))
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex
              (b.label.conjugator.toWord.length + b.label.relator.toWord.length))))
        b.label.relator.toWord := by
      simpa [segment] using segment
    refine ⟨Eq.mp (congrArg
      (fun endpoint => LabelledWalk seed.foldedBalloonBoundaryWalk.graph
        (seed.foldedBalloonBoundaryWalk.hom.mapVertex
          (boundaryHom.mapVertex
            (embedding.mapVertex b.label.conjugator.toWord.length)))
        endpoint b.label.relator.toWord) hloop.symm) hwalk⟩

/-- Each balloon occurrence has a closed walk for its complete conjugate-relator
boundary in the final quotient graph. -/
theorem MinimalAreaRelatorBoundarySeed.foldedBalloon_hasBoundaryLoop
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (b : ReducedRelatorBalloonData P)
    (hb : b ∈ seed.boundary.reducedBalloons) :
    ∃ vertex : seed.foldedBalloonBoundaryWalk.graph.toDartGraph.Vertex,
      Nonempty (LabelledWalk seed.foldedBalloonBoundaryWalk.graph vertex vertex
        b.label.rawWord) := by
  obtain ⟨embedding, hends⟩ := reducedBalloonEndpointPairs_contains
    seed.boundary.reducedBalloons b hb
  let positions := (embedding.mapVertex (0 : Nat),
    embedding.mapVertex b.label.rawWord.length)
  have hpositions : positions ∈ seed.balloonEndpointPairs := by
    simpa [positions, MinimalAreaRelatorBoundarySeed.balloonEndpointPairs] using hends
  have hjoin := wordBoundary_join_eq seed.boundary.reducedLiteralBoundary
    seed.balloonEndpointPairs positions hpositions
  let start := seed.foldedBalloonBoundaryWalk.hom.mapVertex
    (seed.balloonBoundaryHom.mapVertex (embedding.mapVertex (0 : Nat)))
  let finish := seed.foldedBalloonBoundaryWalk.hom.mapVertex
    (seed.balloonBoundaryHom.mapVertex
      (embedding.mapVertex b.label.rawWord.length))
  have hwalk : LabelledWalk seed.foldedBalloonBoundaryWalk.graph start finish
      b.label.rawWord := by
    simpa [start, finish] using
      (((wordPathWalk b.label.rawWord).map embedding).map
        seed.balloonBoundaryHom).map seed.foldedBalloonBoundaryWalk.hom
  have hstartFinish : start = finish := by
    dsimp [start, finish]
    exact congrArg seed.foldedBalloonBoundaryWalk.hom.mapVertex
      (by
        change seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex (0 : Nat)) =
          seed.balloonBoundaryHom.mapVertex
            (embedding.mapVertex b.label.rawWord.length)
        exact hjoin)
  refine ⟨start, ?_⟩
  exact ⟨Eq.mp (congrArg
    (fun endpoint => LabelledWalk seed.foldedBalloonBoundaryWalk.graph
      start endpoint b.label.rawWord) hstartFinish.symm) hwalk⟩

/-- Choose an actual closed relator walk for each indexed balloon occurrence.
This gives the seed a finite face-boundary family on the common folded
1-skeleton; the remaining diagram work is to supply and verify its cyclic
orders and incidence data. -/
noncomputable def MinimalAreaRelatorBoundarySeed.balloonRelatorLoopAt
    {α : Type*} [Fintype α] [DecidableEq α]
    {P : SymmetrizedPresentation α} {w : FreeGroup α}
    (seed : MinimalAreaRelatorBoundarySeed P.relators w)
    (i : Fin seed.boundary.reducedBalloons.length) :
    Σ vertex : seed.foldedBalloonBoundaryWalk.graph.toDartGraph.Vertex,
      LabelledWalk seed.foldedBalloonBoundaryWalk.graph vertex vertex
        (seed.boundary.reducedBalloons.get i).label.relator.toWord := by
  classical
  let balloon := seed.boundary.reducedBalloons.get i
  have hballoon : balloon ∈ seed.boundary.reducedBalloons := List.get_mem _ _
  let hloop := seed.foldedBalloon_hasRelatorLoop balloon hballoon
  refine ⟨Classical.choose hloop, ?_⟩
  simpa [balloon] using (Classical.choose_spec hloop).some

end GreendlingerDehn
