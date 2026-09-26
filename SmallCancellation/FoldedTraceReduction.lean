import SmallCancellation.PlanarCancellation
import SmallCancellation.DartGraphFold
import SmallCancellation.WordPath

namespace GreendlingerDehn

namespace LabelledWalk

/-- The dart occurrences in a labeled walk, in word order. -/
def darts {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {word : Word α}
    (walk : LabelledWalk G u v word) : List G.toDartGraph.Dart :=
  match walk with
  | .nil _ => []
  | .cons d _ _ tail => d :: tail.darts

@[simp] theorem length_darts {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {word : Word α}
    (walk : LabelledWalk G u v word) : walk.darts.length = word.length := by
  induction walk with
  | nil => rfl
  | cons _ _ _ _ ih => simp [darts, ih]

@[simp] theorem darts_append {α : Type*} {G : LabelledDartGraph α}
    {u v w : G.toDartGraph.Vertex} {left right : Word α}
    (first : LabelledWalk G u v left) (second : LabelledWalk G v w right) :
    (first.append second).darts = first.darts ++ second.darts := by
  induction first with
  | nil => simp [darts, append]
  | cons d hsource htarget tail ih =>
      simp [darts, append, ih]

@[simp] theorem darts_cast {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {left right : Word α}
    (h : left = right) (walk : LabelledWalk G u v left) :
    (h ▸ walk).darts = walk.darts := by
  cases h
  rfl

@[simp] theorem darts_castHead {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {a b : Letter α} {tail : Word α}
    (h : a = b) (walk : LabelledWalk G u v (a :: tail)) :
    (h ▸ walk).darts = walk.darts := by
  cases h
  rfl

@[simp] theorem darts_castStart {α : Type*} {G : LabelledDartGraph α}
    {u u' v : G.toDartGraph.Vertex} {word : Word α}
    (h : u = u') (walk : LabelledWalk G u v word) :
    (h ▸ walk).darts = walk.darts := by
  cases h
  rfl

@[simp] theorem darts_castEnd {α : Type*} {G : LabelledDartGraph α}
    {u v v' : G.toDartGraph.Vertex} {word : Word α}
    (h : v = v') (walk : LabelledWalk G u v word) :
    (h ▸ walk).darts = walk.darts := by
  cases h
  rfl

@[simp] theorem darts_eqMpStart {α : Type*} {G : LabelledDartGraph α}
    {u u' v : G.toDartGraph.Vertex} {word : Word α}
    (h : u = u') (walk : LabelledWalk G u v word) :
    (Eq.mp (congrArg (fun x => LabelledWalk G x v word) h) walk).darts =
      walk.darts := by
  cases h
  rfl

@[simp] theorem darts_eqMpEnd {α : Type*} {G : LabelledDartGraph α}
    {u v v' : G.toDartGraph.Vertex} {word : Word α}
    (h : v = v') (walk : LabelledWalk G u v word) :
    (Eq.mp (congrArg (fun x => LabelledWalk G u x word) h) walk).darts =
      walk.darts := by
  cases h
  rfl

@[simp] theorem darts_map {α : Type*} {G H : LabelledDartGraph α}
    (f : LabelledGraphHom G H) {u v : G.toDartGraph.Vertex}
    {word : Word α} (walk : LabelledWalk G u v word) :
    (walk.map f).darts = walk.darts.map f.mapDart := by
  induction walk with
  | nil => rfl
  | cons d hsource htarget tail ih =>
      simp [map, darts_castHead, darts, ih]

theorem darts_edgeOf {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {a : Letter α}
    (walk : LabelledWalk G u v [a]) :
    walk.darts = [walk.edgeOf.dart] := by
  cases walk with
  | cons d hsource htarget tail => cases tail; rfl

@[simp] theorem darts_foldMap {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {word : Word α}
    (walk : LabelledWalk G u v word)
    (a b : G.toDartGraph.Dart)
    (hlabels : G.label a = inverseLetter (G.label b)) :
    (walk.foldMap a b hlabels).darts = walk.darts.map
      (Quotient.mk (EdgeFoldSetoid G.toDartGraph.reverse a b)) := by
  induction walk with
  | nil => rfl
  | cons d hsource htarget tail ih =>
      simp only [foldMap, darts, List.map_cons, ih]
      rfl

/-- Splicing the two surviving parts of an adjacent cancellation maps each
remaining dart through the fold and omits exactly the selected pair. -/
theorem spliceAcrossFold_darts {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {preWord sufWord : Word α}
    (first second : G.toDartGraph.Dart)
    (before : LabelledWalk G u (G.toDartGraph.source first) preWord)
    (after : LabelledWalk G (G.toDartGraph.target second) v sufWord)
    (hlabels : G.label first = inverseLetter (G.label second)) :
    (before.spliceAcrossFold first second after hlabels).darts =
      before.darts.map (Quotient.mk
        (EdgeFoldSetoid G.toDartGraph.reverse first second)) ++
      after.darts.map (Quotient.mk
        (EdgeFoldSetoid G.toDartGraph.reverse first second)) := by
  let beforeFold := before.foldMap first second hlabels
  let afterFold := after.foldMap first second hlabels
  let joinedAfter :=
    DartGraph.foldedEndpointEq G.toDartGraph first second ▸ afterFold
  change (beforeFold.append joinedAfter).darts =
    before.darts.map (Quotient.mk
      (EdgeFoldSetoid G.toDartGraph.reverse first second)) ++
    after.darts.map (Quotient.mk
      (EdgeFoldSetoid G.toDartGraph.reverse first second))
  have happend := LabelledWalk.darts_append
    (G := G.folded α first second hlabels) beforeFold joinedAfter
  have hbefore : beforeFold.darts = before.darts.map (Quotient.mk
      (EdgeFoldSetoid G.toDartGraph.reverse first second)) := by
    exact darts_foldMap before first second hlabels
  have hjoined : joinedAfter.darts = afterFold.darts := by
    exact LabelledWalk.darts_castStart
      (h := (DartGraph.foldedEndpointEq G.toDartGraph first second).symm)
      afterFold
  have hafter : joinedAfter.darts = after.darts.map (Quotient.mk
      (EdgeFoldSetoid G.toDartGraph.reverse first second)) := by
    exact Eq.trans hjoined (darts_foldMap after first second hlabels)
  have hparts : beforeFold.darts ++ joinedAfter.darts =
      before.darts.map (Quotient.mk
        (EdgeFoldSetoid G.toDartGraph.reverse first second)) ++
      after.darts.map (Quotient.mk
        (EdgeFoldSetoid G.toDartGraph.reverse first second)) :=
    Eq.trans (congrArg (fun xs => xs ++ joinedAfter.darts) hbefore)
      (congrArg (fun xs =>
        before.darts.map (Quotient.mk
          (EdgeFoldSetoid G.toDartGraph.reverse first second)) ++ xs) hafter)
  exact Eq.trans happend hparts

/-- Splitting a walk at a word boundary splits its occurrence list at the
same boundary. -/
theorem split_darts {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} (left right : Word α)
    (walk : LabelledWalk G u v (left ++ right)) :
    walk.darts = (LabelledWalk.split left right walk).2.1.darts ++
      (LabelledWalk.split left right walk).2.2.darts := by
  induction left generalizing u with
  | nil => simp [LabelledWalk.split, darts]
  | cons a left ih =>
      cases walk with
      | cons d hsource htarget tail =>
          simpa [LabelledWalk.split, darts] using ih tail

/-- Two positions in a walk already traverse opposite orientations of one
edge. -/
structure OppositeDartsAt {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {word : Word α}
    (walk : LabelledWalk G u v word) (p : Nat × Nat) where
  first : G.toDartGraph.Dart
  second : G.toDartGraph.Dart
  first_at : walk.darts[p.1]? = some first
  second_at : walk.darts[p.2]? = some second
  opposite : second = G.toDartGraph.reverse first

/-- The single fold used to realize an adjacent cancellation identifies the
two source-walk darts at the cancelled positions as opposite orientations. -/
theorem foldCancellation_sourcePair {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {pre post : Word α} (a : Letter α)
    (walk : LabelledWalk G u v
      (pre ++ [a] ++ [inverseLetter a] ++ post)) :
    ∃ first second,
      walk.darts[pre.length]? = some first ∧
      walk.darts[pre.length + 1]? = some second ∧
      (LabelledWalk.foldCancellation
        (FreeCancellationStep.cancel pre post a) walk).hom.mapDart second =
        (LabelledWalk.foldCancellation
          (FreeCancellationStep.cancel pre post a) walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldCancellation
            (FreeCancellationStep.cancel pre post a) walk).hom.mapDart first) := by
  let step := FreeCancellationStep.cancel pre post a
  have hword : (pre ++ [a] ++ [inverseLetter a] ++ post) =
      (pre ++ ([a] ++ ([inverseLetter a] ++ post))) := by
    simp [List.append_assoc]
  let walk' := hword ▸ walk
  let firstSplit := LabelledWalk.split pre
    ([a] ++ ([inverseLetter a] ++ post)) walk'
  let beforeVertex := firstSplit.1
  let before := firstSplit.2.1
  let afterBefore := firstSplit.2.2
  let secondSplit := LabelledWalk.split [a] ([inverseLetter a] ++ post) afterBefore
  let middleVertex := secondSplit.1
  let firstEdge := secondSplit.2.1
  let afterFirst := secondSplit.2.2
  let thirdSplit := LabelledWalk.split [inverseLetter a] post afterFirst
  let afterVertex := thirdSplit.1
  let secondEdge := thirdSplit.2.1
  let after := thirdSplit.2.2
  let firstData := LabelledWalk.edgeOf firstEdge
  let secondData := LabelledWalk.edgeOf secondEdge
  let firstDart := firstData.dart
  let secondDart := secondData.dart
  have hfirstLabel := firstData.label_eq
  have hsecondLabel := secondData.label_eq
  have hlabels : G.label firstDart = inverseLetter (G.label secondDart) := by
    calc
      G.label firstDart = a := hfirstLabel
      _ = inverseLetter (G.label secondDart) := by
        rw [hsecondLabel, LabelledDartGraph.inverseLetter_inverse]
  have hcast : walk.darts = walk'.darts := by
    exact (LabelledWalk.darts_cast hword walk).symm
  have hsplit₁ : walk'.darts = before.darts ++ afterBefore.darts := by
    change walk'.darts =
      (LabelledWalk.split pre ([a] ++ ([inverseLetter a] ++ post)) walk').2.1.darts ++
        (LabelledWalk.split pre ([a] ++ ([inverseLetter a] ++ post)) walk').2.2.darts
    exact LabelledWalk.split_darts pre ([a] ++ ([inverseLetter a] ++ post)) walk'
  have hsplit₂ : afterBefore.darts = firstEdge.darts ++ afterFirst.darts := by
    change afterBefore.darts =
      (LabelledWalk.split [a] ([inverseLetter a] ++ post) afterBefore).2.1.darts ++
        (LabelledWalk.split [a] ([inverseLetter a] ++ post) afterBefore).2.2.darts
    exact LabelledWalk.split_darts [a] ([inverseLetter a] ++ post) afterBefore
  have hsplit₃ : afterFirst.darts = secondEdge.darts ++ after.darts := by
    change afterFirst.darts =
      (LabelledWalk.split [inverseLetter a] post afterFirst).2.1.darts ++
        (LabelledWalk.split [inverseLetter a] post afterFirst).2.2.darts
    exact LabelledWalk.split_darts [inverseLetter a] post afterFirst
  have hfirstDarts : firstEdge.darts = [firstDart] := by
    simpa [firstData, firstDart] using LabelledWalk.darts_edgeOf firstEdge
  have hsecondDarts : secondEdge.darts = [secondDart] := by
    simpa [secondData, secondDart] using LabelledWalk.darts_edgeOf secondEdge
  have hlist : walk.darts = before.darts ++
      ([firstDart, secondDart] ++ after.darts) := by
    calc
      walk.darts = walk'.darts := hcast
      _ = before.darts ++ afterBefore.darts := hsplit₁
      _ = before.darts ++ (firstEdge.darts ++ afterFirst.darts) := by
        rw [hsplit₂]
      _ = before.darts ++ ([firstDart] ++ ([secondDart] ++ after.darts)) := by
        rw [hsplit₃, hfirstDarts, hsecondDarts]
      _ = before.darts ++ ([firstDart, secondDart] ++ after.darts) := by
        simp
  have hbeforeLen : before.darts.length = pre.length := by
    rw [LabelledWalk.length_darts]
  have hfirstAt : walk.darts[pre.length]? = some firstDart := by
    rw [hlist]
    have hindex : pre.length = before.darts.length + 0 := by omega
    rw [hindex, getElem?_append_shift]
    rfl
  have hsecondAt : walk.darts[pre.length + 1]? = some secondDart := by
    rw [hlist]
    have hindex : pre.length + 1 = before.darts.length + 1 := by omega
    rw [hindex, getElem?_append_shift]
    rfl
  have hfolded :
      (LabelledWalk.foldCancellation step walk).hom.mapDart secondDart =
        (LabelledWalk.foldCancellation step walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldCancellation step walk).hom.mapDart firstDart) := by
    simpa only [step, LabelledWalk.foldCancellation, firstData, secondData,
      firstDart, secondDart] using
      (LabelledDartPairFoldResult.oneFold_pair_reverse
        (⟨firstDart, secondDart, hlabels⟩ : LabelledDartPair G))
  exact ⟨firstDart, secondDart, hfirstAt, hsecondAt, hfolded⟩

/-- One free-cancellation fold removes exactly its two adjacent walk
occurrences, mapping every surviving occurrence through the quotient. -/
theorem foldCancellation_darts {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {pre post : Word α} (a : Letter α)
    (walk : LabelledWalk G u v
      (pre ++ [a] ++ [inverseLetter a] ++ post)) :
    ∃ (firstDart secondDart : G.toDartGraph.Dart)
      (before : LabelledWalk G u (G.toDartGraph.source firstDart) pre)
      (after : LabelledWalk G (G.toDartGraph.target secondDart) v post),
      walk.darts = before.darts ++ [firstDart, secondDart] ++ after.darts ∧
      (LabelledWalk.foldCancellation
        (FreeCancellationStep.cancel pre post a) walk).walk.darts =
        before.darts.map (LabelledWalk.foldCancellation
          (FreeCancellationStep.cancel pre post a) walk).hom.mapDart ++
        after.darts.map (LabelledWalk.foldCancellation
          (FreeCancellationStep.cancel pre post a) walk).hom.mapDart := by
  let step := FreeCancellationStep.cancel pre post a
  have hword : (pre ++ [a] ++ [inverseLetter a] ++ post) =
      (pre ++ ([a] ++ ([inverseLetter a] ++ post))) := by
    simp [List.append_assoc]
  let walk' := hword ▸ walk
  let firstSplit := LabelledWalk.split pre
    ([a] ++ ([inverseLetter a] ++ post)) walk'
  let beforeVertex := firstSplit.1
  let before := firstSplit.2.1
  let afterBefore := firstSplit.2.2
  let secondSplit := LabelledWalk.split [a] ([inverseLetter a] ++ post) afterBefore
  let middleVertex := secondSplit.1
  let firstEdge := secondSplit.2.1
  let afterFirst := secondSplit.2.2
  let thirdSplit := LabelledWalk.split [inverseLetter a] post afterFirst
  let afterVertex := thirdSplit.1
  let secondEdge := thirdSplit.2.1
  let after := thirdSplit.2.2
  let firstData := LabelledWalk.edgeOf firstEdge
  let secondData := LabelledWalk.edgeOf secondEdge
  let firstDart := firstData.dart
  let secondDart := secondData.dart
  have hfirstSource := firstData.source_eq
  have hfirstLabel := firstData.label_eq
  have hsecondTarget := secondData.target_eq
  have hsecondLabel := secondData.label_eq
  have hlabels : G.label firstDart = inverseLetter (G.label secondDart) := by
    calc
      G.label firstDart = a := hfirstLabel
      _ = inverseLetter (G.label secondDart) := by
        rw [hsecondLabel, LabelledDartGraph.inverseLetter_inverse]
  let before' : LabelledWalk G u (G.toDartGraph.source firstDart) pre :=
    hfirstSource.symm ▸ before
  let after' : LabelledWalk G (G.toDartGraph.target secondDart) v post :=
    hsecondTarget ▸ after
  have hsplit₁ : walk'.darts = before.darts ++ afterBefore.darts :=
    LabelledWalk.split_darts pre ([a] ++ ([inverseLetter a] ++ post)) walk'
  have hsplit₂ : afterBefore.darts = firstEdge.darts ++ afterFirst.darts :=
    LabelledWalk.split_darts [a] ([inverseLetter a] ++ post) afterBefore
  have hsplit₃ : afterFirst.darts = secondEdge.darts ++ after.darts :=
    LabelledWalk.split_darts [inverseLetter a] post afterFirst
  have hfirstDarts : firstEdge.darts = [firstDart] :=
    LabelledWalk.darts_edgeOf firstEdge
  have hsecondDarts : secondEdge.darts = [secondDart] :=
    LabelledWalk.darts_edgeOf secondEdge
  have hlist : walk.darts = before.darts ++
      ([firstDart, secondDart] ++ after.darts) := by
    calc
      walk.darts = walk'.darts := by
        exact (LabelledWalk.darts_cast hword walk).symm
      _ = before.darts ++ afterBefore.darts := hsplit₁
      _ = before.darts ++ (firstEdge.darts ++ afterFirst.darts) := by
        rw [hsplit₂]
      _ = before.darts ++ ([firstDart] ++ ([secondDart] ++ after.darts)) := by
        rw [hsplit₃, hfirstDarts, hsecondDarts]
      _ = before.darts ++ ([firstDart, secondDart] ++ after.darts) := by
        simp
  have hlist' : walk.darts = before'.darts ++
      ([firstDart, secondDart] ++ after'.darts) := by
    simpa only [before', after', LabelledWalk.darts_castEnd,
      LabelledWalk.darts_castStart] using hlist
  have hresult :
      (LabelledWalk.foldCancellation step walk).walk.darts =
        before'.darts.map (LabelledWalk.foldCancellation step walk).hom.mapDart ++
        after'.darts.map (LabelledWalk.foldCancellation step walk).hom.mapDart := by
    change (before'.spliceAcrossFold firstDart secondDart after' hlabels).darts =
      before'.darts.map (Quotient.mk
        (EdgeFoldSetoid G.toDartGraph.reverse firstDart secondDart)) ++
      after'.darts.map (Quotient.mk
        (EdgeFoldSetoid G.toDartGraph.reverse firstDart secondDart))
    exact spliceAcrossFold_darts firstDart secondDart before' after' hlabels
  exact ⟨firstDart, secondDart, before', after', by
    simpa only [List.append_assoc] using hlist', hresult⟩

/-- Every dart occurrence remaining after one cancellation is the quotient
image of an occurrence in the original walk. -/
theorem foldCancellation_darts_mem {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (step : FreeCancellationStep raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    {d : (LabelledWalk.foldCancellation step walk).graph.toDartGraph.Dart}
    (hd : d ∈ (LabelledWalk.foldCancellation step walk).walk.darts) :
    ∃ source, source ∈ walk.darts ∧
      (LabelledWalk.foldCancellation step walk).hom.mapDart source = d := by
  cases step with
  | cancel pre post a =>
      obtain ⟨firstDart, secondDart, before, after, hdecomp, hresult⟩ :=
        foldCancellation_darts a walk
      rw [hresult] at hd
      rcases List.mem_append.mp hd with hbefore | hafter
      · rcases List.mem_map.mp hbefore with ⟨source, hsource, hmap⟩
        refine ⟨source, ?_, hmap⟩
        rw [hdecomp]
        simp [hsource]
      · rcases List.mem_map.mp hafter with ⟨source, hsource, hmap⟩
        refine ⟨source, ?_, hmap⟩
        rw [hdecomp]
        simp [hsource]

/-- In a full free-cancellation replay, each surviving boundary occurrence
comes from an occurrence of the initial walk through the accumulated graph
map. -/
theorem foldSequence_darts_mem {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    {d : (LabelledWalk.foldSequence steps walk).graph.toDartGraph.Dart}
    (hd : d ∈ (LabelledWalk.foldSequence steps walk).walk.darts) :
    ∃ source, source ∈ walk.darts ∧
      (LabelledWalk.foldSequence steps walk).hom.mapDart source = d := by
  induction steps generalizing G u v with
  | refl word =>
      exact ⟨d, hd, rfl⟩
  | @cons raw mid reduced step rest ih =>
      let first := LabelledWalk.foldCancellation step walk
      let later := LabelledWalk.foldSequence rest first.walk
      have hcurrent : d ∈ later.walk.darts := by
        change d ∈ later.walk.darts at hd
        exact hd
      obtain ⟨middle, hmiddle, hfinal⟩ := ih first.walk hcurrent
      obtain ⟨source, hsource, hfirst⟩ :=
        foldCancellation_darts_mem step walk hmiddle
      refine ⟨source, hsource, ?_⟩
      change later.hom.mapDart (first.hom.mapDart source) = d
      exact (congrArg later.hom.mapDart hfirst).trans hfinal

/-- Later cancellation folds preserve the occurrence pair selected by the
first step of a free-cancellation sequence. -/
theorem foldSequence_headSourcePair {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {reduced : Word α}
    (pre post : Word α) (a : Letter α)
    (rest : FreeCancellationSequence (pre ++ post) reduced)
    (walk : LabelledWalk G u v
      (pre ++ [a] ++ [inverseLetter a] ++ post)) :
    ∃ first second,
      walk.darts[pre.length]? = some first ∧
      walk.darts[pre.length + 1]? = some second ∧
      (LabelledWalk.foldSequence
        (FreeCancellationSequence.cons
          (FreeCancellationStep.cancel pre post a) rest) walk).hom.mapDart second =
        (LabelledWalk.foldSequence
          (FreeCancellationSequence.cons
            (FreeCancellationStep.cancel pre post a) rest) walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldSequence
            (FreeCancellationSequence.cons
              (FreeCancellationStep.cancel pre post a) rest) walk).hom.mapDart first) := by
  obtain ⟨firstDart, secondDart, hfirstAt, hsecondAt, hfolded⟩ :=
    foldCancellation_sourcePair a walk
  let first := LabelledWalk.foldCancellation
    (FreeCancellationStep.cancel pre post a) walk
  let later := LabelledWalk.foldSequence rest first.walk
  have hfinal :
      (LabelledWalk.foldSequence
        (FreeCancellationSequence.cons
          (FreeCancellationStep.cancel pre post a) rest) walk).hom.mapDart secondDart =
        (LabelledWalk.foldSequence
          (FreeCancellationSequence.cons
            (FreeCancellationStep.cancel pre post a) rest) walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldSequence
            (FreeCancellationSequence.cons
              (FreeCancellationStep.cancel pre post a) rest) walk).hom.mapDart firstDart) := by
    simp only [LabelledWalk.foldSequence]
    change (LabelledGraphHom.comp later.hom first.hom).mapDart secondDart =
      later.graph.toDartGraph.reverse
        ((LabelledGraphHom.comp later.hom first.hom).mapDart firstDart)
    change later.hom.mapDart (first.hom.mapDart secondDart) =
      later.graph.toDartGraph.reverse
        (later.hom.mapDart (first.hom.mapDart firstDart))
    calc
      later.hom.mapDart (first.hom.mapDart secondDart) =
          later.hom.mapDart
            (first.graph.toDartGraph.reverse (first.hom.mapDart firstDart)) :=
        congrArg later.hom.mapDart hfolded
      _ = later.graph.toDartGraph.reverse
            (later.hom.mapDart (first.hom.mapDart firstDart)) :=
        (later.hom.map_reverse _).symm
  exact ⟨firstDart, secondDart, hfirstAt, hsecondAt, hfinal⟩

end LabelledWalk

theorem wordPathWalk_darts {α : Type*} (word : Word α) :
    (wordPathWalk word).darts =
      (List.finRange word.length).map fun i => (i, false) := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
      simp only [wordPathWalk, LabelledWalk.darts,
        List.length_cons, List.finRange_succ, List.map_cons]
      congr 1
      have hmap := LabelledWalk.darts_map (wordPathShiftHom a tail)
        (wordPathWalk tail)
      apply Eq.trans hmap
      rw [ih]
      change List.map (fun d : Fin tail.length × Bool => (d.1.succ, d.2))
        (List.map (fun i => (i, false)) (List.finRange tail.length)) = _
      rw [List.map_map, List.map_map]
      rfl

theorem wordPathWalk_darts_get {α : Type*} (word : Word α)
    (i : Fin word.length) :
    (wordPathWalk word).darts[i.val]? = some (i, false) := by
  rw [wordPathWalk_darts]
  change ((List.finRange word.length).map (fun j => (j, false)))[i.val]? =
    some (i, false)
  rw [← List.ofFn_eq_map]
  simp

theorem wordBoundaryLoopWithJoins_darts {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) :
    (wordBoundaryLoopWithJoins word joins).darts =
      (List.finRange word.length).map fun i => (i, false) := by
  let boundaryWalk :=
    (wordPathWalk word).map (wordPathBoundaryHomWithJoins word joins)
  have htransport :
      (Eq.mp
        (congrArg
          (fun endpoint => LabelledWalk (wordBoundaryGraphWithJoins word joins)
            (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0)
            endpoint word)
          (wordBoundary_endpoints_eq_withJoins word joins).symm)
        boundaryWalk).darts = boundaryWalk.darts := by
    exact LabelledWalk.darts_eqMpEnd
      (wordBoundary_endpoints_eq_withJoins word joins).symm boundaryWalk
  have hmap := LabelledWalk.darts_map
    (wordPathBoundaryHomWithJoins word joins) (wordPathWalk word)
  have hrest : boundaryWalk.darts =
      (List.finRange word.length).map (fun i => (i, false)) := by
    exact hmap.trans (by
      rw [wordPathWalk_darts]
      simp only [wordPathBoundaryHomWithJoins]
      exact List.map_id
        ((List.finRange word.length).map fun i => (i, false)))
  change (Eq.mp
      (congrArg
        (fun endpoint => LabelledWalk (wordBoundaryGraphWithJoins word joins)
          (Quotient.mk (BoundaryVertexJoinSetoid word.length joins) 0)
          endpoint word)
        (wordBoundary_endpoints_eq_withJoins word joins).symm)
      boundaryWalk).darts = _
  exact htransport.trans hrest

theorem wordBoundaryLoopWithJoins_darts_get {α : Type*} (word : Word α)
    (joins : List (Nat × Nat)) (i : Fin word.length) :
    (wordBoundaryLoopWithJoins word joins).darts[i.val]? = some (i, false) := by
  rw [wordBoundaryLoopWithJoins_darts]
  change ((List.finRange word.length).map (fun j => (j, false)))[i.val]? =
    some (i, false)
  rw [← List.ofFn_eq_map]
  simp

namespace FreeReductionShape

variable {α : Type*}

/-- Replay a nested free-reduction trace as deletion of backtracks in a graph
where all recorded cancellation pairs have already been folded. This keeps
the graph quotient fixed while shortening the boundary walk. -/
noncomputable def reduceWalkByFoldedPairs {raw reduced : Word α}
    (shape : FreeReductionShape raw reduced)
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    (walk : LabelledWalk G u v raw)
    (hpaired : ∀ p ∈ shape.cancellationPairs,
      walk.OppositeDartsAt p) :
    LabelledWalk G u v reduced := by
  induction shape generalizing u v G with
  | empty =>
      cases walk
      exact LabelledWalk.nil _
  | letter a =>
      exact walk
  | @append raw₁ reduced₁ raw₂ reduced₂ left right ihLeft ihRight =>
      let pieces := LabelledWalk.split left.inputWord right.inputWord walk
      let leftWalk := pieces.2.1
      let rightWalk := pieces.2.2
      have hsplit : walk.darts = leftWalk.darts ++ rightWalk.darts := by
        change walk.darts =
          (LabelledWalk.split left.inputWord right.inputWord walk).2.1.darts ++
            (LabelledWalk.split left.inputWord right.inputWord walk).2.2.darts
        exact LabelledWalk.split_darts left.inputWord right.inputWord walk
      have hleft : ∀ p ∈ left.cancellationPairs,
          leftWalk.OppositeDartsAt p := by
        intro p hp
        have hp' : p ∈ left.cancellationPairs ++
            shiftCancellationPairs left.inputWord.length right.cancellationPairs :=
          List.mem_append_left _ hp
        obtain ⟨d₁, d₂, hd₁, hd₂, hrev⟩ := hpaired p hp'
        have hb₁ : p.1 < leftWalk.darts.length := by
          rw [LabelledWalk.length_darts]
          exact Nat.lt_trans (left.cancellationPairs_inBounds p hp).1
            (left.cancellationPairs_inBounds p hp).2
        have hb₂ : p.2 < leftWalk.darts.length := by
          rw [LabelledWalk.length_darts]
          exact (left.cancellationPairs_inBounds p hp).2
        have hd₁' : leftWalk.darts[p.1]? = some d₁ := by
          have h := hd₁
          rw [hsplit, List.getElem?_append_left hb₁] at h
          exact h
        have hd₂' : leftWalk.darts[p.2]? = some d₂ := by
          have h := hd₂
          rw [hsplit, List.getElem?_append_left hb₂] at h
          exact h
        exact ⟨d₁, d₂, hd₁', hd₂', hrev⟩
      have hright : ∀ p ∈ right.cancellationPairs,
          rightWalk.OppositeDartsAt p := by
        intro p hp
        let shifted := (left.inputWord.length + p.1, left.inputWord.length + p.2)
        have hp' : shifted ∈ left.cancellationPairs ++
            shiftCancellationPairs left.inputWord.length right.cancellationPairs := by
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        obtain ⟨d₁, d₂, hd₁, hd₂, hrev⟩ := hpaired shifted hp'
        have hleftLen : leftWalk.darts.length = left.inputWord.length := by
          rw [LabelledWalk.length_darts]
        have hd₁' : rightWalk.darts[p.1]? = some d₁ := by
          have h := hd₁
          rw [hsplit] at h
          have hindex : shifted.1 = leftWalk.darts.length + p.1 := by
            simp [shifted, hleftLen]
          rw [hindex, getElem?_append_shift] at h
          exact h
        have hd₂' : rightWalk.darts[p.2]? = some d₂ := by
          have h := hd₂
          rw [hsplit] at h
          have hindex : shifted.2 = leftWalk.darts.length + p.2 := by
            simp [shifted, hleftLen]
          rw [hindex, getElem?_append_shift] at h
          exact h
        exact ⟨d₁, d₂, hd₁', hd₂', hrev⟩
      exact (ihLeft leftWalk hleft).append (ihRight rightWalk hright)
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      have hword : ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix) =
          (([a] ++ inner) ++ ([inverseLetter a] ++ suffix)) := by
        rw [List.append_assoc]
      let hwalk' := hword ▸ walk
      let outerPieces := LabelledWalk.split ([a] ++ inner)
        ([inverseLetter a] ++ suffix) hwalk'
      let front := outerPieces.2.1
      let back := outerPieces.2.2
      let frontPieces := LabelledWalk.split [a] inner front
      let openWalk := frontPieces.2.1
      let innerWalk := frontPieces.2.2
      let backPieces := LabelledWalk.split [inverseLetter a] suffix back
      let closeWalk := backPieces.2.1
      let suffixWalk := backPieces.2.2
      have hsplit₁ : hwalk'.darts = front.darts ++ back.darts := by
        simpa [outerPieces, front, back] using
          LabelledWalk.split_darts ([a] ++ inner) ([inverseLetter a] ++ suffix) hwalk'
      have hsplit₂ : front.darts = openWalk.darts ++ innerWalk.darts := by
        simpa [frontPieces, openWalk, innerWalk] using
          LabelledWalk.split_darts [a] inner front
      have hsplit₃ : back.darts = closeWalk.darts ++ suffixWalk.darts := by
        simpa [backPieces, closeWalk, suffixWalk] using
          LabelledWalk.split_darts [inverseLetter a] suffix back
      have hfull : walk.darts =
          ((openWalk.darts ++ innerWalk.darts) ++
            closeWalk.darts) ++ suffixWalk.darts := by
        have hcast : walk.darts = hwalk'.darts :=
          (LabelledWalk.darts_cast hword walk).symm
        calc
          walk.darts = hwalk'.darts := hcast
          _ = (front.darts ++ back.darts) := hsplit₁
          _ = ((openWalk.darts ++ innerWalk.darts) ++
                (closeWalk.darts ++ suffixWalk.darts)) := by
            rw [hsplit₂, hsplit₃]
          _ = ((openWalk.darts ++ innerWalk.darts) ++
                closeWalk.darts) ++ suffixWalk.darts := by
            exact (List.append_assoc (openWalk.darts ++ innerWalk.darts)
              closeWalk.darts suffixWalk.darts).symm
      have hrootMem : (0, inner.length + 1) ∈
          (FreeReductionShape.bracket a innerShape suffixShape).cancellationPairs := by
        change (0, inner.length + 1) ∈ (0, inner.length + 1) :: _
        exact List.mem_cons_self
      obtain ⟨openDart, closeDart, hopen, hclose, hrootReverse⟩ :=
        hpaired (0, inner.length + 1) hrootMem
      have hOpenLen : openWalk.darts.length = 1 := by
        rw [LabelledWalk.length_darts]
        simp
      have hInnerLen : innerWalk.darts.length = inner.length := by
        rw [LabelledWalk.length_darts]
      have hOpenAt : walk.darts[0]? = openWalk.darts[0]? := by
        have hfull' : walk.darts = openWalk.darts ++
            (innerWalk.darts ++ (closeWalk.darts ++ suffixWalk.darts)) := by
          rw [hfull]
          calc
            _ = (openWalk.darts ++ innerWalk.darts) ++
                (closeWalk.darts ++ suffixWalk.darts) :=
              List.append_assoc _ _ _
            _ = openWalk.darts ++
                (innerWalk.darts ++ (closeWalk.darts ++ suffixWalk.darts)) :=
              List.append_assoc _ _ _
        rw [hfull']
        simp [hOpenLen]
      have hCloseAt : walk.darts[inner.length + 1]? = closeWalk.darts[0]? := by
        have hfull' : walk.darts = (openWalk.darts ++ innerWalk.darts) ++
            (closeWalk.darts ++ suffixWalk.darts) := by
          rw [hfull]
          exact List.append_assoc (openWalk.darts ++ innerWalk.darts)
            closeWalk.darts suffixWalk.darts
        rw [hfull']
        have hPrefixLen : (openWalk.darts ++ innerWalk.darts).length =
            inner.length + 1 := by
          simp [hOpenLen, hInnerLen]
          omega
        have hindex : inner.length + 1 =
            (openWalk.darts ++ innerWalk.darts).length + 0 := by
          omega
        rw [hindex, getElem?_append_shift]
        rw [List.getElem?_append_left (by
          rw [LabelledWalk.length_darts]
          simp)]
      have hOpenIs : openWalk.darts[0]? = some openDart :=
        hOpenAt.symm.trans hopen
      have hCloseIs : closeWalk.darts[0]? = some closeDart :=
        hCloseAt.symm.trans hclose
      have hRootPair : closeDart = G.toDartGraph.reverse openDart := hrootReverse
      have hrootDarts : closeWalk.edgeOf.dart =
          G.toDartGraph.reverse openWalk.edgeOf.dart := by
        have h₁ : openWalk.edgeOf.dart = openDart := by
          have h := hOpenIs
          rw [LabelledWalk.darts_edgeOf] at h
          exact Option.some.inj (by simpa using h)
        have h₂ : closeWalk.edgeOf.dart = closeDart := by
          have h := hCloseIs
          rw [LabelledWalk.darts_edgeOf] at h
          exact Option.some.inj (by simpa using h)
        rw [h₂, h₁, hRootPair]
      have hInnerPairs : ∀ p ∈ innerShape.cancellationPairs,
          innerWalk.OppositeDartsAt p := by
        intro p hp
        let shifted := (1 + p.1, 1 + p.2)
        have hp' : shifted ∈
            (FreeReductionShape.bracket a innerShape suffixShape).cancellationPairs := by
          simp only [FreeReductionShape.cancellationPairs, List.mem_cons,
            List.mem_append]
          exact Or.inr (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩))
        obtain ⟨d₁, d₂, hd₁, hd₂, hrev⟩ := hpaired shifted hp'
        have hAt (i : Nat) (hi : i < inner.length) :
            walk.darts[1 + i]? = innerWalk.darts[i]? := by
          rw [hfull]
          have hOpenLen : openWalk.darts.length = 1 := by
            rw [LabelledWalk.length_darts]
            simp
          simpa [hOpenLen, List.append_assoc] using
            (getElem?_append_middle openWalk.darts innerWalk.darts
              (closeWalk.darts ++ suffixWalk.darts) (i := i) (by
                rw [LabelledWalk.length_darts]
                exact hi))
        have hd₁' : innerWalk.darts[p.1]? = some d₁ := by
          have hb := innerShape.cancellationPairs_inBounds p hp
          have h := hAt p.1 (Nat.lt_trans hb.1 hb.2)
          have hd : walk.darts[1 + p.1]? = some d₁ := by
            simpa [shifted] using hd₁
          exact h.symm.trans hd
        have hd₂' : innerWalk.darts[p.2]? = some d₂ := by
          have h := hAt p.2 (innerShape.cancellationPairs_inBounds p hp).2
          have hd : walk.darts[1 + p.2]? = some d₂ := by
            simpa [shifted] using hd₂
          exact h.symm.trans hd
        exact ⟨d₁, d₂, hd₁', hd₂', hrev⟩
      have hSuffixPairs : ∀ p ∈ suffixShape.cancellationPairs,
          suffixWalk.OppositeDartsAt p := by
        intro p hp
        let shifted := (inner.length + 2 + p.1,
          inner.length + 2 + p.2)
        have hp' : shifted ∈
            (FreeReductionShape.bracket a innerShape suffixShape).cancellationPairs := by
          simp only [FreeReductionShape.cancellationPairs, List.mem_cons,
            List.mem_append]
          exact Or.inr (Or.inr (List.mem_map.mpr ⟨p, hp, by
            simp [shifted, FreeReductionShape.inputWord]⟩))
        obtain ⟨d₁, d₂, hd₁, hd₂, hrev⟩ := hpaired shifted hp'
        have hAt (i : Nat) (hi : i < suffix.length) :
            walk.darts[inner.length + 2 + i]? =
              suffixWalk.darts[i]? := by
          rw [hfull]
          have hPrefix :
              ((openWalk.darts ++ innerWalk.darts) ++ closeWalk.darts).length =
                inner.length + 2 := by
            simp [LabelledWalk.length_darts]
            omega
          have hindex : inner.length + 2 + i =
              ((openWalk.darts ++ innerWalk.darts) ++ closeWalk.darts).length + i := by
            rw [hPrefix]
          rw [hindex]
          exact getElem?_append_shift
            ((openWalk.darts ++ innerWalk.darts) ++ closeWalk.darts)
            suffixWalk.darts i
        have hd₁' : suffixWalk.darts[p.1]? = some d₁ := by
          have hb := suffixShape.cancellationPairs_inBounds p hp
          have h := hAt p.1 (Nat.lt_trans hb.1 hb.2)
          have hd : walk.darts[inner.length + 2 + p.1]? = some d₁ := by
            simpa [shifted, FreeReductionShape.inputWord] using hd₁
          exact h.symm.trans hd
        have hd₂' : suffixWalk.darts[p.2]? = some d₂ := by
          have h := hAt p.2 (suffixShape.cancellationPairs_inBounds p hp).2
          have hd : walk.darts[inner.length + 2 + p.2]? = some d₂ := by
            simpa [shifted, FreeReductionShape.inputWord] using hd₂
          exact h.symm.trans hd
        exact ⟨d₁, d₂, hd₁', hd₂', hrev⟩
      let innerReduced := ihInner innerWalk hInnerPairs
      let suffixReduced := ihSuffix suffixWalk hSuffixPairs
      let openData := LabelledWalk.edgeOf openWalk
      let closeData := LabelledWalk.edgeOf closeWalk
      have hinnerEnds : frontPieces.fst = outerPieces.fst :=
        LabelledWalk.endpoints_eq_of_empty innerReduced
      have hstart : backPieces.fst = u := by
        calc
          backPieces.fst = G.toDartGraph.target closeData.dart := closeData.target_eq.symm
          _ = G.toDartGraph.source openData.dart := by
            rw [hrootDarts, G.toDartGraph.target_reverse]
          _ = u := openData.source_eq
      exact hstart ▸ suffixReduced

end FreeReductionShape

end GreendlingerDehn
