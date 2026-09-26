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

theorem darts_eq_occurrenceDarts {α : Type*} {G : LabelledDartGraph α}
    {u v : G.toDartGraph.Vertex} {word : Word α}
    (walk : LabelledWalk G u v word) : walk.darts = walk.occurrenceDarts := by
  induction walk with
  | nil => rfl
  | cons d hsource htarget tail ih => simp [darts, occurrenceDarts, ih]

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
  let data := LabelledWalk.foldCancellationWithPair step walk
  have hfirstOccurrence : walk.occurrenceDarts[pre.length]? =
      some data.pair.first := by
    simpa [step, FreeCancellationStep.prefixLength] using data.first_at
  have hsecondOccurrence : walk.occurrenceDarts[pre.length + 1]? =
      some data.pair.second := by
    simpa [step, FreeCancellationStep.prefixLength] using data.second_at
  have hfirstAt : walk.darts[pre.length]? = some data.pair.first := by
    rw [darts_eq_occurrenceDarts]
    exact hfirstOccurrence
  have hsecondAt : walk.darts[pre.length + 1]? = some data.pair.second := by
    rw [darts_eq_occurrenceDarts]
    exact hsecondOccurrence
  exact ⟨data.pair.first, data.pair.second, hfirstAt, hsecondAt, by
    simpa [data, step, LabelledWalk.foldCancellation] using
      LabelledWalk.foldCancellationWithPair_pair_reverse step walk⟩

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

/-- The residual occurrence list after one cancellation is an
order-preserving sublist of the input occurrence list after mapping through
the fold homomorphism. -/
theorem foldCancellation_darts_sublist {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (step : FreeCancellationStep raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw) :
    List.Sublist (LabelledWalk.foldCancellation step walk).walk.darts
      (walk.darts.map (LabelledWalk.foldCancellation step walk).hom.mapDart) := by
  cases step with
  | cancel pre post a =>
      obtain ⟨firstDart, secondDart, before, after, hdecomp, hresult⟩ :=
        foldCancellation_darts a walk
      let state := LabelledWalk.foldCancellation
        (FreeCancellationStep.cancel pre post a) walk
      let beforeMap := before.darts.map state.hom.mapDart
      let middleMap := [state.hom.mapDart firstDart, state.hom.mapDart secondDart]
      let afterMap := after.darts.map state.hom.mapDart
      have hinput : walk.darts.map state.hom.mapDart =
          beforeMap ++ middleMap ++ afterMap := by
        rw [hdecomp, List.map_append, List.map_append]
        rfl
      change List.Sublist state.walk.darts
        (walk.darts.map state.hom.mapDart)
      rw [hresult, hinput]
      simpa only [state, beforeMap, middleMap, afterMap, List.append_assoc,
        List.nil_append] using
        (List.Sublist.refl beforeMap).append
          ((List.nil_sublist middleMap).append (List.Sublist.refl afterMap))

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

/-- The complete residual boundary is an order-preserving sublist of the
initial boundary after mapping through the accumulated quotient map. -/
theorem foldSequence_darts_sublist {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw) :
    List.Sublist (LabelledWalk.foldSequence steps walk).walk.darts
      (walk.darts.map (LabelledWalk.foldSequence steps walk).hom.mapDart) := by
  induction steps generalizing G u v with
  | refl word =>
      simpa only [LabelledWalk.foldSequence, LabelledGraphHom.id, List.map_id'] using
        (List.Sublist.refl walk.darts)
  | @cons raw mid reduced step rest ih =>
      let first := LabelledWalk.foldCancellation step walk
      let later := LabelledWalk.foldSequence rest first.walk
      have hlater : List.Sublist later.walk.darts
          (first.walk.darts.map later.hom.mapDart) :=
        ih first.walk
      have hfirst : List.Sublist first.walk.darts
          (walk.darts.map first.hom.mapDart) :=
        foldCancellation_darts_sublist step walk
      have htotal : List.Sublist later.walk.darts
          ((walk.darts.map first.hom.mapDart).map later.hom.mapDart) :=
        hlater.trans (hfirst.map later.hom.mapDart)
      change List.Sublist later.walk.darts
        (walk.darts.map (LabelledGraphHom.comp later.hom first.hom).mapDart)
      simpa only [List.map_map, LabelledGraphHom.comp] using htotal

/-- Final boundary positions embed strictly increasingly into initial
boundary positions after the accumulated graph map, preserving each retained
dart occurrence. -/
theorem foldSequence_darts_sourcePositions {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw) :
    ∃ f : Fin (LabelledWalk.foldSequence steps walk).walk.darts.length ↪o
        Fin (walk.darts.map (LabelledWalk.foldSequence steps walk).hom.mapDart).length,
      ∀ i,
        (LabelledWalk.foldSequence steps walk).walk.darts.get i =
          (walk.darts.map (LabelledWalk.foldSequence steps walk).hom.mapDart).get (f i) :=
  List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (foldSequence_darts_sublist steps walk)

/-- Source positions paired by a cancellation sequence, together with the
positions that survive to its output. -/
structure CancellationOccurrencePositions {α : Type*} (source : Word α) where
  pairs : List (Fin source.length × Fin source.length)
  survivors : List (Fin source.length)

/-- All source positions recorded by cancellation pairs, in pair order. -/
def CancellationOccurrencePositions.endpointOccurrences
    {α : Type*} {source : Word α}
    (trace : CancellationOccurrencePositions source) : List (Fin source.length) :=
  trace.pairs.flatMap fun p => [p.1, p.2]

/-- Carry source positions through a cancellation sequence by deleting the
two current positions selected at each step. -/
def sourcePositionTraceAux {α : Type*} (source : Word α) :
    {raw reduced : Word α} →
    (steps : FreeCancellationSequence raw reduced) →
    (origins : List (Fin source.length)) →
    origins.length = raw.length → CancellationOccurrencePositions source
  | _, _, .refl _, origins, _ => ⟨[], origins⟩
  | _, _, @FreeCancellationSequence.cons _ raw mid reduced step rest, origins, hlen => by
      have hrawLen : origins.length = mid.length + 2 := by
        rw [hlen]
        exact step.length_difference
      have hpairBound : step.prefixLength + 2 ≤ origins.length := by
        rw [hlen]
        exact step.prefixLength_add_two_le
      have hfirstBound : step.prefixLength < origins.length := by omega
      have hsecondBound : step.prefixLength + 1 < origins.length := by omega
      let first := origins.get ⟨step.prefixLength, hfirstBound⟩
      let second := origins.get ⟨step.prefixLength + 1, hsecondBound⟩
      let remaining := origins.take step.prefixLength ++
        origins.drop (step.prefixLength + 2)
      have hremaining : remaining.length = mid.length := by
        dsimp [remaining]
        have htake : step.prefixLength ≤ origins.length := by omega
        rw [List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left htake]
        omega
      let later := sourcePositionTraceAux source rest remaining hremaining
      exact ⟨(first, second) :: later.pairs, later.survivors⟩
  termination_by raw reduced _steps origins _hlen => raw.length
  decreasing_by
    omega

/-- The occurrence trace is unchanged when its cancellation sequence is
transported across equalities of its endpoint words. -/
theorem sourcePositionTraceAux_castWords {α : Type*}
    (source : Word α) {raw raw' reduced reduced' : Word α}
    (hraw : raw = raw') (hred : reduced = reduced')
    (steps : FreeCancellationSequence raw reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw'.length) :
    sourcePositionTraceAux source
        (FreeCancellationSequence.castWords hraw hred steps) origins hlen =
      sourcePositionTraceAux source steps origins (by simpa [hraw] using hlen) := by
  cases hraw
  cases hred
  rfl

/-- Initialize the source-position trace with the complete range of input
occurrences. -/
def sourcePositionTrace {α : Type*} {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced) :
    CancellationOccurrencePositions raw :=
  sourcePositionTraceAux raw steps (List.finRange raw.length) (by simp)

/-- The occurrence trace leaves exactly as many source positions as the
reduced word has letters. -/
theorem sourcePositionTraceAux_survivors_length {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length) :
    (sourcePositionTraceAux source steps origins hlen).survivors.length =
      reduced.length := by
  induction steps generalizing origins with
  | refl word => simpa [sourcePositionTraceAux] using hlen
  | @cons raw mid reduced step rest ih =>
      cases step with
      | cancel pre post a =>
          have hraw : origins.length =
              (pre ++ [a] ++ [inverseLetter a] ++ post).length := hlen
          have hrawLen : origins.length = pre.length + 2 + post.length := by
            have hraw' : origins.length = pre.length + (post.length + 2) := by
              simpa [List.length_append] using hraw
            omega
          let remaining := origins.take pre.length ++ origins.drop (pre.length + 2)
          have hremaining : remaining.length = (pre ++ post).length := by
            dsimp [remaining]
            have htake : pre.length ≤ origins.length := by omega
            have hdrop : pre.length + 2 ≤ origins.length := by omega
            have hdropLen : origins.length - (pre.length + 2) = post.length := by
              omega
            rw [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left htake]
            rw [hdropLen]
            simp [List.length_append]
          simpa only [sourcePositionTraceAux.eq_2,
            FreeCancellationStep.prefixLength] using
            (ih remaining hremaining)

/-- Tracing a composite cancellation sequence is the concatenation of the
first trace and the trace of the second sequence on the surviving origins. -/
theorem sourcePositionTraceAux_trans {α : Type*}
    (source : Word α) {raw mid reduced : Word α}
    (first : FreeCancellationSequence raw mid)
    (second : FreeCancellationSequence mid reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length) :
    sourcePositionTraceAux source (first.trans second) origins hlen =
      { pairs :=
          (sourcePositionTraceAux source first origins hlen).pairs ++
            (sourcePositionTraceAux source second
              (sourcePositionTraceAux source first origins hlen).survivors
              (sourcePositionTraceAux_survivors_length source first origins hlen)).pairs
        survivors :=
          (sourcePositionTraceAux source second
            (sourcePositionTraceAux source first origins hlen).survivors
            (sourcePositionTraceAux_survivors_length source first origins hlen)).survivors } := by
  induction first generalizing origins with
  | refl word =>
      simp [FreeCancellationSequence.trans, sourcePositionTraceAux]
  | @cons raw before mid step rest ih =>
      cases step with
      | cancel pre post a =>
          have hraw : origins.length =
              (pre ++ [a] ++ [inverseLetter a] ++ post).length := hlen
          have hrawLen : origins.length = pre.length + 2 + post.length := by
            have hraw' : origins.length = pre.length + (post.length + 2) := by
              simpa [List.length_append] using hraw
            omega
          let remaining := origins.take pre.length ++ origins.drop (pre.length + 2)
          have hremaining : remaining.length = (pre ++ post).length := by
            dsimp [remaining]
            have htake : pre.length ≤ origins.length := by omega
            have hdrop : pre.length + 2 ≤ origins.length := by omega
            have hdropLen : origins.length - (pre.length + 2) = post.length := by
              omega
            rw [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left htake]
            rw [hdropLen]
            simp [List.length_append]
          have hrecursive := ih second remaining hremaining
          simp only [FreeCancellationSequence.trans, sourcePositionTraceAux.eq_2,
            FreeCancellationStep.prefixLength]
          change
            (⟨(origins.get ⟨pre.length, by omega⟩,
                origins.get ⟨pre.length + 1, by omega⟩) ::
                (sourcePositionTraceAux source (rest.trans second) remaining hremaining).pairs,
              (sourcePositionTraceAux source (rest.trans second) remaining hremaining).survivors⟩ :
              CancellationOccurrencePositions source) = _
          rw [hrecursive]
          simp [remaining]

/-- Appending a fixed right context leaves its source occurrences untouched
by the cancellation trace. -/
theorem sourcePositionTraceAux_appendRight {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced) (suffix : Word α)
    (origins suffixOrigins : List (Fin source.length))
    (hlen : origins.length = raw.length)
    (hsuffix : suffixOrigins.length = suffix.length) :
    sourcePositionTraceAux source (steps.appendRight suffix)
        (origins ++ suffixOrigins) (by simp [List.length_append, hlen, hsuffix]) =
      { pairs := (sourcePositionTraceAux source steps origins hlen).pairs,
        survivors :=
          (sourcePositionTraceAux source steps origins hlen).survivors ++ suffixOrigins } := by
  induction steps generalizing origins suffixOrigins with
  | refl word =>
      simp [FreeCancellationSequence.appendRight, sourcePositionTraceAux]
  | @cons raw mid reduced step rest ih =>
      let p := step.prefixLength
      have hstepLength := step.length_difference
      have hpairBound : p + 2 ≤ origins.length := by
        dsimp [p]
        rw [hlen]
        exact step.prefixLength_add_two_le
      have hfirstBound : p < origins.length := by omega
      have hsecondBound : p + 1 < origins.length := by omega
      have hfirstCombined : p < (origins ++ suffixOrigins).length := by
        simp [List.length_append]
        omega
      have hsecondCombined : p + 1 < (origins ++ suffixOrigins).length := by
        simp [List.length_append]
        omega
      let remaining := origins.take p ++ origins.drop (p + 2)
      have hremaining : remaining.length = mid.length := by
        dsimp [remaining]
        have htake : p ≤ origins.length := by omega
        rw [List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left htake, hlen]
        omega
      have htakeCombined : (origins ++ suffixOrigins).take p = origins.take p :=
        List.take_append_of_le_length (by omega)
      have hdropCombined : (origins ++ suffixOrigins).drop (p + 2) =
          origins.drop (p + 2) ++ suffixOrigins :=
        List.drop_append_of_le_length (by omega)
      have hremainingCombined :
          (origins ++ suffixOrigins).take p ++
          (origins ++ suffixOrigins).drop (p + 2) = remaining ++ suffixOrigins := by
        rw [htakeCombined, hdropCombined]
        simp [remaining, List.append_assoc]
      have hfirstEq :
          (origins ++ suffixOrigins).get ⟨p, hfirstCombined⟩ =
            origins.get ⟨p, hfirstBound⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left hfirstBound
      have hsecondEq :
          (origins ++ suffixOrigins).get ⟨p + 1, hsecondCombined⟩ =
            origins.get ⟨p + 1, hsecondBound⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left hsecondBound
      have hrecursive := ih remaining suffixOrigins hremaining hsuffix
      change sourcePositionTraceAux source
          (FreeCancellationSequence.cons (step.appendRight suffix)
            (rest.appendRight suffix)) (origins ++ suffixOrigins) _ = _
      simp only [sourcePositionTraceAux.eq_2,
        FreeCancellationStep.prefixLength_appendRight, p, hfirstEq, hsecondEq,
        hremainingCombined]
      rw [hrecursive]

/-- Appending a fixed left context preserves its source occurrences and shifts
every cancellation pair by the context length. -/
theorem sourcePositionTraceAux_appendLeft {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced) (preContext : Word α)
    (prefixOrigins origins : List (Fin source.length))
    (hprefix : prefixOrigins.length = preContext.length)
    (horigins : origins.length = raw.length) :
    sourcePositionTraceAux source (steps.appendLeft preContext)
        (prefixOrigins ++ origins)
        (by simp [List.length_append, hprefix, horigins]) =
      { pairs := (sourcePositionTraceAux source steps origins horigins).pairs,
        survivors :=
          prefixOrigins ++ (sourcePositionTraceAux source steps origins horigins).survivors } := by
  induction steps generalizing prefixOrigins origins with
  | refl word =>
      simp [FreeCancellationSequence.appendLeft, sourcePositionTraceAux]
  | @cons raw mid reduced step rest ih =>
      let p := step.prefixLength
      let offset := prefixOrigins.length + p
      have hstepLength := step.length_difference
      have hpairBound : p + 2 ≤ origins.length := by
        change step.prefixLength + 2 ≤ origins.length
        rw [horigins]
        exact step.prefixLength_add_two_le
      have hfirstBound : p < origins.length := by omega
      have hsecondBound : p + 1 < origins.length := by omega
      have hfirstCombined : offset < (prefixOrigins ++ origins).length := by
        simp [List.length_append]
        omega
      have hsecondCombined : offset + 1 < (prefixOrigins ++ origins).length := by
        simp [List.length_append]
        omega
      let remaining := origins.take p ++ origins.drop (p + 2)
      have hremaining : remaining.length = mid.length := by
        dsimp [remaining]
        have htake : p ≤ origins.length := by omega
        rw [List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left htake, horigins]
        omega
      have htakeCombined :
          (prefixOrigins ++ origins).take offset = prefixOrigins ++ origins.take p := by
        dsimp [offset]
        exact List.take_length_add_append p
      have hdropIndex : offset + 2 = prefixOrigins.length + (p + 2) := by
        dsimp [offset]
        omega
      have hdropCombined :
          (prefixOrigins ++ origins).drop (offset + 2) = origins.drop (p + 2) := by
        rw [hdropIndex]
        exact List.drop_length_add_append (p + 2)
      have hremainingCombined :
          (prefixOrigins ++ origins).take offset ++
              (prefixOrigins ++ origins).drop (offset + 2) =
            prefixOrigins ++ remaining := by
        rw [htakeCombined, hdropCombined]
        simp [remaining, List.append_assoc]
      have hfirstEq :
          (prefixOrigins ++ origins).get ⟨offset, hfirstCombined⟩ =
            origins.get ⟨p, hfirstBound⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        rw [List.getElem_append_right (by dsimp [offset]; omega)]
        simp [offset]
      have hsecondEq :
          (prefixOrigins ++ origins).get ⟨offset + 1, hsecondCombined⟩ =
            origins.get ⟨p + 1, hsecondBound⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        rw [List.getElem_append_right (by dsimp [offset]; omega)]
        simp [offset]
        congr 1
        omega
      have hrecursive := ih prefixOrigins remaining hprefix hremaining
      have hstepOffset : (step.appendLeft preContext).prefixLength = offset := by
        simp [FreeCancellationStep.prefixLength_appendLeft, offset, p, hprefix]
      change sourcePositionTraceAux source
          (FreeCancellationSequence.cons (step.appendLeft preContext)
            (rest.appendLeft preContext)) (prefixOrigins ++ origins) _ = _
      simp only [sourcePositionTraceAux.eq_2, hstepOffset,
        hfirstEq, hsecondEq, hremainingCombined]
      rw [hrecursive]

/-- Every input occurrence is recorded exactly once, either as one endpoint
of a cancellation pair or as a surviving position. -/
theorem sourcePositionTraceAux_endpoint_partition {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length) :
    List.Perm
      ((sourcePositionTraceAux source steps origins hlen).endpointOccurrences ++
        (sourcePositionTraceAux source steps origins hlen).survivors)
      origins := by
  induction steps generalizing origins with
  | refl word =>
      simp only [sourcePositionTraceAux.eq_1,
        CancellationOccurrencePositions.endpointOccurrences]
      exact List.Perm.refl _
  | @cons raw mid reduced step rest ih =>
      cases step with
      | cancel pre post a =>
          have hraw : origins.length =
              (pre ++ [a] ++ [inverseLetter a] ++ post).length := hlen
          have hrawLen : origins.length = pre.length + 2 + post.length := by
            have hraw' : origins.length = pre.length + (post.length + 2) := by
              simpa [List.length_append] using hraw
            omega
          have hfirstBound : pre.length < origins.length := by omega
          have hsecondBound : pre.length + 1 < origins.length := by omega
          let first := origins.get ⟨pre.length, hfirstBound⟩
          let second := origins.get ⟨pre.length + 1, hsecondBound⟩
          let remaining := origins.take pre.length ++ origins.drop (pre.length + 2)
          have hremaining : remaining.length = (pre ++ post).length := by
            dsimp [remaining]
            have htake : pre.length ≤ origins.length := by omega
            have hdrop : pre.length + 2 ≤ origins.length := by omega
            have hdropLen : origins.length - (pre.length + 2) = post.length := by
              omega
            rw [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left htake]
            rw [hdropLen]
            simp [List.length_append]
          have hpairPrefix : origins.take (pre.length + 2) =
              origins.take pre.length ++ [first, second] := by
            have hfirstValue : first = origins[pre.length] := by
              exact List.get_eq_getElem
            have hsecondValue : second = origins[pre.length + 1] := by
              exact List.get_eq_getElem
            have hfirstTake : origins.take pre.length ++ [first] =
                origins.take (pre.length + 1) := by
              simp [hfirstValue]
            have hsecondTake : origins.take (pre.length + 1) ++ [second] =
                origins.take (pre.length + 2) := by
              simp [hsecondValue]
            calc
              origins.take (pre.length + 2) =
                  origins.take (pre.length + 1) ++ [second] := hsecondTake.symm
              _ = (origins.take pre.length ++ [first]) ++ [second] := by
                rw [hfirstTake]
              _ = origins.take pre.length ++ [first, second] := by
                simp [List.append_assoc]
          have hsplit : origins =
              (origins.take pre.length ++ [first, second]) ++
                origins.drop (pre.length + 2) := by
            calc
              origins = origins.take (pre.length + 2) ++
                  origins.drop (pre.length + 2) :=
                (List.take_append_drop (pre.length + 2) origins).symm
              _ = _ := by rw [hpairPrefix]
          have hrotate : List.Perm ([first, second] ++ remaining) origins := by
            have hstart : [first, second] ++ remaining =
                ([first, second] ++ origins.take pre.length) ++
                  origins.drop (pre.length + 2) := by
              dsimp [remaining]
            have hmiddle : List.Perm
                (([first, second] ++ origins.take pre.length) ++
                  origins.drop (pre.length + 2))
                ((origins.take pre.length ++ [first, second]) ++
                  origins.drop (pre.length + 2)) :=
              List.perm_append_comm.append_right _
            have hend : (origins.take pre.length ++ [first, second]) ++
                origins.drop (pre.length + 2) = origins := by
              exact hsplit.symm
            have hstartPerm : List.Perm ([first, second] ++ remaining)
                (([first, second] ++ origins.take pre.length) ++
                  origins.drop (pre.length + 2)) := by
              rw [hstart]
            have hendPerm : List.Perm
                ((origins.take pre.length ++ [first, second]) ++
                  origins.drop (pre.length + 2)) origins := by
              rw [hend]
            exact hstartPerm.trans (hmiddle.trans hendPerm)
          simp only [sourcePositionTraceAux.eq_2,
            CancellationOccurrencePositions.endpointOccurrences, List.flatMap_cons,
            FreeCancellationStep.prefixLength]
          change List.Perm
            ([first, second] ++
              ((sourcePositionTraceAux source rest remaining hremaining).endpointOccurrences ++
                (sourcePositionTraceAux source rest remaining hremaining).survivors))
            origins
          exact ((ih remaining hremaining).append_left [first, second]).trans hrotate

/-- The boundary left by replay is exactly the ordered list of source
occurrences marked as survivors by the nested cancellation trace. -/
theorem foldSequence_darts_eq_sourcePositionTraceAux_survivors {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin source.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = origins.map sourceDarts) :
    (LabelledWalk.foldSequence steps walk).walk.darts =
      (sourcePositionTraceAux source steps origins hlen).survivors.map
        (fun i => (LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts i)) := by
  induction steps generalizing G u v origins sourceDarts with
  | refl raw =>
      simpa [sourcePositionTraceAux, LabelledWalk.foldSequence,
        LabelledGraphHom.id] using hwalk
  | @cons raw mid reduced step rest ih =>
      cases step with
      | cancel pre post a =>
          have hraw : origins.length =
              (pre ++ [a] ++ [inverseLetter a] ++ post).length := hlen
          have hrawLen : origins.length = pre.length + 2 + post.length := by
            have hraw' : origins.length = pre.length + (post.length + 2) := by
              simpa [List.length_append] using hraw
            omega
          have hfirstBound : pre.length < origins.length := by omega
          have hsecondBound : pre.length + 1 < origins.length := by omega
          let remaining := origins.take pre.length ++ origins.drop (pre.length + 2)
          have hremaining : remaining.length = (pre ++ post).length := by
            dsimp [remaining]
            have htake : pre.length ≤ origins.length := by omega
            have hdrop : pre.length + 2 ≤ origins.length := by omega
            have hdropLen : origins.length - (pre.length + 2) = post.length := by
              omega
            rw [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left htake]
            rw [hdropLen]
            simp [List.length_append]
          let first := LabelledWalk.foldCancellation
            (FreeCancellationStep.cancel pre post a) walk
          obtain ⟨firstDart, secondDart, before, after, hdecomp, hresult⟩ :=
            foldCancellation_darts a walk
          have hbefore : before.darts = walk.darts.take pre.length := by
            rw [hdecomp]
            simp [LabelledWalk.length_darts]
          have hafter : after.darts = walk.darts.drop (pre.length + 2) := by
            have hprefixLen : (before.darts ++ [firstDart, secondDart]).length =
                pre.length + 2 := by simp [LabelledWalk.length_darts]
            have hdropEq :
                ((before.darts ++ [firstDart, secondDart]) ++ after.darts).drop
                    (pre.length + 2) = after.darts := by
              rw [← hprefixLen, List.drop_append_of_le_length (Nat.le_refl _)]
              simp
            rw [hdecomp]
            exact hdropEq.symm
          have hbeforeSource : before.darts =
              (origins.take pre.length).map sourceDarts := by
            calc
              before.darts = walk.darts.take pre.length := hbefore
              _ = (origins.map sourceDarts).take pre.length := by rw [hwalk]
              _ = (origins.take pre.length).map sourceDarts := by simp
          have hafterSource : after.darts =
              (origins.drop (pre.length + 2)).map sourceDarts := by
            calc
              after.darts = walk.darts.drop (pre.length + 2) := hafter
              _ = (origins.map sourceDarts).drop (pre.length + 2) := by rw [hwalk]
              _ = (origins.drop (pre.length + 2)).map sourceDarts := by simp
          let sourceDarts' : Fin source.length → first.graph.toDartGraph.Dart :=
            fun i => first.hom.mapDart (sourceDarts i)
          have hwalk' : first.walk.darts = remaining.map sourceDarts' := by
            rw [hresult, hbeforeSource, hafterSource]
            simp only [List.map_map, Function.comp_def, sourceDarts', remaining,
              List.map_append]
            rfl
          have htail := ih remaining hremaining first.walk sourceDarts' hwalk'
          rw [sourcePositionTraceAux.eq_2]
          simp only [FreeCancellationStep.prefixLength]
          change (LabelledWalk.foldSequence rest first.walk).walk.darts =
            (sourcePositionTraceAux source rest remaining hremaining).survivors.map
              (fun i => (LabelledWalk.foldSequence rest first.walk).hom.mapDart
                (first.hom.mapDart (sourceDarts i)))
          exact htail

/-- The initialized source-position trace records exactly the darts left on
its replayed boundary, in their original order and after the final quotient
map. -/
theorem foldSequence_darts_eq_sourcePositionTrace_survivors {α : Type*}
    {G : LabelledDartGraph α} {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin raw.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = (List.finRange raw.length).map sourceDarts) :
    (LabelledWalk.foldSequence steps walk).walk.darts =
      (sourcePositionTrace steps).survivors.map
        (fun i => (LabelledWalk.foldSequence steps walk).hom.mapDart
          (sourceDarts i)) := by
  simpa only [sourcePositionTrace] using
    (foldSequence_darts_eq_sourcePositionTraceAux_survivors raw steps
      (List.finRange raw.length) (by simp) walk sourceDarts hwalk)

/-- The initialized trace partitions the full input occurrence range. -/
theorem sourcePositionTrace_endpoint_partition {α : Type*}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced) :
    List.Perm ((sourcePositionTrace steps).endpointOccurrences ++
      (sourcePositionTrace steps).survivors) (List.finRange raw.length) := by
  simpa [sourcePositionTrace] using
    sourcePositionTraceAux_endpoint_partition raw steps (List.finRange raw.length) (by simp)

/-- At a cancellation step, the two live walk darts are the images of the
source occurrences recorded at that step's current positions. -/
theorem sourcePositionTraceAux_head_sourceDarts {α : Type*}
    (source : Word α) {pre post : Word α} (a : Letter α)
    (origins : List (Fin source.length))
    (hlen : origins.length = (pre ++ [a] ++ [inverseLetter a] ++ post).length)
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    (walk : LabelledWalk G u v
      (pre ++ [a] ++ [inverseLetter a] ++ post))
    (sourceDarts : Fin source.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = origins.map sourceDarts) :
    ∃ firstDart secondDart,
      walk.darts[pre.length]? = some firstDart ∧
      walk.darts[pre.length + 1]? = some secondDart ∧
      sourceDarts (origins.get ⟨pre.length, by
        have hlen' : origins.length = pre.length + 2 + post.length := by
          have hlen'' : origins.length = pre.length + (post.length + 2) := by
            simpa [List.length_append] using hlen
          omega
        omega⟩) = firstDart ∧
      sourceDarts (origins.get ⟨pre.length + 1, by
        have hlen' : origins.length = pre.length + 2 + post.length := by
          have hlen'' : origins.length = pre.length + (post.length + 2) := by
            simpa [List.length_append] using hlen
          omega
        omega⟩) = secondDart := by
  have hlen' : origins.length = pre.length + 2 + post.length := by
    have hlen'' : origins.length = pre.length + (post.length + 2) := by
      simpa [List.length_append] using hlen
    omega
  have hfirstBound : pre.length < origins.length := by omega
  have hsecondBound : pre.length + 1 < origins.length := by omega
  let firstPosition := origins.get ⟨pre.length, hfirstBound⟩
  let secondPosition := origins.get ⟨pre.length + 1, hsecondBound⟩
  obtain ⟨firstDart, secondDart, hfirstAt, hsecondAt, _⟩ :=
    foldCancellation_sourcePair a walk
  have hfirstValue : firstPosition = origins[pre.length] := by
    exact List.get_eq_getElem
  have hsecondValue : secondPosition = origins[pre.length + 1] := by
    exact List.get_eq_getElem
  have hfirstPosition : origins[pre.length]? = some firstPosition := by
    rw [hfirstValue]
    simp
  have hsecondPosition : origins[pre.length + 1]? = some secondPosition := by
    rw [hsecondValue]
    simp
  have hfirstMap : (origins.map sourceDarts)[pre.length]? =
      some (sourceDarts firstPosition) := by
    rw [List.getElem?_map, hfirstPosition]
    simp
  have hsecondMap : (origins.map sourceDarts)[pre.length + 1]? =
      some (sourceDarts secondPosition) := by
    rw [List.getElem?_map, hsecondPosition]
    simp
  have hfirstWalk : (origins.map sourceDarts)[pre.length]? = some firstDart := by
    rw [← hwalk]
    exact hfirstAt
  have hsecondWalk : (origins.map sourceDarts)[pre.length + 1]? = some secondDart := by
    rw [← hwalk]
    exact hsecondAt
  refine ⟨firstDart, secondDart, hfirstAt, hsecondAt, ?_, ?_⟩
  · have h := hfirstMap.symm.trans hfirstWalk
    exact Option.some.inj h
  · have h := hsecondMap.symm.trans hsecondWalk
    exact Option.some.inj h

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

/-- Every cancellation pair recorded by the source-position trace is folded
into opposite orientations by the accumulated graph map. -/
theorem sourcePositionTraceAux_pairs_folded {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin source.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = origins.map sourceDarts) :
    ∀ p ∈ (sourcePositionTraceAux source steps origins hlen).pairs,
      (LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts p.2) =
        (LabelledWalk.foldSequence steps walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts p.1)) := by
  induction steps generalizing G u v origins sourceDarts with
  | refl word =>
      intro p hp
      simp only [sourcePositionTraceAux.eq_1, List.not_mem_nil] at hp
  | @cons raw mid reduced step rest ih =>
      cases step with
      | cancel pre post a =>
          have hraw : origins.length =
              (pre ++ [a] ++ [inverseLetter a] ++ post).length := hlen
          have hrawLen : origins.length = pre.length + 2 + post.length := by
            have hraw' : origins.length = pre.length + (post.length + 2) := by
              simpa [List.length_append] using hraw
            omega
          have hfirstBound : pre.length < origins.length := by omega
          have hsecondBound : pre.length + 1 < origins.length := by omega
          let firstPosition := origins.get ⟨pre.length, hfirstBound⟩
          let secondPosition := origins.get ⟨pre.length + 1, hsecondBound⟩
          let remaining := origins.take pre.length ++ origins.drop (pre.length + 2)
          have hremaining : remaining.length = (pre ++ post).length := by
            dsimp [remaining]
            have htake : pre.length ≤ origins.length := by omega
            have hdrop : pre.length + 2 ≤ origins.length := by omega
            have hdropLen : origins.length - (pre.length + 2) = post.length := by
              omega
            rw [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left htake]
            rw [hdropLen]
            simp [List.length_append]
          let first := LabelledWalk.foldCancellation
            (FreeCancellationStep.cancel pre post a) walk
          let later := LabelledWalk.foldSequence rest first.walk
          obtain ⟨firstDart, secondDart, before, after, hdecomp, hresult⟩ :=
            foldCancellation_darts a walk
          have hbefore : before.darts = walk.darts.take pre.length := by
            rw [hdecomp]
            simp [LabelledWalk.length_darts]
          have hafter : after.darts = walk.darts.drop (pre.length + 2) := by
            have hprefixLen : (before.darts ++ [firstDart, secondDart]).length =
                pre.length + 2 := by simp [LabelledWalk.length_darts]
            have hdropEq :
                ((before.darts ++ [firstDart, secondDart]) ++ after.darts).drop
                    (pre.length + 2) = after.darts := by
              rw [← hprefixLen, List.drop_append_of_le_length (Nat.le_refl _)]
              simp
            rw [hdecomp]
            exact hdropEq.symm
          have hbeforeSource : before.darts =
              (origins.take pre.length).map sourceDarts := by
            calc
              before.darts = walk.darts.take pre.length := hbefore
              _ = (origins.map sourceDarts).take pre.length := by rw [hwalk]
              _ = (origins.take pre.length).map sourceDarts := by simp
          have hafterSource : after.darts =
              (origins.drop (pre.length + 2)).map sourceDarts := by
            calc
              after.darts = walk.darts.drop (pre.length + 2) := hafter
              _ = (origins.map sourceDarts).drop (pre.length + 2) := by rw [hwalk]
              _ = (origins.drop (pre.length + 2)).map sourceDarts := by simp
          let sourceDarts' : Fin source.length → first.graph.toDartGraph.Dart :=
            fun i => first.hom.mapDart (sourceDarts i)
          have hwalk' : first.walk.darts = remaining.map sourceDarts' := by
            rw [hresult, hbeforeSource, hafterSource]
            simp only [List.map_map, Function.comp_def, sourceDarts', remaining,
              List.map_append]
            rfl
          obtain ⟨traceFirstDart, traceSecondDart, traceFirstAt, traceSecondAt,
              traceFirstSource, traceSecondSource⟩ :=
            sourcePositionTraceAux_head_sourceDarts source a origins hraw
              walk sourceDarts hwalk
          obtain ⟨pairFirstDart, pairSecondDart, pairFirstAt, pairSecondAt,
              hheadFolded⟩ := foldSequence_headSourcePair pre post a rest walk
          have htraceFirstEq : traceFirstDart = pairFirstDart :=
            Option.some.inj (traceFirstAt.symm.trans pairFirstAt)
          have htraceSecondEq : traceSecondDart = pairSecondDart :=
            Option.some.inj (traceSecondAt.symm.trans pairSecondAt)
          have hfirstSource : sourceDarts firstPosition = pairFirstDart := by
            have hsource : sourceDarts firstPosition = traceFirstDart := by
              change sourceDarts
                (origins.get ⟨pre.length, hfirstBound⟩) = traceFirstDart
              exact traceFirstSource
            exact hsource.trans htraceFirstEq
          have hsecondSource : sourceDarts secondPosition = pairSecondDart := by
            have hsource : sourceDarts secondPosition = traceSecondDart := by
              change sourceDarts
                (origins.get ⟨pre.length + 1, hsecondBound⟩) = traceSecondDart
              exact traceSecondSource
            exact hsource.trans htraceSecondEq
          have hlater := ih remaining hremaining first.walk sourceDarts' hwalk'
          intro p hp
          have hp' : p ∈ (firstPosition, secondPosition) ::
              (sourcePositionTraceAux source rest remaining hremaining).pairs := by
            simpa only [sourcePositionTraceAux.eq_2,
              FreeCancellationStep.prefixLength] using hp
          rcases List.mem_cons.mp hp' with hhead | hlaterPair
          · subst p
            simpa [hfirstSource, hsecondSource] using hheadFolded
          · have hfolded := hlater p hlaterPair
            change later.hom.mapDart (first.hom.mapDart (sourceDarts p.2)) =
              later.graph.toDartGraph.reverse
                (later.hom.mapDart (first.hom.mapDart (sourceDarts p.1)))
            exact hfolded

/-- A map that identifies every source pair recorded by a cancellation trace
factors through the sequential fold quotient. The proof carries the source
positions of the surviving walk through each deletion. -/
theorem foldSequence_factor_through_map {α : Type*}
    (source : Word α) {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    {G H : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin source.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = origins.map sourceDarts)
    (f : LabelledGraphHom G H)
    (hfolded : ∀ p ∈ (sourcePositionTraceAux source steps origins hlen).pairs,
      f.mapDart (sourceDarts p.2) =
        H.toDartGraph.reverse (f.mapDart (sourceDarts p.1))) :
    ∃ g : LabelledGraphHom (LabelledWalk.foldSequence steps walk).graph H,
      ∀ i, g.mapDart
          ((LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts i)) =
        f.mapDart (sourceDarts i) := by
  induction steps generalizing G u v origins sourceDarts f with
  | refl raw =>
      refine ⟨f, ?_⟩
      intro i
      rfl
  | @cons raw mid reduced step rest ih =>
      cases step with
      | cancel pre post a =>
          have hraw : origins.length =
              (pre ++ [a] ++ [inverseLetter a] ++ post).length := hlen
          have hrawLen : origins.length = pre.length + 2 + post.length := by
            have hraw' : origins.length = pre.length + (post.length + 2) := by
              simpa [List.length_append] using hraw
            omega
          have hfirstBound : pre.length < origins.length := by omega
          have hsecondBound : pre.length + 1 < origins.length := by omega
          let firstPosition := origins.get ⟨pre.length, hfirstBound⟩
          let secondPosition := origins.get ⟨pre.length + 1, hsecondBound⟩
          let remaining := origins.take pre.length ++ origins.drop (pre.length + 2)
          have hremaining : remaining.length = (pre ++ post).length := by
            dsimp [remaining]
            have htake : pre.length ≤ origins.length := by omega
            have hdrop : pre.length + 2 ≤ origins.length := by omega
            have hdropLen : origins.length - (pre.length + 2) = post.length := by
              omega
            rw [List.length_append, List.length_take, List.length_drop,
              Nat.min_eq_left htake]
            rw [hdropLen]
            simp [List.length_append]
          let first := LabelledWalk.foldCancellation
            (FreeCancellationStep.cancel pre post a) walk
          let firstData := LabelledWalk.foldCancellationWithPair
            (FreeCancellationStep.cancel pre post a) walk
          have hfirstAt : walk.darts[pre.length]? = some firstData.pair.first := by
            have hfirstOccurrence : walk.occurrenceDarts[pre.length]? =
                some firstData.pair.first := by
              simpa [FreeCancellationStep.prefixLength] using firstData.first_at
            rw [darts_eq_occurrenceDarts]
            exact hfirstOccurrence
          have hsecondAt : walk.darts[pre.length + 1]? = some firstData.pair.second := by
            have hsecondOccurrence : walk.occurrenceDarts[pre.length + 1]? =
                some firstData.pair.second := by
              simpa [FreeCancellationStep.prefixLength] using firstData.second_at
            rw [darts_eq_occurrenceDarts]
            exact hsecondOccurrence
          have hfirstPosition : origins[pre.length]? = some firstPosition := by
            simp [firstPosition]
          have hsecondPosition : origins[pre.length + 1]? = some secondPosition := by
            simp [secondPosition]
          have hfirstMap : (origins.map sourceDarts)[pre.length]? =
              some (sourceDarts firstPosition) := by
            rw [List.getElem?_map, hfirstPosition]
            simp
          have hsecondMap : (origins.map sourceDarts)[pre.length + 1]? =
              some (sourceDarts secondPosition) := by
            rw [List.getElem?_map, hsecondPosition]
            simp
          have hfirstWalk : (origins.map sourceDarts)[pre.length]? =
              some firstData.pair.first := by
            rw [← hwalk]
            exact hfirstAt
          have hsecondWalk : (origins.map sourceDarts)[pre.length + 1]? =
              some firstData.pair.second := by
            rw [← hwalk]
            exact hsecondAt
          have hfirstSource : sourceDarts firstPosition = firstData.pair.first :=
            Option.some.inj (hfirstMap.symm.trans hfirstWalk)
          have hsecondSource : sourceDarts secondPosition = firstData.pair.second :=
            Option.some.inj (hsecondMap.symm.trans hsecondWalk)
          have hhead : (firstPosition, secondPosition) ∈
              (sourcePositionTraceAux source
                (FreeCancellationSequence.cons
                  (FreeCancellationStep.cancel pre post a) rest) origins hlen).pairs := by
            simp only [sourcePositionTraceAux.eq_2,
              FreeCancellationStep.prefixLength]
            exact List.mem_cons_self
          have hcurrentFolded : f.mapDart firstData.pair.second =
              H.toDartGraph.reverse (f.mapDart firstData.pair.first) := by
            have h := hfolded (firstPosition, secondPosition) hhead
            calc
              f.mapDart firstData.pair.second = f.mapDart (sourceDarts secondPosition) :=
                congrArg f.mapDart hsecondSource.symm
              _ = H.toDartGraph.reverse (f.mapDart (sourceDarts firstPosition)) := h
              _ = H.toDartGraph.reverse (f.mapDart firstData.pair.first) :=
                congrArg H.toDartGraph.reverse (congrArg f.mapDart hfirstSource)
          let nextMap := LabelledGraphHom.descendFold
            firstData.pair.first firstData.pair.second
            firstData.pair.inverse_labels f hcurrentFolded
          have hnextMap : ∀ d : G.toDartGraph.Dart,
              nextMap.mapDart (first.hom.mapDart d) = f.mapDart d := by
            intro d
            exact LabelledGraphHom.descendFold_mapDart_fold
              firstData.pair.first firstData.pair.second
              firstData.pair.inverse_labels f hcurrentFolded d
          have ⟨firstDart, secondDart, before, after, hdecomp, hresult⟩ :=
            foldCancellation_darts a walk
          have hbefore : before.darts = walk.darts.take pre.length := by
            rw [hdecomp]
            simp [LabelledWalk.length_darts]
          have hafter : after.darts = walk.darts.drop (pre.length + 2) := by
            have hprefixLen : (before.darts ++ [firstDart, secondDart]).length =
                pre.length + 2 := by simp [LabelledWalk.length_darts]
            have hdropEq :
                ((before.darts ++ [firstDart, secondDart]) ++ after.darts).drop
                    (pre.length + 2) = after.darts := by
              rw [← hprefixLen, List.drop_append_of_le_length (Nat.le_refl _)]
              simp
            rw [hdecomp]
            exact hdropEq.symm
          have hbeforeSource : before.darts =
              (origins.take pre.length).map sourceDarts := by
            calc
              before.darts = walk.darts.take pre.length := hbefore
              _ = (origins.map sourceDarts).take pre.length := by rw [hwalk]
              _ = (origins.take pre.length).map sourceDarts := by simp
          have hafterSource : after.darts =
              (origins.drop (pre.length + 2)).map sourceDarts := by
            calc
              after.darts = walk.darts.drop (pre.length + 2) := hafter
              _ = (origins.map sourceDarts).drop (pre.length + 2) := by rw [hwalk]
              _ = (origins.drop (pre.length + 2)).map sourceDarts := by simp
          let sourceDarts' : Fin source.length → first.graph.toDartGraph.Dart :=
            fun i => first.hom.mapDart (sourceDarts i)
          have hwalk' : first.walk.darts = remaining.map sourceDarts' := by
            rw [hresult, hbeforeSource, hafterSource]
            simp only [List.map_map, Function.comp_def, sourceDarts', remaining,
              List.map_append]
            rfl
          have hnextFolded : ∀ p ∈ (sourcePositionTraceAux source rest
              remaining hremaining).pairs,
              nextMap.mapDart (sourceDarts' p.2) =
                H.toDartGraph.reverse (nextMap.mapDart (sourceDarts' p.1)) := by
            intro p hp
            have hpFull : p ∈
                (sourcePositionTraceAux source
                  (FreeCancellationSequence.cons
                    (FreeCancellationStep.cancel pre post a) rest) origins hlen).pairs := by
              simpa only [sourcePositionTraceAux.eq_2,
                FreeCancellationStep.prefixLength] using
                (List.mem_cons_of_mem (firstPosition, secondPosition) hp)
            have h := hfolded p hpFull
            calc
              nextMap.mapDart (sourceDarts' p.2) = f.mapDart (sourceDarts p.2) :=
                hnextMap (sourceDarts p.2)
              _ = H.toDartGraph.reverse (f.mapDart (sourceDarts p.1)) := h
              _ = H.toDartGraph.reverse (nextMap.mapDart (sourceDarts' p.1)) := by
                rw [hnextMap]
          obtain ⟨laterMap, hlaterMap⟩ :=
            ih remaining hremaining first.walk sourceDarts' hwalk' nextMap hnextFolded
          refine ⟨laterMap, ?_⟩
          intro i
          change laterMap.mapDart
              ((LabelledWalk.foldSequence rest first.walk).hom.mapDart
                (first.hom.mapDart (sourceDarts i))) = f.mapDart (sourceDarts i)
          calc
            _ = nextMap.mapDart (sourceDarts' i) := hlaterMap i
            _ = f.mapDart (sourceDarts i) := hnextMap (sourceDarts i)

/-- The initialized cancellation trace's input darts are paired as opposite
orientations in the final sequential quotient. -/
theorem sourcePositionTrace_pairs_folded {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin raw.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = (List.finRange raw.length).map sourceDarts) :
    ∀ p ∈ (sourcePositionTrace steps).pairs,
      (LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts p.2) =
        (LabelledWalk.foldSequence steps walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts p.1)) := by
  simpa only [sourcePositionTrace] using
    (sourcePositionTraceAux_pairs_folded raw steps (List.finRange raw.length) (by simp)
      walk sourceDarts hwalk)

/-- Source darts at each recorded cancellation pair have inverse labels. -/
theorem sourcePositionTrace_pairs_inverseLabels {α : Type*}
    {G : LabelledDartGraph α} {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin raw.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = (List.finRange raw.length).map sourceDarts) :
    ∀ p ∈ (sourcePositionTrace steps).pairs,
      G.label (sourceDarts p.1) = inverseLetter (G.label (sourceDarts p.2)) := by
  intro p hp
  let final := LabelledWalk.foldSequence steps walk
  have hfold := sourcePositionTrace_pairs_folded steps walk sourceDarts hwalk p hp
  have hlabel : final.graph.label (final.hom.mapDart (sourceDarts p.2)) =
      inverseLetter (final.graph.label (final.hom.mapDart (sourceDarts p.1))) := by
    calc
      final.graph.label (final.hom.mapDart (sourceDarts p.2)) =
          final.graph.label (final.graph.toDartGraph.reverse
            (final.hom.mapDart (sourceDarts p.1))) :=
        congrArg final.graph.label hfold
      _ = inverseLetter (final.graph.label (final.hom.mapDart (sourceDarts p.1))) :=
        final.graph.label_reverse _
  calc
    G.label (sourceDarts p.1) =
        final.graph.label (final.hom.mapDart (sourceDarts p.1)) :=
      (final.hom.map_label _).symm
    _ = inverseLetter (inverseLetter
          (final.graph.label (final.hom.mapDart (sourceDarts p.1)))) := by
      exact (LabelledDartGraph.inverseLetter_inverse _).symm
    _ = inverseLetter (final.graph.label (final.hom.mapDart (sourceDarts p.2))) := by
      rw [hlabel]
    _ = inverseLetter (G.label (sourceDarts p.2)) := by rw [final.hom.map_label]

/-- Turn the trace's source-position pairing into the finite list of labeled
dart pairs consumed by the direct pair-fold quotient. -/
def CancellationOccurrencePositions.toLabelledDartPairs {α : Type*}
    {source : Word α} {G : LabelledDartGraph α}
    (trace : CancellationOccurrencePositions source)
    (sourceDarts : Fin source.length → G.toDartGraph.Dart)
    (hlabels : ∀ p ∈ trace.pairs,
      G.label (sourceDarts p.1) = inverseLetter (G.label (sourceDarts p.2))) :
    List (LabelledDartPair G) :=
  trace.pairs.attach.map fun p =>
    ⟨sourceDarts p.1.1, sourceDarts p.1.2, hlabels p.1 p.2⟩

/-- Any pair-fold quotient whose requested pairs are all identified by a
sequential cancellation replay maps into that replay's final quotient. -/
noncomputable def pairFoldToReplay {α : Type*} {G : LabelledDartGraph α}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    (pairs : List (LabelledDartPair G))
    (hfolded : ∀ pair ∈ pairs,
      (LabelledWalk.foldSequence steps walk).hom.mapDart pair.second =
        (LabelledWalk.foldSequence steps walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldSequence steps walk).hom.mapDart pair.first)) :
    LabelledGraphHom (LabelledDartPairFoldResult.foldAll G pairs).graph
      (LabelledWalk.foldSequence steps walk).graph :=
  LabelledDartPairFoldResult.descendAll
    (LabelledWalk.foldSequence steps walk).hom pairs hfolded

/-- Every source-position dart pair from the trace is folded in the final
sequential cancellation quotient. -/
theorem sourcePositionTrace_dartPairs_folded {α : Type*}
    {G : LabelledDartGraph α} {raw reduced : Word α}
    (steps : FreeCancellationSequence raw reduced)
    {u v : G.toDartGraph.Vertex} (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin raw.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = (List.finRange raw.length).map sourceDarts) :
    ∀ pair ∈ (sourcePositionTrace steps).toLabelledDartPairs sourceDarts
      (sourcePositionTrace_pairs_inverseLabels steps walk sourceDarts hwalk),
      (LabelledWalk.foldSequence steps walk).hom.mapDart pair.second =
        (LabelledWalk.foldSequence steps walk).graph.toDartGraph.reverse
          ((LabelledWalk.foldSequence steps walk).hom.mapDart pair.first) := by
  intro pair hp
  rcases List.mem_map.mp hp with ⟨sourcePair, hsourcePair, rfl⟩
  exact sourcePositionTrace_pairs_folded steps walk sourceDarts hwalk
    sourcePair.1 sourcePair.2

/-- The sequential cancellation quotient maps back to the quotient obtained by
folding all recorded source-position pairs at once. On every boundary dart,
the two quotient maps agree after precomposition with the original boundary
map. -/
theorem foldSequence_factors_through_tracePairFold {α : Type*}
    {G : LabelledDartGraph α} {u v : G.toDartGraph.Vertex}
    {raw reduced : Word α} (steps : FreeCancellationSequence raw reduced)
    (walk : LabelledWalk G u v raw)
    (sourceDarts : Fin raw.length → G.toDartGraph.Dart)
    (hwalk : walk.darts = (List.finRange raw.length).map sourceDarts) :
    ∃ g : LabelledGraphHom (LabelledWalk.foldSequence steps walk).graph
        (LabelledDartPairFoldResult.foldAll G
          ((sourcePositionTrace steps).toLabelledDartPairs sourceDarts
            (sourcePositionTrace_pairs_inverseLabels steps walk sourceDarts hwalk))).graph,
      ∀ i, g.mapDart
          ((LabelledWalk.foldSequence steps walk).hom.mapDart (sourceDarts i)) =
        (LabelledDartPairFoldResult.foldAll G
          ((sourcePositionTrace steps).toLabelledDartPairs sourceDarts
            (sourcePositionTrace_pairs_inverseLabels steps walk sourceDarts hwalk))).hom.mapDart
          (sourceDarts i) := by
  let trace := sourcePositionTrace steps
  let traceLabels := sourcePositionTrace_pairs_inverseLabels steps walk sourceDarts hwalk
  let tracePairs := trace.toLabelledDartPairs sourceDarts traceLabels
  let target := WalkFoldResult.foldPairs tracePairs walk
  have hfolded : ∀ p ∈ trace.pairs,
      target.hom.mapDart (sourceDarts p.2) =
        target.graph.toDartGraph.reverse (target.hom.mapDart (sourceDarts p.1)) := by
    intro p hp
    let pair : LabelledDartPair G :=
      ⟨sourceDarts p.1, sourceDarts p.2, traceLabels p hp⟩
    have hpair : pair ∈ tracePairs := by
      dsimp [tracePairs, CancellationOccurrencePositions.toLabelledDartPairs]
      apply List.mem_map.mpr
      refine ⟨⟨p, hp⟩, List.mem_attach _ ⟨p, hp⟩, ?_⟩
      rfl
    simpa [target, pair] using
      WalkFoldResult.foldPairs_pair_reverse tracePairs walk pair hpair
  obtain ⟨g, hg⟩ := foldSequence_factor_through_map raw steps
    (List.finRange raw.length) (by simp) walk sourceDarts hwalk target.hom hfolded
  refine ⟨g, ?_⟩
  intro i
  simpa [target, trace, tracePairs, WalkFoldResult.foldPairs] using hg i

end LabelledWalk

namespace FreeReductionShape

/-- Cancellation pairs listed in the order that the executable sequence
performs them. For a bracket, the inner word is reduced first, then the
bracket's outer pair, and then the suffix. -/
def replayCancellationPairs {α : Type*} {raw reduced : Word α} :
    FreeReductionShape raw reduced → List (Nat × Nat)
  | .empty => []
  | .letter _ => []
  | .append left right =>
      left.replayCancellationPairs ++
        shiftCancellationPairs left.inputWord.length
          right.replayCancellationPairs
  | .bracket _ inner suffix =>
      shiftCancellationPairs 1 inner.replayCancellationPairs ++
        [(0, inner.inputWord.length + 1)] ++
        shiftCancellationPairs (inner.inputWord.length + 2)
          suffix.replayCancellationPairs

/-- The structural, root-first pairing and the chronological replay pairing
have the same pairs; only their list order differs. -/
theorem cancellationPairs_perm_replayCancellationPairs
    {α : Type*} {raw reduced : Word α}
    (shape : FreeReductionShape raw reduced) :
    List.Perm shape.cancellationPairs shape.replayCancellationPairs := by
  induction shape with
  | empty => rfl
  | letter _ => rfl
  | @append u u' v v' left right ihLeft ihRight =>
      apply List.Perm.append ihLeft
      simpa [shiftCancellationPairs] using
        ihRight.map fun p =>
          (left.inputWord.length + p.1, left.inputWord.length + p.2)
  | @bracket a inner suffix result hinner hsuffix ihInner ihSuffix =>
      simp only [cancellationPairs, replayCancellationPairs]
      have hInner := ihInner.map fun p => (1 + p.1, 1 + p.2)
      have hSuffix := ihSuffix.map fun p =>
        (hinner.inputWord.length + 2 + p.1,
          hinner.inputWord.length + 2 + p.2)
      have hinnerShift :
          List.Perm (shiftCancellationPairs 1 hinner.cancellationPairs)
            (shiftCancellationPairs 1 hinner.replayCancellationPairs) := by
        simpa [shiftCancellationPairs] using hInner
      have hsuffixShift :
          List.Perm (shiftCancellationPairs (hinner.inputWord.length + 2)
              hsuffix.cancellationPairs)
            (shiftCancellationPairs (hinner.inputWord.length + 2)
              hsuffix.replayCancellationPairs) := by
        simpa [shiftCancellationPairs] using hSuffix
      have htail := List.Perm.append hinnerShift hsuffixShift
      have hroot :
          List.Perm ((0, hinner.inputWord.length + 1) ::
              (shiftCancellationPairs 1 hinner.replayCancellationPairs ++
                shiftCancellationPairs (hinner.inputWord.length + 2)
                  hsuffix.replayCancellationPairs))
            (shiftCancellationPairs 1 hinner.replayCancellationPairs ++
              [(0, hinner.inputWord.length + 1)] ++
                shiftCancellationPairs (hinner.inputWord.length + 2)
                  hsuffix.replayCancellationPairs) := by
        have hcomm : List.Perm
            ([(0, hinner.inputWord.length + 1)] ++
                shiftCancellationPairs 1 hinner.replayCancellationPairs)
            (shiftCancellationPairs 1 hinner.replayCancellationPairs ++
                [(0, hinner.inputWord.length + 1)]) := by
          exact List.perm_append_comm
        simpa [List.append_assoc] using
          (List.Perm.append hcomm (List.Perm.refl
            (shiftCancellationPairs (hinner.inputWord.length + 2)
              hsuffix.replayCancellationPairs)))
      exact htail.cons (0, hinner.inputWord.length + 1) |>.trans hroot

/-- Flattening pair endpoints preserves a permutation of the pair list. -/
theorem pairEndpoints_perm {left right : List (Nat × Nat)}
    (h : List.Perm left right) :
    List.Perm (pairEndpoints left) (pairEndpoints right) := by
  unfold pairEndpoints
  exact h.flatMap fun p hp => List.Perm.refl [p.1, p.2]

/-- The same nested pairing as an indexed trace whose pairs are listed in
chronological replay order. All source-position and survivor facts are
inherited from the original tree pairing. -/
def toReplayIndexedBoundaryTrace {α : Type*} {raw reduced : Word α}
    (shape : FreeReductionShape raw reduced) :
    IndexedBoundaryTrace raw reduced where
  cancellationPairs := shape.replayCancellationPairs
  survivorOccurrences := shape.survivorOccurrences
  pairs_noncrossing := by
    intro p hp q hq
    exact shape.cancellationPairs_noncrossing p
      (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hp)
      q (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hq)
  pairs_are_inverseLetters := by
    intro p hp
    exact shape.cancellationPairs_are_inverseLetterOccurrences p
      (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hp)
  pairs_inBounds := by
    intro p hp
    exact shape.cancellationPairs_inBounds p
      (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hp)
  endpoints_nodup := by
    have h := pairEndpoints_perm
      shape.cancellationPairs_perm_replayCancellationPairs
    exact h.nodup_iff.mp shape.cancellationEndpoints_nodup
  endpoints_inBounds := by
    intro i hi
    have h := pairEndpoints_perm
      shape.cancellationPairs_perm_replayCancellationPairs
    exact shape.cancellationEndpoints_inBounds i (h.mem_iff.mpr hi)
  survivors_labels := shape.survivorOccurrences_labels
  survivors_length := shape.survivorOccurrences_length
  survivorPositions_nodup := shape.survivorOccurrencePositions_nodup
  survivorPositions_strict := shape.survivorOccurrencePositions_strict
  survivors_are_sourceLetters := shape.survivorOccurrences_are_sourceLetters
  survivors_inBounds := shape.survivorOccurrences_inBounds
  endpoints_disjoint_survivors := by
    intro i hi j hj
    rcases List.mem_flatMap.mp hi with ⟨p, hp, hip⟩
    rcases List.mem_map.mp hj with ⟨o, ho, hoj⟩
    have hdis := shape.survivorOccurrences_disjointFromCancellationPairs o ho p
      (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hp)
    simp at hip
    rcases hip with hip | hip
    · intro hij
      apply hdis.1
      calc
        o.1 = j := hoj
        _ = i := hij.symm
        _ = p.1 := hip
    · intro hij
      apply hdis.2
      calc
        o.1 = j := hoj
        _ = i := hij.symm
        _ = p.2 := hip
  no_survivor_inside_pair := by
    intro p hp o ho hleft hright
    exact shape.cancellationPairs_contain_no_survivor p
      (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hp)
      o ho hleft hright
  endpoint_survivor_count := by
    have h := pairEndpoints_perm
      shape.cancellationPairs_perm_replayCancellationPairs
    calc
      (pairEndpoints shape.replayCancellationPairs).length +
          (shape.survivorOccurrences.map Prod.fst).length =
        (pairEndpoints shape.cancellationPairs).length +
          (shape.survivorOccurrences.map Prod.fst).length := by
            rw [h.length_eq]
      _ = raw.length := by
        simpa [FreeReductionShape.inputWord] using
          shape.survivorAndCancellationEndpointCount
  sourcePositions_partition := by
    intro i hi
    rcases shape.sourcePositions_partition i hi with hend | hsurvivor
    · left
      have h := pairEndpoints_perm
        shape.cancellationPairs_perm_replayCancellationPairs
      exact h.mem_iff.mp hend
    · exact Or.inr hsurvivor

end FreeReductionShape

namespace FreeReductionShape

/-- Relabel a finite list of natural-number source positions by their
occurrences in an arbitrary ambient source list. -/
def mapSourcePositions {α : Type*} {raw : Word α} {source : Word α}
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    (positions : List Nat) (hbound : ∀ i ∈ positions, i < raw.length) :
    List (Fin source.length) :=
    positions.attach.map fun i =>
      origins.get (Fin.cast hlen.symm ⟨i.1, hbound i.1 i.2⟩)

theorem mapSourcePositions_congr_origins {α : Type*} {raw : Word α}
    {source : Word α} {origins origins' : List (Fin source.length)}
    (horigins : origins = origins')
    (hlen : origins.length = raw.length)
    (hlen' : origins'.length = raw.length)
    (positions : List Nat) (hbound : ∀ i ∈ positions, i < raw.length) :
    mapSourcePositions origins hlen positions hbound =
      mapSourcePositions origins' hlen' positions hbound := by
  cases horigins
  rfl

/-- Relabeling an appended position list splits into the two component traces. -/
theorem mapSourcePositions_append {α : Type*} {raw : Word α} {source : Word α}
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    (left right : List Nat)
    (hbound : ∀ i ∈ left ++ right, i < raw.length)
    (hleft : ∀ i ∈ left, i < raw.length)
    (hright : ∀ i ∈ right, i < raw.length) :
    mapSourcePositions origins hlen (left ++ right) hbound =
      mapSourcePositions origins hlen left hleft ++
        mapSourcePositions origins hlen right hright := by
  simp only [mapSourcePositions, List.attach_append, List.map_append,
    List.map_map]
  congr 1

/-- Shifting positions past a fixed prefix is the same as dropping that
prefix from the ambient occurrence list. -/
theorem mapSourcePositions_shiftSource {α : Type*} {whole raw : Word α}
    {source : Word α} (prefixOrigins origins : List (Fin source.length))
    (offset : Nat) (hprefix : prefixOrigins.length = offset)
    (hlen : origins.length = raw.length)
    (hwhole : whole.length = offset + raw.length)
    (htotal : (prefixOrigins ++ origins).length = whole.length)
    (positions : List Nat) (hpositions : ∀ i ∈ positions, i < raw.length) :
    mapSourcePositions (prefixOrigins ++ origins) htotal
        (positions.map (offset + ·)) (by
          intro i hi
          rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
          simp only [List.length_append] at htotal
          rw [hwhole] at htotal
          have := hpositions j hj
          omega) =
      mapSourcePositions origins hlen positions hpositions := by
  simp only [mapSourcePositions, List.attach_map, List.map_map]
  apply List.map_congr_left
  intro i hi
  apply Fin.ext
  simp only [Fin.val_cast, List.get_eq_getElem, Function.comp_apply,
    ]
  rw [List.getElem_append_right (by rw [hprefix]; omega)]
  simp [hprefix]

/-- Positions bounded by a prefix select the same occurrences before and
after a suffix is appended. -/
theorem mapSourcePositions_prefixSource {α : Type*} {whole left : Word α}
    {source : Word α} (prefixOrigins suffixOrigins : List (Fin source.length))
    (hprefix : prefixOrigins.length = left.length)
    (htotal : (prefixOrigins ++ suffixOrigins).length = whole.length)
    (positions : List Nat) (hpositions : ∀ i ∈ positions, i < left.length) :
    mapSourcePositions (prefixOrigins ++ suffixOrigins) htotal positions
        (by
          intro i hi
          have := hpositions i hi
          simp only [List.length_append] at htotal
          omega) =
      mapSourcePositions prefixOrigins hprefix positions hpositions := by
  simp only [mapSourcePositions]
  apply List.map_congr_left
  intro i hi
  apply Fin.ext
  simp only [Fin.val_cast, List.get_eq_getElem]
  rw [List.getElem_append_left (by rw [hprefix]; exact hpositions i.1 i.2)]

/-- Relabel both endpoints of each bounded source pair by its ambient source
occurrences. -/
def mapSourcePairs {α : Type*} {raw : Word α} {source : Word α}
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    (pairs : List (Nat × Nat))
    (hbound : ∀ p ∈ pairs, p.1 < raw.length ∧ p.2 < raw.length) :
    List (Fin source.length × Fin source.length) :=
  pairs.attach.map fun p =>
    (origins.get (Fin.cast hlen.symm ⟨p.1.1,
      (hbound p.1 p.2).1⟩),
     origins.get (Fin.cast hlen.symm ⟨p.1.2,
      (hbound p.1 p.2).2⟩))

theorem mapSourcePairs_congr_origins {α : Type*} {raw : Word α}
    {source : Word α} {origins origins' : List (Fin source.length)}
    (horigins : origins = origins')
    (hlen : origins.length = raw.length)
    (hlen' : origins'.length = raw.length)
    (pairs : List (Nat × Nat))
    (hbound : ∀ p ∈ pairs, p.1 < raw.length ∧ p.2 < raw.length) :
    mapSourcePairs origins hlen pairs hbound =
      mapSourcePairs origins' hlen' pairs hbound := by
  cases horigins
  rfl

/-- Relabeling pair endpoints after an index shift agrees with dropping the
fixed prefix from the source occurrence list. -/
theorem mapSourcePairs_shiftSource {α : Type*} {whole raw : Word α}
    {source : Word α} (prefixOrigins origins : List (Fin source.length))
    (offset : Nat) (hprefix : prefixOrigins.length = offset)
    (hlen : origins.length = raw.length)
    (hwhole : whole.length = offset + raw.length)
    (htotal : (prefixOrigins ++ origins).length = whole.length)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, p.1 < raw.length ∧ p.2 < raw.length) :
    mapSourcePairs (prefixOrigins ++ origins) htotal
        (shiftCancellationPairs offset pairs) (by
          intro p hp
          rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
          simp only [List.length_append] at htotal
          rw [hwhole] at htotal
          have hq' := hpairs q hq
          constructor <;> omega) =
      mapSourcePairs origins hlen pairs hpairs := by
  simp only [mapSourcePairs, shiftCancellationPairs, List.attach_map,
    List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · apply Fin.ext
    simp only [Fin.val_cast, List.get_eq_getElem, Function.comp_apply]
    rw [List.getElem_append_right (by rw [hprefix]; omega)]
    simp [hprefix]
  · apply Fin.ext
    simp only [Fin.val_cast, List.get_eq_getElem, Function.comp_apply]
    rw [List.getElem_append_right (by rw [hprefix]; omega)]
    simp [hprefix]

/-- Pair endpoints whose positions stay in a prefix are unaffected by a
suffix appended to their source list. -/
theorem mapSourcePairs_prefixSource {α : Type*} {whole left : Word α}
    {source : Word α} (prefixOrigins suffixOrigins : List (Fin source.length))
    (hprefix : prefixOrigins.length = left.length)
    (htotal : (prefixOrigins ++ suffixOrigins).length = whole.length)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, p.1 < left.length ∧ p.2 < left.length) :
    mapSourcePairs (prefixOrigins ++ suffixOrigins) htotal pairs
        (by
          intro p hp
          have := hpairs p hp
          simp only [List.length_append] at htotal
          omega) =
      mapSourcePairs prefixOrigins hprefix pairs hpairs := by
  simp only [mapSourcePairs]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · apply Fin.ext
    simp only [Fin.val_cast, List.get_eq_getElem]
    rw [List.getElem_append_left (by rw [hprefix]; exact (hpairs p.1 p.2).1)]
  · apply Fin.ext
    simp only [Fin.val_cast, List.get_eq_getElem]
    rw [List.getElem_append_left (by rw [hprefix]; exact (hpairs p.1 p.2).2)]

/-- Relabeling an appended pair list splits into the two component traces. -/
theorem mapSourcePairs_append {α : Type*} {raw : Word α} {source : Word α}
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length)
    (left right : List (Nat × Nat))
    (hbound : ∀ p ∈ left ++ right, p.1 < raw.length ∧ p.2 < raw.length)
    (hleft : ∀ p ∈ left, p.1 < raw.length ∧ p.2 < raw.length)
    (hright : ∀ p ∈ right, p.1 < raw.length ∧ p.2 < raw.length) :
    mapSourcePairs origins hlen (left ++ right) hbound =
      mapSourcePairs origins hlen left hleft ++
        mapSourcePairs origins hlen right hright := by
  simp only [mapSourcePairs, List.attach_append, List.map_append,
    List.map_map]
  congr 1

/-- The chronological pairing inherited from a reduction tree remains in the
input word's positional range. -/
theorem replayCancellationPairs_inBounds {α : Type*} {raw reduced : Word α}
    (shape : FreeReductionShape raw reduced) :
    ∀ p ∈ shape.replayCancellationPairs,
      p.1 < raw.length ∧ p.2 < raw.length := by
  intro p hp
  have h := shape.cancellationPairs_inBounds p
    (shape.cancellationPairs_perm_replayCancellationPairs.mem_iff.mpr hp)
  simp only [FreeReductionShape.inputWord] at h
  constructor <;> omega

/-- The replayed reduction tree's source-position trace, relabeled by a given
list of ambient source occurrences. -/
def replayMappedTrace {α : Type*} {raw reduced : Word α}
    (shape : FreeReductionShape raw reduced) {source : Word α}
    (origins : List (Fin source.length)) (hlen : origins.length = raw.length) :
    LabelledWalk.CancellationOccurrencePositions source where
  pairs := mapSourcePairs origins hlen shape.replayCancellationPairs
    (replayCancellationPairs_inBounds shape)
  survivors := mapSourcePositions origins hlen
    (shape.survivorOccurrences.map Prod.fst) (by
      intro i hi
      rcases List.mem_map.mp hi with ⟨o, ho, rfl⟩
      exact shape.survivorOccurrences_inBounds o ho)

/-- The replay trace of an append node is the concatenation of the child
traces, after splitting ambient source occurrences at the word boundary. -/
theorem append_to_cancellationSequence_trace
    {u u' v v' : Word α}
    (left : FreeReductionShape u u') (right : FreeReductionShape v v')
    {source : Word α}
    (origins : List (Fin source.length))
    (leftOrigins rightOrigins : List (Fin source.length))
    (horigins : origins = leftOrigins ++ rightOrigins)
    (hleftLen : leftOrigins.length = u.length)
    (hrightLen : rightOrigins.length = v.length)
    (hlen : origins.length = (u ++ v).length)
    (ihLeft : ∀ (lo : List (Fin source.length))
      (hlo : lo.length = u.length),
      LabelledWalk.sourcePositionTraceAux source left.to_cancellationSequence
        lo hlo = left.replayMappedTrace lo hlo)
    (ihRight : ∀ (ro : List (Fin source.length))
      (hro : ro.length = v.length),
      LabelledWalk.sourcePositionTraceAux source right.to_cancellationSequence
        ro hro = right.replayMappedTrace ro hro) :
    LabelledWalk.sourcePositionTraceAux source
      (FreeReductionShape.append left right).to_cancellationSequence origins hlen =
    (FreeReductionShape.append left right).replayMappedTrace origins hlen := by
  subst origins
  have hlenParts : (leftOrigins ++ rightOrigins).length = (u ++ v).length := hlen
  let leftSeq := left.to_cancellationSequence
  let rightSeq := right.to_cancellationSequence
  let leftTrace := LabelledWalk.sourcePositionTraceAux source leftSeq
    leftOrigins hleftLen
  let rightTrace := LabelledWalk.sourcePositionTraceAux source rightSeq
    rightOrigins hrightLen
  have hleftTrace := ihLeft leftOrigins hleftLen
  have hrightTrace := ihRight rightOrigins hrightLen
  have hleftSurvivorsLength :=
    LabelledWalk.sourcePositionTraceAux_survivors_length source leftSeq
      leftOrigins hleftLen
  have happendRight :=
    LabelledWalk.sourcePositionTraceAux_appendRight source leftSeq v
      leftOrigins rightOrigins hleftLen hrightLen
  have happendLeft :=
    LabelledWalk.sourcePositionTraceAux_appendLeft source rightSeq u'
      leftTrace.survivors rightOrigins hleftSurvivorsLength hrightLen
  have htrace :
      LabelledWalk.sourcePositionTraceAux source
        ((leftSeq.appendRight v).trans (rightSeq.appendLeft u'))
        (leftOrigins ++ rightOrigins) hlenParts =
        ⟨leftTrace.pairs ++ rightTrace.pairs,
          leftTrace.survivors ++ rightTrace.survivors⟩ := by
    rw [LabelledWalk.sourcePositionTraceAux_trans]
    simp only [happendRight]
    change
      (⟨leftTrace.pairs ++
          (LabelledWalk.sourcePositionTraceAux source (rightSeq.appendLeft u')
            (leftTrace.survivors ++ rightOrigins) _).pairs,
          (LabelledWalk.sourcePositionTraceAux source (rightSeq.appendLeft u')
            (leftTrace.survivors ++ rightOrigins) _).survivors⟩ :
        LabelledWalk.CancellationOccurrencePositions source) = _
    rw [happendLeft]
  have hseq :
      (FreeReductionShape.append left right).to_cancellationSequence =
        (leftSeq.appendRight v).trans (rightSeq.appendLeft u') := by
    simp [FreeReductionShape.to_cancellationSequence, leftSeq, rightSeq]
  have hleftPairs : ∀ p ∈ left.replayCancellationPairs,
      p.1 < u.length ∧ p.2 < u.length := by
    intro p hp
    have hb := left.replayCancellationPairs_inBounds p hp
    simpa [FreeReductionShape.inputWord] using hb
  have hrightPairs : ∀ p ∈ right.replayCancellationPairs,
      p.1 < v.length ∧ p.2 < v.length := by
    intro p hp
    have hb := right.replayCancellationPairs_inBounds p hp
    simpa [FreeReductionShape.inputWord] using hb
  have hleftPairsWhole : ∀ p ∈ left.replayCancellationPairs,
      p.1 < (u ++ v).length ∧ p.2 < (u ++ v).length := by
    intro p hp
    have hb := hleftPairs p hp
    simp only [List.length_append]
    omega
  have hrightPairsWhole : ∀ p ∈ shiftCancellationPairs u.length
      right.replayCancellationPairs,
      p.1 < (u ++ v).length ∧ p.2 < (u ++ v).length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hb := hrightPairs q hq
    simp only [List.length_append]
    constructor <;> omega
  have hwholePairs : ∀ p ∈ left.replayCancellationPairs ++
      shiftCancellationPairs u.length right.replayCancellationPairs,
      p.1 < (u ++ v).length ∧ p.2 < (u ++ v).length := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hleftPairsWhole p hp
    · exact hrightPairsWhole p hp
  have hleftSurvivors : ∀ i ∈ left.survivorOccurrences.map Prod.fst,
      i < u.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨o, ho, rfl⟩
    have hb := left.survivorOccurrences_inBounds o ho
    simpa [FreeReductionShape.inputWord] using hb
  have hrightSurvivors : ∀ i ∈ right.survivorOccurrences.map Prod.fst,
      i < v.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨o, ho, rfl⟩
    have hb := right.survivorOccurrences_inBounds o ho
    simpa [FreeReductionShape.inputWord] using hb
  have hleftSurvivorsWhole : ∀ i ∈ left.survivorOccurrences.map Prod.fst,
      i < (u ++ v).length := by
    intro i hi
    have hb := hleftSurvivors i hi
    simp only [List.length_append]
    omega
  have hrightSurvivorsWhole : ∀ i ∈ (right.survivorOccurrences.map Prod.fst).map
      (u.length + ·), i < (u ++ v).length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
    have hb := hrightSurvivors j hj
    simp only [List.length_append]
    omega
  have hsurvivorPositions :
      (FreeReductionShape.append left right).survivorOccurrences.map Prod.fst =
        left.survivorOccurrences.map Prod.fst ++
          (right.survivorOccurrences.map Prod.fst).map (u.length + ·) := by
    simp [FreeReductionShape.survivorOccurrences, FreeReductionShape.inputWord,
      shiftLetterOccurrences_positions]
  have hwholeSurvivors : ∀ i ∈
      (FreeReductionShape.append left right).survivorOccurrences.map Prod.fst,
      i < (u ++ v).length := by
    intro i hi
    rw [hsurvivorPositions] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hleftSurvivorsWhole i hi
    · exact hrightSurvivorsWhole i hi
  have hmappedPairs :
      FreeReductionShape.mapSourcePairs (leftOrigins ++ rightOrigins) hlenParts
        (left.replayCancellationPairs ++ shiftCancellationPairs u.length
          right.replayCancellationPairs) hwholePairs =
        FreeReductionShape.mapSourcePairs leftOrigins hleftLen
          left.replayCancellationPairs hleftPairs ++
        FreeReductionShape.mapSourcePairs rightOrigins hrightLen
          right.replayCancellationPairs hrightPairs := by
    calc
      _ = FreeReductionShape.mapSourcePairs (leftOrigins ++ rightOrigins) hlenParts
            left.replayCancellationPairs hleftPairsWhole ++
          FreeReductionShape.mapSourcePairs (leftOrigins ++ rightOrigins) hlenParts
            (shiftCancellationPairs u.length right.replayCancellationPairs)
            hrightPairsWhole := by
              exact FreeReductionShape.mapSourcePairs_append
                (leftOrigins ++ rightOrigins) hlenParts
                left.replayCancellationPairs
                (shiftCancellationPairs u.length right.replayCancellationPairs)
                hwholePairs hleftPairsWhole hrightPairsWhole
      _ = FreeReductionShape.mapSourcePairs leftOrigins hleftLen
            left.replayCancellationPairs hleftPairs ++
          FreeReductionShape.mapSourcePairs rightOrigins hrightLen
            right.replayCancellationPairs hrightPairs := by
              congr 1
              · exact FreeReductionShape.mapSourcePairs_prefixSource
                  leftOrigins rightOrigins hleftLen hlenParts
                  left.replayCancellationPairs hleftPairs
              · exact FreeReductionShape.mapSourcePairs_shiftSource
                  leftOrigins rightOrigins u.length hleftLen hrightLen
                  (by simp [List.length_append]) hlenParts
                  right.replayCancellationPairs hrightPairs
  have hwholeSurvivorsBound : ∀ i ∈ left.survivorOccurrences.map Prod.fst ++
      (right.survivorOccurrences.map Prod.fst).map (u.length + ·),
      i < (u ++ v).length := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hleftSurvivorsWhole i hi
    · exact hrightSurvivorsWhole i hi
  have hmappedSurvivorsDecomposed :
      FreeReductionShape.mapSourcePositions (leftOrigins ++ rightOrigins) hlenParts
        (left.survivorOccurrences.map Prod.fst ++
          (right.survivorOccurrences.map Prod.fst).map (u.length + ·))
        hwholeSurvivorsBound =
        FreeReductionShape.mapSourcePositions leftOrigins hleftLen
          (left.survivorOccurrences.map Prod.fst) hleftSurvivors ++
        FreeReductionShape.mapSourcePositions rightOrigins hrightLen
          (right.survivorOccurrences.map Prod.fst) hrightSurvivors := by
    calc
      _ = FreeReductionShape.mapSourcePositions (leftOrigins ++ rightOrigins)
            hlenParts (left.survivorOccurrences.map Prod.fst) hleftSurvivorsWhole ++
          FreeReductionShape.mapSourcePositions (leftOrigins ++ rightOrigins)
            hlenParts ((right.survivorOccurrences.map Prod.fst).map (u.length + ·))
            hrightSurvivorsWhole := by
              exact FreeReductionShape.mapSourcePositions_append
                (leftOrigins ++ rightOrigins) hlenParts
                (left.survivorOccurrences.map Prod.fst)
                ((right.survivorOccurrences.map Prod.fst).map (u.length + ·))
                hwholeSurvivorsBound hleftSurvivorsWhole hrightSurvivorsWhole
      _ = FreeReductionShape.mapSourcePositions leftOrigins hleftLen
            (left.survivorOccurrences.map Prod.fst) hleftSurvivors ++
          FreeReductionShape.mapSourcePositions rightOrigins hrightLen
            (right.survivorOccurrences.map Prod.fst) hrightSurvivors := by
              congr 1
              · exact FreeReductionShape.mapSourcePositions_prefixSource
                  leftOrigins rightOrigins hleftLen hlenParts
                  (left.survivorOccurrences.map Prod.fst) hleftSurvivors
              · exact FreeReductionShape.mapSourcePositions_shiftSource
                  leftOrigins rightOrigins u.length hleftLen hrightLen
                  (by simp [List.length_append]) hlenParts
                  (right.survivorOccurrences.map Prod.fst) hrightSurvivors
  have hmappedSurvivors :
      FreeReductionShape.mapSourcePositions (leftOrigins ++ rightOrigins) hlenParts
        ((FreeReductionShape.append left right).survivorOccurrences.map Prod.fst)
        hwholeSurvivors =
        FreeReductionShape.mapSourcePositions leftOrigins hleftLen
          (left.survivorOccurrences.map Prod.fst) hleftSurvivors ++
        FreeReductionShape.mapSourcePositions rightOrigins hrightLen
          (right.survivorOccurrences.map Prod.fst) hrightSurvivors := by
    simpa only [hsurvivorPositions] using hmappedSurvivorsDecomposed
  have hleftTracePairs : leftTrace.pairs =
      FreeReductionShape.mapSourcePairs leftOrigins hleftLen
        left.replayCancellationPairs hleftPairs := by
    simpa [leftTrace, FreeReductionShape.replayMappedTrace] using
      congrArg (fun t : LabelledWalk.CancellationOccurrencePositions source => t.pairs)
        hleftTrace
  have hrightTracePairs : rightTrace.pairs =
      FreeReductionShape.mapSourcePairs rightOrigins hrightLen
        right.replayCancellationPairs hrightPairs := by
    simpa [rightTrace, FreeReductionShape.replayMappedTrace] using
      congrArg (fun t : LabelledWalk.CancellationOccurrencePositions source => t.pairs)
        hrightTrace
  have hleftTraceSurvivors : leftTrace.survivors =
      FreeReductionShape.mapSourcePositions leftOrigins hleftLen
        (left.survivorOccurrences.map Prod.fst) hleftSurvivors := by
    simpa [leftTrace, FreeReductionShape.replayMappedTrace] using
      congrArg (fun t : LabelledWalk.CancellationOccurrencePositions source => t.survivors)
        hleftTrace
  have hrightTraceSurvivors : rightTrace.survivors =
      FreeReductionShape.mapSourcePositions rightOrigins hrightLen
        (right.survivorOccurrences.map Prod.fst) hrightSurvivors := by
    simpa [rightTrace, FreeReductionShape.replayMappedTrace] using
      congrArg (fun t : LabelledWalk.CancellationOccurrencePositions source => t.survivors)
        hrightTrace
  rw [hseq]
  rw [htrace]
  change
    (⟨leftTrace.pairs ++ rightTrace.pairs,
      leftTrace.survivors ++ rightTrace.survivors⟩ :
        LabelledWalk.CancellationOccurrencePositions source) =
      ⟨FreeReductionShape.mapSourcePairs (leftOrigins ++ rightOrigins) hlenParts
          (left.replayCancellationPairs ++ shiftCancellationPairs u.length
            right.replayCancellationPairs) hwholePairs,
        FreeReductionShape.mapSourcePositions (leftOrigins ++ rightOrigins) hlenParts
          ((FreeReductionShape.append left right).survivorOccurrences.map Prod.fst)
          hwholeSurvivors⟩
  apply congrArg₂ (fun pairs survivors =>
    (⟨pairs, survivors⟩ : LabelledWalk.CancellationOccurrencePositions source))
  · rw [hmappedPairs, hleftTracePairs, hrightTracePairs]
  · rw [hmappedSurvivors, hleftTraceSurvivors, hrightTraceSurvivors]

/-- A bracket replays its inner cancellations, removes the enclosing pair,
then replays its suffix. The trace keeps the source occurrences from all
three stages. -/
theorem bracket_sourcePositionTraceAux
    {a : Letter α} {inner suffix result : Word α}
    (innerShape : FreeReductionShape inner [])
    (suffixShape : FreeReductionShape suffix result)
    {source : Word α} (origins : List (Fin source.length))
    (opening closing : Fin source.length)
    (innerOrigins suffixOrigins : List (Fin source.length))
    (horigins : origins = ([opening] ++ innerOrigins) ++
      ([closing] ++ suffixOrigins))
    (hinnerLen : innerOrigins.length = inner.length)
    (hsuffixLen : suffixOrigins.length = suffix.length)
    (hlen : origins.length =
      (((( [a] ++ inner) ++ [inverseLetter a]) ++ suffix).length)) :
    LabelledWalk.sourcePositionTraceAux source
      (FreeReductionShape.bracket a innerShape suffixShape).to_cancellationSequence
      origins hlen =
      ⟨(LabelledWalk.sourcePositionTraceAux source
          innerShape.to_cancellationSequence innerOrigins hinnerLen).pairs ++
          [(opening, closing)] ++
        (LabelledWalk.sourcePositionTraceAux source
          suffixShape.to_cancellationSequence suffixOrigins hsuffixLen).pairs,
       (LabelledWalk.sourcePositionTraceAux source
          suffixShape.to_cancellationSequence suffixOrigins hsuffixLen).survivors⟩ := by
  subst origins
  let contextSuffix := [inverseLetter a] ++ suffix
  have hraw :
      ([a] ++ inner) ++ contextSuffix =
        ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix) := by
    simp [contextSuffix, List.append_assoc]
  have hmid :
      ([a] ++ []) ++ contextSuffix =
        ((([a] ++ []) ++ [inverseLetter a]) ++ suffix) := by
    simp [contextSuffix, List.append_assoc]
  let innerSeq := innerShape.to_cancellationSequence
  let suffixSeq := suffixShape.to_cancellationSequence
  let contextSeqRaw := (innerSeq.appendLeft [a]).appendRight contextSuffix
  let contextSeq := FreeCancellationSequence.castWords hraw hmid contextSeqRaw
  let rootSeq := FreeCancellationSequence.cons
    (FreeCancellationStep.cancel [] suffix a) (.refl suffix)
  let innerTrace := LabelledWalk.sourcePositionTraceAux source innerSeq
    innerOrigins hinnerLen
  let suffixTrace := LabelledWalk.sourcePositionTraceAux source suffixSeq
    suffixOrigins hsuffixLen
  have hbaseTrace :=
    LabelledWalk.sourcePositionTraceAux_appendLeft source innerSeq [a]
      [opening] innerOrigins (by simp) hinnerLen
  have hinnerSurvivorsLength :=
    LabelledWalk.sourcePositionTraceAux_survivors_length source innerSeq
      innerOrigins hinnerLen
  have hinnerSurvivors : innerTrace.survivors = [] := by
    apply List.length_eq_zero_iff.mp
    simpa [innerTrace, innerSeq] using hinnerSurvivorsLength
  have hcontextTrace :=
    LabelledWalk.sourcePositionTraceAux_appendRight source
      (innerSeq.appendLeft [a]) contextSuffix
      ([opening] ++ innerOrigins) ([closing] ++ suffixOrigins)
      (by simp [hinnerLen]) (by simp [contextSuffix, hsuffixLen])
  have hcontextWholeLen :
      (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins)).length =
        ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix).length := by
    simpa [List.append_assoc] using hlen
  have hcontextRawLen :
      (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins)).length =
        (([a] ++ inner) ++ contextSuffix).length := by
    simpa [contextSuffix, List.append_assoc] using hlen
  have hcontextRaw :
      LabelledWalk.sourcePositionTraceAux source contextSeqRaw
        (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins))
        hcontextRawLen =
        ⟨innerTrace.pairs, [opening, closing] ++ suffixOrigins⟩ := by
    rw [hbaseTrace] at hcontextTrace
    simpa [contextSeqRaw, innerTrace, hinnerSurvivors,
      List.append_assoc] using hcontextTrace
  have hcontext :
      LabelledWalk.sourcePositionTraceAux source contextSeq
        (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins))
        hcontextWholeLen =
        ⟨innerTrace.pairs, [opening, closing] ++ suffixOrigins⟩ := by
    have htransport := LabelledWalk.sourcePositionTraceAux_castWords
      source hraw hmid contextSeqRaw
      (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins))
      hcontextWholeLen
    simpa [contextSeq, innerTrace] using htransport.trans hcontextRaw
  have hrootTrace :
      LabelledWalk.sourcePositionTraceAux source rootSeq
        ([opening, closing] ++ suffixOrigins)
        (by simp [rootSeq, List.length_append, hsuffixLen]) =
        ⟨[(opening, closing)], suffixOrigins⟩ := by
    simp [rootSeq, LabelledWalk.sourcePositionTraceAux,
      FreeCancellationStep.prefixLength, List.length_append]
  have hinnerRootTrace :
      LabelledWalk.sourcePositionTraceAux source (contextSeq.trans rootSeq)
        (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins))
        hcontextWholeLen =
        ⟨innerTrace.pairs ++ [(opening, closing)], suffixOrigins⟩ := by
    rw [LabelledWalk.sourcePositionTraceAux_trans]
    simp only [hcontext]
    change
      (⟨innerTrace.pairs ++
          (LabelledWalk.sourcePositionTraceAux source rootSeq
            ([opening, closing] ++ suffixOrigins) _).pairs,
        (LabelledWalk.sourcePositionTraceAux source rootSeq
          ([opening, closing] ++ suffixOrigins) _).survivors⟩ :
        LabelledWalk.CancellationOccurrencePositions source) = _
    rw [hrootTrace]
  have hwholeTrace :
      LabelledWalk.sourcePositionTraceAux source
        ((contextSeq.trans rootSeq).trans suffixSeq)
        (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins))
        hcontextWholeLen =
        ⟨(innerTrace.pairs ++ [(opening, closing)]) ++ suffixTrace.pairs,
          suffixTrace.survivors⟩ := by
    rw [LabelledWalk.sourcePositionTraceAux_trans]
    simp only [hinnerRootTrace, suffixTrace]
  have hseq :
      (FreeReductionShape.bracket a innerShape suffixShape).to_cancellationSequence =
        (contextSeq.trans rootSeq).trans suffixSeq := by
    simp [FreeReductionShape.to_cancellationSequence,
      contextSeq, rootSeq, suffixSeq, innerSeq, contextSuffix,
      hraw, hmid, List.append_assoc]
    all_goals rfl
  rw [hseq]
  exact hwholeTrace

/-- Relabeling the chronological bracket replay selects the same ambient
occurrences as the inner replay, root cancellation, and suffix replay. -/
theorem bracket_replayMappedTrace
    {a : Letter α} {inner suffix result : Word α}
    (innerShape : FreeReductionShape inner [])
    (suffixShape : FreeReductionShape suffix result)
    {source : Word α} (origins : List (Fin source.length))
    (opening closing : Fin source.length)
    (innerOrigins suffixOrigins : List (Fin source.length))
    (horigins : origins = ([opening] ++ innerOrigins) ++
      ([closing] ++ suffixOrigins))
    (hinnerLen : innerOrigins.length = inner.length)
    (hsuffixLen : suffixOrigins.length = suffix.length)
    (hlen : origins.length =
      (((( [a] ++ inner) ++ [inverseLetter a]) ++ suffix).length)) :
    (FreeReductionShape.bracket a innerShape suffixShape).replayMappedTrace
        origins hlen =
      ⟨(innerShape.replayMappedTrace innerOrigins hinnerLen).pairs ++
          [(opening, closing)] ++
        (suffixShape.replayMappedTrace suffixOrigins hsuffixLen).pairs,
       (suffixShape.replayMappedTrace suffixOrigins hsuffixLen).survivors⟩ := by
  subst origins
  let tailOrigins := innerOrigins ++ ([closing] ++ suffixOrigins)
  let tailWord := inner ++ ([inverseLetter a] ++ suffix)
  let wholeWord := ((([a] ++ inner) ++ [inverseLetter a]) ++ suffix)
  let innerPairs := shiftCancellationPairs 1 innerShape.replayCancellationPairs
  let rootPairs := [(0, inner.length + 1)]
  let suffixPairs := shiftCancellationPairs (inner.length + 2)
    suffixShape.replayCancellationPairs
  have hfullOrigins :
      (([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins)) =
        [opening] ++ tailOrigins := by
    simp [tailOrigins, List.append_assoc]
  have htailLen : tailOrigins.length = tailWord.length := by
    simp [tailOrigins, tailWord, List.length_append, hinnerLen, hsuffixLen]
  have hwholeTailLen : wholeWord.length = 1 + tailWord.length := by
    simp [wholeWord, tailWord, List.length_append]
    omega
  have htotal : ([opening] ++ tailOrigins).length = wholeWord.length := by
    rw [← hfullOrigins]
    simpa [wholeWord] using hlen
  have hwholeLen : wholeWord.length = inner.length + suffix.length + 2 := by
    simp [wholeWord, List.length_append]
    omega
  have hinnerChildBound : ∀ p ∈ innerShape.replayCancellationPairs,
      p.1 < inner.length ∧ p.2 < inner.length := by
    intro p hp
    simpa [FreeReductionShape.inputWord] using
      innerShape.replayCancellationPairs_inBounds p hp
  have hinnerTailBound : ∀ p ∈ innerShape.replayCancellationPairs,
      p.1 < tailWord.length ∧ p.2 < tailWord.length := by
    intro p hp
    have hb := hinnerChildBound p hp
    simp [tailWord, List.length_append]
    omega
  have hsuffixChildBound : ∀ p ∈ suffixShape.replayCancellationPairs,
      p.1 < suffix.length ∧ p.2 < suffix.length := by
    intro p hp
    simpa [FreeReductionShape.inputWord] using
      suffixShape.replayCancellationPairs_inBounds p hp
  have hinnerBound : ∀ p ∈ innerPairs,
      p.1 < wholeWord.length ∧ p.2 < wholeWord.length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hb := hinnerChildBound q hq
    rw [hwholeLen]
    simp only [shiftCancellationPairs, List.length_append]
    constructor <;> omega
  have hrootBound : ∀ p ∈ rootPairs,
      p.1 < wholeWord.length ∧ p.2 < wholeWord.length := by
    intro p hp
    simp only [rootPairs, List.mem_singleton] at hp
    subst p
    rw [hwholeLen]
    constructor <;> omega
  have hsuffixBound : ∀ p ∈ suffixPairs,
      p.1 < wholeWord.length ∧ p.2 < wholeWord.length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hb := hsuffixChildBound q hq
    rw [hwholeLen]
    simp only [shiftCancellationPairs]
    constructor <;> omega
  have hrestBound : ∀ p ∈ rootPairs ++ suffixPairs,
      p.1 < wholeWord.length ∧ p.2 < wholeWord.length := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hrootBound p hp
    · exact hsuffixBound p hp
  have hallBound : ∀ p ∈ innerPairs ++ (rootPairs ++ suffixPairs),
      p.1 < wholeWord.length ∧ p.2 < wholeWord.length := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hinnerBound p hp
    · exact hrestBound p hp
  have htailPairsShift := mapSourcePairs_shiftSource
    ([opening]) tailOrigins 1 (by simp) htailLen hwholeTailLen htotal
    innerShape.replayCancellationPairs hinnerTailBound
  have htailPairsPrefix := mapSourcePairs_prefixSource
    innerOrigins ([closing] ++ suffixOrigins) hinnerLen htailLen
    innerShape.replayCancellationPairs hinnerChildBound
  have hinnerMap :
    mapSourcePairs (([opening] ++ innerOrigins) ++
          ([closing] ++ suffixOrigins)) hlen innerPairs hinnerBound =
        mapSourcePairs innerOrigins hinnerLen
          innerShape.replayCancellationPairs hinnerChildBound := by
    calc
      _ = mapSourcePairs ([opening] ++ tailOrigins) htotal innerPairs hinnerBound := by
        exact mapSourcePairs_congr_origins hfullOrigins hlen htotal
          innerPairs hinnerBound
      _ = mapSourcePairs tailOrigins htailLen
            innerShape.replayCancellationPairs hinnerTailBound := by
        simpa [innerPairs] using htailPairsShift
      _ = mapSourcePairs innerOrigins hinnerLen
            innerShape.replayCancellationPairs hinnerChildBound :=
        htailPairsPrefix
  have hrootMap :
      mapSourcePairs (([opening] ++ innerOrigins) ++
          ([closing] ++ suffixOrigins)) hlen rootPairs hrootBound =
        [(opening, closing)] := by
    simp [FreeReductionShape.mapSourcePairs, rootPairs, hfullOrigins,
      tailOrigins, List.getElem_append_left, List.getElem_append_right,
      List.length_append, hinnerLen]
  let suffixPrefixOrigins := ([opening] ++ innerOrigins) ++ [closing]
  have hsuffixPrefixLen :
      suffixPrefixOrigins.length = inner.length + 2 := by
    simp [suffixPrefixOrigins, hinnerLen]
  have hwholeSuffixLen : wholeWord.length = inner.length + 2 + suffix.length := by
    rw [hwholeLen]
    omega
  have hsplitSuffixOrigins :
      suffixPrefixOrigins ++ suffixOrigins =
        ([opening] ++ innerOrigins) ++ ([closing] ++ suffixOrigins) := by
    simp [suffixPrefixOrigins, List.append_assoc]
  have hwholeSuffixOrigins :
      (suffixPrefixOrigins ++ suffixOrigins).length = wholeWord.length := by
    rw [hsplitSuffixOrigins]
    simpa [wholeWord] using hlen
  have htailSuffixShift := mapSourcePairs_shiftSource
    suffixPrefixOrigins suffixOrigins (inner.length + 2)
    hsuffixPrefixLen hsuffixLen hwholeSuffixLen hwholeSuffixOrigins
    suffixShape.replayCancellationPairs hsuffixChildBound
  have hsuffixMap :
      mapSourcePairs (([opening] ++ innerOrigins) ++
          ([closing] ++ suffixOrigins)) hlen suffixPairs hsuffixBound =
        mapSourcePairs suffixOrigins hsuffixLen
          suffixShape.replayCancellationPairs hsuffixChildBound := by
    calc
      _ = mapSourcePairs (suffixPrefixOrigins ++ suffixOrigins)
          hwholeSuffixOrigins suffixPairs hsuffixBound :=
        mapSourcePairs_congr_origins hsplitSuffixOrigins.symm hlen hwholeSuffixOrigins
          suffixPairs hsuffixBound
      _ = mapSourcePairs suffixOrigins hsuffixLen
          suffixShape.replayCancellationPairs hsuffixChildBound := by
        simpa [suffixPairs] using htailSuffixShift
  have hpairMap :
      mapSourcePairs (([opening] ++ innerOrigins) ++
          ([closing] ++ suffixOrigins)) hlen
          (innerPairs ++ (rootPairs ++ suffixPairs)) hallBound =
        mapSourcePairs innerOrigins hinnerLen
            innerShape.replayCancellationPairs hinnerChildBound ++
          [(opening, closing)] ++
        mapSourcePairs suffixOrigins hsuffixLen
            suffixShape.replayCancellationPairs hsuffixChildBound := by
    calc
      _ = mapSourcePairs (([opening] ++ innerOrigins) ++
            ([closing] ++ suffixOrigins)) hlen innerPairs hinnerBound ++
          mapSourcePairs (([opening] ++ innerOrigins) ++
            ([closing] ++ suffixOrigins)) hlen (rootPairs ++ suffixPairs)
              hrestBound := by
        exact mapSourcePairs_append _ _ _ _ hallBound hinnerBound hrestBound
      _ = mapSourcePairs (([opening] ++ innerOrigins) ++
            ([closing] ++ suffixOrigins)) hlen innerPairs hinnerBound ++
          (mapSourcePairs (([opening] ++ innerOrigins) ++
              ([closing] ++ suffixOrigins)) hlen rootPairs hrootBound ++
            mapSourcePairs (([opening] ++ innerOrigins) ++
              ([closing] ++ suffixOrigins)) hlen suffixPairs hsuffixBound) := by
        congr 1
        exact mapSourcePairs_append _ _ _ _ hrestBound hrootBound hsuffixBound
      _ = _ := by
        rw [hinnerMap, hrootMap, hsuffixMap]
        simp [List.append_assoc]
  have hsurvivorBound : ∀ i ∈
      ((suffixShape.survivorOccurrences.map Prod.fst).map
        (inner.length + 2 + ·)), i < wholeWord.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
    rcases List.mem_map.mp hj with ⟨o, ho, rfl⟩
    have hb' := suffixShape.survivorOccurrences_inBounds o ho
    simp only [FreeReductionShape.inputWord] at hb'
    rw [hwholeLen]
    omega
  have hsurvivorBound' : ∀ i ∈
      (FreeReductionShape.bracket a innerShape suffixShape).survivorOccurrences.map
        Prod.fst, i < wholeWord.length := by
    simpa [FreeReductionShape.survivorOccurrences,
      shiftLetterOccurrences_positions, FreeReductionShape.inputWord] using
        hsurvivorBound
  have hsurvivorMap := mapSourcePositions_shiftSource
    suffixPrefixOrigins suffixOrigins (inner.length + 2)
    hsuffixPrefixLen hsuffixLen hwholeSuffixLen hwholeSuffixOrigins
    (suffixShape.survivorOccurrences.map Prod.fst)
    (by
      intro i hi
      rcases List.mem_map.mp hi with ⟨o, ho, rfl⟩
      simpa [FreeReductionShape.inputWord] using
        suffixShape.survivorOccurrences_inBounds o ho)
  have hsurvivorOriginMap := mapSourcePositions_congr_origins
    hsplitSuffixOrigins.symm hlen hwholeSuffixOrigins
    ((suffixShape.survivorOccurrences.map Prod.fst).map
      (inner.length + 2 + ·)) hsurvivorBound
  have hsurvivors :
      mapSourcePositions (([opening] ++ innerOrigins) ++
          ([closing] ++ suffixOrigins)) hlen
          ((FreeReductionShape.bracket a innerShape suffixShape).survivorOccurrences.map
            Prod.fst) hsurvivorBound' =
        mapSourcePositions suffixOrigins hsuffixLen
          (suffixShape.survivorOccurrences.map Prod.fst)
            (by
              intro i hi
              rcases List.mem_map.mp hi with ⟨o, ho, rfl⟩
              simpa [FreeReductionShape.inputWord] using
                suffixShape.survivorOccurrences_inBounds o ho) := by
    simpa [FreeReductionShape.survivorOccurrences,
      shiftLetterOccurrences_positions, FreeReductionShape.inputWord] using
        hsurvivorOriginMap.trans hsurvivorMap
  unfold FreeReductionShape.replayMappedTrace
  apply congrArg₂ (fun pairs survivors =>
    (⟨pairs, survivors⟩ : LabelledWalk.CancellationOccurrencePositions source))
  · simpa [FreeReductionShape.replayCancellationPairs, innerPairs,
      rootPairs, suffixPairs, FreeReductionShape.inputWord,
      List.append_assoc] using hpairMap
  · simpa [FreeReductionShape.survivorOccurrences,
      shiftLetterOccurrences_positions, FreeReductionShape.inputWord] using
        hsurvivors

/-- Any occurrence list whose length matches a bracket input splits into its
opening occurrence, inner occurrences, closing occurrence, and suffix. -/
theorem exists_bracket_origin_decomposition {β : Type*}
    (origins : List β) (innerLength suffixLength : Nat)
    (hlen : origins.length = innerLength + suffixLength + 2) :
    ∃ opening inner closing suffix,
      origins = [opening] ++ inner ++ [closing] ++ suffix ∧
      inner.length = innerLength ∧ suffix.length = suffixLength := by
  induction innerLength generalizing origins with
  | zero =>
      cases origins with
      | nil => simp at hlen
      | cons opening tail =>
          have htail : tail.length = suffixLength + 1 := by
            simp at hlen
            omega
          cases tail with
          | nil => simp at htail
          | cons closing suffix =>
              have hsuffix : suffix.length = suffixLength := by
                simp at htail
                omega
              refine ⟨opening, [], closing, suffix, ?_, by simp, hsuffix⟩
              simp [List.append_assoc]
  | succ n ih =>
      cases origins with
      | nil => simp at hlen
      | cons opening tail =>
          have htail : tail.length = n + suffixLength + 2 := by
            simp at hlen
            omega
          obtain ⟨first, inner, closing, suffix, horigins,
              hinner, hsuffix⟩ := ih tail htail
          refine ⟨opening, first :: inner, closing, suffix, ?_, ?_, hsuffix⟩
          · simp [horigins, List.append_assoc]
          · simpa using congrArg Nat.succ hinner

/-- The executable cancellation sequence and the structural replay schedule
produce exactly the same occurrence trace for every reduction tree. -/
theorem to_cancellationSequence_sourcePositionTraceAux
    {raw reduced : Word α} (shape : FreeReductionShape raw reduced)
    {source : Word α} (origins : List (Fin source.length))
    (hlen : origins.length = raw.length) :
    LabelledWalk.sourcePositionTraceAux source shape.to_cancellationSequence
      origins hlen = shape.replayMappedTrace origins hlen := by
  induction shape generalizing origins with
  | empty =>
      cases origins with
      | nil =>
          simp [FreeReductionShape.to_cancellationSequence,
            FreeReductionShape.replayMappedTrace,
            FreeReductionShape.replayCancellationPairs,
            FreeReductionShape.survivorOccurrences,
            mapSourcePairs, mapSourcePositions,
            LabelledWalk.sourcePositionTraceAux]
      | cons _ _ => simp at hlen
  | letter a =>
      cases origins with
      | nil => simp at hlen
      | cons occurrence tail =>
          cases tail with
          | nil =>
              simp [FreeReductionShape.to_cancellationSequence,
                FreeReductionShape.replayMappedTrace,
                FreeReductionShape.replayCancellationPairs,
                FreeReductionShape.survivorOccurrences,
                mapSourcePairs, mapSourcePositions,
                LabelledWalk.sourcePositionTraceAux]
          | cons _ _ => simp at hlen
  | @append u u' v v' left right ihLeft ihRight =>
      let leftOrigins := origins.take u.length
      let rightOrigins := origins.drop u.length
      have horigins : origins = leftOrigins ++ rightOrigins := by
        simp [leftOrigins, rightOrigins, List.take_append_drop]
      have hleftBound : u.length ≤ origins.length := by
        rw [hlen]
        simp [List.length_append]
      have hleftLen : leftOrigins.length = u.length := by
        simp [leftOrigins, Nat.min_eq_left hleftBound]
      have hrightLen : rightOrigins.length = v.length := by
        dsimp [rightOrigins]
        rw [List.length_drop, hlen]
        simp only [List.length_append]
        omega
      exact append_to_cancellationSequence_trace left right origins
        leftOrigins rightOrigins horigins hleftLen hrightLen hlen
        ihLeft ihRight
  | @bracket a inner suffix result innerShape suffixShape ihInner ihSuffix =>
      have hlenRaw : origins.length = inner.length + suffix.length + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      obtain ⟨opening, innerOrigins, closing, suffixOrigins,
          horigins, hinnerLen, hsuffixLen⟩ :=
        exists_bracket_origin_decomposition origins inner.length suffix.length
          hlenRaw
      have horigins' : origins = ([opening] ++ innerOrigins) ++
          ([closing] ++ suffixOrigins) := by
        simpa [List.append_assoc] using horigins
      have htrace := bracket_sourcePositionTraceAux innerShape suffixShape
        origins opening closing innerOrigins suffixOrigins horigins'
        hinnerLen hsuffixLen hlen
      have hmapped := bracket_replayMappedTrace innerShape suffixShape
        origins opening closing innerOrigins suffixOrigins horigins'
        hinnerLen hsuffixLen hlen
      rw [htrace, hmapped, ihInner innerOrigins hinnerLen,
        ihSuffix suffixOrigins hsuffixLen]

/-- On the complete source range, the executable trace's finite endpoints are
exactly the natural positions in the chronological replay schedule. -/
theorem sourcePositionTrace_pairPositions_eq_replayCancellationPairs
    {raw reduced : Word α} (shape : FreeReductionShape raw reduced) :
    ((LabelledWalk.sourcePositionTrace shape.to_cancellationSequence).pairs.map
      fun p => (p.1.val, p.2.val)) = shape.replayCancellationPairs := by
  have htrace := shape.to_cancellationSequence_sourcePositionTraceAux
    (source := raw) (List.finRange raw.length) (by simp)
  have hpairs := congrArg
    (fun trace : LabelledWalk.CancellationOccurrencePositions raw =>
      trace.pairs.map fun p => (p.1.val, p.2.val)) htrace
  have hreplay :
      (shape.replayMappedTrace (List.finRange raw.length) (by simp)).pairs.map
        (fun p => (p.1.val, p.2.val)) =
      shape.replayCancellationPairs := by
    dsimp [FreeReductionShape.replayMappedTrace,
      FreeReductionShape.mapSourcePairs]
    rw [List.map_map]
    apply Eq.trans ?_ (List.attach_map_subtype_val _)
    apply List.map_congr_left
    intro p hp
    rcases p with ⟨⟨i, j⟩, hmem⟩
    simp [List.get_eq_getElem, Fin.val_cast]
  simpa [LabelledWalk.sourcePositionTrace] using hpairs.trans hreplay

end FreeReductionShape

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
