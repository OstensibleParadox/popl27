import DSeparation.Trail.Blocking

open Finset

namespace DSeparation

noncomputable section

/-! # Active Trails to Bayes-Ball Bridges

Lemmas that lift an active (non-blocked) trail into a Bayes-ball path, both as
reachability and as explicit `BayesBallPath` objects.  Includes helper lemmas
about active non-colliders, colliders, and ancestry preservation along active
trail segments.
-/

lemma BayesBallStep.of_active_triple {G : DAG} {Z : Finset ℕ}
    {a b c : ℕ} {arrival departure : TrailDir}
    (hab : TrailDir.edgeIntoCurrent G a b arrival)
    (hbc : TrailDir.edgeIntoCurrent G b c departure)
    (hactive : ¬ TripleBlocked G Z a b c) :
    BayesBallStep G Z (b, arrival) (c, departure) :=
  BayesBallStep.step hbc
    (by
      rwa [directionalTripleBlocked_iff_tripleBlocked hab hbc])

theorem bayesBallReachable_of_active_trail_from_prev {G : DAG} {Z : Finset ℕ}
    {prev u v : ℕ} {arrival : TrailDir}
    (hprev : TrailDir.edgeIntoCurrent G prev u arrival)
    (t : Trail G u v)
    (h_active : ¬ TrailBlocked G Z (prev :: t.toList)) :
    ∃ final_dir, BayesBallReachable G Z (u, arrival) (v, final_dir) := by
  induction t generalizing prev arrival with
  | nil v =>
      exact ⟨arrival, Relation.ReflTransGen.refl⟩
  | forward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ TripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.into) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ TrailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩
  | backward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ TripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.outOf) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ TrailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩

def bayesBallPath_of_active_trail_from_prev {G : DAG} {Z : Finset ℕ}
    {prev u v : ℕ} {arrival : TrailDir}
    (hprev : TrailDir.edgeIntoCurrent G prev u arrival)
    (t : Trail G u v)
    (h_active : ¬ TrailBlocked G Z (prev :: t.toList)) :
    Σ final_dir, BayesBallPath G Z (u, arrival) (v, final_dir) := by
  induction t generalizing prev arrival with
  | nil v =>
      exact ⟨arrival, BayesBallPath.nil (v, arrival)⟩
  | forward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ TripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.into) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ TrailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩
  | backward h tail ih =>
      rename_i u0 w0 v0
      have hhead : ¬ TripleBlocked G Z prev u0 w0 :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail) h_active
      have hstep :
          BayesBallStep G Z (u0, arrival) (w0, TrailDir.outOf) := by
        exact BayesBallStep.of_active_triple hprev
          (by simpa [TrailDir.edgeIntoCurrent] using h) hhead
      have htail_active : ¬ TrailBlocked G Z (u0 :: tail.toList) :=
        not_trailBlocked_tail_of_not_trailBlocked_cons h_active
      rcases ih (prev := u0) (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩

theorem bayesBallReachable_of_active_trail {G : DAG} {Z : Finset ℕ} {u v : ℕ}
    (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z)
    (init_dir : TrailDir)
    (h_start : t.StartOpen Z init_dir) :
    ∃ final_dir, BayesBallReachable G Z (u, init_dir) (v, final_dir) := by
  cases t with
  | nil v =>
      exact ⟨init_dir, Relation.ReflTransGen.refl⟩
  | forward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.into) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.StartOpen] using h_start)
      have htail_active : ¬ TrailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallReachable_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩
  | backward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.outOf) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.StartOpen] using h_start)
      have htail_active : ¬ TrailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallReachable_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, (Relation.ReflTransGen.single hstep).trans htail⟩

def bayesBallPath_of_active_trail {G : DAG} {Z : Finset ℕ} {u v : ℕ}
    (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z)
    (init_dir : TrailDir)
    (h_start : t.StartOpen Z init_dir) :
    Σ final_dir, BayesBallPath G Z (u, init_dir) (v, final_dir) := by
  cases t with
  | nil v =>
      exact ⟨init_dir, BayesBallPath.nil (u, init_dir)⟩
  | forward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.into) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.StartOpen] using h_start)
      have htail_active : ¬ TrailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallPath_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.into)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩
  | backward h tail =>
      rename_i w0
      have hstep :
          BayesBallStep G Z (u, init_dir) (w0, TrailDir.outOf) :=
        BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using h)
          (by simpa [Trail.StartOpen] using h_start)
      have htail_active : ¬ TrailBlocked G Z (u :: tail.toList) := by
        simpa [Trail.isBlocked, Trail.toList] using h_active
      rcases bayesBallPath_of_active_trail_from_prev
          (G := G) (Z := Z) (prev := u) (u := w0) (v := v)
          (arrival := TrailDir.outOf)
          (by simpa [TrailDir.edgeIntoCurrent] using h) tail htail_active with
        ⟨final_dir, htail⟩
      exact ⟨final_dir, BayesBallPath.cons hstep htail⟩

lemma Trail.startOpen_outOf_of_not_mem {G : DAG} {Z : Finset ℕ} {u v : ℕ}
    {t : Trail G u v} (huZ : u ∉ Z) :
    t.StartOpen Z TrailDir.outOf := by
  cases t <;> 
    simp [Trail.StartOpen, DirectionalTripleBlocked, TrailDir.colliderAtCurrent, huZ]

theorem bayesBallReachable_of_active_trail_outOf {G : DAG} {Z : Finset ℕ}
    {u v : ℕ} (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z) (huZ : u ∉ Z) :
    ∃ final_dir, BayesBallReachable G Z (u, TrailDir.outOf) (v, final_dir) :=
  bayesBallReachable_of_active_trail t h_active TrailDir.outOf
    (Trail.startOpen_outOf_of_not_mem huZ)

def bayesBallPath_of_active_trail_outOf {G : DAG} {Z : Finset ℕ}
    {u v : ℕ} (t : Trail G u v)
    (h_active : ¬ t.isBlocked Z) (huZ : u ∉ Z) :
    Σ final_dir, BayesBallPath G Z (u, TrailDir.outOf) (v, final_dir) :=
  bayesBallPath_of_active_trail t h_active TrailDir.outOf
    (Trail.startOpen_outOf_of_not_mem huZ)

lemma not_mem_Z_of_active_noncollider {G : DAG} {Z : Finset ℕ} {a b c : ℕ}
    (hactive : ¬ TripleBlocked G Z a b c)
    (hncoll : ¬ TripleCollider G a b c) :
    b ∉ Z := by
  intro hbZ
  exact hactive (Or.inl ⟨hncoll, hbZ⟩)

lemma not_mem_Z_of_active_directional_noncollider {G : DAG} {Z : Finset ℕ}
    {b : ℕ} {arrival departure : TrailDir}
    (hopen : ¬ DirectionalTripleBlocked G Z b arrival departure)
    (hnot : ¬ (arrival = TrailDir.into ∧ departure = TrailDir.outOf)) :
    b ∉ Z := by
  intro hbZ
  exact hopen (Or.inl ⟨by simpa [TrailDir.colliderAtCurrent] using hnot, hbZ⟩)

lemma collider_mem_ancestralSubgraphNodes_of_active {G : DAG} {X Y Z : Finset ℕ}
    {a b c : ℕ}
    (hactive : ¬ TripleBlocked G Z a b c)
    (hcoll : TripleCollider G a b c) :
    b ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
  classical
  have hnotDis :
      ¬ Disjoint ({b} ∪ descendants G b) Z := by
    intro hdis
    exact hactive (Or.inr ⟨hcoll, hdis⟩)
  rw [Finset.disjoint_left] at hnotDis
  push Not at hnotDis
  rcases hnotDis with ⟨z, hz_left, hzZ⟩
  have hbG : b ∈ G.nodes := (G.edges_subset hcoll.1).2
  have hreach : Reachable G b z := by
    rcases Finset.mem_union.mp hz_left with hz_single | hz_desc
    · simp at hz_single
      subst z
      exact Relation.ReflTransGen.refl
    · exact (Finset.mem_filter.mp hz_desc).2.2
  have hzS : z ∈ X ∪ Y ∪ Z := by
    simp [hzZ]
  exact Finset.mem_biUnion.mpr
    ⟨z, hzS, by simp [DAG.ancestors, hbG, hreach]⟩

/--
If a trail segment starts with a forward edge `u → w` and remains active, then
the first target `w` is ancestral to `X ∪ Y ∪ Z`, provided the trail endpoint is.
Forward chains inherit ancestry from the right; a first reversal is an active
collider and is ancestral through `Z`.
-/
lemma first_forward_target_mem_ancestral_of_active
    {G : DAG} {X Y Z : Finset ℕ} {u w v : ℕ}
    (h : G.HasEdge u w) (tail : Trail G w v)
    (h_active : ¬ TrailBlocked G Z (u :: tail.toList))
    (hvA : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
    w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
  induction tail generalizing u with
  | nil w =>
      simpa [Trail.toList] using hvA
  | forward h₂ tail₂ ih =>
      have htail_active :=
        not_trailBlocked_tail_of_not_trailBlocked_cons
          (by simpa [Trail.toList] using h_active)
      have hcA := ih h₂ htail_active hvA
      exact DAG.mem_ancestralSubgraphNodes_of_hasEdge_left h₂ hcA
  | backward h₂ tail₂ =>
      have hhead :=
        not_tripleBlocked_head_of_not_trailBlocked_trail (t := tail₂)
          (by simpa [Trail.toList] using h_active)
      exact collider_mem_ancestralSubgraphNodes_of_active
        (G := G) (X := X) (Y := Y) (Z := Z) hhead ⟨h, h₂⟩

end

end DSeparation
