import DSeparation.MAGWalk

open Finset

namespace DSeparation

noncomputable section

/-! # Trace Synthesis: From Moral Graph Reachability to Active Trails

This module implements the reverse direction of the d-separation equivalence:
from ¬DAG.dSeparated (i.e. moral-graph reachability) we synthesize an active
trail witness.  The pipeline is:

  Reachable → StaticRoute → NormalizedStaticRoute → BayesBallPath → ActiveRoute
    → ∃ Trail, ¬ isBlocked → ¬ dSeparates

The key design decision is that normalization may change endpoints: a bad
(collider) node whose descendants miss Z is rerouted to a different node in X
or Y through leaked ancestry.
-/

-- ============================================================
-- Phase 1: Explicit Static Path IR
-- ============================================================

/-- A single step in the d-separation graph, as explicit evidence. -/
inductive StaticStep (G : DAG) (X Y Z : Finset ℕ) : ℕ → ℕ → Type where
  | directForward {u v : ℕ}
      (hEdge : G.HasEdge u v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      StaticStep G X Y Z u v
  | directBackward {u v : ℕ}
      (hEdge : G.HasEdge v u)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      StaticStep G X Y Z u v
  | moralJump {u v w : ℕ}
      (huw : G.HasEdge u w)
      (hvw : G.HasEdge v w)
      (hne : u ≠ v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z)
      (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
      StaticStep G X Y Z u v

/-- A route is a sequence of static steps. -/
inductive StaticRoute (G : DAG) (X Y Z : Finset ℕ) : ℕ → ℕ → Type where
  | nil (u : ℕ) : StaticRoute G X Y Z u u
  | cons {u v w : ℕ}
      (step : StaticStep G X Y Z u v)
      (rest : StaticRoute G X Y Z v w) :
      StaticRoute G X Y Z u w

namespace StaticStep

/-- Every static step gives a MAGWalk step. -/
def toMAGWalk {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (step : StaticStep G X Y Z u v) : MAGWalk G X Y Z u v :=
  match step with
  | directForward hEdge hu hv => MAGWalk.single (Or.inl hEdge) hu hv
  | directBackward hEdge hu hv => MAGWalk.single (Or.inr hEdge) hu hv
  | moralJump huw hvw hne hu hv hw => MAGWalk.jump huw hvw hne hu hv hw

end StaticStep

namespace StaticRoute

/-- Every static route gives a MAGWalk. -/
def toMAGWalk {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (route : StaticRoute G X Y Z u v) : MAGWalk G X Y Z u v :=
  match route with
  | nil u => MAGWalk.refl u
  | cons step rest => MAGWalk.trans step.toMAGWalk rest.toMAGWalk

/-- Append two static routes. -/
def append {G : DAG} {X Y Z : Finset ℕ} {u v w : ℕ}
    (p : StaticRoute G X Y Z u v) (q : StaticRoute G X Y Z v w) :
    StaticRoute G X Y Z u w :=
  match p with
  | nil _ => q
  | cons step rest => cons step (rest.append q)

/-- Length of a static route (number of steps). -/
def length {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (route : StaticRoute G X Y Z u v) : ℕ :=
  match route with
  | nil _ => 0
  | cons _ rest => rest.length + 1

end StaticRoute

/-- Convert a single adjacency in the d-separation graph to a StaticStep. -/
noncomputable def staticStep_of_dSeparationGraph_adj {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} (h : (G.dSeparationGraph X Y Z).Adj u v) :
    StaticStep G X Y Z u v :=
  Classical.choice (show Nonempty (StaticStep G X Y Z u v) from by
    rcases h with ⟨hu, hv, hmoral⟩
    dsimp [DAG.moralGraph] at hmoral
    rcases hmoral with ⟨huA, hvA, hne, hdir | hrev | hcop⟩
    · -- Direct edge u → v in ancestral subgraph
      have huv : G.HasEdge u v := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at hdir ⊢
        exact hdir.1
      exact ⟨StaticStep.directForward huv hu hv⟩
    · -- Direct edge v → u in ancestral subgraph
      have hvu : G.HasEdge v u := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at hrev ⊢
        exact hrev.1
      exact ⟨StaticStep.directBackward hvu hu hv⟩
    · -- Co-parents through common child w
      rcases hcop with ⟨w, huw', hvw', hne_uv⟩
      have huw : G.HasEdge u w := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at huw' ⊢
        exact huw'.1
      have hvw : G.HasEdge v w := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at hvw' ⊢
        exact hvw'.1
      have hwA : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at huw' ⊢
        exact huw'.2.2
      exact ⟨StaticStep.moralJump huw hvw hne_uv hu hv hwA⟩)

/-- From a SimpleGraph walk in the d-separation graph, build a StaticRoute. -/
noncomputable def staticRoute_of_dSeparationGraph_walk {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} (p : SimpleGraph.Walk (G.dSeparationGraph X Y Z) u v) :
    StaticRoute G X Y Z u v := by
  induction p with
  | nil =>
      exact StaticRoute.nil _
  | cons hAdj _ ih =>
      exact StaticRoute.cons (staticStep_of_dSeparationGraph_adj hAdj) ih

/-- From reachability in the d-separation graph, obtain a StaticRoute (noncomputable). -/
theorem nonemptyStaticRoute_of_dSeparationGraph_reachable
    {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (h : (G.dSeparationGraph X Y Z).Reachable u v) :
    Nonempty (StaticRoute G X Y Z u v) := by
  rcases h with ⟨p⟩
  exact ⟨staticRoute_of_dSeparationGraph_walk p⟩

-- ============================================================
-- Phase 2 & 3: Compiler from StaticRoute to BayesBallPath
-- ============================================================

/-- The arrival direction at the destination of a static step. -/
def StaticStep.nextArrival {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (step : StaticStep G X Y Z u v) : TrailDir :=
  match step with
  | StaticStep.directForward .. => TrailDir.into
  | StaticStep.directBackward .. => TrailDir.outOf
  | StaticStep.moralJump .. => TrailDir.outOf

/-- Count how many bad colliders a static route would have if expanded. -/
noncomputable def countBadColliders {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (arr : TrailDir) (route : StaticRoute G X Y Z x y) : ℕ :=
  match route with
  | StaticRoute.nil _ => 0
  | StaticRoute.cons step rest =>
      let stepBad : ℕ := match step with
        | StaticStep.directForward .. => 0
        | StaticStep.directBackward .. =>
            if arr = TrailDir.into ∧ Disjoint ({x} ∪ descendants G x) Z then 1 else 0
        | StaticStep.moralJump (w := w) .. =>
            if Disjoint ({w} ∪ descendants G w) Z then 1 else 0
      stepBad + countBadColliders step.nextArrival rest

/-- A forward direct step never creates a collider at its source. -/
lemma not_directionalTripleBlocked_forward_of_not_mem_Z {G : DAG} {Z : Finset ℕ}
    {x : ℕ} {arr : TrailDir}
    (hxZ : x ∉ Z) :
    ¬ DirectionalTripleBlocked G Z x arr TrailDir.into := by
  have hnot_coll : ¬ TrailDir.colliderAtCurrent arr TrailDir.into := by
    cases arr <;> simp [TrailDir.colliderAtCurrent]
  simp [DirectionalTripleBlocked, hnot_coll, hxZ]

/-- If countBadColliders is zero, we can construct a BayesBallPath witness. -/
theorem nonemptyBayesBallPath_of_countBadColliders_zero {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    {arr : TrailDir} {route : StaticRoute G X Y Z x y}
    (hzero : countBadColliders arr route = 0) :
    Nonempty (Σ d, BayesBallPath G Z (x, arr) (y, d)) := by
  induction route generalizing arr with
  | nil x => exact ⟨arr, BayesBallPath.nil (x, arr)⟩
  | cons step rest ih =>
      rename_i src mid dst
      have hrest : countBadColliders step.nextArrival rest = 0 := by
        simp [countBadColliders] at hzero
        omega
      rcases ih hrest with ⟨d, p⟩
      cases step with
      | directForward hEdge hu hv =>
          have hsrcZ : src ∉ Z := (Finset.mem_sdiff.mp (by simpa [DAG.dSeparationGraphNodes] using hu)).2
          exact ⟨⟨d, BayesBallPath.cons
            (BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using hEdge)
              (not_directionalTripleBlocked_forward_of_not_mem_Z hsrcZ)) p⟩⟩
      | directBackward hEdge hu hv =>
          have hnot_bad : ¬ (arr = TrailDir.into ∧ Disjoint ({src} ∪ descendants G src) Z) := by
            intro h
            simp [countBadColliders, h] at hzero
            have hsrcZ : src ∉ Z := by
              intro hsrc_mem_Z
              exact (Finset.disjoint_left.mp h.2 (by simp)) hsrc_mem_Z
            have hdescZ : Disjoint (descendants G src) Z := by
              rw [Finset.disjoint_left]
              intro z hzdesc hzZ
              exact (Finset.disjoint_left.mp h.2
                (by exact Finset.mem_union.mpr (Or.inr hzdesc))) hzZ
            exact hzero.1 hsrcZ hdescZ
          have hsrcZ : src ∉ Z := (Finset.mem_sdiff.mp (by simpa [DAG.dSeparationGraphNodes] using hu)).2
          have hopen : ¬ DirectionalTripleBlocked G Z src arr TrailDir.outOf := by
            cases arr with
            | into =>
                have hdis : ¬ Disjoint ({src} ∪ descendants G src) Z := by
                  intro hdis
                  exact hnot_bad ⟨rfl, hdis⟩
                intro hblock
                rcases hblock with hnoncoll | hcoll
                · exact hnoncoll.1 (by simp [TrailDir.colliderAtCurrent])
                · exact hdis hcoll.2
            | outOf =>
                intro hblock
                rcases hblock with hnoncoll | hcoll
                · exact hsrcZ hnoncoll.2
                · cases hcoll.1.1
          exact ⟨⟨d, BayesBallPath.cons
            (BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using hEdge) hopen) p⟩⟩
      | moralJump huw hvw hne hu hv hw =>
          rename_i child
          have hdis : ¬ Disjoint ({child} ∪ descendants G child) Z := by
            intro h
            simp [countBadColliders] at hzero
            have hchildZ : child ∉ Z := by
              intro hchild_mem_Z
              exact (Finset.disjoint_left.mp h (by simp)) hchild_mem_Z
            have hdescZ : Disjoint (descendants G child) Z := by
              rw [Finset.disjoint_left]
              intro z hzdesc hzZ
              exact (Finset.disjoint_left.mp h
                (by exact Finset.mem_union.mpr (Or.inr hzdesc))) hzZ
            exact hzero.1 hchildZ hdescZ
          have hsrcZ : src ∉ Z := (Finset.mem_sdiff.mp (by simpa [DAG.dSeparationGraphNodes] using hu)).2
          have hopen1 : ¬ DirectionalTripleBlocked G Z src arr TrailDir.into := by
            intro hblock
            rcases hblock with hnoncoll | hcoll
            · exact hsrcZ hnoncoll.2
            · have hnot_coll : ¬ TrailDir.colliderAtCurrent arr TrailDir.into := by
                cases arr <;> simp [TrailDir.colliderAtCurrent]
              exact hnot_coll hcoll.1
          have hopen2 : ¬ DirectionalTripleBlocked G Z child TrailDir.into TrailDir.outOf := by
            intro hblock
            rcases hblock with hnoncoll | hcoll
            · exact hnoncoll.1 (by simp [TrailDir.colliderAtCurrent])
            · exact hdis hcoll.2
          exact ⟨⟨d, BayesBallPath.cons
            (BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using huw) hopen1)
            (BayesBallPath.cons
              (BayesBallStep.step (by simpa [TrailDir.edgeIntoCurrent] using hvw) hopen2) p)⟩⟩

end

end DSeparation
