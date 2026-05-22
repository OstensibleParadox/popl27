import DSeparation.MAGWalk
import DSeparation.TraceSynthesis.Assembly

open Finset

namespace DSeparation

noncomputable section

/-! # Equivalence: Graph Separation Implies Trail Blocking

The main soundness (completeness) result: under the pairwise-disjoint domain
(`DisjointSets X Y Z`), if the moralized ancestral graph separates `X` from `Y`
after deleting `Z` (`DAG.dSeparated`), then every trail from `X` to `Y` is
blocked by `Z` (`dSeparates`).

Conversely, if separation fails, the reverse trace synthesis pipeline
constructs a certified active trail witness.
-/

theorem dSeparationGraph_reachable_of_active_trail_disjoint
    {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hxX : x ∈ X) (hyY : y ∈ Y)
    (t : Trail G x y) (h_active : ¬ t.isBlocked Z) :
    (G.dSeparationGraph X Y Z).Reachable x y := by
  have hxZ : x ∉ Z := DAG.not_mem_right_of_disjoint_left hXZ hxX
  have hyZ : y ∉ Z := DAG.not_mem_right_of_disjoint_left hYZ hyY
  cases t with
  | nil x =>
      exact SimpleGraph.Reachable.refl x
  | forward h tail =>
      rename_i w
      have hxG : x ∈ G.nodes := (G.edges_subset h).1
      have hyG : y ∈ G.nodes :=
        Trail.target_mem_graph_nodes_of_source_mem
          (Trail.forward (G := G) (u := x) (w := w) (v := y) h tail) hxG
      have hxD : x ∈ G.dSeparationGraphNodes X Y Z :=
        DAG.mem_dSeparationGraphNodes_of_mem_left hxX hxG hxZ
      have hyD : y ∈ G.dSeparationGraphNodes X Y Z :=
        DAG.mem_dSeparationGraphNodes_of_mem_right hyY hyG hyZ
      have hxA : x ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hxD
      rcases bayesBallPathCert_of_active_trail_outOf
          (G := G) (X := X) (Y := Y) (Z := Z)
          (u := x) (v := y)
          (Trail.forward (G := G) (u := x) (w := w) (v := y) h tail)
          h_active hxZ hxA hyD with
        ⟨final_dir, ⟨p, hreq⟩⟩
      exact MAGWalk.to_dSeparationGraph_reachable
        (BayesBallPath.compress
          (G := G) (X := X) (Y := Y) (Z := Z)
          (s := (x, TrailDir.outOf)) (t := (y, final_dir))
          p hxD hyD hreq)
  | backward h tail =>
      rename_i w
      have hxG : x ∈ G.nodes := (G.edges_subset h).2
      have hyG : y ∈ G.nodes :=
        Trail.target_mem_graph_nodes_of_source_mem
          (Trail.backward (G := G) (u := x) (w := w) (v := y) h tail) hxG
      have hxD : x ∈ G.dSeparationGraphNodes X Y Z :=
        DAG.mem_dSeparationGraphNodes_of_mem_left hxX hxG hxZ
      have hyD : y ∈ G.dSeparationGraphNodes X Y Z :=
        DAG.mem_dSeparationGraphNodes_of_mem_right hyY hyG hyZ
      have hxA : x ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hxD
      rcases bayesBallPathCert_of_active_trail_outOf
          (G := G) (X := X) (Y := Y) (Z := Z)
          (u := x) (v := y)
          (Trail.backward (G := G) (u := x) (w := w) (v := y) h tail)
          h_active hxZ hxA hyD with
        ⟨final_dir, ⟨p, hreq⟩⟩
      exact MAGWalk.to_dSeparationGraph_reachable
        (BayesBallPath.compress
          (G := G) (X := X) (Y := Y) (Z := Z)
          (s := (x, TrailDir.outOf)) (t := (y, final_dir))
          p hxD hyD hreq)

theorem dsep_complete_of_endpoint_disjoint
    {G : DAG} {X Y Z : Finset ℕ}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    DAG.dSeparated G X Y Z → dSeparates G X Y Z := by
  intro hdsep x hxX y hyY t
  by_contra h_active
  exact hdsep x hxX y hyY
    (dSeparationGraph_reachable_of_active_trail_disjoint
      (G := G) (X := X) (Y := Y) (Z := Z)
      hXZ hYZ hxX hyY t h_active)

theorem dsep_complete_of_query
    {G : DAG} {X Y Z : Finset ℕ}
    (hquery : DSeparationQuery X Y Z) :
    DAG.dSeparated G X Y Z → dSeparates G X Y Z :=
  dsep_complete_of_endpoint_disjoint hquery.2.1 hquery.2.2

/-- **Soundness of d-separation under pairwise-disjoint domain.**
    If `X`, `Y`, `Z` are pairwise disjoint (`DisjointSets X Y Z`) and the
    moralized ancestral graph separates `X` from `Y` after deleting `Z`
    (`DAG.dSeparated G X Y Z`), then every trail from `X` to `Y` is blocked
    by `Z` (`dSeparates G X Y Z`).

    This is the reliability (completeness) direction: moral-graph separation
    implies trail blocking.  The proof follows the three-stage pipeline:
    1. `bayesBallPath_of_active_trail_outOf` lifts an active trail to a
       Bayes-ball path (possible because endpoint-disjointness keeps the
       start node out of `Z`).
    2. `bayesBallPathCert_of_active_trail_outOf` certifies that every
       `RequiredState` node survives deletion of `Z`.
    3. `BayesBallPath.compress` turns the path into a `MAGWalk`, and
       `MAGWalk.to_dSeparationGraph_reachable` yields reachability in the
       moralized graph, contradicting `DAG.dSeparated`.

    The unrestricted converse is false: see
    `dsep_complete_endpoint_in_Z_counterexample`. -/
theorem dSeparated_of_dSeparated_disjoint
    {G : DAG} {X Y Z : Finset ℕ}
    (hXYZ : DisjointSets X Y Z)
    (hsep : DAG.dSeparated G X Y Z) : dSeparates G X Y Z := by
  exact dsep_complete_of_endpoint_disjoint hXYZ.2.1 hXYZ.2.2 hsep

/-- If an active witness exists, then X and Y are not d-separated by Z. -/
theorem activeWitness_implies_not_dSeparates {G : DAG} {X Y Z : Finset ℕ}
    (w : ActiveWitness G X Y Z) : ¬ dSeparates G X Y Z := by
  rcases w with ⟨x, hx, y, hy, d, ⟨route⟩⟩
  rcases ActiveRoute.to_activeTrail route with ⟨tr, h_active⟩
  intro hsep
  exact h_active (hsep x hx y hy tr)

/-- **Full equivalence of d-separation under pairwise-disjoint domain.**
    `X`, `Y`, and `Z` are pairwise disjoint (`DisjointSets X Y Z`).
    The moralized ancestral graph separates `X` from `Y` after deleting `Z`
    (`DAG.dSeparated G X Y Z`) if and only if every trail from `X` to `Y`
    is blocked by `Z` (`dSeparates G X Y Z`). -/
theorem dSeparated_iff_dSeparates
    {G : DAG} {X Y Z : Finset ℕ} (hXYZ : DisjointSets X Y Z) :
    DAG.dSeparated G X Y Z ↔ dSeparates G X Y Z := by
  constructor
  · exact dSeparated_of_dSeparated_disjoint hXYZ
  · intro hsep
    by_contra hnot
    have hwit := activeWitness_of_not_dSeparated hnot
    exact (activeWitness_implies_not_dSeparates hwit) hsep

end

end DSeparation
