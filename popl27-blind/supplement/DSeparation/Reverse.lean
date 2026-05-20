import DSeparation.Equivalence

open Finset

namespace DSeparation

noncomputable section

/-! # Reverse Direction Infrastructure

This module starts the converse construction for the textbook equivalence:
turning moral-graph reachability back into an active trail witness.  The first
critical case is singleton co-parent moralization: if `u` and `v` are connected
by a moral edge through a common child `w` in the ancestral graph of
`{u} ∪ {v} ∪ Z`, then acyclicity prevents `w` from being ancestral to either
endpoint.  Hence `w` must be ancestral to `Z`, which opens the collider
`u -> w <- v`.
-/

namespace DAG

lemma not_reachable_source_of_hasEdge {G : DAG} {u v : ℕ}
    (h : G.HasEdge u v) : ¬ Reachable G v u := by
  intro hreach
  have hcycle : Relation.TransGen (fun a b => G.HasEdge a b) u u :=
    Relation.TransGen.head' h hreach
  exact (not_transGen_self_of_wellFounded G.acyclic u) hcycle

end DAG

lemma not_trailBlocked_two {G : DAG} {Z : Finset ℕ} {a b : ℕ} :
    ¬ TrailBlocked G Z [a, b] := by
  intro hblocked
  rcases hblocked with ⟨x, y, z, htriple, _⟩
  rcases htriple with ⟨pre, post, hlist⟩
  have hlen := congrArg List.length hlist
  simp at hlen
  omega

lemma not_trailBlocked_three_of_not_tripleBlocked
    {G : DAG} {Z : Finset ℕ} {a b c : ℕ}
    (hopen : ¬ TripleBlocked G Z a b c) :
    ¬ TrailBlocked G Z [a, b, c] := by
  intro hblocked
  rcases hblocked with ⟨x, y, z, htriple, hxyz⟩
  rcases htriple with ⟨pre, post, hlist⟩
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simp at hlist
          rcases hlist with ⟨rfl, rfl, rfl⟩
          exact hopen hxyz
      | cons p ps =>
          have hlen := congrArg List.length hlist
          simp at hlen
  | cons p ps =>
      have hlen := congrArg List.length hlist
      simp at hlen
      omega

lemma not_isBlocked_forward_single {G : DAG} {Z : Finset ℕ} {u v : ℕ}
    (h : G.HasEdge u v) :
    ¬ (Trail.forward (G := G) (u := u) (w := v) (v := v) h
      (Trail.nil v)).isBlocked Z := by
  simpa [Trail.isBlocked, Trail.toList] using
    (not_trailBlocked_two (G := G) (Z := Z) (a := u) (b := v))

lemma not_isBlocked_backward_single {G : DAG} {Z : Finset ℕ} {u v : ℕ}
    (h : G.HasEdge v u) :
    ¬ (Trail.backward (G := G) (u := u) (w := v) (v := v) h
      (Trail.nil v)).isBlocked Z := by
  simpa [Trail.isBlocked, Trail.toList] using
    (not_trailBlocked_two (G := G) (Z := Z) (a := u) (b := v))

lemma not_disjoint_descendants_of_reachable
    {G : DAG} {Z : Finset ℕ} {w z : ℕ}
    (hwG : w ∈ G.nodes) (hzZ : z ∈ Z) (hreach : Reachable G w z) :
    ¬ Disjoint ({w} ∪ descendants G w) Z := by
  classical
  rw [Finset.disjoint_left]
  push Not
  refine ⟨z, ?_, hzZ⟩
  by_cases hzw : z = w
  · subst z
    simp
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_filter.mpr
        ⟨DAG.target_mem_nodes_of_reachable hreach hwG, hzw, hreach⟩

lemma exists_conditioned_descendant_of_singleton_moral_child
    {G : DAG} {Z : Finset ℕ} {u v w : ℕ}
    (huw : G.HasEdge u w) (hvw : G.HasEdge v w)
    (hwA : w ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) :
    ∃ z, z ∈ Z ∧ Reachable G w z := by
  classical
  rcases Finset.mem_biUnion.mp hwA with ⟨s, hsS, hws⟩
  have hreach_ws : Reachable G w s := (Finset.mem_filter.mp hws).2
  have hs_cases : s = u ∨ s = v ∨ s ∈ Z := by
    simpa using hsS
  rcases hs_cases with rfl | rfl | hsZ
  · exact False.elim ((DAG.not_reachable_source_of_hasEdge huw) hreach_ws)
  · exact False.elim ((DAG.not_reachable_source_of_hasEdge hvw) hreach_ws)
  · exact ⟨s, hsZ, hreach_ws⟩

lemma not_disjoint_descendants_of_singleton_moral_child
    {G : DAG} {Z : Finset ℕ} {u v w : ℕ}
    (huw : G.HasEdge u w) (hvw : G.HasEdge v w)
    (hwA : w ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) :
    ¬ Disjoint ({w} ∪ descendants G w) Z := by
  rcases exists_conditioned_descendant_of_singleton_moral_child
      (G := G) (Z := Z) huw hvw hwA with
    ⟨z, hzZ, hwz⟩
  exact not_disjoint_descendants_of_reachable
    (G := G) (Z := Z) (w := w) (z := z)
    ((G.edges_subset huw).2) hzZ hwz

/--
In the singleton ancestral graph, a co-parent moral edge always unrolls to an
active collider.  The common child cannot be ancestral to either endpoint,
because either case would close a directed cycle with one of the parent edges.
-/
lemma not_tripleBlocked_singleton_moral_collider
    {G : DAG} {Z : Finset ℕ} {u v w : ℕ}
    (huw : G.HasEdge u w) (hvw : G.HasEdge v w)
    (hwA : w ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) :
    ¬ TripleBlocked G Z u w v := by
  intro hblocked
  have hcoll : TripleCollider G u w v := ⟨huw, hvw⟩
  rcases hblocked with hncoll | hcoll_blocked
  · exact hncoll.1 hcoll
  · exact
      (not_disjoint_descendants_of_singleton_moral_child
        (G := G) (Z := Z) huw hvw hwA) hcoll_blocked.2

lemma not_isBlocked_singleton_moral_collider
    {G : DAG} {Z : Finset ℕ} {u v w : ℕ}
    (huw : G.HasEdge u w) (hvw : G.HasEdge v w)
    (hwA : w ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) :
    ¬ (Trail.forward (G := G) (u := u) (w := w) (v := v) huw
      (Trail.backward (G := G) (u := w) (w := v) (v := v) hvw
        (Trail.nil v))).isBlocked Z := by
  simpa [Trail.isBlocked, Trail.toList] using
    not_trailBlocked_three_of_not_tripleBlocked
      (G := G) (Z := Z) (a := u) (b := w) (c := v)
      (not_tripleBlocked_singleton_moral_collider
        (G := G) (Z := Z) huw hvw hwA)

/--
A single moralized adjacency in the singleton query graph has an active-trail
realizer in the original DAG.  Direct moral edges become one-edge trails; a
co-parent moral edge `u -- v` is unrolled to the active collider
`u -> w <- v`.
-/
theorem activeTrail_of_singleton_dSeparationGraph_adj
    {G : DAG} {Z : Finset ℕ} {u v : ℕ}
    (h : (G.dSeparationGraph ({u} : Finset ℕ) ({v} : Finset ℕ) Z).Adj u v) :
    ∃ t : Trail G u v, ¬ t.isBlocked Z := by
  classical
  rcases h with ⟨_, _, hmoral⟩
  dsimp [DAG.moralGraph] at hmoral
  rcases hmoral with ⟨_, _, _, hdir | hrev | hcop⟩
  · have hmem :
        (u, v) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge] using hdir
    have huv : G.HasEdge u v := by
      simpa [DAG.HasEdge] using (Finset.mem_filter.mp hmem).1
    exact ⟨Trail.forward huv (Trail.nil v), not_isBlocked_forward_single huv⟩
  · have hmem :
        (v, u) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge] using hrev
    have hvu : G.HasEdge v u := by
      simpa [DAG.HasEdge] using (Finset.mem_filter.mp hmem).1
    exact ⟨Trail.backward hvu (Trail.nil v), not_isBlocked_backward_single hvu⟩
  · rcases hcop with ⟨w, huw', hvw', _⟩
    have huw_mem :
        (u, w) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge] using huw'
    have hvw_mem :
        (v, w) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z) ∧
            e.2 ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z)) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge] using hvw'
    have huw : G.HasEdge u w := by
      simpa [DAG.HasEdge] using (Finset.mem_filter.mp huw_mem).1
    have hvw : G.HasEdge v w := by
      simpa [DAG.HasEdge] using (Finset.mem_filter.mp hvw_mem).1
    have hwA : w ∈ G.ancestralSubgraphNodes (({u} : Finset ℕ) ∪ ({v} : Finset ℕ) ∪ Z) := by
      exact (Finset.mem_filter.mp huw_mem).2.2
    exact
      ⟨Trail.forward huw (Trail.backward hvw (Trail.nil v)),
        not_isBlocked_singleton_moral_collider
          (G := G) (Z := Z) huw hvw hwA⟩

end

end DSeparation
