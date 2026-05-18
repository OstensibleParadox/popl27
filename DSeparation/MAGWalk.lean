import DSeparation.BayesBall.Certified
import DSeparation.DAG.Moralization

open Finset

namespace DSeparation

noncomputable section

/-! # MAG Walks

`MAGWalk` is a compressed walk language equivalent to reachability in the
d-separation graph.  It supports single edges, moralization jumps over active
colliders, and transitive composition.  This module also contains the
`BayesBallPath.compress` algorithm that turns a certified Bayes-ball path into a
`MAGWalk`.
-/

/--
Reachability in the moralized ancestral graph, packaged as explicit "large
steps": either a direct underlying DAG edge survives deletion of `Z`, or two
co-parents are connected by the moralization jump.
-/
inductive MAGWalk (G : DAG) (X Y Z : Finset ℕ) : ℕ → ℕ → Prop where
  | refl (u : ℕ) : MAGWalk G X Y Z u u
  | single {u v : ℕ}
      (hEdge : G.HasEdge u v ∨ G.HasEdge v u)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      MAGWalk G X Y Z u v
  | jump {u v w : ℕ}
      (huw : G.HasEdge u w)
      (hvw : G.HasEdge v w)
      (hne : u ≠ v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z)
      (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
      MAGWalk G X Y Z u v
  | trans {u v w : ℕ}
      (huv : MAGWalk G X Y Z u v)
      (hvw : MAGWalk G X Y Z v w) :
      MAGWalk G X Y Z u w

lemma mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes
    {G : DAG} {X Y Z : Finset ℕ} {v : ℕ}
    (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
    v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
  exact (Finset.mem_sdiff.mp (by simpa [DAG.dSeparationGraphNodes] using hv)).1

lemma dSeparationGraph_adj_of_mag_single {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hEdge : G.HasEdge u v ∨ G.HasEdge v u)
    (hu : u ∈ G.dSeparationGraphNodes X Y Z)
    (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
    (G.dSeparationGraph X Y Z).Adj u v := by
  let S := X ∪ (Y ∪ Z)
  have huA : u ∈ G.ancestralSubgraphNodes S := by
    simpa [S] using mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes (G := G) (X := X)
      (Y := Y) (Z := Z) hu
  have hvA : v ∈ G.ancestralSubgraphNodes S := by
    simpa [S] using mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes (G := G) (X := X)
      (Y := Y) (Z := Z) hv
  have hne : u ≠ v := by
    rcases hEdge with huv | hvu
    · exact G.ne_of_hasEdge huv
    · exact Ne.symm (G.ne_of_hasEdge hvu)
  have huA0 : u ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
    simpa [S, Finset.union_assoc] using huA
  have hvA0 : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
    simpa [S, Finset.union_assoc] using hvA
  refine ⟨hu, hv, ?_⟩
  dsimp [DAG.moralGraph]
  refine ⟨huA0, hvA0, hne, ?_⟩
  rcases hEdge with huv | hvu
  · left
    exact Finset.mem_filter.mpr ⟨by simpa [DAG.HasEdge] using huv, huA0, hvA0⟩
  · right
    left
    exact Finset.mem_filter.mpr ⟨by simpa [DAG.HasEdge] using hvu, hvA0, huA0⟩

lemma dSeparationGraph_adj_of_mag_jump {G : DAG} {X Y Z : Finset ℕ} {u v w : ℕ}
    (huw : G.HasEdge u w)
    (hvw : G.HasEdge v w)
    (hne : u ≠ v)
    (hu : u ∈ G.dSeparationGraphNodes X Y Z)
    (hv : v ∈ G.dSeparationGraphNodes X Y Z)
    (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
    (G.dSeparationGraph X Y Z).Adj u v := by
  let S := X ∪ (Y ∪ Z)
  have huA : u ∈ G.ancestralSubgraphNodes S := by
    simpa [S] using mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes (G := G) (X := X)
      (Y := Y) (Z := Z) hu
  have hvA : v ∈ G.ancestralSubgraphNodes S := by
    simpa [S] using mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes (G := G) (X := X)
      (Y := Y) (Z := Z) hv
  have hwA : w ∈ G.ancestralSubgraphNodes S := by
    simpa [S] using hw
  have huA0 : u ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
    simpa [S, Finset.union_assoc] using huA
  have hvA0 : v ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
    simpa [S, Finset.union_assoc] using hvA
  have hwA0 : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
    simpa [S, Finset.union_assoc] using hwA
  refine ⟨hu, hv, ?_⟩
  dsimp [DAG.moralGraph]
  refine ⟨huA0, hvA0, hne, Or.inr (Or.inr ?_)⟩
  refine ⟨w, ?_, ?_, hne⟩
  · exact Finset.mem_filter.mpr ⟨by simpa [DAG.HasEdge] using huw, huA0, hwA0⟩
  · exact Finset.mem_filter.mpr ⟨by simpa [DAG.HasEdge] using hvw, hvA0, hwA0⟩

theorem MAGWalk.to_dSeparationGraph_reachable {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (h : MAGWalk G X Y Z u v) :
    (G.dSeparationGraph X Y Z).Reachable u v := by
  induction h with
  | refl u =>
      exact SimpleGraph.Reachable.refl u
  | single hEdge hu hv =>
      exact SimpleGraph.Adj.reachable (dSeparationGraph_adj_of_mag_single hEdge hu hv)
  | jump huw hvw hne hu hv hw =>
      exact SimpleGraph.Adj.reachable (dSeparationGraph_adj_of_mag_jump huw hvw hne hu hv hw)
  | trans _ _ ihuv ihvw =>
      exact SimpleGraph.Reachable.trans ihuv ihvw

lemma mag_single_or_jump_of_dSeparationGraph_adj {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (h : (G.dSeparationGraph X Y Z).Adj u v) :
    MAGWalk G X Y Z u v := by
  let S := X ∪ (Y ∪ Z)
  rcases h with ⟨hu, hv, hmoral⟩
  dsimp [DAG.moralGraph] at hmoral
  rcases hmoral with ⟨_, _, hne, hdir | hrev | hcop⟩
  · have hmem :
        (u, v) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes S ∧ e.2 ∈ G.ancestralSubgraphNodes S) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge, S] using hdir
    exact MAGWalk.single (G := G) (X := X) (Y := Y) (Z := Z)
      (Or.inl (by simpa [DAG.HasEdge] using (Finset.mem_filter.mp hmem).1)) hu hv
  · have hmem :
        (v, u) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes S ∧ e.2 ∈ G.ancestralSubgraphNodes S) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge, S] using hrev
    exact MAGWalk.single (G := G) (X := X) (Y := Y) (Z := Z)
      (Or.inr (by simpa [DAG.HasEdge] using (Finset.mem_filter.mp hmem).1)) hu hv
  · rcases hcop with ⟨w, huw', hvw', huw_ne_v⟩
    have huw_mem :
        (u, w) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes S ∧ e.2 ∈ G.ancestralSubgraphNodes S) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge, S] using huw'
    have hvw_mem :
        (v, w) ∈ G.edges.filter (fun e =>
          e.1 ∈ G.ancestralSubgraphNodes S ∧ e.2 ∈ G.ancestralSubgraphNodes S) := by
        simpa [DAG.ancestralSubgraph, DAG.HasEdge, S] using hvw'
    exact MAGWalk.jump (G := G) (X := X) (Y := Y) (Z := Z)
      (by simpa [DAG.HasEdge] using (Finset.mem_filter.mp huw_mem).1)
      (by simpa [DAG.HasEdge] using (Finset.mem_filter.mp hvw_mem).1)
      huw_ne_v hu hv (by
        simpa [S] using (Finset.mem_filter.mp huw_mem).2.2)

theorem MAGWalk.of_dSeparationGraph_reachable {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (h : (G.dSeparationGraph X Y Z).Reachable u v) :
    MAGWalk G X Y Z u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil =>
      exact MAGWalk.refl _
  | cons hAdj _ ih =>
      exact MAGWalk.trans (mag_single_or_jump_of_dSeparationGraph_adj hAdj) ih

theorem magWalk_iff_dSeparationGraph_reachable {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ} :
    MAGWalk G X Y Z u v ↔ (G.dSeparationGraph X Y Z).Reachable u v :=
  ⟨MAGWalk.to_dSeparationGraph_reachable, MAGWalk.of_dSeparationGraph_reachable⟩

lemma MAGWalk.jump_of_active_collider {G : DAG} {X Y Z : Finset ℕ} {u x w : ℕ}
    (hux : G.HasEdge u x)
    (hwx : G.HasEdge w x)
    (hactive : ¬ TripleBlocked G Z u x w)
    (hu : u ∈ G.dSeparationGraphNodes X Y Z)
    (hw : w ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z u w := by
  by_cases huw : u = w
  · subst w
    exact MAGWalk.refl u
  · exact MAGWalk.jump hux hwx huw hu hw
      (collider_mem_ancestralSubgraphNodes_of_active hactive ⟨hux, hwx⟩)

lemma MAGWalk.single_of_bayesBallStep {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} {arrival departure : TrailDir}
    (hstep : BayesBallStep G Z (u, arrival) (v, departure))
    (hu : u ∈ G.dSeparationGraphNodes X Y Z)
    (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z u v := by
  cases hstep with
  | step hEdge _ =>
      cases departure
      · exact MAGWalk.single
          (Or.inl (by simpa [TrailDir.edgeIntoCurrent] using hEdge)) hu hv
      · exact MAGWalk.single
          (Or.inr (by simpa [TrailDir.edgeIntoCurrent] using hEdge)) hu hv

lemma MAGWalk.jump_of_bayesBall_collider {G : DAG} {X Y Z : Finset ℕ}
    {a b c : ℕ} {arrival : TrailDir}
    (hInto : BayesBallStep G Z (a, arrival) (b, TrailDir.into))
    (hOut : BayesBallStep G Z (b, TrailDir.into) (c, TrailDir.outOf))
    (ha : a ∈ G.dSeparationGraphNodes X Y Z)
    (hc : c ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z a c := by
  cases hInto with
  | step hIntoEdge _ =>
      cases hOut with
      | step hOutEdge hOutOpen =>
          have hactive : ¬ TripleBlocked G Z a b c := by
            intro hblocked
            exact hOutOpen
              ((directionalTripleBlocked_iff_tripleBlocked hIntoEdge hOutEdge).mpr hblocked)
          have hcoll : TripleCollider G a b c := by
            exact ⟨by simpa [TrailDir.edgeIntoCurrent] using hIntoEdge,
              by simpa [TrailDir.edgeIntoCurrent] using hOutEdge⟩
          have hb : b ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
            collider_mem_ancestralSubgraphNodes_of_active hactive hcoll
          by_cases hac : a = c
          · subst c
            exact MAGWalk.refl a
          · exact MAGWalk.jump
              (by simpa [TrailDir.edgeIntoCurrent] using hIntoEdge)
              (by simpa [TrailDir.edgeIntoCurrent] using hOutEdge)
              hac ha hc hb

/--
Compressed Bayes-ball-to-MAG step for an active collider.  The middle collider
`b` is not required to survive deletion of `Z`; its active-open premise supplies
ancestral membership, and the MAG step jumps directly from `a` to `c`.
-/
lemma MAGWalk.trans_jump_of_bayesBall_collider {G : DAG} {X Y Z : Finset ℕ}
    {r a b c : ℕ} {arrival : TrailDir}
    (hprefix : MAGWalk G X Y Z r a)
    (hInto : BayesBallStep G Z (a, arrival) (b, TrailDir.into))
    (hOut : BayesBallStep G Z (b, TrailDir.into) (c, TrailDir.outOf))
    (ha : a ∈ G.dSeparationGraphNodes X Y Z)
    (hc : c ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z r c :=
  MAGWalk.trans hprefix
    (MAGWalk.jump_of_bayesBall_collider hInto hOut ha hc)

namespace BayesBallPath

/--
Compress an explicit Bayes-ball path to a `MAGWalk`, scanning with a two-step
window.  Non-collider windows consume one step as a `MAGWalk.single`; collider
windows of the form `(a, _) → (b, into) → (c, outOf)` consume two steps as one
`MAGWalk.jump`, so the skipped collider `b` need not be present in
`dSeparationGraphNodes`.
-/
def compressWithFuel {G : DAG} {X Y Z : Finset ℕ} :
    (fuel : ℕ) →
    {s t : ℕ × TrailDir} →
    (p : BayesBallPath G Z s t) →
    p.length ≤ fuel →
    s.1 ∈ G.dSeparationGraphNodes X Y Z →
    t.1 ∈ G.dSeparationGraphNodes X Y Z →
    (∀ {q : ℕ × TrailDir}, RequiredState p q →
      q.1 ∈ G.dSeparationGraphNodes X Y Z) →
    MAGWalk G X Y Z s.1 t.1
  | 0, s, _, nil _, _, hs, _, _ =>
      MAGWalk.refl s.1
  | 0, _, _, cons step rest, hfuel, _, _, _ => by
      simp [BayesBallPath.length] at hfuel
  | _ + 1, s, _, nil _, _, hs, _, _ =>
      MAGWalk.refl s.1
  | _ + 1, _, _, cons step (nil _), _, hs, ht, _ =>
      MAGWalk.single_of_bayesBallStep step hs ht
  | fuel + 1, _, _, cons (s := start) (t := mid) step₁
      (cons (s := _) (t := next) step₂ rest), hfuel, hs, ht, hreq => by
      rcases start with ⟨a, arrA⟩
      rcases mid with ⟨b, arrB⟩
      rcases next with ⟨c, arrC⟩
      by_cases hcoll : arrB = TrailDir.into ∧ arrC = TrailDir.outOf
      · have hc : c ∈ G.dSeparationGraphNodes X Y Z :=
          hreq (q := (c, arrC))
            (RequiredState.colliderTarget
              (G := G) (Z := Z) (s := (a, arrA)) (mid := (b, arrB))
              (next := (c, arrC)) (step₁ := step₁) (step₂ := step₂)
              (rest := rest) hcoll)
        rcases hcoll with ⟨harrB, harrC⟩
        subst arrB
        subst arrC
        have hreq_rest :
            ∀ {q : ℕ × TrailDir}, RequiredState rest q →
              q.1 ∈ G.dSeparationGraphNodes X Y Z := by
          intro q hq
          exact hreq (q := q)
            (RequiredState.colliderRest
              (G := G) (Z := Z) (s := (a, arrA))
              (mid := (b, TrailDir.into)) (next := (c, TrailDir.outOf))
              (step₁ := step₁) (step₂ := step₂) (rest := rest)
              ⟨rfl, rfl⟩ hq)
        have hfuel_rest : rest.length ≤ fuel := by
          simp [BayesBallPath.length] at hfuel ⊢
          omega
        exact MAGWalk.trans
          (MAGWalk.jump_of_bayesBall_collider
            (G := G) (X := X) (Y := Y) (Z := Z)
            (a := a) (b := b) (c := c) (arrival := arrA)
            step₁ step₂ hs hc)
          (compressWithFuel fuel rest hfuel_rest hc ht hreq_rest)
      · have hb : b ∈ G.dSeparationGraphNodes X Y Z :=
          hreq (q := (b, arrB))
            (RequiredState.noncolliderTarget
              (G := G) (Z := Z) (s := (a, arrA)) (mid := (b, arrB))
              (next := (c, arrC)) (step₁ := step₁) (step₂ := step₂)
              (rest := rest) hcoll)
        have hreq_tail :
            ∀ {q : ℕ × TrailDir}, RequiredState (cons step₂ rest) q →
              q.1 ∈ G.dSeparationGraphNodes X Y Z := by
          intro q hq
          exact hreq (q := q)
            (RequiredState.noncolliderRest
              (G := G) (Z := Z) (s := (a, arrA)) (mid := (b, arrB))
              (next := (c, arrC)) (step₁ := step₁) (step₂ := step₂)
              (rest := rest) hcoll hq)
        have hfuel_tail : (cons step₂ rest).length ≤ fuel := by
          simp [BayesBallPath.length] at hfuel ⊢
          omega
        exact MAGWalk.trans
          (MAGWalk.single_of_bayesBallStep
            (G := G) (X := X) (Y := Y) (Z := Z)
            (u := a) (v := b) (arrival := arrA) (departure := arrB)
            step₁ hs hb)
          (compressWithFuel fuel (cons step₂ rest) hfuel_tail hb ht hreq_tail)

/-- Fuel-free wrapper for the compressed Bayes-ball path scanner. -/
def compress {G : DAG} {X Y Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPath G Z s t)
    (hs : s.1 ∈ G.dSeparationGraphNodes X Y Z)
    (ht : t.1 ∈ G.dSeparationGraphNodes X Y Z)
    (hreq : ∀ {q : ℕ × TrailDir}, RequiredState p q →
      q.1 ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z s.1 t.1 :=
  compressWithFuel p.length p le_rfl hs ht hreq

end BayesBallPath

lemma magWalk_of_bayesBall_pair {G : DAG} {X Y Z : Finset ℕ}
    {s t : ℕ × TrailDir}
    (h_bb : BayesBallReachable G Z s t)
    (hmem : ∀ {n : ℕ} {d : TrailDir},
      BayesBallReachable G Z s (n, d) →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z s.1 t.1 := by
  induction h_bb with
  | refl =>
      exact MAGWalk.refl s.1
  | tail hreach hstep ih =>
      rename_i current target
      rcases current with ⟨n, arrival⟩
      rcases target with ⟨w, departure⟩
      cases hstep with
      | step hEdge hopen =>
          have hn : n ∈ G.dSeparationGraphNodes X Y Z := hmem hreach
          have hnext :
              BayesBallReachable G Z s (w, departure) :=
            hreach.trans (Relation.ReflTransGen.single
              (BayesBallStep.step (G := G) (Z := Z) hEdge hopen))
          have hw : w ∈ G.dSeparationGraphNodes X Y Z := hmem hnext
          exact MAGWalk.trans ih
            (MAGWalk.single_of_bayesBallStep
              (G := G) (X := X) (Y := Y) (Z := Z)
              (u := n) (v := w) (arrival := arrival) (departure := departure)
              (BayesBallStep.step hEdge hopen) hn hw)

lemma magWalk_of_bayesBall {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} {d₁ d₂ : TrailDir}
    (h_bb : BayesBallReachable G Z (u, d₁) (v, d₂))
    (hmem : ∀ {n : ℕ} {d : TrailDir},
      BayesBallReachable G Z (u, d₁) (n, d) →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z u v :=
  magWalk_of_bayesBall_pair h_bb hmem

end

end DSeparation
