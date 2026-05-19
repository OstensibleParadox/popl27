import DSeparation.MAGWalk

open Finset

namespace DSeparation

noncomputable section

/-! # Static route IR

Type-valued evidence for walks in the d-separation graph.  This layer keeps the
directed-edge and moral-jump witnesses that are hidden by graph reachability.
-/

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

/-- Every static step gives a MAG walk step. -/
def toMAGWalk {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (step : StaticStep G X Y Z u v) : MAGWalk G X Y Z u v :=
  match step with
  | directForward hEdge hu hv => MAGWalk.single (Or.inl hEdge) hu hv
  | directBackward hEdge hu hv => MAGWalk.single (Or.inr hEdge) hu hv
  | moralJump huw hvw hne hu hv hw => MAGWalk.jump huw hvw hne hu hv hw

/-- Convert a single adjacency in the d-separation graph to a static step. -/
noncomputable def ofDSeparationGraphAdj {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} (h : (G.dSeparationGraph X Y Z).Adj u v) :
    StaticStep G X Y Z u v :=
  Classical.choice (show Nonempty (StaticStep G X Y Z u v) from by
    rcases h with ⟨hu, hv, hmoral⟩
    dsimp [DAG.moralGraph] at hmoral
    rcases hmoral with ⟨_huA, _hvA, _hne, hdir | hrev | hcop⟩
    · have huv : G.HasEdge u v := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at hdir ⊢
        exact hdir.1
      exact ⟨StaticStep.directForward huv hu hv⟩
    · have hvu : G.HasEdge v u := by
        simp only [DAG.ancestralSubgraph, DAG.HasEdge, Finset.mem_filter] at hrev ⊢
        exact hrev.1
      exact ⟨StaticStep.directBackward hvu hu hv⟩
    · rcases hcop with ⟨w, huw', hvw', hne_uv⟩
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

/-- The arrival direction at the destination of a static step. -/
def nextArrival {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (step : StaticStep G X Y Z u v) : TrailDir :=
  match step with
  | StaticStep.directForward .. => TrailDir.into
  | StaticStep.directBackward .. => TrailDir.outOf
  | StaticStep.moralJump .. => TrailDir.outOf

end StaticStep

namespace StaticRoute

/-- Every static route gives a MAG walk. -/
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

lemma append_nil {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (route : StaticRoute G X Y Z x y) :
    route.append (StaticRoute.nil y) = route := by
  induction route with
  | nil _ => rfl
  | cons _ _ ih => dsimp [append]; rw [ih]

lemma append_assoc {G : DAG} {X Y Z : Finset ℕ} {x y z w : ℕ}
    (p : StaticRoute G X Y Z x y) (q : StaticRoute G X Y Z y z) (r : StaticRoute G X Y Z z w) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil _ => rfl
  | cons step rest ih => dsimp [append]; rw [ih]

/-- Length of a static route, measured in static steps. -/
def length {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (route : StaticRoute G X Y Z u v) : ℕ :=
  match route with
  | nil _ => 0
  | cons _ rest => rest.length + 1

/-- The arrival direction at the end of a static route. -/
def finalArrival {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (initialArrival : TrailDir) (route : StaticRoute G X Y Z u v) : TrailDir :=
  match route with
  | nil _ => initialArrival
  | cons step rest => rest.finalArrival step.nextArrival

/-- From a `SimpleGraph.Walk` in the d-separation graph, build a static route. -/
noncomputable def ofDSeparationGraphWalk {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} (p : SimpleGraph.Walk (G.dSeparationGraph X Y Z) u v) :
    StaticRoute G X Y Z u v := by
  induction p with
  | nil =>
      exact StaticRoute.nil _
  | cons hAdj _ ih =>
      exact StaticRoute.cons (StaticStep.ofDSeparationGraphAdj hAdj) ih

/-- Construct a chain of backward directed steps from directed reachability. -/
noncomputable def ofBackwardReachable {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    StaticRoute G X Y Z v u :=
  G.acyclic.fix (C := fun v => Reachable G u v →
      (∀ n, Reachable G u n → Reachable G n v → n ∈ G.dSeparationGraphNodes X Y Z) →
      StaticRoute G X Y Z v u)
    (fun v ih hreach hnodes =>
      if h : u = v then
        h ▸ StaticRoute.nil (G := G) (X := X) (Y := Y) (Z := Z) v
      else
        let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        let m := step.val
        let h_u_m := step.property.1
        let h_m_v := step.property.2
        have h_m_nodes : m ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes m h_u_m (Relation.ReflTransGen.single h_m_v)
        have h_v_nodes : v ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes v hreach .refl
        StaticRoute.cons (StaticStep.directBackward h_m_v h_v_nodes h_m_nodes)
          (ih m h_m_v h_u_m (fun n h1 h2 => hnodes n h1 (h2.trans (.single h_m_v)))))
    v hreach hnodes

/-- Unfolding lemma for `ofBackwardReachable`. -/
lemma ofBackwardReachable_eq {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    ofBackwardReachable hreach hnodes =
      if h : u = v then
        h ▸ StaticRoute.nil (G := G) (X := X) (Y := Y) (Z := Z) v
      else
        let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        let m := step.val
        let h_u_m := step.property.1
        let h_m_v := step.property.2
        have h_m_nodes : m ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes m h_u_m (Relation.ReflTransGen.single h_m_v)
        have h_v_nodes : v ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes v hreach .refl
        StaticRoute.cons (StaticStep.directBackward h_m_v h_v_nodes h_m_nodes)
          (ofBackwardReachable h_u_m (fun n h1 h2 => hnodes n h1 (h2.trans (.single h_m_v)))) := by
  unfold ofBackwardReachable
  rw [WellFounded.fix_eq]

/-- Construct a chain of forward directed steps from directed reachability. -/
noncomputable def ofForwardReachable {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    StaticRoute G X Y Z u v :=
  G.acyclic.fix (C := fun v => Reachable G u v →
      (∀ n, Reachable G u n → Reachable G n v → n ∈ G.dSeparationGraphNodes X Y Z) →
      StaticRoute G X Y Z u v)
    (fun v ih hreach hnodes =>
      if h : u = v then
        h.symm ▸ StaticRoute.nil (G := G) (X := X) (Y := Y) (Z := Z) u
      else
        let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        let m := step.val
        let h_u_m := step.property.1
        let h_m_v := step.property.2
        have h_m_nodes : m ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes m h_u_m (Relation.ReflTransGen.single h_m_v)
        have h_v_nodes : v ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes v hreach .refl
        (ih m h_m_v h_u_m (fun n h1 h2 =>
          hnodes n h1 (h2.trans (.single h_m_v)))).append
          (StaticRoute.cons (StaticStep.directForward h_m_v h_m_nodes h_v_nodes) (.nil v)))
    v hreach hnodes

/-- Unfolding lemma for `ofForwardReachable`. -/
lemma ofForwardReachable_eq {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    ofForwardReachable hreach hnodes =
      if h : u = v then
        h.symm ▸ StaticRoute.nil (G := G) (X := X) (Y := Y) (Z := Z) u
      else
        let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        let m := step.val
        let h_u_m := step.property.1
        let h_m_v := step.property.2
        have h_m_nodes : m ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes m h_u_m (Relation.ReflTransGen.single h_m_v)
        have h_v_nodes : v ∈ G.dSeparationGraphNodes X Y Z :=
          hnodes v hreach .refl
        (ofForwardReachable h_u_m (fun n h1 h2 =>
          hnodes n h1 (h2.trans (.single h_m_v)))).append
          (StaticRoute.cons (StaticStep.directForward h_m_v h_m_nodes h_v_nodes) (.nil v)) := by
  unfold ofForwardReachable
  rw [WellFounded.fix_eq]

end StaticRoute

/-- From reachability in the d-separation graph, obtain a static route. -/
theorem nonemptyStaticRoute_of_dSeparationGraph_reachable
    {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (h : (G.dSeparationGraph X Y Z).Reachable u v) :
    Nonempty (StaticRoute G X Y Z u v) := by
  rcases h with ⟨p⟩
  exact ⟨StaticRoute.ofDSeparationGraphWalk p⟩

/- Compatibility names for older scratch files. -/
noncomputable def staticStep_of_dSeparationGraph_adj {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} (h : (G.dSeparationGraph X Y Z).Adj u v) :
    StaticStep G X Y Z u v :=
  StaticStep.ofDSeparationGraphAdj h

noncomputable def staticRoute_of_dSeparationGraph_walk {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} (p : SimpleGraph.Walk (G.dSeparationGraph X Y Z) u v) :
    StaticRoute G X Y Z u v :=
  StaticRoute.ofDSeparationGraphWalk p

end

end DSeparation
