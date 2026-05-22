import DSeparation.TraceSynthesis.StaticRoute.Basic

open Finset

namespace DSeparation

noncomputable section

namespace StaticRoute

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

end

end DSeparation
