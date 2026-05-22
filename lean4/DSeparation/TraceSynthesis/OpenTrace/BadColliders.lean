import DSeparation.TraceSynthesis.OpenTrace.Basic

open Finset
open Classical

namespace DSeparation

noncomputable section

/-- Check if a single step is a bad collider given an arrival direction. -/
def isStepBad {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (arrival : TrailDir) (step : StaticStep G X Y Z u v) : Prop :=
  match step with
  | .directForward _ _ _ => False
  | .directBackward _ _ _ => arrival = TrailDir.into ∧ Disjoint ({u} ∪ descendants G u) Z
  | @StaticStep.moralJump _ _ _ _ _ _ w _ _ _ _ _ _ => Disjoint ({w} ∪ descendants G w) Z

/-- Count bad collider obligations created by expanding a static route. -/
noncomputable def countBadColliders {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (arrival : TrailDir) (route : StaticRoute G X Y Z x y) : ℕ :=
  match route with
  | StaticRoute.nil _ => 0
  | StaticRoute.cons step rest =>
      (if isStepBad arrival step then 1 else 0) + countBadColliders step.nextArrival rest

lemma countBadColliders_cons {G : DAG} {X Y Z : Finset ℕ} {u v w : ℕ}
    (arrival : TrailDir) (step : StaticStep G X Y Z u v) (rest : StaticRoute G X Y Z v w) :
    countBadColliders arrival (StaticRoute.cons step rest) =
      (if isStepBad arrival step then 1 else 0) + countBadColliders step.nextArrival rest := by
  rfl

/-- Bad collider count is additive over route append. -/
lemma countBadColliders_append {G : DAG} {X Y Z : Finset ℕ} {u v w : ℕ}
    (arrival : TrailDir) (p : StaticRoute G X Y Z u v) (q : StaticRoute G X Y Z v w) :
    countBadColliders arrival (p.append q) =
    countBadColliders arrival p + countBadColliders (p.finalArrival arrival) q := by
  induction p generalizing arrival with
  | nil _ => simp [StaticRoute.append, StaticRoute.finalArrival, countBadColliders]
  | cons step rest ih =>
      simp [StaticRoute.append, countBadColliders, StaticRoute.finalArrival]
      rw [ih]
      ac_rfl

/-- Backward reachable chains starting with `outOf` have no bad colliders. -/
lemma countBadColliders_ofBackwardReachable_eq_zero
    {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    countBadColliders TrailDir.outOf
      (StaticRoute.ofBackwardReachable hreach hnodes) = 0 := by
  induction v using G.acyclic.induction with
  | h v ih =>
      rw [StaticRoute.ofBackwardReachable_eq]
      split_ifs with h_eq
      · subst h_eq; rfl
      · let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        simp [countBadColliders, isStepBad, StaticStep.nextArrival]
        apply ih step.val step.property.2

/-- Forward reachable chains have no bad colliders. -/
lemma countBadColliders_ofForwardReachable_eq_zero
    {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (arrival : TrailDir)
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    countBadColliders arrival
      (StaticRoute.ofForwardReachable hreach hnodes) = 0 := by
  induction v using G.acyclic.induction with
  | h v ih =>
      rw [StaticRoute.ofForwardReachable_eq]
      split_ifs with h_eq
      · subst h_eq; cases arrival <;> rfl
      · let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        simp [countBadColliders_append, countBadColliders, isStepBad]
        apply ih step.val step.property.2

/-- Backward reachable chains starting with `outOf` maintain `outOf` arrival. -/
lemma finalArrival_ofBackwardReachable {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    StaticRoute.finalArrival TrailDir.outOf (StaticRoute.ofBackwardReachable hreach hnodes) = TrailDir.outOf := by
  induction v using G.acyclic.induction with
  | h v ih =>
      rw [StaticRoute.ofBackwardReachable_eq]
      split_ifs with h_eq
      · subst h_eq; rfl
      · let step := Classical.indefiniteDescription (fun m => Reachable G u m ∧ G.HasEdge m v) (by
          cases hreach with
          | refl => contradiction
          | tail h1 h2 => exact ⟨_, h1, h2⟩)
        simp [StaticRoute.finalArrival, StaticStep.nextArrival]
        apply ih step.val step.property.2

/-- Rerouting to X strictly decreases bad-collider count. -/
lemma countBadColliders_backwardEscape_append_suffix_lt {G : DAG} {X Y Z : Finset ℕ}
    {xNew b child y : ℕ}
    (hreach : Reachable G child xNew)
    (hnodes : ∀ n, Reachable G child n → Reachable G n xNew → n ∈ G.dSeparationGraphNodes X Y Z)
    (hEdge : G.HasEdge b child)
    (hb : b ∈ G.dSeparationGraphNodes X Y Z)
    (suf : StaticRoute G X Y Z b y)
    (hchild : child ∈ G.dSeparationGraphNodes X Y Z) :
    countBadColliders TrailDir.outOf
      ((StaticRoute.ofBackwardReachable hreach hnodes).append
        (StaticRoute.cons (StaticStep.directBackward hEdge hchild hb) suf))
      < 1 + countBadColliders TrailDir.outOf suf := by
  rw [countBadColliders_append, countBadColliders_ofBackwardReachable_eq_zero hreach hnodes]
  rw [finalArrival_ofBackwardReachable hreach hnodes]
  simp [countBadColliders, isStepBad, StaticStep.nextArrival]

/-- Rerouting to Y strictly decreases bad-collider count. -/
lemma countBadColliders_prefix_append_forwardEscape_lt {G : DAG} {X Y Z : Finset ℕ}
    {x a child yNew : ℕ}
    (pre : StaticRoute G X Y Z x a)
    (hpre : countBadColliders TrailDir.outOf pre = 0)
    (hEdge : G.HasEdge a child)
    (ha : a ∈ G.dSeparationGraphNodes X Y Z)
    (hreach : Reachable G child yNew)
    (hnodes : ∀ n, Reachable G child n → Reachable G n yNew → n ∈ G.dSeparationGraphNodes X Y Z)
    (hchild : child ∈ G.dSeparationGraphNodes X Y Z) :
    countBadColliders TrailDir.outOf
      (pre.append (StaticRoute.cons (StaticStep.directForward hEdge ha hchild)
        (StaticRoute.ofForwardReachable hreach hnodes)))
      < 1 + countBadColliders TrailDir.outOf pre := by
  rw [countBadColliders_append, hpre]
  simp [countBadColliders, isStepBad, countBadColliders_ofForwardReachable_eq_zero]

/-- A forward direct step never creates a collider at its source. -/
lemma not_directionalTripleBlocked_forward_of_not_mem_Z {G : DAG} {Z : Finset ℕ}
    {x : ℕ} {arrival : TrailDir}
    (hxZ : x ∉ Z) :
    ¬ DirectionalTripleBlocked G Z x arrival TrailDir.into := by
  have hnotColl : ¬ TrailDir.colliderAtCurrent arrival TrailDir.into := by
    cases arrival <;> simp [TrailDir.colliderAtCurrent]
  simp [DirectionalTripleBlocked, hnotColl, hxZ]

end

end DSeparation
