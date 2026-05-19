import DSeparation.TraceSynthesis.OpenTrace

open Finset
open Classical

namespace DSeparation

noncomputable section

/-! # Route splitting

Extraction of the first bad collider from a static route.
-/

/-- Data extracted from the first bad collider in a static route. -/
structure Split (G : DAG) (X Y Z : Finset ℕ) (x y : ℕ) where
  a : ℕ
  b : ℕ
  child : ℕ
  pre : StaticRoute G X Y Z x a
  suf : StaticRoute G X Y Z b y
  huw : G.HasEdge a child
  hbw : G.HasEdge b child
  ha : a ∈ G.dSeparationGraphNodes X Y Z
  hb : b ∈ G.dSeparationGraphNodes X Y Z
  hchildA : child ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)
  hbad : Disjoint ({child} ∪ descendants G child) Z
  hprefixZero : countBadColliders TrailDir.outOf pre = 0
  route : StaticRoute G X Y Z x y
  hcount : countBadColliders TrailDir.outOf pre + 1 + countBadColliders TrailDir.outOf suf ≤ countBadColliders TrailDir.outOf route

/-- Check if a single step is a bad collider given an arrival direction. -/
def isStepBad {G : DAG} {X Y Z : Finset ℕ} {u v : ℕ}
    (arrival : TrailDir) (step : StaticStep G X Y Z u v) : Prop :=
  match step with
  | .directForward _ _ _ => False
  | .directBackward _ _ _ => arrival = TrailDir.into ∧ Disjoint ({u} ∪ descendants G u) Z
  | @StaticStep.moralJump _ _ _ _ _ _ w _ _ _ _ _ _ => Disjoint ({w} ∪ descendants G w) Z

lemma countBadColliders_cons {G : DAG} {X Y Z : Finset ℕ} {u v w : ℕ}
    (arrival : TrailDir) (step : StaticStep G X Y Z u v) (rest : StaticRoute G X Y Z v w) :
    countBadColliders arrival (StaticRoute.cons step rest) =
      (if isStepBad arrival step then 1 else 0) + countBadColliders step.nextArrival rest := by
  cases step <;> simp [countBadColliders, isStepBad]

lemma append_nil {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (route : StaticRoute G X Y Z x y) :
    route.append (StaticRoute.nil y) = route := by
  induction route with
  | nil _ => rfl
  | cons _ _ ih => dsimp [StaticRoute.append]; rw [ih]

lemma append_assoc {G : DAG} {X Y Z : Finset ℕ} {x y z w : ℕ}
    (p : StaticRoute G X Y Z x y) (q : StaticRoute G X Y Z y z) (r : StaticRoute G X Y Z z w) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil _ => rfl
  | cons step rest ih => dsimp [StaticRoute.append]; rw [ih]

lemma finalArrival_into_decomp_aux {G : DAG} {X Y Z : Finset ℕ} {x a : ℕ}
    (arr_init : TrailDir)
    (pre : StaticRoute G X Y Z x a) :
    pre.finalArrival arr_init = TrailDir.into →
    (∃ h : x = a, pre = h ▸ StaticRoute.nil x ∧ arr_init = TrailDir.into) ∨
    ∃ (a' : ℕ) (pre' : StaticRoute G X Y Z x a') (hEdge : G.HasEdge a' a)
      (hu : a' ∈ G.dSeparationGraphNodes X Y Z) (hv : a ∈ G.dSeparationGraphNodes X Y Z),
      pre = pre'.append (StaticRoute.cons (StaticStep.directForward hEdge hu hv) (StaticRoute.nil a)) := by
  induction pre generalizing arr_init with
  | nil _ =>
      intro harr
      exact Or.inl ⟨rfl, rfl, harr⟩
  | cons step rest ih =>
      intro harr
      cases h_rest : rest with
      | nil _ =>
          subst h_rest
          match step with
          | .directForward hEdge hu hv =>
              exact Or.inr ⟨_, StaticRoute.nil _, hEdge, hu, hv, rfl⟩
          | .directBackward _ _ _ =>
              dsimp [StaticRoute.finalArrival, StaticStep.nextArrival] at harr
              contradiction
          | @StaticStep.moralJump _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [StaticRoute.finalArrival, StaticStep.nextArrival] at harr
              contradiction
      | cons step2 rest2 =>
          have harr2 : rest.finalArrival step.nextArrival = TrailDir.into := harr
          rcases ih step.nextArrival harr2 with ⟨h_eq, h_nil, _⟩ | ⟨a', pre', hEdge, hu, hv, hpre'_eq⟩
          · subst h_eq
            rw [h_nil] at h_rest
            contradiction
          · exact Or.inr ⟨a', StaticRoute.cons step pre', hEdge, hu, hv, by
              dsimp [StaticRoute.append]
              rw [← h_rest]
              rw [hpre'_eq]⟩

lemma finalArrival_into_decomp {G : DAG} {X Y Z : Finset ℕ} {x a : ℕ}
    (pre : StaticRoute G X Y Z x a)
    (harr : pre.finalArrival TrailDir.outOf = TrailDir.into) :
    ∃ (a' : ℕ) (pre' : StaticRoute G X Y Z x a') (hEdge : G.HasEdge a' a)
      (hu : a' ∈ G.dSeparationGraphNodes X Y Z) (hv : a ∈ G.dSeparationGraphNodes X Y Z),
      pre = pre'.append (StaticRoute.cons (StaticStep.directForward hEdge hu hv) (StaticRoute.nil a)) := by
  rcases finalArrival_into_decomp_aux TrailDir.outOf pre harr with contra | result
  · rcases contra with ⟨_, _, h_contra⟩
    contradiction
  · exact result

lemma exists_split_aux {G : DAG} {X Y Z : Finset ℕ} {x a y : ℕ}
    (pre : StaticRoute G X Y Z x a)
    (suf : StaticRoute G X Y Z a y)
    (hpre : countBadColliders TrailDir.outOf pre = 0)
    (hroute : countBadColliders TrailDir.outOf (pre.append suf) ≠ 0) :
    ∃ s : Split G X Y Z x y, s.route = pre.append suf := by
  induction len : suf.length generalizing a pre with
  | zero =>
      cases h_suf : suf with
      | nil _ =>
          rw [h_suf, append_nil] at hroute
          exact False.elim (hroute hpre)
      | cons step rest =>
          subst h_suf
          simp [StaticRoute.length] at len
  | succ n ih =>
      cases h_suf : suf with
      | nil _ =>
          subst h_suf
          simp [StaticRoute.length] at len
      | cons step rest =>
          rename_i mid
          have hlen : rest.length = n := by
            subst h_suf
            injection len
          let arr := pre.finalArrival TrailDir.outOf
          have harr_eq : arr = pre.finalArrival TrailDir.outOf := rfl
          by_cases hbad : isStepBad arr step
          · match h_step : step with
            | .directForward _ _ _ =>
                exfalso
                subst h_step
                revert hbad
                dsimp [isStepBad]
                intro h
                cases h
            | .directBackward hEdge hu hv =>
                have harr_into : pre.finalArrival TrailDir.outOf = TrailDir.into := by
                  rw [← harr_eq]
                  exact hbad.1
                rcases finalArrival_into_decomp pre harr_into with ⟨a', pre', hEdge', hu', hv', hpre_eq⟩
                use {
                  a := a', b := mid, child := a,
                  pre := pre', suf := rest,
                  huw := hEdge', hbw := hEdge,
                  ha := hu', hb := hv, hchildA := (Finset.mem_sdiff.mp hv').1,
                  hbad := hbad.2,
                  hprefixZero := by
                    rw [hpre_eq, countBadColliders_append] at hpre
                    omega,
                  route := pre.append suf,
                  hcount := by
                    subst h_suf
                    rw [countBadColliders_append, hpre, zero_add, countBadColliders_cons, if_pos hbad]
                    have hdb_next : step.nextArrival = TrailDir.outOf := by
                      subst h_step
                      rfl
                    simp [StaticStep.nextArrival]
                    have hpre'_zero : countBadColliders TrailDir.outOf pre' = 0 := by
                      rw [hpre_eq, countBadColliders_append] at hpre
                      omega
                    rw [hpre'_zero]
                }
                subst h_suf
                rfl
            | @StaticStep.moralJump _ _ _ _ _ _ w huw hvw hne hu hv hwA =>
                use {
                  a := a, b := mid, child := w,
                  pre := pre, suf := rest,
                  huw := huw, hbw := hvw,
                  ha := hu, hb := hv, hchildA := hwA,
                  hbad := hbad,
                  hprefixZero := hpre,
                  route := pre.append suf,
                  hcount := by
                    subst h_suf
                    rw [countBadColliders_append, hpre, zero_add, countBadColliders_cons, if_pos hbad]
                    have hmj_next : step.nextArrival = TrailDir.outOf := by
                      subst h_step
                      rfl
                    simp [StaticStep.nextArrival]
                }
                subst h_suf
                rfl
          · let pre' := pre.append (StaticRoute.cons step (StaticRoute.nil mid))
            have heq : pre'.append rest = pre.append (StaticRoute.cons step rest) := by
              dsimp [pre']
              rw [append_assoc]
              rfl
            have hbad' : ¬ isStepBad (pre.finalArrival TrailDir.outOf) step := by
              rw [← harr_eq]
              exact hbad
            have hpre' : countBadColliders TrailDir.outOf pre' = 0 := by
              dsimp [pre']
              rw [countBadColliders_append, hpre, zero_add, countBadColliders_cons, if_neg hbad']
              rfl
            have hroute_cons : countBadColliders TrailDir.outOf (pre.append (StaticRoute.cons step rest)) ≠ 0 := by
              rw [← h_suf]
              exact hroute
            have hroute' : countBadColliders TrailDir.outOf (pre'.append rest) ≠ 0 := by
              rw [heq]
              exact hroute_cons
            rcases ih pre' rest hpre' hroute' hlen with ⟨s, hs_route⟩
            use s
            have hs_route' : s.route = pre.append (StaticRoute.cons step rest) := by
              rw [heq] at hs_route
              exact hs_route
            exact hs_route'

/--
If a route has a non-zero bad-collider count, it contains at least one
bad collider that can be extracted as a `Split`.
-/
theorem exists_split {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (route : StaticRoute G X Y Z x y) :
    countBadColliders TrailDir.outOf route ≠ 0 →
    ∃ s : Split G X Y Z x y, s.route = route := by
  intro h
  have heq : route = (StaticRoute.nil x).append route := rfl
  rw [heq] at h
  rcases exists_split_aux (StaticRoute.nil x) route rfl h with ⟨s, hs⟩
  use s
  rw [← heq] at hs
  exact hs

end

end DSeparation
