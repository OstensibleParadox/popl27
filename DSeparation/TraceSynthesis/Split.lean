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
      cases h_rest_eq : rest with
      | nil _ =>
          subst h_rest_eq
          cases step with
          | directForward hEdge hu hv =>
              exact Or.inr ⟨_, StaticRoute.nil _, hEdge, hu, hv, rfl⟩
          | directBackward _ _ _ =>
              dsimp [StaticRoute.finalArrival, StaticStep.nextArrival] at harr
              contradiction
          | moralJump _ _ _ _ _ _ =>
              dsimp [StaticRoute.finalArrival, StaticStep.nextArrival] at harr
              contradiction
      | cons step2 rest2 =>
          have harr2 : rest.finalArrival step.nextArrival = TrailDir.into := harr
          rcases ih step.nextArrival harr2 with ⟨h_eq, h_nil, _⟩ | ⟨a', pre', hEdge, hu, hv, hpre'_eq⟩
          · subst h_eq
            rw [h_nil] at h_rest_eq
            contradiction
          · exact Or.inr ⟨a', StaticRoute.cons step pre', hEdge, hu, hv, by
              dsimp [StaticRoute.append]
              rw [← h_rest_eq]
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
          rw [h_suf, StaticRoute.append_nil] at hroute
          exact False.elim (hroute hpre)
      | cons _ _ =>
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
          · cases h_step : step with
            | directForward _ _ _ =>
                exfalso
                subst h_step
                revert hbad
                dsimp [isStepBad]
                intro h
                cases h
            | directBackward hEdge hu hv =>
                have harr_into : pre.finalArrival TrailDir.outOf = TrailDir.into := by
                  subst h_step
                  exact hbad.1
                rcases finalArrival_into_decomp pre harr_into with ⟨a', pre', hEdge', hu', hv', hpre_eq⟩
                use {
                  a := a', b := mid, child := a,
                  pre := pre', suf := rest,
                  huw := hEdge', hbw := hEdge,
                  ha := hu', hb := hv, hchildA := (Finset.mem_sdiff.mp hv').1,
                  hbad := by
                    subst h_step
                    exact hbad.2,
                  hprefixZero := by
                    rw [hpre_eq, countBadColliders_append] at hpre
                    omega,
                  route := pre.append suf,
                  hcount := by
                    rw [h_suf, countBadColliders_append, hpre, zero_add, countBadColliders_cons]
                    have h_bad_eval : isStepBad arr step := hbad
                    rw [if_pos h_bad_eval]
                    have h_step_next : step.nextArrival = TrailDir.outOf := by
                      subst h_step
                      rfl
                    rw [h_step_next]
                    have hpre'_zero : countBadColliders TrailDir.outOf pre' = 0 := by
                      rw [hpre_eq, countBadColliders_append] at hpre
                      omega
                    rw [hpre'_zero]
                }
                subst h_suf h_step
                rfl
            | moralJump huw hvw hne hu hv hwA =>
                rename_i child
                use {
                  a := a, b := mid, child := child,
                  pre := pre, suf := rest,
                  huw := huw, hbw := hvw,
                  ha := hu, hb := hv, hchildA := hwA,
                  hbad := by
                    subst h_step
                    exact hbad,
                  hprefixZero := hpre,
                  route := pre.append suf,
                  hcount := by
                    rw [h_suf, countBadColliders_append, hpre, zero_add, countBadColliders_cons]
                    have h_bad_eval : isStepBad arr step := hbad
                    rw [if_pos h_bad_eval]
                    have h_step_next : step.nextArrival = TrailDir.outOf := by
                      subst h_step
                      rfl
                    rw [h_step_next]
                    omega
                }
                subst h_suf h_step
                rfl
          · let pre' := pre.append (StaticRoute.cons step (StaticRoute.nil mid))
            have heq : pre'.append rest = pre.append suf := by
              subst h_suf
              dsimp [pre']
              rw [StaticRoute.append_assoc]
              rfl
            have hpre' : countBadColliders TrailDir.outOf pre' = 0 := by
              dsimp [pre']
              rw [countBadColliders_append, hpre, zero_add, countBadColliders_cons, if_neg hbad]
              rfl
            have hroute' : countBadColliders TrailDir.outOf (pre'.append rest) ≠ 0 := by
              rw [heq]
              exact hroute
            rcases ih pre' rest hpre' hroute' hlen with ⟨s, hs_route⟩
            use s
            subst h_suf
            rw [heq] at hs_route
            exact hs_route

/--
If a route has a non-zero bad-collider count, it contains at least one
bad collider that can be extracted as a `Split`.
-/
theorem exists_split {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (route : StaticRoute G X Y Z x y) :
    countBadColliders TrailDir.outOf route ≠ 0 →
    ∃ s : Split G X Y Z x y, s.route = route := by
  intro h
  rcases exists_split_aux (StaticRoute.nil x) route rfl h with ⟨s, hs⟩
  use s
  exact hs

end

end DSeparation
