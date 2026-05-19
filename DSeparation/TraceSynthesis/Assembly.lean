import DSeparation.TraceSynthesis.MinimalWitness
import DSeparation.TraceSynthesis.Split
import DSeparation.TraceSynthesis.Graph

open Finset

namespace DSeparation

noncomputable section

/-! # Reverse synthesis assembly

Final assembly layer for the reverse direction.  The remaining proof debt is
isolated in `route_improves_of_bad`.
-/

/-- Core structural lemma: any route with bad colliders can be strictly improved. -/
theorem route_improves_of_bad {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) (hbad : routeBadCount w ≠ 0) :
    ∃ w' : StaticRouteWitness G X Y Z, routeBadCount w' < routeBadCount w := by
  -- 1. Extract the first bad collider.
  obtain ⟨s, hroute_eq⟩ := exists_split w.route hbad
  -- 2. Use escape lemma to choose reroute target.
  rcases ancestor_escape s.hchildA s.hbad with ⟨xNew, hxNew, hreachX⟩ | ⟨yNew, hyNew, hreachY⟩
  · -- Case 1: Leak to X. New route: xNew ->* child <- b ->* oldY.
    have hchild : s.child ∈ G.dSeparationGraphNodes X Y Z :=
      bad_child_survives s.hchildA s.hbad
    have hnodes : ∀ n, Reachable G s.child n → Reachable G n xNew → n ∈ G.dSeparationGraphNodes X Y Z :=
      escape_path_survives s.hchildA s.hbad (Finset.mem_union.mpr (Or.inl hxNew))
    use {
      x := xNew, hx := hxNew,
      y := w.y, hy := w.hy,
      route := (StaticRoute.ofBackwardReachable hreachX hnodes).append
        (StaticRoute.cons (StaticStep.directBackward s.hbw hchild s.hb) s.suf)
    }
    -- Use countBadColliders_backwardEscape_append_suffix_lt
    dsimp [routeBadCount, StaticRouteWitness.badCount]
    have hlt := countBadColliders_backwardEscape_append_suffix_lt hreachX hnodes s.hbw s.hb s.suf hchild
    have hbound := s.hcount
    rw [← hroute_eq]
    omega
  · -- Case 2: Leak to Y. New route: oldX ->* a -> child ->* yNew.
    have hchild : s.child ∈ G.dSeparationGraphNodes X Y Z :=
      bad_child_survives s.hchildA s.hbad
    have hnodes : ∀ n, Reachable G s.child n → Reachable G n yNew → n ∈ G.dSeparationGraphNodes X Y Z :=
      escape_path_survives s.hchildA s.hbad (Finset.mem_union.mpr (Or.inr hyNew))
    use {
      x := w.x, hx := w.hx,
      y := yNew, hy := hyNew,
      route := s.pre.append
        (StaticRoute.cons (StaticStep.directForward s.huw s.ha hchild)
          (StaticRoute.ofForwardReachable hreachY hnodes))
    }
    -- Use countBadColliders_prefix_append_forwardEscape_lt
    dsimp [routeBadCount, StaticRouteWitness.badCount]
    have hlt := countBadColliders_prefix_append_forwardEscape_lt s.pre s.hprefixZero s.huw s.ha hreachY hnodes hchild
    have hbound := s.hcount
    rw [← hroute_eq]
    omega

/-- From moral graph reachability to an active trace witness. -/
theorem activeWitness_of_not_dSeparated {G : DAG} {X Y Z : Finset ℕ}
    (hnot : ¬ DAG.dSeparated G X Y Z) :
    ActiveWitness G X Y Z := by
  unfold DAG.dSeparated at hnot
  push Not at hnot
  rcases hnot with ⟨x, hx, y, hy, hreach⟩
  have ⟨route⟩ := nonemptyStaticRoute_of_dSeparationGraph_reachable hreach
  have hwit : ∃ w : StaticRouteWitness G X Y Z, True :=
    ⟨⟨x, hx, y, hy, route⟩, trivial⟩
  rcases normalized_route_exists_of_improves hwit route_improves_of_bad with
    ⟨wmin, hzero⟩
  rcases activeRoute_of_countBadColliders_zero hzero with
    ⟨⟨finalDir, activeRoute⟩⟩
  exact ⟨wmin.x, wmin.hx, wmin.y, wmin.hy, finalDir, ⟨activeRoute⟩⟩

end

end DSeparation
