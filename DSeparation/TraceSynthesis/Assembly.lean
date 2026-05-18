import DSeparation.TraceSynthesis.MinimalWitness

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
  sorry

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
