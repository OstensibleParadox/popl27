import DSeparation.Examples
import DSeparation.DAG.Moralization
import DSeparation.Trail.Blocking

open Finset

namespace DSeparation

noncomputable section

/-! # Counterexample: Unrestricted Equivalence is False

If an endpoint lies in the conditioning set `Z`, `DAG.dSeparationGraph` deletes
that endpoint, while the trail predicate still allows the one-edge trail with
no internal triple.  This breaks the unrestricted equivalence between graph
separation and trail blocking.
-/

/--
The unrestricted statement `DAG.dSeparated G X Y Z → dSeparates G X Y Z` is
false for the current public definitions.  If an endpoint is conditioned on,
`DAG.dSeparationGraph` deletes that endpoint, while the trail predicate still
allows the one-edge trail with no internal triple.
-/
theorem dsep_complete_endpoint_in_Z_counterexample :
    ∃ (G : DAG) (X Y Z : Finset ℕ),
      DAG.dSeparated G X Y Z ∧ ¬ dSeparates G X Y Z := by
  classical
  refine ⟨DAGExamples.chain3, ({0} : Finset ℕ), ({1} : Finset ℕ), ({0} : Finset ℕ),
    ?_, ?_⟩
  · intro x hx y hy hreach
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    rcases hreach with ⟨p⟩
    cases p with
    | cons h _ =>
        have h0_not_mem :
            0 ∉ DAGExamples.chain3.dSeparationGraphNodes ({0} : Finset ℕ)
              ({1} : Finset ℕ) ({0} : Finset ℕ) := by
          simp [DAG.dSeparationGraphNodes]
        exact h0_not_mem h.1
  · intro hsep
    have hblocked :
        (Trail.forward (G := DAGExamples.chain3) (u := 0) (w := 1) (v := 1)
          (by
            change (0, 1) ∈ ({(0, 1), (1, 2)} : Finset (ℕ × ℕ))
            simp)
          (Trail.nil 1)).isBlocked ({0} : Finset ℕ) :=
      hsep 0 (by simp) 1 (by simp)
        (Trail.forward (G := DAGExamples.chain3) (u := 0) (w := 1) (v := 1)
          (by
            change (0, 1) ∈ ({(0, 1), (1, 2)} : Finset (ℕ × ℕ))
            simp)
          (Trail.nil 1))
    rcases hblocked with ⟨a, b, c, htriple, _⟩
    rcases htriple with ⟨pre, post, hlist⟩
    have hlen := congrArg List.length hlist
    simp [Trail.toList] at hlen
    omega

theorem not_forall_dsep_complete :
    ¬ ∀ (G : DAG) (X Y Z : Finset ℕ), DAG.dSeparated G X Y Z → dSeparates G X Y Z := by
  intro h
  rcases dsep_complete_endpoint_in_Z_counterexample with ⟨G, X, Y, Z, hdsep, hnot⟩
  exact hnot (h G X Y Z hdsep)

theorem not_forall_dsep_iff :
    ¬ ∀ (G : DAG) (X Y Z : Finset ℕ), dSeparates G X Y Z ↔ DAG.dSeparated G X Y Z := by
  intro h
  rcases dsep_complete_endpoint_in_Z_counterexample with ⟨G, X, Y, Z, hdsep, hnot⟩
  exact hnot ((h G X Y Z).mpr hdsep)

end

end DSeparation
