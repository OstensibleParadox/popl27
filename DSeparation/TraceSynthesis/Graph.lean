import DSeparation.DAG.Moralization

open Finset

namespace DSeparation

noncomputable section

/-! # Trace-synthesis graph lemmas

Small graph facts used by the reverse trace-synthesis normalization argument.
-/

/--
If `w` is ancestral to `X ∪ Y ∪ Z` but neither `w` nor any descendant of `w`
lies in `Z`, then the ancestral target reached from `w` must lie in `X` or `Y`.
-/
lemma ancestor_escape {G : DAG} {X Y Z : Finset ℕ} {w : ℕ}
    (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hZ : Disjoint ({w} ∪ descendants G w) Z) :
    (∃ x, x ∈ X ∧ Reachable G w x) ∨
      (∃ y, y ∈ Y ∧ Reachable G w y) := by
  classical
  rcases Finset.mem_biUnion.mp hw with ⟨s, hsS, hws⟩
  have hwG : w ∈ G.nodes := (Finset.mem_filter.mp hws).1
  have hwsReach : Reachable G w s := (Finset.mem_filter.mp hws).2
  rcases Finset.mem_union.mp hsS with hsXY | hsZ
  · rcases Finset.mem_union.mp hsXY with hsX | hsY
    · exact Or.inl ⟨s, hsX, hwsReach⟩
    · exact Or.inr ⟨s, hsY, hwsReach⟩
  · have hsCone : s ∈ ({w} ∪ descendants G w) := by
      by_cases hsw : s = w
      · subst s
        simp
      · exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr
            ⟨DAG.target_mem_nodes_of_reachable hwsReach hwG, hsw, hwsReach⟩
    exact False.elim ((Finset.disjoint_left.mp hZ) hsCone hsZ)

end

end DSeparation
