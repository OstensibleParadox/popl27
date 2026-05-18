import DSeparation.DAG.Basic
import DSeparation.DAG.Reachability
import DSeparation.Trail.Blocking

open Finset

namespace DSeparation

noncomputable section

/-! # Concrete DAG Examples

Small checkable DAG instances: a three-node chain, fork, and collider, together
with sample trails and blocking checks.
-/

namespace DAGExamples

/-- The chain `0 → 1 → 2`. -/
def chain3 : DAG :=
  DAG.ofRank ({0, 1, 2} : Finset ℕ) ({(0, 1), (1, 2)} : Finset (ℕ × ℕ)) id
    (by
      intro u v h
      simp at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)
    (by
      intro u v h
      simp at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)

/-- The fork `1 → 0` and `1 → 2`. -/
def fork3 : DAG :=
  DAG.ofRank ({0, 1, 2} : Finset ℕ) ({(1, 0), (1, 2)} : Finset (ℕ × ℕ))
    (fun n => if n = 1 then 0 else 1)
    (by
      intro u v h
      simp at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)
    (by
      intro u v h
      simp at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)

/-- The collider `0 → 1 ← 2`. -/
def collider3 : DAG :=
  DAG.ofRank ({0, 1, 2} : Finset ℕ) ({(0, 1), (2, 1)} : Finset (ℕ × ℕ))
    (fun n => if n = 1 then 1 else 0)
    (by
      intro u v h
      simp at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)
    (by
      intro u v h
      simp at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)

example : parents chain3 1 = {0} := by
  decide

example : children chain3 1 = {2} := by
  decide

example : (chain3.deleteLeaf 2).nodes = ({0, 1} : Finset ℕ) := by
  decide

example : (chain3.deleteLeaf 2).edges = ({(0, 1)} : Finset (ℕ × ℕ)) := by
  decide

example : (chain3.deleteLeaf 2).nodes.card < chain3.nodes.card :=
  DAG.deleteLeaf_card_lt (G := chain3) (v := 2) (by decide)

def chainTrail02 : Trail chain3 0 2 :=
  Trail.forward (u := 0) (w := 1) (v := 2)
    (by
      change (0, 1) ∈ ({(0, 1), (1, 2)} : Finset (ℕ × ℕ))
      simp)
    (Trail.forward (u := 1) (w := 2) (v := 2)
      (by
        change (1, 2) ∈ ({(0, 1), (1, 2)} : Finset (ℕ × ℕ))
        simp)
      (Trail.nil 2))

example : chainTrail02.isBlocked ({1} : Finset ℕ) := by
  unfold Trail.isBlocked TrailBlocked TripleBlocked TripleCollider HasTriple
  refine ⟨0, 1, 2, ?_, ?_⟩
  · refine ⟨[], [], ?_⟩
    simp [chainTrail02, Trail.toList]
  · left
    constructor
    · change ¬
        ((0, 1) ∈ ({(0, 1), (1, 2)} : Finset (ℕ × ℕ)) ∧
          (2, 1) ∈ ({(0, 1), (1, 2)} : Finset (ℕ × ℕ)))
      simp
    · simp

def colliderTrail02 : Trail collider3 0 2 :=
  Trail.forward (u := 0) (w := 1) (v := 2)
    (by
      change (0, 1) ∈ ({(0, 1), (2, 1)} : Finset (ℕ × ℕ))
      simp)
    (Trail.backward (u := 1) (w := 2) (v := 2)
      (by
        change (2, 1) ∈ ({(0, 1), (2, 1)} : Finset (ℕ × ℕ))
        simp)
      (Trail.nil 2))

example : colliderTrail02.isBlocked (∅ : Finset ℕ) := by
  unfold Trail.isBlocked TrailBlocked TripleBlocked TripleCollider HasTriple
  refine ⟨0, 1, 2, ?_, ?_⟩
  · refine ⟨[], [], ?_⟩
    simp [colliderTrail02, Trail.toList]
  · right
    constructor
    · change
        (0, 1) ∈ ({(0, 1), (2, 1)} : Finset (ℕ × ℕ)) ∧
          (2, 1) ∈ ({(0, 1), (2, 1)} : Finset (ℕ × ℕ))
      simp
    · simp

end DAGExamples

end

end DSeparation
