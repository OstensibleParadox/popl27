import DSeparation.DAG.Reachability

open Finset

namespace DSeparation

noncomputable section

/-! # Trails and Local Blocking

Core trail syntax, triple predicates, local triple blocking, and directed
Bayes-ball edge orientations.
-/

/-- A list contains the consecutive triple `a, b, c`. -/
def HasTriple (xs : List ℕ) (a b c : ℕ) : Prop :=
  ∃ pre post : List ℕ, xs = pre ++ a :: b :: c :: post

/-- A trail is a finite undirected walk in the underlying graph. -/
inductive Trail (G : DAG) : ℕ → ℕ → Type where
  | nil (v : ℕ) : Trail G v v
  | forward {u w v : ℕ} (h : G.HasEdge u w) (tail : Trail G w v) : Trail G u v
  | backward {u w v : ℕ} (h : G.HasEdge w u) (tail : Trail G w v) : Trail G u v

namespace Trail

/-- Vertices visited by a trail, in order. -/
def toList {G : DAG} : {u v : ℕ} → Trail G u v → List ℕ
  | _, _, nil v => [v]
  | u, _, forward (u := _) (w := _) (v := _) _ tail => u :: toList tail
  | u, _, backward (u := _) (w := _) (v := _) _ tail => u :: toList tail

/-- Vertices visited by a trail as a finite set. -/
def nodes {G : DAG} {u v : ℕ} (t : Trail G u v) : Finset ℕ :=
  t.toList.toFinset

@[simp]
lemma mem_nodes {G : DAG} {u v a : ℕ} {t : Trail G u v} :
    a ∈ t.nodes ↔ a ∈ t.toList := by
  simp [nodes]

/-- If the start of a trail is a graph node, then so is its endpoint. -/
lemma target_mem_graph_nodes_of_source_mem {G : DAG} {u v : ℕ}
    (t : Trail G u v) (hu : u ∈ G.nodes) :
    v ∈ G.nodes := by
  induction t with
  | nil _ =>
      exact hu
  | forward h tail ih =>
      exact ih (G.edges_subset h).2
  | backward h tail ih =>
      exact ih (G.edges_subset h).1

/-- Concatenate two DAG trails. -/
def append {G : DAG} {u v w : ℕ} (p : Trail G u v) (q : Trail G v w) :
    Trail G u w :=
  match p with
  | nil _ => q
  | forward h tail => forward h (tail.append q)
  | backward h tail => backward h (tail.append q)

/-- A directed reachability proof gives a trail following all edges forward. -/
lemma exists_ofReachableForward {G : DAG} {u v : ℕ}
    (h : Reachable G u v) : Nonempty (Trail G u v) := by
  induction h with
  | refl =>
      exact ⟨Trail.nil u⟩
  | tail _ hstep ih =>
      rcases ih with ⟨tail⟩
      exact ⟨tail.append (Trail.forward hstep (Trail.nil _))⟩

/-- A directed reachability proof gives a trail in reverse by traversing edges backward. -/
lemma exists_ofReachableBackward {G : DAG} {u v : ℕ}
    (h : Reachable G u v) : Nonempty (Trail G v u) := by
  induction h with
  | refl =>
      exact ⟨Trail.nil u⟩
  | tail _ hstep ih =>
      rcases ih with ⟨tail⟩
      exact ⟨(Trail.backward hstep (Trail.nil _)).append tail⟩

end Trail

/-- A middle vertex is a collider on the local triple `a-b-c`. -/
def TripleCollider (G : DAG) (a b c : ℕ) : Prop :=
  G.HasEdge a b ∧ G.HasEdge c b

/--
The local triple is blocked by the conditioning set.  Non-colliders are blocked
when conditioned on directly; colliders are blocked unless the collider or one
of its descendants is conditioned on.
-/
def TripleBlocked (G : DAG) (Z : Finset ℕ) (a b c : ℕ) : Prop :=
  (¬ TripleCollider G a b c ∧ b ∈ Z) ∨
    (TripleCollider G a b c ∧ Disjoint ({b} ∪ descendants G b) Z)

/--
Direction of an edge as seen from the vertex being entered.  `into` means the
edge arrow points into the current vertex; `outOf` means the arrow points out of
the current vertex toward the previous one.
-/
inductive TrailDir where
  | into
  | outOf
  deriving DecidableEq

namespace TrailDir

/-- The directed edge orientation by which a trail enters `curr` from `prev`. -/
def edgeIntoCurrent (G : DAG) (prev curr : ℕ) : TrailDir → Prop
  | into => G.HasEdge prev curr
  | outOf => G.HasEdge curr prev

/--
The local triple is a collider exactly when the trail enters the middle vertex
along an incoming arrow and leaves along another arrow into the middle vertex.
-/
def colliderAtCurrent (arrival departure : TrailDir) : Prop :=
  arrival = into ∧ departure = outOf

end TrailDir

/-- Direction-only version of `TripleBlocked`, used by the Bayes-ball scaffold. -/
def DirectionalTripleBlocked (G : DAG) (Z : Finset ℕ) (b : ℕ)
    (arrival departure : TrailDir) : Prop :=
  (¬ TrailDir.colliderAtCurrent arrival departure ∧ b ∈ Z) ∨
    (TrailDir.colliderAtCurrent arrival departure ∧
      Disjoint ({b} ∪ descendants G b) Z)

lemma directionalTripleBlocked_iff_tripleBlocked {G : DAG} {Z : Finset ℕ}
    {a b c : ℕ} {arrival departure : TrailDir}
    (hab : TrailDir.edgeIntoCurrent G a b arrival)
    (hbc : TrailDir.edgeIntoCurrent G b c departure) :
    DirectionalTripleBlocked G Z b arrival departure ↔ TripleBlocked G Z a b c := by
  cases arrival <;> cases departure
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_cb : ¬ G.HasEdge c b := by
      intro hrev
      have hcycle : Relation.TransGen (fun u v => G.HasEdge u v) b b :=
        Relation.TransGen.head hbc (Relation.TransGen.single hrev)
      exact (not_transGen_self_of_wellFounded G.acyclic b) hcycle
    have hnot : ¬ TripleCollider G a b c := fun hcoll => hnot_cb hcoll.2
    simp [DirectionalTripleBlocked, TrailDir.colliderAtCurrent, TripleBlocked, hnot]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hcoll : TripleCollider G a b c := ⟨hab, hbc⟩
    simp [DirectionalTripleBlocked, TrailDir.colliderAtCurrent, TripleBlocked, hcoll]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_ab : ¬ G.HasEdge a b := by
      intro hrev
      have hcycle : Relation.TransGen (fun u v => G.HasEdge u v) b b :=
        Relation.TransGen.head hab (Relation.TransGen.single hrev)
      exact (not_transGen_self_of_wellFounded G.acyclic b) hcycle
    have hnot : ¬ TripleCollider G a b c := fun hcoll => hnot_ab hcoll.1
    simp [DirectionalTripleBlocked, TrailDir.colliderAtCurrent, TripleBlocked, hnot]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_ab : ¬ G.HasEdge a b := by
      intro hrev
      have hcycle : Relation.TransGen (fun u v => G.HasEdge u v) b b :=
        Relation.TransGen.head hab (Relation.TransGen.single hrev)
      exact (not_transGen_self_of_wellFounded G.acyclic b) hcycle
    have hnot : ¬ TripleCollider G a b c := fun hcoll => hnot_ab hcoll.1
    simp [DirectionalTripleBlocked, TrailDir.colliderAtCurrent, TripleBlocked, hnot]

lemma HasTriple.cons {xs : List ℕ} {a b c x : ℕ}
    (h : HasTriple xs a b c) :
    HasTriple (x :: xs) a b c := by
  rcases h with ⟨pre, post, hxs⟩
  exact ⟨x :: pre, post, by simp [hxs, List.cons_append]⟩

lemma HasTriple.head_of_trail {G : DAG} {a b c v : ℕ} (t : Trail G c v) :
    HasTriple (a :: b :: t.toList) a b c := by
  cases t with
  | nil v =>
      exact ⟨[], [], by simp [Trail.toList]⟩
  | forward h tail =>
      exact ⟨[], tail.toList, by simp [Trail.toList]⟩
  | backward h tail =>
      exact ⟨[], tail.toList, by simp [Trail.toList]⟩

end

end DSeparation
