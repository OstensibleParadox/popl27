import DSeparation.DAG.Reachability

open Finset

namespace DSeparation

noncomputable section

/-! # Trails, Triple Blocking, and Bayes-Ball Paths

Trails as undirected walks in a DAG, triple membership, collider detection,
local triple blocking (both vertex-based and direction-based), the Bayes-ball
state machine, explicit Bayes-ball paths, and required-state bookkeeping.
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

/--
Bayes-ball step relation over `(node, arrival-direction)` states.  A step is
available when the edge to the next node has the recorded orientation and the
local direction-only triple at the current node is not blocked by `Z`.
-/
inductive BayesBallStep (G : DAG) (Z : Finset ℕ) :
    ℕ × TrailDir → ℕ × TrailDir → Prop where
  | step {v w : ℕ} {arrival departure : TrailDir}
      (hEdge : TrailDir.edgeIntoCurrent G v w departure)
      (hopen : ¬ DirectionalTripleBlocked G Z v arrival departure) :
      BayesBallStep G Z (v, arrival) (w, departure)

/-- Reachability in the Bayes-ball state graph. -/
def BayesBallReachable (G : DAG) (Z : Finset ℕ)
    (s t : ℕ × TrailDir) : Prop :=
  Relation.ReflTransGen (BayesBallStep G Z) s t

/-- Explicit Bayes-ball paths, used when proofs need a two-step scan window. -/
inductive BayesBallPath (G : DAG) (Z : Finset ℕ) :
    ℕ × TrailDir → ℕ × TrailDir → Type where
  | nil (s : ℕ × TrailDir) : BayesBallPath G Z s s
  | cons {s t u : ℕ × TrailDir}
      (step : BayesBallStep G Z s t)
      (rest : BayesBallPath G Z t u) :
      BayesBallPath G Z s u

namespace BayesBallPath

/-- Number of Bayes-ball steps in an explicit path. -/
def length {G : DAG} {Z : Finset ℕ} :
    {s t : ℕ × TrailDir} → BayesBallPath G Z s t → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ rest => rest.length + 1

/-- Forget an explicit Bayes-ball path to reflexive-transitive reachability. -/
def toReachable {G : DAG} {Z : Finset ℕ} :
    {s t : ℕ × TrailDir} → BayesBallPath G Z s t → BayesBallReachable G Z s t
  | _, _, nil _ => Relation.ReflTransGen.refl
  | _, _, cons step rest => (Relation.ReflTransGen.single step).trans rest.toReachable

/-- Append a final Bayes-ball step to an explicit path. -/
def snoc {G : DAG} {Z : Finset ℕ} {s t u : ℕ × TrailDir}
    (p : BayesBallPath G Z s t) (step : BayesBallStep G Z t u) :
    BayesBallPath G Z s u :=
  match p with
  | nil _ => cons step (nil u)
  | cons head rest => cons head (rest.snoc step)

/--
States whose node-membership proof is required by the compressed path scanner.
For a collider window `(a, _) → (b, into) → (c, outOf)`, the scanner jumps
directly from `a` to `c`, so `b` is deliberately not required here.
-/
inductive RequiredState {G : DAG} {Z : Finset ℕ} :
    {s t : ℕ × TrailDir} → BayesBallPath G Z s t → ℕ × TrailDir → Prop where
  | one {s mid : ℕ × TrailDir} (step : BayesBallStep G Z s mid) :
      RequiredState (BayesBallPath.cons step (BayesBallPath.nil mid)) mid
  | colliderTarget {s mid next finish : ℕ × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      (hcoll : mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) next
  | colliderRest {s mid next finish : ℕ × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      {q : ℕ × TrailDir}
      (hcoll : mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf)
      (hreq : RequiredState rest q) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) q
  | noncolliderTarget {s mid next finish : ℕ × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      (hnot : ¬ (mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf)) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) mid
  | noncolliderRest {s mid next finish : ℕ × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      {q : ℕ × TrailDir}
      (hnot : ¬ (mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf))
      (hreq : RequiredState (BayesBallPath.cons step₂ rest) q) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) q

/-- A first target reached with `outOf` arrival is never a collider target. -/
lemma required_first_target_of_outOf {G : DAG} {Z : Finset ℕ}
    {s mid finish : ℕ × TrailDir}
    (step : BayesBallStep G Z s mid)
    (rest : BayesBallPath G Z mid finish)
    (hmid : mid.2 = TrailDir.outOf) :
    RequiredState (BayesBallPath.cons step rest) mid := by
  cases rest with
  | nil _ =>
      exact RequiredState.one step
  | cons step₂ rest₂ =>
      exact RequiredState.noncolliderTarget (by
        intro hcoll
        rw [hmid] at hcoll
        cases hcoll.1)

/-- Required states of a suffix remain required after an `outOf` first target. -/
lemma required_rest_of_outOf {G : DAG} {Z : Finset ℕ}
    {s mid finish : ℕ × TrailDir}
    (step : BayesBallStep G Z s mid)
    (rest : BayesBallPath G Z mid finish)
    (hmid : mid.2 = TrailDir.outOf)
    {q : ℕ × TrailDir}
    (hreq : RequiredState rest q) :
    RequiredState (BayesBallPath.cons step rest) q := by
  cases rest with
  | nil _ =>
      cases hreq
  | cons step₂ rest₂ =>
      exact RequiredState.noncolliderRest (by
        intro hcoll
        rw [hmid] at hcoll
        cases hcoll.1) hreq

end BayesBallPath

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
