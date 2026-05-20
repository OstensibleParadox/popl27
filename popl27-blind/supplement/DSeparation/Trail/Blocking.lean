import DSeparation.Trail.Basic

open Finset

namespace DSeparation

noncomputable section

/-! # Trail Blocking and d-Separation Predicates

Global trail blocking, the `StartOpen` condition for the first Bayes-ball step,
and the high-level d-separation predicates `dSeparates`, `DSeparationQuery`,
and `DisjointSets`.
-/

/-- A trail is blocked if at least one internal triple on it is blocked. -/
def TrailBlocked (G : DAG) (Z : Finset ℕ) (xs : List ℕ) : Prop :=
  ∃ a b c : ℕ, HasTriple xs a b c ∧ TripleBlocked G Z a b c

/-- A trail object is blocked by `Z`. -/
def Trail.isBlocked {G : DAG} {u v : ℕ} (Z : Finset ℕ) (t : Trail G u v) : Prop :=
  TrailBlocked G Z t.toList

/--
Opening condition for the first step of a Bayes-ball run generated from a
trail.  Trail blocking only looks at internal triples, so the first vertex must
be handled separately.
-/
def Trail.StartOpen {G : DAG} {u v : ℕ} (Z : Finset ℕ) (init_dir : TrailDir)
    (t : Trail G u v) : Prop :=
  match t with
  | Trail.nil _ => True
  | Trail.forward (u := u) _ _ =>
      ¬ DirectionalTripleBlocked G Z u init_dir TrailDir.into
  | Trail.backward (u := u) _ _ =>
      ¬ DirectionalTripleBlocked G Z u init_dir TrailDir.outOf

/-- `Z` d-separates node set `X` from node set `Y`. -/
def dSeparates (G : DAG) (X Y Z : Finset ℕ) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → ∀ t : Trail G x y, t.isBlocked Z

/-- Standard domain for a d-separation query: `X`, `Y`, and `Z` are pairwise disjoint. -/
def DSeparationQuery (X Y Z : Finset ℕ) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z

/-- `X`, `Y`, and `Z` are pairwise disjoint.
    This is the standard domain for a d-separation query
    (Oxford Graphical Models §8.3, Theorem 8.1). -/
def DisjointSets (X Y Z : Finset ℕ) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z

/-- `DSeparationQuery` and `DisjointSets` are definitionally equivalent. -/
theorem DSeparationQuery_iff_DisjointSets (X Y Z : Finset ℕ) :
    DSeparationQuery X Y Z ↔ DisjointSets X Y Z :=
  Iff.rfl

lemma TrailBlocked.cons {G : DAG} {Z : Finset ℕ} {xs : List ℕ} {x : ℕ}
    (h : TrailBlocked G Z xs) :
    TrailBlocked G Z (x :: xs) := by
  rcases h with ⟨a, b, c, htriple, hblocked⟩
  exact ⟨a, b, c, HasTriple.cons htriple, hblocked⟩

lemma not_trailBlocked_tail_of_not_trailBlocked_cons {G : DAG} {Z : Finset ℕ}
    {xs : List ℕ} {x : ℕ}
    (h : ¬ TrailBlocked G Z (x :: xs)) :
    ¬ TrailBlocked G Z xs := by
  intro htail
  exact h (TrailBlocked.cons htail)

lemma trailBlocked_of_head_tripleBlocked {G : DAG} {Z : Finset ℕ}
    {a b c : ℕ} {xs : List ℕ}
    (h : TripleBlocked G Z a b c) :
    TrailBlocked G Z (a :: b :: c :: xs) := by
  exact ⟨a, b, c, ⟨[], xs, rfl⟩, h⟩

lemma not_tripleBlocked_head_of_not_trailBlocked {G : DAG} {Z : Finset ℕ}
    {a b c : ℕ} {xs : List ℕ}
    (h : ¬ TrailBlocked G Z (a :: b :: c :: xs)) :
    ¬ TripleBlocked G Z a b c := by
  intro htriple
  exact h (trailBlocked_of_head_tripleBlocked htriple)

lemma trailBlocked_of_head_tripleBlocked_trail {G : DAG} {Z : Finset ℕ}
    {a b c v : ℕ} (t : Trail G c v)
    (h : TripleBlocked G Z a b c) :
    TrailBlocked G Z (a :: b :: t.toList) :=
  ⟨a, b, c, HasTriple.head_of_trail t, h⟩

lemma not_tripleBlocked_head_of_not_trailBlocked_trail {G : DAG} {Z : Finset ℕ}
    {a b c v : ℕ} {t : Trail G c v}
    (h : ¬ TrailBlocked G Z (a :: b :: t.toList)) :
    ¬ TripleBlocked G Z a b c := by
  intro htriple
  exact h (trailBlocked_of_head_tripleBlocked_trail t htriple)

end

end DSeparation
