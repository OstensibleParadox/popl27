import DSeparation.Trail.Basic.Core

open Finset

namespace DSeparation

noncomputable section

/-! # Bayes-Ball Paths

Bayes-ball steps, reachability, explicit paths, and required-state bookkeeping
for path compression.
-/

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

end

end DSeparation
