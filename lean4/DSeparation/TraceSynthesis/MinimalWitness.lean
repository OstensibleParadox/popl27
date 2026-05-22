import DSeparation.TraceSynthesis.Graph
import DSeparation.TraceSynthesis.OpenTrace

open Finset

namespace DSeparation

noncomputable section

/-! # Minimal bad-collider witnesses

Endpoint-carrying static routes and the `Nat.find` wrapper that reduces
normalization to a local improvement lemma.
-/

/-- A static route between some endpoint in `X` and some endpoint in `Y`. -/
structure StaticRouteWitness (G : DAG) (X Y Z : Finset ℕ) where
  x : ℕ
  hx : x ∈ X
  y : ℕ
  hy : y ∈ Y
  route : StaticRoute G X Y Z x y

namespace StaticRouteWitness

/-- Number of bad collider obligations on a witness when started from `outOf`. -/
noncomputable def badCount {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) : ℕ :=
  countBadColliders TrailDir.outOf w.route

/-- Number of static steps in the witness route. -/
def length {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) : ℕ :=
  w.route.length

end StaticRouteWitness

/-- Global shorthand for the bad-collider count of a witness. -/
noncomputable def routeBadCount {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) : ℕ :=
  w.badCount

/-- There is a route witness with exactly bad-count `n`. -/
def HasRouteBadCount (G : DAG) (X Y Z : Finset ℕ) (n : ℕ) : Prop :=
  ∃ w : StaticRouteWitness G X Y Z, routeBadCount w = n

lemma exists_routeBadCount_of_witness {G : DAG} {X Y Z : Finset ℕ}
    (hwit : ∃ _w : StaticRouteWitness G X Y Z, True) :
    ∃ n, HasRouteBadCount G X Y Z n := by
  rcases hwit with ⟨w, _⟩
  exact ⟨routeBadCount w, w, rfl⟩

/-- The least bad-collider count among all current static route witnesses. -/
noncomputable def minRouteBadCount {G : DAG} {X Y Z : Finset ℕ}
    (hwit : ∃ _w : StaticRouteWitness G X Y Z, True) : ℕ := by
  classical
  exact Nat.find (exists_routeBadCount_of_witness hwit)

/-- A witness whose bad-collider count is minimal. -/
noncomputable def minRouteBadCountWitness {G : DAG} {X Y Z : Finset ℕ}
    (hwit : ∃ _w : StaticRouteWitness G X Y Z, True) :
    StaticRouteWitness G X Y Z := by
  classical
  exact Classical.choose
    (Nat.find_spec (exists_routeBadCount_of_witness hwit))

lemma routeBadCount_minRouteBadCountWitness {G : DAG} {X Y Z : Finset ℕ}
    (hwit : ∃ _w : StaticRouteWitness G X Y Z, True) :
    routeBadCount (minRouteBadCountWitness hwit) = minRouteBadCount hwit := by
  classical
  unfold minRouteBadCountWitness minRouteBadCount
  exact Classical.choose_spec
    (Nat.find_spec (exists_routeBadCount_of_witness hwit))

/-- The selected witness minimizes bad-collider count among all witnesses. -/
theorem minRouteBadCountWitness_minimal {G : DAG} {X Y Z : Finset ℕ}
    (hwit : ∃ _w : StaticRouteWitness G X Y Z, True)
    (w : StaticRouteWitness G X Y Z) :
    routeBadCount (minRouteBadCountWitness hwit) ≤ routeBadCount w := by
  classical
  rw [routeBadCount_minRouteBadCountWitness hwit]
  exact Nat.find_min'
    (exists_routeBadCount_of_witness hwit)
    (show HasRouteBadCount G X Y Z (routeBadCount w) from ⟨w, rfl⟩)

/--
If every nonzero bad-count witness can be improved, then a zero-bad-collider
witness exists.  The missing rerouting proof should discharge `himprove`.
-/
theorem normalized_route_exists_of_improves {G : DAG} {X Y Z : Finset ℕ}
    (hwit : ∃ _w : StaticRouteWitness G X Y Z, True)
    (himprove :
      ∀ w : StaticRouteWitness G X Y Z,
        routeBadCount w ≠ 0 →
          ∃ w' : StaticRouteWitness G X Y Z,
            routeBadCount w' < routeBadCount w) :
    ∃ w : StaticRouteWitness G X Y Z, routeBadCount w = 0 := by
  let wmin := minRouteBadCountWitness hwit
  by_cases hzero : routeBadCount wmin = 0
  · exact ⟨wmin, hzero⟩
  · rcases himprove wmin hzero with ⟨wbetter, hbetter⟩
    have hminimal : routeBadCount wmin ≤ routeBadCount wbetter :=
      minRouteBadCountWitness_minimal hwit wbetter
    omega

end

end DSeparation
