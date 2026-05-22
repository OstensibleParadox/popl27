import DSeparation.BayesBall.Basic

open Finset

namespace DSeparation

noncomputable section

/-! # ActiveRoute: Stateful Active Paths

An ActiveRoute wraps a BayesBallPath, providing stateful append and conversion
to an unblocked Trail.  Because `BayesBallStep` is `Prop`-valued, we introduce
a parallel `Type`-valued `BayesBallStepT` for the recursive construction.
-/

namespace BayesBallPath

/-- Append two BayesBallPaths at a matching intermediate state. -/
def append {G : DAG} {Z : Finset ℕ} {s t u : ℕ × TrailDir}
    (p : BayesBallPath G Z s t) (q : BayesBallPath G Z t u) :
    BayesBallPath G Z s u :=
  match p with
  | nil _ => q
  | cons step rest => cons step (rest.append q)

end BayesBallPath

/-- Type-valued copy of `BayesBallStep` for computational extraction. -/
inductive BayesBallStepT (G : DAG) (Z : Finset ℕ) :
    ℕ × TrailDir → ℕ × TrailDir → Type where
  | step {v w : ℕ} {arrival departure : TrailDir}
      (hEdge : TrailDir.edgeIntoCurrent G v w departure)
      (hopen : ¬ DirectionalTripleBlocked G Z v arrival departure) :
      BayesBallStepT G Z (v, arrival) (w, departure)

/-- Type-valued copy of `BayesBallPath` for computational extraction. -/
inductive BayesBallPathT (G : DAG) (Z : Finset ℕ) :
    ℕ × TrailDir → ℕ × TrailDir → Type where
  | nil (s : ℕ × TrailDir) : BayesBallPathT G Z s s
  | cons {s t u : ℕ × TrailDir}
      (step : BayesBallStepT G Z s t)
      (rest : BayesBallPathT G Z t u) :
      BayesBallPathT G Z s u

namespace BayesBallPathT

/-- Append two explicit type-valued paths. -/
def append {G : DAG} {Z : Finset ℕ} {s t u : ℕ × TrailDir}
    (p : BayesBallPathT G Z s t) (q : BayesBallPathT G Z t u) :
    BayesBallPathT G Z s u :=
  match p with
  | nil _ => q
  | cons step rest => cons step (rest.append q)

end BayesBallPathT

/-- Convert a `Prop`-valued step to a `Type`-valued step. -/
def bayesBallStepT_of_bayesBallStep {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (step : BayesBallStep G Z s t) : BayesBallStepT G Z s t :=
  Classical.choice (show Nonempty (BayesBallStepT G Z s t) from by
    cases step with
    | step hEdge hopen =>
        exact ⟨BayesBallStepT.step hEdge hopen⟩)

/-- Convert a `Prop`-valued path to a `Type`-valued path. -/
def bayesBallPathT_of_bayesBallPath {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPath G Z s t) : BayesBallPathT G Z s t := by
  induction p with
  | nil s => exact BayesBallPathT.nil s
  | cons step rest ih =>
      exact BayesBallPathT.cons (bayesBallStepT_of_bayesBallStep step) ih

/-- An ActiveRoute is a BayesBallPath packaged as a route witness. -/
structure ActiveRoute (G : DAG) (Z : Finset ℕ)
    (s t : ℕ × TrailDir) : Type where
  path : BayesBallPath G Z s t

namespace ActiveRoute

/-- Append two ActiveRoutes when the intermediate state matches exactly. -/
def append {G : DAG} {Z : Finset ℕ} {s mid t : ℕ × TrailDir}
    (p : ActiveRoute G Z s mid) (q : ActiveRoute G Z mid t) :
    ActiveRoute G Z s t :=
  ⟨p.path.append q.path⟩

/-- Convert a `BayesBallStepT` to a one-edge Trail segment. -/
def trailOfStep {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (step : BayesBallStepT G Z s t) : Trail G s.1 t.1 := by
  cases step with
  | step hEdge hopen =>
      rename_i v w arrival departure
      cases departure
      · exact Trail.forward (by simpa [TrailDir.edgeIntoCurrent] using hEdge) (Trail.nil _)
      · exact Trail.backward (by simpa [TrailDir.edgeIntoCurrent] using hEdge) (Trail.nil _)

/-- Convert a `BayesBallPathT` to a Trail by concatenating edge segments. -/
def toTrailT {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPathT G Z s t) : Trail G s.1 t.1 :=
  match p with
  | BayesBallPathT.nil _ => Trail.nil s.1
  | BayesBallPathT.cons step rest =>
      (trailOfStep step).append (toTrailT rest)

/-- Convert a `BayesBallPath` to a Trail via the type-valued copy. -/
def toTrail {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPath G Z s t) : Trail G s.1 t.1 :=
  toTrailT (bayesBallPathT_of_bayesBallPath p)

/-- The list of a `cons` path starts with the source node. -/
lemma toList_toTrailT_cons {G : DAG} {Z : Finset ℕ} {s t u : ℕ × TrailDir}
    (step : BayesBallStepT G Z s t) (rest : BayesBallPathT G Z t u) :
    (toTrailT (BayesBallPathT.cons step rest)).toList = s.1 :: (toTrailT rest).toList := by
  cases step with
  | step hEdge hopen =>
      rename_i v w arrival departure
      cases departure <;> simp [toTrailT, trailOfStep, Trail.append, Trail.toList]

/-- The list of a constructed trail starts with the path source. -/
lemma toList_toTrailT_starts {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPathT G Z s t) :
    ∃ xs, (toTrailT p).toList = s.1 :: xs := by
  cases p with
  | nil _ =>
      exact ⟨[], by simp [toTrailT, Trail.toList]⟩
  | cons step rest =>
      exact ⟨(toTrailT rest).toList, toList_toTrailT_cons step rest⟩

lemma hasTriple_cons_iff {xs : List ℕ} {x a b c : ℕ} :
    HasTriple (x :: xs) a b c ↔
      (x = a ∧ ∃ post : List ℕ, xs = b :: c :: post) ∨ HasTriple xs a b c := by
  constructor
  · intro h
    rcases h with ⟨pre, post, hlist⟩
    cases pre with
    | nil =>
        simp at hlist
        rcases hlist with ⟨hxa, hxs⟩
        exact Or.inl ⟨hxa, ⟨post, hxs⟩⟩
    | cons p ps =>
        right
        refine ⟨ps, post, ?_⟩
        simp [List.cons_append] at hlist
        exact hlist.2
  · intro h
    rcases h with hhead | htail
    · rcases hhead with ⟨hxa, post, hxs⟩
      refine ⟨[], post, ?_⟩
      simp [hxa, hxs]
    · exact HasTriple.cons htail

/-- Helper: a list of length ≤ 2 contains no triple. -/
lemma not_trailBlocked_of_short_list {G : DAG} {Z : Finset ℕ} {xs : List ℕ}
    (hlen : xs.length ≤ 2) :
    ¬ TrailBlocked G Z xs := by
  intro h
  rcases h with ⟨a, b, c, htriple, habc⟩
  rcases htriple with ⟨pre, post, hlist⟩
  have hlen2 : xs.length ≥ 3 := by
    calc xs.length = (pre ++ a :: b :: c :: post).length := by rw [hlist]
         _ = pre.length + 3 + post.length := by
              simp [List.length_append, List.length_cons]
              omega
         _ ≥ 3 := by omega
  omega

/-- The constructed `Type`-valued trail is never blocked by `Z`. -/
theorem toTrailT_not_blocked {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPathT G Z s t) :
    ¬ (toTrailT p).isBlocked Z := by
  induction p with
  | nil s =>
      simpa [Trail.isBlocked, toTrailT, Trail.toList] using
        (not_trailBlocked_of_short_list (G := G) (Z := Z) (xs := [s.1]) (by simp))
  | cons step rest ih =>
      rename_i start mid finish
      intro hblocked
      unfold Trail.isBlocked at hblocked
      rcases hblocked with ⟨a, b, c, htriple, hblocked_abc⟩
      have htriple' : HasTriple (start.1 :: (toTrailT rest).toList) a b c := by
        simpa [toList_toTrailT_cons step rest] using htriple
      rcases (hasTriple_cons_iff.mp htriple') with hhead | htail
      · rcases hhead with ⟨ha, post, htailList⟩
        cases rest with
        | nil mid =>
            have hlen := congrArg List.length htailList
            simp [toTrailT, Trail.toList] at hlen
        | cons step₂ rest₂ =>
            cases step with
            | step hEdge hopen =>
                cases step₂ with
                | step hEdge₂ hopen₂ =>
                    have hrestList :=
                      toList_toTrailT_cons (BayesBallStepT.step hEdge₂ hopen₂) rest₂
                    rw [hrestList] at htailList
                    injection htailList with hb htailRest
                    rcases toList_toTrailT_starts rest₂ with ⟨xs, hstarts⟩
                    rw [hstarts] at htailRest
                    injection htailRest with hc _
                    subst a
                    subst b
                    subst c
                    exact hopen₂
                      ((directionalTripleBlocked_iff_tripleBlocked hEdge hEdge₂).mpr hblocked_abc)
      · exact ih (by
          unfold Trail.isBlocked
          exact ⟨a, b, c, htail, hblocked_abc⟩)

/-- Every ActiveRoute yields an active (non-blocked) Trail witness. -/
theorem to_activeTrail {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (route : ActiveRoute G Z s t) :
    ∃ tr : Trail G s.1 t.1, ¬ tr.isBlocked Z :=
  ⟨toTrail route.path, toTrailT_not_blocked (bayesBallPathT_of_bayesBallPath route.path)⟩

end ActiveRoute

/-- Existential witness: some `x ∈ X` can reach some `y ∈ Y` via an ActiveRoute
    that starts with direction `outOf` (required when `x ∉ Z`). -/
def ActiveWitness (G : DAG) (X Y Z : Finset ℕ) : Prop :=
  ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧
    ∃ d, Nonempty (ActiveRoute G Z (x, TrailDir.outOf) (y, d))

end

end DSeparation
