import DSeparation.ActiveRoute
import DSeparation.TraceSynthesis.StaticRoute

open Finset

namespace DSeparation

noncomputable section

/-! # Open traces

The compiler target for static routes before converting to `ActiveRoute`.
Each step stores its oriented DAG traversal and the local non-blocking
obligation needed by Bayes-ball.
-/

/-- An expanded trace that records oriented traversals and local open junctions. -/
inductive OpenTrace (G : DAG) (Z : Finset ℕ) : ℕ × TrailDir → ℕ × TrailDir → Type where
  | nil (s : ℕ × TrailDir) : OpenTrace G Z s s
  | cons {u v w : ℕ} {arrival departure finalDir : TrailDir}
      (hEdge : TrailDir.edgeIntoCurrent G u v departure)
      (hOpen : ¬ DirectionalTripleBlocked G Z u arrival departure)
      (rest : OpenTrace G Z (v, departure) (w, finalDir)) :
      OpenTrace G Z (u, arrival) (w, finalDir)

namespace OpenTrace

/-- Convert an open trace to a propositional Bayes-ball path. -/
def toBayesBallPath {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : OpenTrace G Z s t) : BayesBallPath G Z s t :=
  match p with
  | nil s => BayesBallPath.nil s
  | cons hEdge hOpen rest =>
      BayesBallPath.cons (BayesBallStep.step hEdge hOpen) rest.toBayesBallPath

/-- Convert an open trace to the final `ActiveRoute` witness. -/
def toActiveRoute {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : OpenTrace G Z s t) : ActiveRoute G Z s t :=
  ⟨p.toBayesBallPath⟩

end OpenTrace

/- Compatibility names for older scratch files. -/
def bayesBallPath_of_openTrace {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : OpenTrace G Z s t) : BayesBallPath G Z s t :=
  p.toBayesBallPath

def activeRoute_of_openTrace {G : DAG} {Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : OpenTrace G Z s t) : ActiveRoute G Z s t :=
  p.toActiveRoute

/-- Count bad collider obligations created by expanding a static route. -/
noncomputable def countBadColliders {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    (arrival : TrailDir) (route : StaticRoute G X Y Z x y) : ℕ :=
  match route with
  | StaticRoute.nil _ => 0
  | StaticRoute.cons step rest =>
      let stepBad : ℕ := match step with
        | StaticStep.directForward .. => 0
        | StaticStep.directBackward .. =>
            if arrival = TrailDir.into ∧ Disjoint ({x} ∪ descendants G x) Z then 1 else 0
        | StaticStep.moralJump (w := w) .. =>
            if Disjoint ({w} ∪ descendants G w) Z then 1 else 0
      stepBad + countBadColliders step.nextArrival rest

/-- A forward direct step never creates a collider at its source. -/
lemma not_directionalTripleBlocked_forward_of_not_mem_Z {G : DAG} {Z : Finset ℕ}
    {x : ℕ} {arrival : TrailDir}
    (hxZ : x ∉ Z) :
    ¬ DirectionalTripleBlocked G Z x arrival TrailDir.into := by
  have hnotColl : ¬ TrailDir.colliderAtCurrent arrival TrailDir.into := by
    cases arrival <;> simp [TrailDir.colliderAtCurrent]
  simp [DirectionalTripleBlocked, hnotColl, hxZ]

/-- If `countBadColliders` is zero, a static route compiles to an open trace. -/
theorem openTrace_of_countBadColliders_zero {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    {arrival : TrailDir} {route : StaticRoute G X Y Z x y}
    (hzero : countBadColliders arrival route = 0) :
    Nonempty (Σ finalDir, OpenTrace G Z (x, arrival) (y, finalDir)) := by
  induction route generalizing arrival with
  | nil x => exact ⟨⟨arrival, OpenTrace.nil (x, arrival)⟩⟩
  | cons step rest ih =>
      rename_i src mid dst
      have hrest : countBadColliders step.nextArrival rest = 0 := by
        simp [countBadColliders] at hzero
        omega
      rcases ih hrest with ⟨⟨finalDir, p⟩⟩
      cases step with
      | directForward hEdge hu hv =>
          have hsrcZ : src ∉ Z := (Finset.mem_sdiff.mp (by
            simpa [DAG.dSeparationGraphNodes] using hu)).2
          exact ⟨⟨finalDir, OpenTrace.cons (by
            simpa [TrailDir.edgeIntoCurrent] using hEdge)
            (not_directionalTripleBlocked_forward_of_not_mem_Z hsrcZ) p⟩⟩
      | directBackward hEdge hu hv =>
          have hnotBad :
              ¬ (arrival = TrailDir.into ∧ Disjoint ({src} ∪ descendants G src) Z) := by
            intro h
            simp [countBadColliders, h] at hzero
            have hsrcZ : src ∉ Z := by
              intro hsrcMemZ
              exact (Finset.disjoint_left.mp h.2 (by simp)) hsrcMemZ
            have hdescZ : Disjoint (descendants G src) Z := by
              rw [Finset.disjoint_left]
              intro z hzDesc hzZ
              exact (Finset.disjoint_left.mp h.2
                (by exact Finset.mem_union.mpr (Or.inr hzDesc))) hzZ
            exact hzero.1 hsrcZ hdescZ
          have hsrcZ : src ∉ Z := (Finset.mem_sdiff.mp (by
            simpa [DAG.dSeparationGraphNodes] using hu)).2
          have hopen : ¬ DirectionalTripleBlocked G Z src arrival TrailDir.outOf := by
            cases arrival with
            | into =>
                have hdis : ¬ Disjoint ({src} ∪ descendants G src) Z := by
                  intro hdis
                  exact hnotBad ⟨rfl, hdis⟩
                intro hblock
                rcases hblock with hnoncoll | hcoll
                · exact hnoncoll.1 (by simp [TrailDir.colliderAtCurrent])
                · exact hdis hcoll.2
            | outOf =>
                intro hblock
                rcases hblock with hnoncoll | hcoll
                · exact hsrcZ hnoncoll.2
                · cases hcoll.1.1
          exact ⟨⟨finalDir, OpenTrace.cons (by
            simpa [TrailDir.edgeIntoCurrent] using hEdge) hopen p⟩⟩
      | moralJump huw hvw hne hu hv hw =>
          rename_i child
          have hdis : ¬ Disjoint ({child} ∪ descendants G child) Z := by
            intro h
            simp [countBadColliders] at hzero
            have hchildZ : child ∉ Z := by
              intro hchildMemZ
              exact (Finset.disjoint_left.mp h (by simp)) hchildMemZ
            have hdescZ : Disjoint (descendants G child) Z := by
              rw [Finset.disjoint_left]
              intro z hzDesc hzZ
              exact (Finset.disjoint_left.mp h
                (by exact Finset.mem_union.mpr (Or.inr hzDesc))) hzZ
            exact hzero.1 hchildZ hdescZ
          have hsrcZ : src ∉ Z := (Finset.mem_sdiff.mp (by
            simpa [DAG.dSeparationGraphNodes] using hu)).2
          have hopen1 : ¬ DirectionalTripleBlocked G Z src arrival TrailDir.into := by
            intro hblock
            rcases hblock with hnoncoll | hcoll
            · exact hsrcZ hnoncoll.2
            · have hnotColl : ¬ TrailDir.colliderAtCurrent arrival TrailDir.into := by
                cases arrival <;> simp [TrailDir.colliderAtCurrent]
              exact hnotColl hcoll.1
          have hopen2 :
              ¬ DirectionalTripleBlocked G Z child TrailDir.into TrailDir.outOf := by
            intro hblock
            rcases hblock with hnoncoll | hcoll
            · exact hnoncoll.1 (by simp [TrailDir.colliderAtCurrent])
            · exact hdis hcoll.2
          exact ⟨⟨finalDir, OpenTrace.cons (by
            simpa [TrailDir.edgeIntoCurrent] using huw) hopen1
            (OpenTrace.cons (by
              simpa [TrailDir.edgeIntoCurrent] using hvw) hopen2 p)⟩⟩

/-- A zero-bad-collider static route compiles to an active route witness. -/
theorem activeRoute_of_countBadColliders_zero {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    {arrival : TrailDir} {route : StaticRoute G X Y Z x y}
    (hzero : countBadColliders arrival route = 0) :
    Nonempty (Σ finalDir, ActiveRoute G Z (x, arrival) (y, finalDir)) := by
  rcases openTrace_of_countBadColliders_zero (G := G) (X := X) (Y := Y) (Z := Z)
      (x := x) (y := y) (arrival := arrival) (route := route) hzero with
    ⟨⟨finalDir, trace⟩⟩
  exact ⟨⟨finalDir, trace.toActiveRoute⟩⟩

/-- A zero-bad-collider static route yields an active trail witness. -/
theorem activeTrail_of_countBadColliders_zero {G : DAG} {X Y Z : Finset ℕ} {x y : ℕ}
    {arrival : TrailDir} {route : StaticRoute G X Y Z x y}
    (hzero : countBadColliders arrival route = 0) :
    ∃ _ : TrailDir, ∃ tr : Trail G x y, ¬ tr.isBlocked Z := by
  rcases activeRoute_of_countBadColliders_zero (G := G) (X := X) (Y := Y) (Z := Z)
      (x := x) (y := y) (arrival := arrival) (route := route) hzero with
    ⟨⟨finalDir, route⟩⟩
  rcases ActiveRoute.to_activeTrail route with ⟨tr, htr⟩
  exact ⟨finalDir, tr, htr⟩

end

end DSeparation
