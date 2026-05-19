import DSeparation.MAGWalk.Basic
import DSeparation.MAGWalk.Lemmas

open Finset

namespace DSeparation

noncomputable section

/-! # MAG Walks

`MAGWalk` is a compressed walk language equivalent to reachability in the
d-separation graph.  It supports single edges, moralization jumps over active
colliders, and transitive composition.  This module also contains the
`BayesBallPath.compress` algorithm that turns a certified Bayes-ball path into a
`MAGWalk`.
-/

namespace BayesBallPath

/--
Compress an explicit Bayes-ball path to a `MAGWalk`, scanning with a two-step
window.  Non-collider windows consume one step as a `MAGWalk.single`; collider
windows of the form `(a, _) → (b, into) → (c, outOf)` consume two steps as one
`MAGWalk.jump`, so the skipped collider `b` need not be present in
`dSeparationGraphNodes`.
-/
def compressWithFuel {G : DAG} {X Y Z : Finset ℕ} :
    (fuel : ℕ) →
    {s t : ℕ × TrailDir} →
    (p : BayesBallPath G Z s t) →
    p.length ≤ fuel →
    s.1 ∈ G.dSeparationGraphNodes X Y Z →
    t.1 ∈ G.dSeparationGraphNodes X Y Z →
    (∀ {q : ℕ × TrailDir}, RequiredState p q →
      q.1 ∈ G.dSeparationGraphNodes X Y Z) →
    MAGWalk G X Y Z s.1 t.1
  | 0, s, _, nil _, _, hs, _, _ =>
      MAGWalk.refl s.1
  | 0, _, _, cons step rest, hfuel, _, _, _ => by
      simp [BayesBallPath.length] at hfuel
  | _ + 1, s, _, nil _, _, hs, _, _ =>
      MAGWalk.refl s.1
  | _ + 1, _, _, cons step (nil _), _, hs, ht, _ =>
      MAGWalk.single_of_bayesBallStep step hs ht
  | fuel + 1, _, _, cons (s := start) (t := mid) step₁
      (cons (s := _) (t := next) step₂ rest), hfuel, hs, ht, hreq => by
      rcases start with ⟨a, arrA⟩
      rcases mid with ⟨b, arrB⟩
      rcases next with ⟨c, arrC⟩
      by_cases hcoll : arrB = TrailDir.into ∧ arrC = TrailDir.outOf
      · have hc : c ∈ G.dSeparationGraphNodes X Y Z :=
          hreq (q := (c, arrC))
            (RequiredState.colliderTarget
              (G := G) (Z := Z) (s := (a, arrA)) (mid := (b, arrB))
              (next := (c, arrC)) (step₁ := step₁) (step₂ := step₂)
              (rest := rest) hcoll)
        rcases hcoll with ⟨harrB, harrC⟩
        subst arrB
        subst arrC
        have hreq_rest :
            ∀ {q : ℕ × TrailDir}, RequiredState rest q →
              q.1 ∈ G.dSeparationGraphNodes X Y Z := by
          intro q hq
          exact hreq (q := q)
            (RequiredState.colliderRest
              (G := G) (Z := Z) (s := (a, arrA))
              (mid := (b, TrailDir.into)) (next := (c, TrailDir.outOf))
              (step₁ := step₁) (step₂ := step₂) (rest := rest)
              ⟨rfl, rfl⟩ hq)
        have hfuel_rest : rest.length ≤ fuel := by
          simp [BayesBallPath.length] at hfuel ⊢
          omega
        exact MAGWalk.trans
          (MAGWalk.jump_of_bayesBall_collider
            (G := G) (X := X) (Y := Y) (Z := Z)
            (a := a) (b := b) (c := c) (arrival := arrA)
            step₁ step₂ hs hc)
          (compressWithFuel fuel rest hfuel_rest hc ht hreq_rest)
      · have hb : b ∈ G.dSeparationGraphNodes X Y Z :=
          hreq (q := (b, arrB))
            (RequiredState.noncolliderTarget
              (G := G) (Z := Z) (s := (a, arrA)) (mid := (b, arrB))
              (next := (c, arrC)) (step₁ := step₁) (step₂ := step₂)
              (rest := rest) hcoll)
        have hreq_tail :
            ∀ {q : ℕ × TrailDir}, RequiredState (cons step₂ rest) q →
              q.1 ∈ G.dSeparationGraphNodes X Y Z := by
          intro q hq
          exact hreq (q := q)
            (RequiredState.noncolliderRest
              (G := G) (Z := Z) (s := (a, arrA)) (mid := (b, arrB))
              (next := (c, arrC)) (step₁ := step₁) (step₂ := step₂)
              (rest := rest) hcoll hq)
        have hfuel_tail : (cons step₂ rest).length ≤ fuel := by
          simp [BayesBallPath.length] at hfuel ⊢
          omega
        exact MAGWalk.trans
          (MAGWalk.single_of_bayesBallStep
            (G := G) (X := X) (Y := Y) (Z := Z)
            (u := a) (v := b) (arrival := arrA) (departure := arrB)
            step₁ hs hb)
          (compressWithFuel fuel (cons step₂ rest) hfuel_tail hb ht hreq_tail)

/-- Fuel-free wrapper for the compressed Bayes-ball path scanner. -/
def compress {G : DAG} {X Y Z : Finset ℕ} {s t : ℕ × TrailDir}
    (p : BayesBallPath G Z s t)
    (hs : s.1 ∈ G.dSeparationGraphNodes X Y Z)
    (ht : t.1 ∈ G.dSeparationGraphNodes X Y Z)
    (hreq : ∀ {q : ℕ × TrailDir}, RequiredState p q →
      q.1 ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z s.1 t.1 :=
  compressWithFuel p.length p le_rfl hs ht hreq

end BayesBallPath

lemma magWalk_of_bayesBall_pair {G : DAG} {X Y Z : Finset ℕ}
    {s t : ℕ × TrailDir}
    (h_bb : BayesBallReachable G Z s t)
    (hmem : ∀ {n : ℕ} {d : TrailDir},
      BayesBallReachable G Z s (n, d) →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z s.1 t.1 := by
  induction h_bb with
  | refl =>
      exact MAGWalk.refl s.1
  | tail hreach hstep ih =>
      rename_i current target
      rcases current with ⟨n, arrival⟩
      rcases target with ⟨w, departure⟩
      cases hstep with
      | step hEdge hopen =>
          have hn : n ∈ G.dSeparationGraphNodes X Y Z := hmem hreach
          have hnext :
              BayesBallReachable G Z s (w, departure) :=
            hreach.trans (Relation.ReflTransGen.single
              (BayesBallStep.step (G := G) (Z := Z) hEdge hopen))
          have hw : w ∈ G.dSeparationGraphNodes X Y Z := hmem hnext
          exact MAGWalk.trans ih
            (MAGWalk.single_of_bayesBallStep
              (G := G) (X := X) (Y := Y) (Z := Z)
              (u := n) (v := w) (arrival := arrival) (departure := departure)
              (BayesBallStep.step hEdge hopen) hn hw)

lemma magWalk_of_bayesBall {G : DAG} {X Y Z : Finset ℕ}
    {u v : ℕ} {d₁ d₂ : TrailDir}
    (h_bb : BayesBallReachable G Z (u, d₁) (v, d₂))
    (hmem : ∀ {n : ℕ} {d : TrailDir},
      BayesBallReachable G Z (u, d₁) (n, d) →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    MAGWalk G X Y Z u v :=
  magWalk_of_bayesBall_pair h_bb hmem

end

end DSeparation
