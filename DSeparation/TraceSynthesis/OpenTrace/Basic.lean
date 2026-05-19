import DSeparation.ActiveRoute
import DSeparation.TraceSynthesis.StaticRoute

open Finset
open Classical

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

end

end DSeparation
