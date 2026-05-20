import DSeparation.BayesBall.Certified
import DSeparation.DAG.Moralization

open Finset

namespace DSeparation

/--
Reachability in the moralized ancestral graph, packaged as explicit "large
steps": either a direct underlying DAG edge survives deletion of `Z`, or two
co-parents are connected by the moralization jump.
-/
inductive MAGWalk (G : DAG) (X Y Z : Finset ℕ) : ℕ → ℕ → Prop where
  | refl (u : ℕ) : MAGWalk G X Y Z u u
  | single {u v : ℕ}
      (hEdge : G.HasEdge u v ∨ G.HasEdge v u)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      MAGWalk G X Y Z u v
  | jump {u v w : ℕ}
      (huw : G.HasEdge u w)
      (hvw : G.HasEdge v w)
      (hne : u ≠ v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z)
      (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
      MAGWalk G X Y Z u v
  | trans {u v w : ℕ}
      (huv : MAGWalk G X Y Z u v)
      (hvw : MAGWalk G X Y Z v w) :
      MAGWalk G X Y Z u w

end DSeparation
