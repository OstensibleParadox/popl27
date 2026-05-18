import DSeparation.DAG.Basic
import DSeparation.DAG.Reachability
import DSeparation.DAG.Moralization
import DSeparation.Trail.Basic
import DSeparation.Trail.Blocking
import DSeparation.BayesBall.Basic
import DSeparation.BayesBall.Certified
import DSeparation.MAGWalk
import DSeparation.Equivalence
import DSeparation.ActiveRoute
import DSeparation.Reverse
import DSeparation.Counterexample
import DSeparation.Examples

/-! # DSeparation

Root module for the d-separation formalization. This library provides:

- Finite DAG infrastructure (`DAG` structure, reachability, ancestors, descendants)
- Moralized ancestral graph and the graph-theoretic separation criterion
- Trail blocking and the active-trail predicate
- Bayes-ball state-machine compilation from active trails
- `MAGWalk` as a compressed walk language equivalent to moral-graph reachability
- Soundness theorem: `DAG.dSeparated → dSeparates` under `DisjointSets X Y Z`
- Concrete counterexample showing unrestricted equivalence is false

All proofs are constructive and carry zero sorries.
-/
