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
import DSeparation.InfoTheoryBridge

/-! # DSeparation

Root module for the d-separation formalization. This library provides:

- Finite DAG infrastructure (`DAG` structure, reachability, ancestors, descendants)
- Moralized ancestral graph and the graph-theoretic separation criterion
- Trail blocking and the active-trail predicate
- Bayes-ball state-machine compilation from active trails
- `MAGWalk` as a compressed walk language equivalent to moral-graph reachability
- Grand Equivalence Theorem: `DAG.dSeparated ↔ dSeparates` under `DisjointSets X Y Z`
- Reverse witness-synthesis pipeline for constructive active-trail generation
- Concrete counterexample showing unrestricted equivalence is false
- Scaffold for the Information-Theory bridge to probabilistic conditional independence

The core d-separation theory and Reverse Synthesis pipeline are **fully proved
and verified**.  `InfoTheoryBridge.lean` is an explicit scaffold for the next
integration layer and currently carries the probability-semantics proof debt.
-/
