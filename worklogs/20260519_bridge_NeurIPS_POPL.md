# 2026-05-19 Bridge Memo: NeurIPS Information Theory -> POPL Information-Flow Calculus

This note records the integration boundary between the NeurIPS 2026 verification
stack and the POPL 2027 information-flow core calculus / audit-engine stack.
It is intentionally an engineering map, not a paper section.  In the POPL
framing, d-separation is the graph-semantic substrate for trace compilation and
decompilation; it is not the whole project identity.

## Current State

| Layer | Asset | Status |
|---|---|---|
| Type-safe graph syntax | `DAG`, `DisjointSets` | Present in `popl27`; a surface AST/typechecker would be future paper packaging. |
| Trace semantics / core IR | `Trail -> BayesBallPath -> MAGWalk` and `StaticRoute -> OpenTrace -> ActiveRoute` | Almost complete in `popl27`; one proof debt remains. |
| Quantitative information flow | `FinitePMF`, entropy, KL, CMI, conditional DPI, dual/KKT certificates | Present in `neurips26/verification`; not imported by `popl27`. |

The two codebases are physically separate Lake projects.  Their DAG definitions
are nearly isomorphic, but there is currently no import relation or shared base
module.

## Immediate POPL Blocker

The current local blocker is:

```lean
theorem route_improves_of_bad {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) (hbad : routeBadCount w ≠ 0) :
    ∃ w' : StaticRouteWitness G X Y Z, routeBadCount w' < routeBadCount w
```

Actual file:

```text
DSeparation/TraceSynthesis/Assembly.lean
```

This is the only `sorry` in `DSeparation/`.  Everything else in the reverse
pipeline is already wired around it:

```text
dSeparationGraph.Reachable
  -> StaticRoute
  -> min bad-count StaticRouteWitness
  -> zero-bad StaticRouteWitness
  -> OpenTrace
  -> ActiveRoute
  -> exists Trail, not isBlocked
```

## Current POPL Module Boundaries

Do not add new declarations to `DSeparation/TraceSynthesis.lean`; it is only an
aggregate import.

| Module | Responsibility |
|---|---|
| `TraceSynthesis/Graph.lean` | Graph-only facts needed by normalization, currently `ancestor_escape`. |
| `TraceSynthesis/StaticRoute.lean` | Static IR, MAG-walk bridge, d-separation graph reachability decompilation. |
| `TraceSynthesis/OpenTrace.lean` | `OpenTrace`, `countBadColliders`, zero-bad route compiler. |
| `TraceSynthesis/MinimalWitness.lean` | `StaticRouteWitness`, bad-count minimization, contradiction wrapper. |
| `TraceSynthesis/Assembly.lean` | Final theorem wiring and the remaining `route_improves_of_bad` proof debt. |
| `DAG/Reachability.lean` | Shared graph reachability facts, including `DAG.target_mem_nodes_of_reachable`. |

## Rerouting Proof Plan

The remaining proof should be decomposed into small lemmas before trying to
close `route_improves_of_bad`.

### 1. Directed Chains Do Not Add Bad Colliders

Goal: construct static routes from directed reachability and prove they have
zero bad-collider count.

Candidate interfaces:

```lean
def StaticRoute.ofForwardReachable ...
def StaticRoute.ofBackwardReachable ...

lemma countBadColliders_ofForwardReachable_eq_zero ...
lemma countBadColliders_ofBackwardReachable_eq_zero ...
```

The exact statement must account for node-survival obligations:
every intermediate node in the constructed route must be in
`G.dSeparationGraphNodes X Y Z`.

### 2. Route Splitting Around the First Bad Collider

Goal: from `routeBadCount w ≠ 0`, extract a first offending window:

```text
prefix ++ bad moral jump(a -> child <- b) ++ suffix
```

Required data:

```lean
prefix : StaticRoute G X Y Z w.x a
badStep : StaticStep.moralJump ...
suffix : StaticRoute G X Y Z b w.y
countBadColliders TrailDir.outOf prefix = 0
```

Using the first bad collider is important: it gives a clean strict-decrease
argument without carrying many unrelated previous bad windows.

### 3. Append / Count Accounting

Goal: prove that replacing the segment containing the bad collider strictly
decreases `routeBadCount`.

The useful shape is not necessarily equality.  An inequality is enough:

```lean
countBadColliders arrival (prefix.append suffix)
  <= countBadColliders arrival prefix
     + countBadColliders prefixFinalArrival suffix
     + junctionCost
```

For the intended reroute:

```text
descendant chain cost = 0
junction cost = 0
removed bad moral jump cost = 1
```

Therefore the new witness has smaller bad count.

### 4. Use `ancestor_escape`

Already available:

```lean
lemma ancestor_escape
    (hw : wNode ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hZ : Disjoint ({wNode} ∪ descendants G wNode) Z) :
    (∃ x, x ∈ X ∧ Reachable G wNode x) ∨
      (∃ y, y ∈ Y ∧ Reachable G wNode y)
```

This isolates the graph fact: a bad moral-jump child is ancestral to
`X ∪ Y ∪ Z`, and if its descendant cone misses `Z`, the escape target
must be in `X` or `Y`.

## NeurIPS Bridge

The NeurIPS stack already has the information-theoretic layer:

| Asset | Location | Status |
|---|---|---|
| Entropy, KL, CMI non-negativity | `neurips26/InfoTheory.lean` | Complete. |
| Conditional DPI | `neurips26/InfoTheory.lean` | Complete. |
| Conditional Markov property | `neurips26/InfoTheory.lean` | Present. |
| Trace-gap chain rule | `neurips26/InfoTheoryHelpers` | Present. |
| Additive and static cardinality bounds | `neurips26/DualCertificate.lean` | Present. |
| Cut-set / min-cut / KKT bounds | `neurips26/*` | Structurally present, with external axioms or Markov assumptions. |

The missing bridge is not another entropy library.  The missing bridge is:

```lean
theorem dSeparation_implies_conditional_independence
    (hsep : dSeparates G X Y Z)
    (P : FinitePMF ...)
    (hMarkov : MarkovCompatible P G) :
    ConditionalIndependence P X Y Z
```

Once this exists, NeurIPS cut-set capacity axioms can be attacked by:

```text
d-separation
  -> conditional independence / Markov property
  -> conditional DPI
  -> cut-set mutual-information bound
```

## Priority Order

1. Finish `route_improves_of_bad` in `TraceSynthesis/Assembly.lean`.
2. Keep `popl27` focused on the information-flow core calculus: typed query
   well-formedness, trace optimization, and witness decompilation.
3. Only after the d-separation equivalence is closed, create an integration
   layer for the `neurips26` and `popl27` DAG definitions.
4. Then formalize `d-separation -> conditional independence`.
5. Finally replace NeurIPS cut-set capacity axioms with theorem-level proofs.

## Notes for Future Agents

- Use `scratch/lean-experiments/` for temporary Lean files.
- Do not put new declarations in `DSeparation/TraceSynthesis.lean`.
- Prefer adding small lemmas in the appropriate submodule over extending
  `route_improves_of_bad` directly.
- `lake build DSeparation.TraceSynthesis` is the local regression target.
