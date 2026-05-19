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
| Trace semantics / core IR | `Trail -> BayesBallPath -> MAGWalk` and `StaticRoute -> OpenTrace -> ActiveRoute` | Complete in `popl27`; Phase 4 normalization and Phase 5 cleanup are closed. |
| Quantitative information flow | `FinitePMF`, entropy, KL, CMI, conditional DPI, dual/KKT certificates | Present in `neurips26/verification`; not imported by `popl27`. |

The two codebases are physically separate Lake projects.  Their DAG definitions
are nearly isomorphic, but there is currently no import relation or shared base
module.

## Immediate POPL Working Area

The high-level Assembly lemma is the intended wiring point:

```lean
theorem route_improves_of_bad {G : DAG} {X Y Z : Finset ℕ}
    (w : StaticRouteWitness G X Y Z) (hbad : routeBadCount w ≠ 0) :
    ∃ w' : StaticRouteWitness G X Y Z, routeBadCount w' < routeBadCount w
```

Actual file:

```text
DSeparation/TraceSynthesis/Assembly.lean
```

The Phase 4 helper work is closed in:

```text
DSeparation/TraceSynthesis/Split.lean   -- exists_split
DSeparation/TraceSynthesis/Graph.lean   -- escape_path_survives
```

The reverse pipeline is intended to run through those helper lemmas:

```text
dSeparationGraph.Reachable
  -> StaticRoute
  -> min bad-count StaticRouteWitness
  -> zero-bad StaticRouteWitness
  -> OpenTrace
  -> ActiveRoute
  -> ∃ Trail, not isBlocked
```

## Current POPL Module Boundaries

Do not add new declarations to `DSeparation/TraceSynthesis.lean`; it is only an
aggregate import.

| Module | Responsibility |
|---|---|
| `TraceSynthesis/Graph.lean` | Graph-only facts needed by normalization, currently `ancestor_escape`. |
| `TraceSynthesis/StaticRoute.lean` | Static IR, append lemmas, MAG-walk bridge, d-separation graph reachability decompilation. |
| `TraceSynthesis/OpenTrace.lean` | `OpenTrace`, `isStepBad`, `countBadColliders`, zero-bad route compiler. |
| `TraceSynthesis/MinimalWitness.lean` | `StaticRouteWitness`, bad-count minimization, contradiction wrapper. |
| `TraceSynthesis/Split.lean` | First-bad-collider extraction and count interface. |
| `TraceSynthesis/Assembly.lean` | Final theorem wiring: `route_improves_of_bad`, `activeWitness_of_not_dSeparated`. |
| `DAG/Reachability.lean` | Shared graph reachability facts, including `DAG.target_mem_nodes_of_reachable`. |

## Completed Rerouting Components

This section is retained as implementation rationale.  The plan has been
completed: directed-chain constructors, bad-count lemmas, splitter extraction,
graph survival, and final assembly all build in `DSeparation.TraceSynthesis`.

Regression command after every moved lemma:

```bash
lake build DSeparation.TraceSynthesis
```

### 1. Directed Chains Do Not Add Bad Colliders

Goal: construct static routes from directed reachability and prove they have
zero bad-collider count.  Put these in
`DSeparation/TraceSynthesis/StaticRoute.lean` and
`DSeparation/TraceSynthesis/OpenTrace.lean`.

Candidate interfaces:

```lean
noncomputable def StaticRoute.ofBackwardReachable
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    StaticRoute G X Y Z v u

lemma countBadColliders_ofBackwardReachable_eq_zero
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    countBadColliders TrailDir.outOf
      (StaticRoute.ofBackwardReachable (G := G) (X := X) (Y := Y) (Z := Z)
        hreach hnodes) = 0
```

Start with the backward version.  It is easier because every step is
`StaticStep.directBackward`, and `countBadColliders TrailDir.outOf` never sees
the `arrival = TrailDir.into` condition.

Then add the forward version:

```lean
noncomputable def StaticRoute.ofForwardReachable
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    StaticRoute G X Y Z u v

lemma countBadColliders_ofForwardReachable_eq_zero
    (arrival : TrailDir)
    (hreach : Reachable G u v)
    (hnodes :
      ∀ n, Reachable G u n → Reachable G n v →
        n ∈ G.dSeparationGraphNodes X Y Z) :
    countBadColliders arrival
      (StaticRoute.ofForwardReachable (G := G) (X := X) (Y := Y) (Z := Z)
        hreach hnodes) = 0
```

The `hnodes` hypothesis is necessary: `StaticStep.directForward` and
`StaticStep.directBackward` require both endpoints to survive in
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

Put the splitter in `TraceSynthesis/MinimalWitness.lean` or a new
`TraceSynthesis/Split.lean` if it grows.  Prefer a structure over a large tuple:

```lean
structure FirstBadMoralJump (G : DAG) (X Y Z : Finset ℕ)
    {x y : ℕ} (route : StaticRoute G X Y Z x y) where
  a : ℕ
  b : ℕ
  child : ℕ
  prefix : StaticRoute G X Y Z x a
  suffix : StaticRoute G X Y Z b y
  huw : G.HasEdge a child
  hbw : G.HasEdge b child
  hne : a ≠ b
  ha : a ∈ G.dSeparationGraphNodes X Y Z
  hb : b ∈ G.dSeparationGraphNodes X Y Z
  hchildA : child ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)
  hbad : Disjoint ({child} ∪ descendants G child) Z
  hprefixZero : countBadColliders TrailDir.outOf prefix = 0
```

Only add route-equality fields if Lean really needs them.  If equality across
dependent endpoints becomes painful, write the splitter as a recursive
procedure that directly returns the data needed to build the improved witness.
The important invariant is that `prefix` is before the first bad collider, so
its bad count is zero.

### 3. Append / Count Accounting

Goal: prove that replacing the segment containing the bad collider strictly
decreases `routeBadCount`.  Put generic append facts near `StaticRoute.append`
or near `countBadColliders`, depending on which imports are needed.

The useful shape is not necessarily equality.  An inequality is enough:

```lean
countBadColliders arrival (prefix.append suffix)
  ≤ countBadColliders arrival prefix
     + countBadColliders prefixFinalArrival suffix
     + junctionCost
```

If `prefixFinalArrival` is awkward, first prove specialized append lemmas for
the two actual reroutes:

```lean
-- leak to X: new route is backward chain xNew -> child, then child -> b,
-- then the old suffix from b to y.
lemma countBadColliders_backwardEscape_append_suffix_lt ...

-- leak to Y: new route is old prefix to a, then a -> child,
-- then forward chain child -> yNew.
lemma countBadColliders_prefix_append_forwardEscape_lt ...
```

For the intended reroute:

```text
descendant chain cost = 0
junction cost = 0
removed bad moral jump cost = 1
```

Therefore the new witness has smaller bad count.

### 4. Use `ancestor_escape` to Choose the Reroute

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

Use cases:

```text
escape to X:
  child ->* xNew, xNew ∈ X
  build route xNew ->* child by backward reachable
  append directBackward for b -> child, then old suffix b -> oldY
  new witness endpoints: xNew ∈ X, oldY ∈ Y

escape to Y:
  child ->* yNew, yNew ∈ Y
  keep old prefix oldX -> a
  append directForward for a -> child, then forward reachable child ->* yNew
  new witness endpoints: oldX ∈ X, yNew ∈ Y
```

The moral-jump step being removed had bad cost `1`.  The replacement chains
have cost `0`, and the arrival direction at the old suffix is still `outOf` in
the X-escape case.  That is the strict decrease needed by
`normalized_route_exists_of_improves`.

### 5. Assembly Status

The final proof in `TraceSynthesis/Assembly.lean` should remain the intended
short dispatcher:

1. destruct `w : StaticRouteWitness`;
2. extract `FirstBadMoralJump w.route` from `hbad`;
3. call `ancestor_escape` on the bad child;
4. build the new witness in the X or Y case;
5. close the strict inequality with the count lemmas and `omega`.

Keep it that way.  The active work is in `Split.exists_split` and
`Graph.escape_path_survives`, not in expanding `Assembly.lean`.

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

1. Treat `TraceSynthesis` as the closed graph-semantics and witness-extraction
   core.
2. Keep `popl27` focused on the information-flow core calculus: typed query
   well-formedness, trace optimization, and witness decompilation.
3. Create an integration layer for the `neurips26` and `popl27` DAG definitions.
4. Then formalize `d-separation -> conditional independence`.
5. Finally replace NeurIPS cut-set capacity axioms with theorem-level proofs.

## Notes for Future Agents

- Use `scratch/lean-experiments/` for temporary Lean files.
- Do not put new declarations in `DSeparation/TraceSynthesis.lean`.
- Prefer adding small lemmas in the appropriate submodule over extending
  `route_improves_of_bad` directly; it is now only wiring.
- `lake build DSeparation.TraceSynthesis` is the local regression target.

## Progress Update (2026-05-19 Evening)

### Completed
- **Step 1 (Directed Chains):** Fully implemented and proved in `StaticRoute.lean` and `OpenTrace.lean`. Directed chains are now correctly established to have zero bad colliders.
- **Step 3 (Count Invariants):** `countBadColliders_append` and strict reduction lemmas for X and Y reroutes are proved.
- **Step 4 & 5 (Assembly):** `route_improves_of_bad` is structurally complete in `Assembly.lean`, successfully using the `Split` interface to close numerical goals.

### Technical Hurdles Resolved
- **Splitter Implementation (Step 2):** `exists_split` is proved in `DSeparation/TraceSynthesis/Split.lean`.
    - The dependent-type mismatch was resolved by length induction and by constructing the absorbed prefix state (`pre'`, `hpre'`, `hroute'`) outside recursive calls.
- **Graph Survival:** `bad_child_survives` and `escape_path_survives` are proved in `Graph.lean`, correctly utilizing the descendant cone property to avoid set Z.
- **Phase 5 cleanup:** structural route lemmas now live in `StaticRoute.lean`; bad-collider count facts now live in `OpenTrace.lean`; `Reverse.lean` uses `DAG.target_mem_nodes_of_reachable`.

## Phase 4 Completion (2026-05-19 Night)

The entire Reverse Synthesis workspace (`DSeparation.TraceSynthesis`) is now **fully proved and verified**. 

### Final Architecture
1. **Normalization by Rerouting:** Proved that any trail in the d-separation graph containing "bad colliders" (illegal Bayes-ball junctions) can be strictly improved into a trail with fewer such junctions.
2. **Constructive Compiler:** The proof chain provides a constructive path from moral-graph reachability to a certified `ActiveRoute`.
3. **Formal Integrity:** The solution resolves all dependent type (`HEq`) hurdles using length-based induction and explicit state construction.

`lake build DSeparation.TraceSynthesis` status: **GREEN (Zero sorrys, Zero warnings).**
