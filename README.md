# DSeparation: A Mechanized Analysis of d-Separation Equivalence

Standalone Lean 4 package formalizing the two standard characterizations of
d-separation (trail blocking and moralized ancestral-graph separation) and
proving that unrestricted equivalence is false.

## Build

```bash
lake exe cache get   # optional; caches Mathlib artifacts
lake build
```

Pinned by `lean-toolchain` and `lake-manifest.json`.

```bash
lake build   # all ~8300 jobs typecheck; InfoTheoryBridge currently emits scaffold sorry warnings
lake build DSeparation.TraceSynthesis  # reverse-direction workspace
```

## Workspace Hygiene

Keep temporary Lean proof experiments out of the repository root.  Put scratch
files under:

```text
scratch/lean-experiments/
```

For example:

```bash
lake env lean scratch/lean-experiments/test_exists.lean
```

Both `scratch/` and root-level `test_*.lean` files are ignored by Git, but new
agents should still use `scratch/lean-experiments/` so the root directory stays
readable.

Do not add declarations directly to `DSeparation/TraceSynthesis.lean`; it is an
aggregate import only.  Put new reverse-synthesis code in the appropriate
submodule under `DSeparation/TraceSynthesis/`.

## Main Results

| Result | File | Declaration |
|---|---|---|
| Endpoint caveat counterexample | `DSeparation/Counterexample.lean` | `dsep_complete_endpoint_in_Z_counterexample` |
| Unrestricted equivalence is false | `DSeparation/Counterexample.lean` | `not_forall_dsep_iff` |
| Soundness under disjointness | `DSeparation/Equivalence.lean` | `dSeparated_of_dSeparated_disjoint` |
| Trail → Bayes-ball path | `DSeparation/BayesBall/Basic.lean` | `bayesBallPath_of_active_trail_outOf` |
| Certified Bayes-ball path | `DSeparation/BayesBall/Certified.lean` | `bayesBallPathCert_of_active_trail_outOf` |
| Bayes-ball → MAGWalk | `DSeparation/MAGWalk.lean` | `BayesBallPath.compress` |
| MAGWalk ↔ graph reachability | `DSeparation/MAGWalk.lean` | `magWalk_iff_dSeparationGraph_reachable` |
| Static route IR for reverse synthesis | `DSeparation/TraceSynthesis/StaticRoute.lean` | `StaticStep`, `StaticRoute` |
| Reachability → static route witness | `DSeparation/TraceSynthesis/StaticRoute.lean` | `nonemptyStaticRoute_of_dSeparationGraph_reachable` |
| Zero-bad-collider route → open trace | `DSeparation/TraceSynthesis/OpenTrace.lean` | `openTrace_of_countBadColliders_zero` |
| Zero-bad-collider route → active witness | `DSeparation/TraceSynthesis/OpenTrace.lean` | `activeRoute_of_countBadColliders_zero`, `activeTrail_of_countBadColliders_zero` |
| Minimal bad-collider witness wrapper | `DSeparation/TraceSynthesis/MinimalWitness.lean` | `StaticRouteWitness`, `minRouteBadCountWitness`, `normalized_route_exists_of_improves` |
| First bad-collider extraction | `DSeparation/TraceSynthesis/Split.lean` | `exists_split` |
| Bad-collider route improvement | `DSeparation/TraceSynthesis/Assembly.lean` | `route_improves_of_bad` |
| Moral reachability → active witness | `DSeparation/TraceSynthesis/Assembly.lean` | `activeWitness_of_not_dSeparated` |
| Full d-separation equivalence | `DSeparation/Equivalence.lean` | `dSeparated_iff_dSeparates` |

## Module Structure

```
DSeparation/
├── DAG/
│   ├── Basic.lean              -- DAG structure, edges, parents, children
│   ├── Reachability.lean       -- ancestors, descendants, ancestral subgraph
│   └── Moralization.lean       -- moral graph, d-separation graph
├── Trail/
│   ├── Basic.lean              -- Trail inductive, Bayes-ball state machine
│   └── Blocking.lean           -- blocking predicates, dSeparates, DisjointSets
├── BayesBall/
│   ├── Basic.lean              -- active trail → Bayes-ball path
│   └── Certified.lean          -- certified version with node-survival proofs
├── MAGWalk.lean                -- compressed walk language, equivalence theorem
├── Equivalence.lean            -- main soundness theorem
├── ActiveRoute.lean            -- Type-valued Bayes-ball routes and active trails
├── TraceSynthesis.lean         -- aggregate import for reverse synthesis
├── TraceSynthesis/
│   ├── Graph.lean              -- graph lemmas used by normalization
│   ├── StaticRoute.lean        -- static route IR, append lemmas, reachability bridge
│   ├── OpenTrace.lean          -- bad-collider counts, local-open trace compiler
│   ├── MinimalWitness.lean     -- bad-collider minimality wrapper
│   ├── Split.lean              -- first-bad-collider extraction
│   └── Assembly.lean           -- final reverse-direction assembly
├── Reverse.lean                -- singleton moral-adjacency active-trail witnesses
├── InfoTheoryBridge.lean       -- scaffold for d-separation → conditional independence
├── Counterexample.lean         -- concrete counterexample
└── Examples.lean               -- checkable DAG instances (chain3, fork3, collider3)
```

## Paper

The `paper/` directory contains the POPL 2027 submission draft:

```bash
cd paper
pdflatex main.tex   # compiles to main.pdf
```

## Design Choices

- **Finite concrete DAGs**: nodes are `ℕ`, edges are `Finset (ℕ × ℕ)`, acyclicity
  is well-foundedness of the edge relation.
- **Constructive proofs**: all existence proofs are computable; counterexamples
  are explicit `DAG` instances.
- **Typed reverse-synthesis IR**: static moral-graph evidence is preserved as
  `StaticRoute`, with forward/backward direct steps and moral jumps represented
  as data rather than hidden inside `Prop`.
- **Layered reverse synthesis**: `TraceSynthesis` is split into graph lemmas,
  static route IR, open-trace compilation, minimal-witness selection, and final
  assembly.  The aggregate `DSeparation.TraceSynthesis` import remains stable.
- **Verification status**: The core d-separation and reverse-synthesis theory is
  **fully proved and verified**. `lake build DSeparation.TraceSynthesis` is
  green with no `sorry`s. The top-level `lake build` also succeeds, with two
  intentional scaffold `sorry` warnings in `InfoTheoryBridge.lean`.
