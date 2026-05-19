# DSeparation: A Mechanized Analysis of d-Separation Equivalence

Standalone Lean 4 package formalizing the two standard characterizations of
d-separation (trail blocking and moralized ancestral-graph separation) and
proving that unrestricted equivalence is false.

## Documentation Map

- Architecture & strategy: `docs/ARCHITECTURE.md`
- History: `CHANGELOG.md`
- Provenance archive (verbatim): `worklogs/archive/`
- Paper critique audit and polishing notes: `worklogs/paper-polishing-log.md`

## Document Roles and Expiry

Use this table to decide whether a document is live guidance or provenance.
Before archiving any active document, move unresolved action items into the
current canonical doc or a fresh plan.

| Document | Function | Expiry / archive rule |
|---|---|---|
| `README.md` | Front-door index: build commands, paper-track split, theorem map, and module tree. | No expiry. Keep active; review on 2026-07-10 after the POPL deadline, but do not move to `worklogs/archive/`. |
| `CHANGELOG.md` | Append-only human-readable history of code and documentation changes. | No expiry. Keep active; do not archive individual sections unless the release process changes. |
| `docs/ARCHITECTURE.md` | Current architecture contract: layer map, module invariants, NeurIPS-to-POPL boundary, and TODO priorities. | Review on 2026-07-10. If superseded by a final POPL appendix or newer architecture doc, move the old copy to `worklogs/archive/ARCHITECTURE-20260710.md`; otherwise refresh in place. |
| `plans/20260519_architecture_reuse_inventory_plan.md` | Short-lived execution plan and provenance for the May 19 architecture/doc pass. | Expires 2026-05-26, or immediately after this batch is committed or abandoned. Move to `worklogs/archive/20260519_architecture_reuse_inventory_plan.md` once it stops driving active edits. |
| `worklogs/paper-polishing-log.md` | Active critique ledger for grounded vs over-harsh paper-polishing notes. | Expires 2026-07-10. First extract unresolved TODOs into `docs/ARCHITECTURE.md` or a paper issue list, then move to `worklogs/archive/paper-polishing-log-20260710.md`. |
| `worklogs/archive/` | Immutable archive for stale plans, audits, and provenance notes. | No expiry. Add archived files here; do not edit old entries except for mechanical path fixes. |

## Build

```bash
lake exe cache get   # optional; caches Mathlib artifacts
lake build
```

Pinned by `lean-toolchain` and `lake-manifest.json`.

```bash
lake build   # all ~8310 jobs typecheck; InfoTheoryBridge currently emits scaffold sorry warnings
lake build DSeparation.TraceSynthesis  # reverse-direction workspace
```

## Paper Tracks

This repository currently supports two paper-facing tracks:

- `paper/main_arxiv.tex` is the arXiv-facing version for immediate release.
  It should describe only the current verified assets and explicitly mark the
  probabilistic bridge as future/integration work.
- `paper/main.tex` is the POPL 2027 submission track.  The POPL deadline is
  July 9, 2026 (50+ days after May 19, 2026), so this file may carry
  forward-looking architecture work that is planned for completion before
  submission, provided the current verification boundary is stated clearly.

Current code assets live in this repository under `DSeparation/`.  The
information-theoretic/QIF assets live in the separate
`/Users/ostensible_paradox/Documents/neurips26/verification` Lake project; its
README maps the main statements at
`/Users/ostensible_paradox/Documents/neurips26/verification/README.md:21`,
especially the probe-certificate/DPI row at line 31.

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
| MAGWalk core and reachability lemmas | `DSeparation/MAGWalk/{Basic,Lemmas}.lean` | `MAGWalk`, `magWalk_iff_dSeparationGraph_reachable` |
| Static route IR for reverse synthesis | `DSeparation/TraceSynthesis/StaticRoute/Basic.lean` | `StaticStep`, `StaticRoute` |
| Reachability → static route witness | `DSeparation/TraceSynthesis/StaticRoute/Basic.lean` | `nonemptyStaticRoute_of_dSeparationGraph_reachable` |
| Directed reachability → route chains | `DSeparation/TraceSynthesis/StaticRoute/Reachability.lean` | `StaticRoute.ofBackwardReachable`, `StaticRoute.ofForwardReachable` |
| Zero-bad-collider route → open trace | `DSeparation/TraceSynthesis/OpenTrace/Compile.lean` | `openTrace_of_countBadColliders_zero` |
| Zero-bad-collider route → active witness | `DSeparation/TraceSynthesis/OpenTrace/Compile.lean` | `activeRoute_of_countBadColliders_zero`, `activeTrail_of_countBadColliders_zero` |
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
│   ├── Basic.lean              -- aggregate import for Trail.Basic submodules
│   ├── Basic/
│   │   ├── Core.lean           -- Trail, triples, local blocking, TrailDir
│   │   └── BayesBall.lean      -- Bayes-ball state machine and path bookkeeping
│   └── Blocking.lean           -- blocking predicates, dSeparates, DisjointSets
├── BayesBall/
│   ├── Basic.lean              -- active trail → Bayes-ball path
│   └── Certified.lean          -- certified version with node-survival proofs
├── MAGWalk.lean                -- aggregate + BayesBallPath compression
├── MAGWalk/
│   ├── Basic.lean              -- compressed walk language
│   └── Lemmas.lean             -- MAGWalk ↔ d-separation graph reachability
├── Equivalence.lean            -- main soundness theorem
├── ActiveRoute.lean            -- Type-valued Bayes-ball routes and active trails
├── TraceSynthesis.lean         -- aggregate import for reverse synthesis
├── TraceSynthesis/
│   ├── Graph.lean              -- graph lemmas used by normalization
│   ├── StaticRoute.lean        -- aggregate import for static route modules
│   ├── StaticRoute/
│   │   ├── Basic.lean          -- static route IR, append lemmas, graph-walk bridge
│   │   └── Reachability.lean   -- directed reachability route constructors
│   ├── OpenTrace.lean          -- aggregate import for open-trace modules
│   ├── OpenTrace/
│   │   ├── Basic.lean          -- local-open trace witness and conversions
│   │   ├── BadColliders.lean   -- bad-collider metric and reroute bounds
│   │   └── Compile.lean        -- zero-bad route to active witness
│   ├── MinimalWitness.lean     -- bad-collider minimality wrapper
│   ├── Split.lean              -- first-bad-collider extraction
│   └── Assembly.lean           -- final reverse-direction assembly
├── Reverse.lean                -- singleton moral-adjacency active-trail witnesses
├── InfoTheoryBridge.lean       -- scaffold for d-separation → conditional independence
├── Counterexample.lean         -- concrete counterexample
└── Examples.lean               -- checkable DAG instances (chain3, fork3, collider3)
```

## Paper

The `paper/` directory contains both paper-facing tracks:

```bash
cd paper
pdflatex main_arxiv.tex   # immediate arXiv-facing artifact
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
