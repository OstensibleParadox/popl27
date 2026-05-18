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
lake build   # all ~8300 jobs pass, zero sorries
```

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
- **Zero sorries**: the entire development compiles without `sorry` or `admit`.
