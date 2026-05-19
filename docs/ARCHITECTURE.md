# Architecture

## Status & Canonical Sources

- [README.md](../README.md) is canonical for build commands, verification status, the theorem index, and the module tree.
- [paper/main.tex](../paper/main.tex) is canonical for published paper wording (including the external-facing PL dictionary table).
- Proof status: everything under `DSeparation/TraceSynthesis/` is fully proved; the only remaining `sorry`s are two intentional scaffold stubs in [DSeparation/InfoTheoryBridge.lean](../DSeparation/InfoTheoryBridge.lean) (lines 29 and 49).
- This document owns the "why": layering, module-boundary invariants, and the NeurIPS integration boundary (assets, gaps, priorities).

## The Three-Layer Stack

| Layer | PL Framing | Formal Asset | Status |
|---|---|---|---|
| L1: Syntax & Types | Type-safe graph syntax for conditional flow; `DisjointSets` is an ownership/aliasing side-condition for conditioned variables. Includes a first-order surface calculus with rank-based acyclicity certificates. | `DAG`, `DisjointSets`, `DAG.ofRank`, blocking predicates. | Core definitions complete; surface AST and rank-based elaboration are in place. |
| L2: Trace Bisimulation | Verified bisimulation: certified compilation and decompilation of information traces. Forward is a certified optimizer; backward is witness decompilation. | Forward: `Trail -> BayesBallPath -> MAGWalk`. Backward: `MAGWalk -> StaticRoute -> OpenTrace -> ActiveRoute -> Trail`. | Forward + reverse pipelines are complete and closed; key reverse theorems include `route_improves_of_bad` and `activeWitness_of_not_dSeparated` (in `TraceSynthesis/Assembly.lean`). |
| L3: Quantitative Bounds | From qualitative reachability to Shannon-style bounds (QIF / cut-set certificates). | Information-theory layer lives in the separate `neurips26` project; this repo contains the scaffold entrypoint `InfoTheoryBridge.lean`. | Not integrated yet: needs a bridge from d-separation to conditional independence plus a shared DAG foundation. |

## PL Dictionary (Engineering-Internal)

This table is an internal engineering map. For paper-ready naming and any external claim, treat the PL-mapping table in `paper/main.tex` as canonical.

| Engineering Name | POPL Framing |
|---|---|
| `DAG` | Dataflow AST / dependency-graph syntax |
| `DisjointSets X Y Z` | Resource-isolating ownership/aliasing constraint |
| Active trail | Operational trace of semantics |
| `MAGWalk` | Reachability IR (compressed moral-graph walk) |
| Collider jump (`MAGWalk.jump`) | Peephole optimization / semantic fold |
| `BayesBallPath.compress` | Certified trace optimizer |
| `StaticRoute -> OpenTrace -> ActiveRoute` | Decompiler / exploitability-certificate generator |
| Cut-set / mutual information | Quantitative information flow capacity bounds |

## Forward / Backward Pipeline

```
Forward (Soundness / Optimizer):
  Trail (active, ¬isBlocked)
    → BayesBallPath          (BayesBall.Basic)
    → Certified BayesBallPath (BayesBall.Certified)
    → MAGWalk                (MAGWalk.compress)
    → dSeparationGraph.Reachable

Backward (Completeness / Decompiler):
  ¬DAG.dSeparated
    → dSeparationGraph.Reachable
    → StaticRoute            (TraceSynthesis.StaticRoute)
    → NormalizedStaticRoute  (TraceSynthesis.MinimalWitness + Assembly)
    → OpenTrace              (TraceSynthesis.OpenTrace)
    → ActiveRoute            (TraceSynthesis.OpenTrace)
    → ∃ Trail, ¬isBlocked    (ActiveRoute.to_activeTrail)
    → ¬dSeparates
```

## Module Boundaries & Invariants

- `DSeparation/TraceSynthesis.lean` is aggregate-import-only: do not add declarations there.
- Prefer adding small lemmas in the appropriate `TraceSynthesis/*` submodule over extending `route_improves_of_bad` directly; `TraceSynthesis/Assembly.lean` should remain wiring.
- Treat `DSeparation/TraceSynthesis/` as the closed graph-semantics + witness-extraction core; avoid changes unless there is a regression or a clear API need.
- New proof work targets `DSeparation/InfoTheoryBridge.lean` (probability semantics, Markov compatibility, and d-separation to conditional independence).
- Local regression target for the reverse workspace: `lake build DSeparation.TraceSynthesis` (see `README.md` for the full build section).

## NeurIPS <-> POPL Integration Boundary

The NeurIPS 2026 verification stack (`neurips26`) and this POPL 2027 core calculus (`popl27`) are separate Lake projects. Their DAG definitions are nearly isomorphic, but there is currently no import relation or shared base module.

### Asset Map

| Asset | Location | Status | Note |
|---|---|---|---|
| Entropy, KL, CMI non-negativity | `neurips26/InfoTheory.lean` | Complete | Proved from Mathlib primitives. |
| Conditional DPI | `neurips26/InfoTheory.lean` | Complete | |
| Conditional Markov property | `neurips26/InfoTheory.lean` | Present | |
| Trace-gap chain rule | `neurips26/InfoTheoryHelpers` | Present | |
| Additive decomposition + static cardinality bounds | `neurips26/DualCertificate.lean` | Present | |
| Autoregressive zero-cut | `neurips26/Screenability.lean` | Complete | |
| Predictability route impossibility | `neurips26/InternalImpossibility.lean` | Complete | |
| Cut-set / min-cut / bottleneck / KKT-style bounds | `neurips26/*` | Structurally present | Still relies on external capacity or Markov assumptions in places. |
| d-separation graph semantics | `DSeparation/*` | Complete | Moralization, blocking, Bayes-ball, `MAGWalk`. |
| Reverse witness extraction | `DSeparation/TraceSynthesis/*` | Complete | Reverse pipeline + cleanup closed. |

### NeurIPS Reuse Inventory

"Unused" here means "not yet migrated into popl27", not dead code. The following NeurIPS assets remain unmigrated and are reusable once the DAG/CI bridge exists:

- **Called by architecture**: `InfoTheory.lean`, `InfoTheoryHelpers.lean`, `DualCertificate.lean`, `Screenability.lean`, `InternalImpossibility.lean`, `CutSetBoundExtract.lean`, `ChannelCapacity.lean`, `CaseStudy.lean`, `MarkovGenerator.lean`.
- **Supporting/secondary modules**: CMI definitions, trace-recoverability bridges, quotient/semantic closure, PAC/geometric/impossibility utilities, aggregate shims.
- `DAGParser.lean` is already migrated/split into `DSeparation/*` and is not considered unused.

### Actual Gaps (TODOList)

| # | Gap | Difficulty | Note |
|---|---|---|---|
| 1 | Build a shared-DAG or explicit-translation layer between neurips26 and popl27. | Medium engineering | Required before importing `neurips26` results. |
| 2 | Replace `InfoTheoryBridge.lean` stubs by proving/stating the d-separation $\to$ conditional-independence bridge using NeurIPS machinery. | High | After DAG bridge. |
| 3 | Reuse NeurIPS conditional DPI and cut-set/KKT pipeline after the DAG/CI bridge exists. | High | Depends on above. |
| 4 | Preserve `TraceSynthesis` as the frozen closed graph-semantics core. | Low | Regression target only. |

### Priority Order (TODOList)

1. Preserve `TraceSynthesis` as frozen closed graph-semantics core.
2. Build a shared-DAG or explicit-translation layer between neurips26 and popl27.
3. Replace `InfoTheoryBridge.lean` stubs by proving/stating the d-separation $\to$ conditional-independence bridge using NeurIPS machinery.
4. Reuse NeurIPS conditional DPI and cut-set/KKT pipeline after the DAG/CI bridge exists.
5. Report remaining external assumptions separately from mechanized reusable proofs.

### Bridge Chain

```
d-separation
  -> conditional independence (Markov semantics)
  -> conditional DPI
  -> cut-set mutual-information bound
```
