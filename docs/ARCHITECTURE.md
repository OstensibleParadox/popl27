# Architecture

## Status & Canonical Sources

- [README.md](../README.md) is canonical for build commands, verification status, the theorem index, and the module tree.
- [paper/main_arxiv.tex](../paper/main_arxiv.tex) is the arXiv-facing paper track for immediate release.
- [paper/main.tex](../paper/main.tex) is the POPL 2027 submission track.  The submission deadline is July 9, 2026 (50+ days after May 19, 2026), so this track may include planned architecture work if the current-code boundary is explicit.
- Proof status: everything under `DSeparation/TraceSynthesis/` is fully proved; the only remaining `sorry`s are two intentional scaffold stubs in [DSeparation/InfoTheoryBridge.lean](../DSeparation/InfoTheoryBridge.lean) (lines 29 and 49).
- This document owns the "why": layering, module-boundary invariants, and the NeurIPS integration boundary (assets, gaps, priorities).

## The Three-Layer Stack

| Layer | PL Framing | Formal Asset | Status |
|---|---|---|---|
| L1: Syntax & Types | Type-safe graph syntax for conditional flow; `DisjointSets` is an ownership/aliasing side-condition for conditioned variables. The POPL-facing plan includes a first-order surface calculus with rank-based acyclicity certificates. | Current: `DAG`, `DisjointSets`, `DAG.ofRank`, blocking predicates. Planned: surface AST/elaboration layer for POPL. | Core definitions complete; surface calculus is future work for the POPL track. |
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

## Current Code Assets

`popl27` currently contains the d-separation / graph-semantics core:

- `DSeparation/DAG/*`: finite DAGs, reachability, ancestry, moralization, and d-separation graph construction.
- `DSeparation/Trail/*`: trail syntax, local triple blocking, `dSeparates`, `DisjointSets`, and Bayes-ball state/path bookkeeping.
- `DSeparation/BayesBall/*`: active-trail to Bayes-ball path construction and certified node-survival proofs.
- `DSeparation/MAGWalk/*`: compressed moral-graph walk language, MAGWalk reachability lemmas, and Bayes-ball path compression.
- `DSeparation/TraceSynthesis/*`: reverse witness extraction from moral-graph reachability to active trails.
- `DSeparation/InfoTheoryBridge.lean`: explicit integration scaffold for d-separation to conditional independence; this is intentionally not discharged in `popl27` yet.

The separate `/Users/ostensible_paradox/Documents/neurips26/verification` project contains the actual QIF/security machinery: finite PMFs, entropy/CMI, conditional DPI, cut-set bounds, KKT certificate structure, and the linear-chain case study. Its README maps these assets at `/Users/ostensible_paradox/Documents/neurips26/verification/README.md:21`, especially the probe-certificate/DPI row at line 31.

## Current Theory Split

- **`paper/main_arxiv.tex` today**: should present the current verified graph-semantics core, the endpoint caveat, the disjointness repair, the optimizer/decompiler bisimulation, and the explicit `InfoTheoryBridge.lean` boundary.
- **`paper/main.tex` for POPL 2027**: may retain the broader POPL-facing architecture, including the planned first-order surface calculus and the NeurIPS-to-POPL QIF integration, so long as current code assets and future work are separated.
- **`popl27` code**: proves the d-separation / graph-semantics core and keeps the probabilistic bridge as an explicit scaffold.
- **`neurips26/verification` code**: proves or structures the finite information-theoretic machinery: `FinitePMF`, entropy/CMI, conditional DPI, cut-set bounds, KKT certificates, and the linear-chain case study.
- **Integration boundary**: this document's NeurIPS-to-POPL section records planned reuse, not nonexistent work.

### Paper Track Governance

**Forbidden claims policy** — enforced in all drafts targeting arXiv or POPL:

| Forbidden phrase | Requires qualifier |
|---|---|
| "Complete integration" | `planned` / `scaffold` |
| "Quantitative verification" | `planned` / `scaffold` |
| "Solves QIF" | `planned` / `scaffold` |

Any occurrence without the qualifier is a P0 blocking deletion.

**Double-write risk** — `main_arxiv.tex` and `main.tex` share graph-semantics content but are physically separate.  
Mitigation (ship-safe): apply any typo/formatting fix to both files manually at time of edit.  
Deferred: extract shared content into `\input{core_semantics.tex}` after arXiv submission.

**arXiv submission checkpoint** — tag the exact commit that produces the final `main_arxiv.pdf`:

```bash
git tag -a v1.0.0-arxiv-submitted -m "Zero sorries checkpoint for arXiv v1"
```

This tag is the verifiable snapshot of what was submitted; POPL revisions diverging from it are expected and acceptable.

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
| Entropy, KL, CMI non-negativity | `neurips26/verification/FiniteQuerySandbox/InfoTheory.lean` | Complete | Proved from Mathlib primitives. |
| Conditional DPI | `neurips26/verification/FiniteQuerySandbox/InfoTheory.lean` | Complete | |
| Conditional Markov property | `neurips26/verification/FiniteQuerySandbox/InfoTheory.lean` | Present | |
| Trace-gap chain rule | `neurips26/verification/InfoTheoryHelpers.lean` | Present | |
| Additive decomposition + static cardinality bounds | `neurips26/verification/FiniteQuerySandbox/DualCertificate.lean` | Present | |
| Autoregressive zero-cut | `neurips26/verification/FiniteQuerySandbox/Screenability.lean` | Complete | |
| Predictability route impossibility | `neurips26/verification/FiniteQuerySandbox/InternalImpossibility.lean` | Complete | |
| Cut-set / min-cut / bottleneck / KKT-style bounds | `neurips26/verification/*` | Structurally present | Still relies on external capacity or Markov assumptions in places. |
| d-separation graph semantics | `DSeparation/*` | Complete | Moralization, blocking, Bayes-ball, `MAGWalk`. |
| Reverse witness extraction | `DSeparation/TraceSynthesis/*` | Complete | Reverse pipeline + cleanup closed. |

### NeurIPS Reuse Inventory

"Unused" here means "not yet migrated into popl27", not dead code. The following NeurIPS assets remain unmigrated and are reusable once the DAG/CI bridge exists:

- **Called by architecture**: `FiniteQuerySandbox/InfoTheory.lean`, `InfoTheoryHelpers.lean`, `FiniteQuerySandbox/DualCertificate.lean`, `FiniteQuerySandbox/Screenability.lean`, `FiniteQuerySandbox/InternalImpossibility.lean`, `CutSetBoundExtract.lean`, `FiniteQuerySandbox/ChannelCapacity.lean`, `FiniteQuerySandbox/CaseStudy.lean`, `FiniteQuerySandbox/MarkovGenerator.lean`.
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

### POPL 2027 Timeline

Submission deadline: July 9, 2026.

| Window | Target | Deliverable |
|---|---|---|
| Now / arXiv | Release current graph-semantics artifact honestly. | `paper/main_arxiv.tex` plus README/architecture status matching current code. |
| Late May 2026 | Stabilize POPL-facing architecture. | Surface-calculus design note, theorem-dependency appendix plan, and explicit current-vs-planned claim table. |
| June 2026 | Integrate or sharply specify the DAG/CI bridge. | Shared-DAG/translation layer or a precise proof-obligation interface for `InfoTheoryBridge.lean`. |
| Late June 2026 | Reuse NeurIPS QIF machinery. | Conditional DPI / cut-set / KKT pipeline connected through the bridge, or explicitly reported as external assumptions. |
| July 1-8, 2026 | Paper hardening. | POPL draft with appendix, verification table, scoped novelty claims, and no ambiguity between verified results and planned integration. |

### Bridge Chain

```
d-separation
  -> conditional independence (Markov semantics)
  -> conditional DPI
  -> cut-set mutual-information bound
```
