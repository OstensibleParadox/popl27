# Architecture

## Status & Canonical Sources

- [README.md](../README.md) is canonical for build commands, verification status, the theorem index, and the module tree.
- [paper/main.tex](../paper/main.tex) is canonical for published paper wording (including the external-facing PL dictionary table).
- Proof status: everything under `DSeparation/TraceSynthesis/` is fully proved; the only remaining `sorry`s are two intentional scaffold stubs in [DSeparation/InfoTheoryBridge.lean](../DSeparation/InfoTheoryBridge.lean) (lines 29 and 49).
- This document owns the "why": layering, module-boundary invariants, and the NeurIPS integration boundary (assets, gaps, priorities).

## The Three-Layer Stack

| Layer | PL Framing | Formal Asset | Status |
|---|---|---|---|
| L1: Syntax & Types | Type-safe graph syntax for conditional flow; `DisjointSets` is an ownership/aliasing side-condition for conditioned variables. | `DAG`, `DisjointSets`, blocking predicates. | Core definitions complete; a surface AST + typechecker is future packaging work. |
| L2: Trace Bisimulation | Verified bisimulation: certified compilation and decompilation of information traces. Forward is a certified optimizer; backward is witness decompilation. | Forward: `Trail -> BayesBallPath -> MAGWalk`. Backward: `MAGWalk -> StaticRoute -> OpenTrace -> ActiveRoute -> Trail`. | Forward + reverse pipelines are complete and closed; key reverse theorems include `route_improves_of_bad` and `activeWitness_of_not_dSeparated` (in `TraceSynthesis/Assembly.lean`). |
| L3: Quantitative Bounds | From qualitative reachability to Shannon-style bounds (QIF / cut-set certificates). | Information-theory layer lives in the separate `neurips26` project; this repo contains the scaffold entrypoint `InfoTheoryBridge.lean`. | Not integrated yet: needs a bridge from d-separation to conditional independence plus a shared DAG foundation. |

## L1 Roadmap: Pitfall-Avoiding Extrinsic Surface Calculus (Target: 2026-07-09)

The current artifact enforces the key well-formedness conditions (e.g. `DisjointSets X Y Z`)
*intrinsically* via dependent typing.  For a POPL-style presentation of an
*extrinsic* type system ("raw AST + evaluator + typing judgment + Progress/Preservation"),
the fastest path that avoids known Lean time-sinks is:

### 1. Surface Language Boundary ("do not summon the binder demon")

- **Do not** introduce higher-order binders (no `λ`, no closures).
- Use a first-order, command-like surface language with a simple environment:
  `let S = SetLit; let G = GraphLit; query(G, X, Y, Z)`.
- Semantics can be big-step (`eval : Env → Term → Result`) or small-step; big-step is usually simpler here.

### 2. "May-Go-Wrong" Raw Syntax (AST) + Explicit Errors

- Raw graph syntax should admit ill-formed inputs (dangling edges, nodes outside `nodes`, missing certificates).
- Raw set syntax for `X`, `Y`, `Z` plus minimal combinators needed for examples.
- Make failures explicit as data: `BadGraph`, `NotInNodes`, `NotDisjoint`, `CycleCertRejected`, etc.

### 3. Certified Acyclicity via a Rank Certificate (PCC-style speedup)

- Require the surface graph to carry a **rank certificate** (e.g. `rank : ℕ → ℕ` or a topo-order witness).
- The typechecker only verifies the local property "`rank u < rank v` for every edge (u,v)" (linear-time).
- Elaborate validated graphs into the intrinsic `DAG` via `DAG.ofRank`.
  This offloads the hard termination/proof burden away from "compute SCCs in Lean" and fits a proof-carrying-code story.

### 4. Ownership/Disjointness Tracking: Prefer `WF` Judgments + One Key Side-Condition

- Keep the story close to the paper claim "affine ownership":
  define lightweight well-formedness judgments (`WFGraph`, `WFSet`, `WFQuery`).
- In the `Query` typing rule, require the single critical side-condition:
  `DisjointSets X Y Z` (and any necessary membership premises).
  This keeps the Progress/Preservation proof lean while still explaining the repaired equivalence domain.

### 5. Type Soundness (Wright--Felleisen) with Minimal Lemma Debt

- Prove Preservation and Progress for the surface evaluator.
- With the recommended first-order language, you typically avoid the heavy substitution stack:
  environment extension lemmas replace λ-calculus substitution.
- Conclude "well-typed programs do not go wrong" (no `stuck`, no unexpected runtime error).

### 6. Elaboration to the Semantic Core ("Interpreter → Typechecker → Certified IR Extraction")

- Define `elab` from well-typed surface programs into intrinsic objects (`DAG`, `X`, `Y`, `Z`, ...).
- Prove elaboration soundness/completeness against intrinsic definitions (`dSeparates`, `DAG.dSeparated`,
  `dSeparated_iff_dSeparates`).
- Reuse the existing decompiler as the surface witness generator:
  `activeWitness_of_not_dSeparated` is the intended end-to-end payload.

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

### Actual Gaps

| # | Gap | Difficulty | Note |
|---|---|---|---|
| 1 | Bridge the two DAG definitions (shared foundation or explicit translation). | Medium engineering | Required before importing `neurips26` results into this repo. |
| 2 | Prove d-separation implies conditional independence (under a Markov-compatible semantics). | High | Needs probabilistic graphical model semantics. |
| 3 | Replace NeurIPS cut-set capacity axioms using the bridge plus DPI. | High | Depends on (2). |
| 4 | Preserve the closed reverse witness extractor while building the bridge. | Low | Keep `TraceSynthesis` stable and regression-tested. |

### Priority Order

1. Treat `TraceSynthesis` as the closed graph-semantics and witness-extraction core.
2. Keep `popl27` focused on the information-flow core calculus: typed query well-formedness, trace optimization, and witness decompilation.
3. Create an integration layer for the `neurips26` and `popl27` DAG definitions.
4. Then formalize d-separation to conditional independence.
5. Finally replace NeurIPS cut-set capacity axioms with theorem-level proofs.

### Bridge Chain

```
d-separation
  -> conditional independence (Markov semantics)
  -> conditional DPI
  -> cut-set mutual-information bound
```
