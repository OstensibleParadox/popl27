> ARCHIVED 2026-05-19 — superseded by docs/ARCHITECTURE.md and CHANGELOG.md.
# Phase 5: Code Quality Review & Integration Prep

## Objective

Clean up the trace synthesis modules so the reverse witness-synthesis pipeline
is modular, stable, and ready for the information-theory bridge.

## Completed Changes

| Area | Status | Notes |
|---|---|---|
| `TraceSynthesis/StaticRoute.lean` | Complete | Moved general structural route lemmas into the `StaticRoute` namespace: `append_nil`, `append_assoc`. |
| `TraceSynthesis/OpenTrace.lean` | Complete | Moved bad-collider step logic into the open-trace layer: `isStepBad`, `countBadColliders_cons`; `countBadColliders` now factors through `isStepBad`. |
| `TraceSynthesis/Split.lean` | Complete | Removed general lemmas that belonged to parent modules; kept the module focused on first-bad-collider extraction and the `Split` interface. |
| `Reverse.lean` | Complete | Removed duplicate reachability-node membership logic and uses `DAG.target_mem_nodes_of_reachable`. |
| `TraceSynthesis/Assembly.lean` | Complete | Renamed the extracted splitter witness from `s` to `split` in `route_improves_of_bad`. |

## Verification

```bash
lake build DSeparation.TraceSynthesis
lake build
```

`DSeparation.TraceSynthesis` builds without `sorry`s.  The full top-level build
succeeds; the only current warnings are the two intentional scaffold `sorry`s
in `DSeparation/InfoTheoryBridge.lean`.

## Current Boundary

The graph-semantics and reverse witness-extraction core is closed.  New proof
work should avoid changing `TraceSynthesis` unless there is a regression or a
clear API need.  The next active boundary is the information-theory bridge:
probability semantics, Markov compatibility, and
`d-separation ⇒ conditional independence`.
