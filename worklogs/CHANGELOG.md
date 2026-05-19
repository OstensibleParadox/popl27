# Changelog

## [2026-05-19] — doc cleanup

### Archive/merge pass

- Archived `plans/20260519_architecture_reuse_inventory_plan.md` → `worklogs/archive/20260519_architecture_reuse_inventory_plan.md`; all durable content already merged into `docs/ARCHITECTURE.md`.
- Archived `worklogs/paper-polishing-log.md` → `worklogs/archive/20260519_paper_polishing_audit.md`; unresolved TODOs already tracked in `docs/ARCHITECTURE.md` GAP list.
- Removed empty `plans/` directory.
- Replaced the "Document Roles and Expiry" table in `README.md` with a one-line rule; active docs are now `README.md`, `docs/ARCHITECTURE.md`, and `CHANGELOG.md` only.

## [2026-05-19]

### Reverse synthesis closed (Phase 4/6)

- `route_improves_of_bad`, `exists_split`, `escape_path_survives`, `bad_child_survives`, `activeWitness_of_not_dSeparated` proved.
- `dSeparated_iff_dSeparates` closed (`DSeparation/Equivalence.lean:134`).
- Technical note: the dependent-type mismatch (`HEq`) in the splitter path was resolved via length induction, with the absorbed-prefix state constructed outside recursive calls.

### Module-quality cleanup (Phase 5)

- `TraceSynthesis/StaticRoute.lean`: moved structural route lemmas into `StaticRoute` (`append_nil`, `append_assoc`).
- `TraceSynthesis/OpenTrace.lean`: moved bad-collider step logic into the open-trace layer (`isStepBad`, `countBadColliders_cons`); `countBadColliders` now factors through `isStepBad`.
- `TraceSynthesis/Split.lean`: removed general lemmas; kept the module focused on first-bad-collider extraction and the `Split` interface.
- `Reverse.lean`: removed duplicate reachability-node membership logic; uses `DAG.target_mem_nodes_of_reachable`.
- `TraceSynthesis/Assembly.lean`: renamed the extracted splitter witness from `s` to `split` in `route_improves_of_bad`.

### Module hierarchy split (Phase 6)

- `MAGWalk.lean` is now an aggregate/compression layer; core constructors live in `MAGWalk/Basic.lean`, and graph-reachability lemmas live in `MAGWalk/Lemmas.lean`.
- `Trail/Basic.lean` is now an aggregate import; trail/triple/local-blocking definitions live in `Trail/Basic/Core.lean`, and Bayes-ball state/path bookkeeping lives in `Trail/Basic/BayesBall.lean`.
- `TraceSynthesis/StaticRoute.lean` is now an aggregate import; static route IR lives in `TraceSynthesis/StaticRoute/Basic.lean`, and directed reachability route constructors live in `TraceSynthesis/StaticRoute/Reachability.lean`.
- `TraceSynthesis/OpenTrace.lean` is now an aggregate import; open-trace witnesses live in `TraceSynthesis/OpenTrace/Basic.lean`, bad-collider metrics and reroute bounds live in `TraceSynthesis/OpenTrace/BadColliders.lean`, and zero-bad route compilation lives in `TraceSynthesis/OpenTrace/Compile.lean`.
- Full `lake build` passed after the split with only the two existing `InfoTheoryBridge.lean` scaffold `sorry` warnings.

### Paper architecture and reuse inventory

- Documented the two paper tracks: `paper/main_arxiv.tex` for immediate arXiv release, and `paper/main.tex` for the POPL 2027 submission path toward the July 9, 2026 deadline.
- Clarified the current theory split: `popl27` contains the d-separation/graph-semantics core plus `InfoTheoryBridge.lean` as an integration scaffold; `neurips26/verification` contains the finite PMF, entropy/CMI, conditional DPI, cut-set, KKT, and linear-chain QIF/security machinery.
- Recorded the NeurIPS-to-POPL integration boundary as future work, not nonexistent work.
- Added a document roles and expiry table so active docs, short-lived plans, and `worklogs/archive/` provenance have explicit ownership and archive dates.
