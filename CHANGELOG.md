# Changelog

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

