# Planner Phase: Architecture Reuse Inventory and Paper-Track Split

## Explored State
- Read full docs/ARCHITECTURE.md: integration boundary at lines 62-106, with Asset Map (66-80), Actual Gaps (81-89 as TODOList), Priority Order (90-97), Bridge Chain (98-106).
- Inspected paper/main.tex and paper/main_arxiv.tex via grep + targeted reads (lines ~157-181 for three-layer/L1, ~506-532 for PL dict, ~550-569 for QIF/InfoTheoryBridge status, ~500-502 for sorry claims).
- Clarified paper-track roles: `paper/main_arxiv.tex` is the arXiv-facing release artifact for today; `paper/main.tex` is the POPL 2027 submission track with 50+ days before the July 9, 2026 deadline.
- Clarified surface-calculus status: the first-order surface calculus is POPL-facing future work and part of the intended architecture, not a claim that the current arXiv artifact already contains a complete surface AST/elaborator.
- Insertion point: after ### Asset Map (post line 80), before ### Actual Gaps, as new ### NeurIPS Reuse Inventory subsection.
- Current uncommitted non-doc changes are generated paper artifacts (`paper/*.log`, `paper/*.pdf`); do not stage them as part of the architecture update.

## Exact Edit Design
- Add a paper-track split: arXiv today vs POPL 2027 July 9 submission.
- Add current code assets: `popl27` graph-semantics core plus explicit `InfoTheoryBridge.lean` integration scaffold.
- Add current theory split:
  - `popl27`: d-separation / graph-semantics core, endpoint caveat, disjoint repair, forward/reverse bisimulation, scaffold bridge.
  - `neurips26/verification`: actual QIF/security machinery: finite PMFs, entropy/CMI, conditional DPI, cut-set bounds, KKT certificate structure, and the linear-chain case study.
  - `docs/ARCHITECTURE.md`: integration boundary, not evidence of nonexistent work.
- Update README module map for the post-split Lean hierarchy.
- Add README document roles/expiry table covering active docs, short-lived plans, and `worklogs/archive/`.
- Update CHANGELOG with Phase 6 modularization and paper-architecture documentation.
- Append a corrective audit to `worklogs/paper-polishing-log.md` instead of deleting the original critique log.
- No changes to TeX in this plan.

## POPL 2027 TODO Timeline
- **Now / arXiv**: release current graph-semantics artifact honestly; keep QIF bridge explicit.
- **Late May 2026**: stabilize POPL-facing surface-calculus plan and appendix outline.
- **June 2026**: build shared-DAG or translation layer between `neurips26` and `popl27`; replace or refine `InfoTheoryBridge.lean` stubs.
- **Late June 2026**: reuse NeurIPS conditional DPI / cut-set / KKT pipeline through the bridge, or report remaining external assumptions.
- **July 1-8, 2026**: harden POPL draft before the July 9 deadline.

Plan updated 2026-05-19 after source-grounded critique audit.
