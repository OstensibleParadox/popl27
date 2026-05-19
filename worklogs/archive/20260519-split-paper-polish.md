
# Docs Review + Split Paper-Polishing Logs

## Summary

- Treated commit 40bfa0c as baseline.
- Archived mixed polishing log; did NOT split into two active logs.
- Removed `plans/` directory after archiving its only file.
- Updated `README.md` with a two-line rule (no new active log references).
- Added `### Paper Track Governance` subsection to `docs/ARCHITECTURE.md` with
  forbidden-claims policy, double-write mitigation, and arXiv submission checkpoint.

## Actual Changes (vs Original Plan)

- **`worklogs/paper-polishing-log.md`** → archived to
  `worklogs/archive/20260519_paper_polishing_audit.md`.
  (Plan named destination `20260519_paper-polishing-initial-audit.md` — actual name differs.)
- **`plans/20260519_architecture_reuse_inventory_plan.md`** → archived to
  `worklogs/archive/20260519_architecture_reuse_inventory_plan.md`; durable content already in
  `docs/ARCHITECTURE.md`.
- **`plans/`** directory removed (empty after move).
- **`README.md`**: removed `worklogs/paper-polishing-log.md` reference and "Document Roles and
  Expiry" table; replaced with two-line rule:
  > Active guidance lives in `README.md`, `docs/ARCHITECTURE.md`, and `CHANGELOG.md`.
  > Stale plans and audits go to `worklogs/archive/`.
- **`docs/ARCHITECTURE.md`**: no change to track-split language (already clean). Added new
  `### Paper Track Governance` subsection under `## Current Theory Split`:
  - Forbidden-claims table (three P0 phrases that require `planned`/`scaffold` qualifier).
  - Double-write risk + ship-safe mitigation + deferred `\input{core_semantics.tex}` note.
  - arXiv submission checkpoint: `git tag -a v1.0.0-arxiv-submitted`.
- **`CHANGELOG.md`**: prepended archive/merge entry naming both archived files.
- **`worklogs/paper-polishing-arxiv.md`** and **`worklogs/paper-polishing-popl.md`**: NOT
  created. Governance content lives in `docs/ARCHITECTURE.md` instead.

## Deviations from Original Plan

| Plan item | Actual outcome |
|---|---|
| Create two active split logs | Not created; governance went to ARCHITECTURE.md |
| Archive destination `…-initial-audit.md` | Actual: `20260519_paper_polishing_audit.md` |
| Edit ARCHITECTURE.md track-split language | Already clean; only added new `### Paper Track Governance` |
| README lists two active log paths | README uses two-line rule only |
