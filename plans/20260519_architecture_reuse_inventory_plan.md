# Planner Phase: ARCHITECTURE.md Update Plan (Frozen)

## Explored State
- Read full docs/ARCHITECTURE.md: integration boundary at lines 62-106, with Asset Map (66-80), Actual Gaps (81-89 as TODOList), Priority Order (90-97), Bridge Chain (98-106).
- Inspected paper/main.tex and paper/main_arxiv.tex via grep + targeted reads (lines ~157-181 for three-layer/L1, ~506-532 for PL dict, ~550-569 for QIF/InfoTheoryBridge status, ~500-502 for sorry claims).
- Noted: main_arxiv.tex has additional extrinsic L1 surface-calculus wording (lines 175-179) absent in main.tex; both have matching three-layer, QIF chain (d-separation → CI → DPI → cut-set), PL table, and InfoTheoryBridge sorry claims (exactly two intentional in InfoTheoryBridge.lean).
- Insertion point: after ### Asset Map (post line 80), before ### Actual Gaps, as new ### NeurIPS Reuse Inventory subsection.
- Uncommitted changes preserved: only in paper/*.tex (git status shows M for both TeX).

## Exact Edit Design (Single Targeted)
- Add NeurIPS Reuse Inventory subsection defining "unused" = not yet migrated to popl27.
- List grouped assets (called-by-arch: InfoTheory.lean etc.; supporting: CMI etc.; mark DAGParser.lean migrated).
- Update Actual Gaps / Priority Order (TODOList) in-place with specified points on TraceSynthesis frozen, shared-DAG layer, replace stubs, reuse DPI/cut-set, report external assumptions.
- No changes to TeX, no new files beyond plan, single edit only to ARCHITECTURE.md.

## Post-Edit Check
- Report-only: rg/sed/grep line checks vs TeX for 5 items; report file:line mismatches only.
- Then git diff -- docs/ARCHITECTURE.md; no edits after check start.

Plan frozen 2026-05-19. Switch to Executor now.