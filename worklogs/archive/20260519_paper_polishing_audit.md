
# First edit: codex /skills paper-humanizer 

```markdown

# Tue 19 May 17:15
# Didn't check neurips26/verification
# Didn't check ARCHITECTURE.md 
# Didn't parallel-compare future-promised /Users/ostensible_paradox/Documents/popl27/paper/main.tex and direct repo dump main_arxiv.tex (to maintain future arXiv v1 honesty vs. What's promised for POPL27)
# Treated every mismatch between paper and repo as dishonesty, left no room for development

Argument Skeleton

  - Abstract/intro: strong endpoint-caveat hook, then compiler/decompiler framing.
  - Background/counterexample: cleanly explains the two d-separation criteria and the disjointness
    repair.
  - Architecture/forward/reverse: proof-asset map and constructive pipelines.
  - PL dictionary/related work/QIF: POPL positioning plus future-work bridge.
  - Conclusion: mostly restates abstract and contribution list.

  Redundancy / Stale-Layer Findings

  - The optimizer/decompiler slogan is repeated too many times: abstract paper/main.tex:66, intro
    paper/main.tex:117, contributions paper/main.tex:136, figures paper/main.tex:251, sections
    paper/main.tex:385, paper/main.tex:441, related work paper/main.tex:601, conclusion paper/
    main.tex:630. Keep it in abstract/intro, then use theorem names.
  - The “first-order surface calculus” paragraph looks stale or overclaimed: paper/main.tex:177.
    Repo search found DAG.ofRank in DSeparation/DAG/Basic.lean:34, but no visible surface AST/
    elaborator module.
  - “Exploitability certificate” and QIF substrate language outruns the verified result while
    InfoTheoryBridge.lean is explicitly stubbed: paper/main.tex:606, DSeparation/
    InfoTheoryBridge.lean:28.
  - The conclusion is a near replay of the abstract. It should synthesize why the endpoint caveat
    changes mechanized causal graph semantics, not restate all claims.

  Appendix Audit

  - There is no \appendix, so sufficiency fails for a proof-heavy POPL submission.
  - Necessary appendix items: full definitions, counterexample proof, forward survival lemma
    chain, reverse normalization tree, and verification-status table.
  - Natural-deduction order should be: definitions → endpoint counterexample → disjoint repair →
    forward contrapositive → reverse witness extraction → equivalence → QIF boundary. The main
    text already has this order, but the reverse proof is too compressed at paper/main.tex:501.

  Streamline Plan

  1. Delete or sharply qualify the surface-calculus paragraph unless there is a real surface AST
     to cite.
  2. Merge the two pipeline figures or make Figure 2 carry module names and theorem declarations;
     Figure 1 and Figure 2 currently duplicate conceptual work.
  3. Move the PL dictionary to a shorter paragraph or appendix unless POPL framing is central to
     the contribution.
  4. Add an appendix with theorem-dependency proof sketches and explicit pointers to Lean
     declarations.
  5. Soften “first mechanized” / “sole culprit” unless you add precise scope language.

  Risk Check

  - Preserve the endpoint caveat example; it is the paper’s strongest hook.
  - Preserve the zero-sorry graph-core claim, but keep the InfoTheoryBridge boundary explicit.
  - Do not cut the disjointness repair or reverse witness-production claim; those are the real
    contribution.

  Brutal ACM Verdict: Borderline Reject
  Hits: 5/17.

  Hits:

  1. Bait-and-switch scope risk: QIF/security framing appears, but QIF is only a scaffold.
  2. Random tangent/padding: PL dictionary and QIF future-work section feel bolted on.
  3. Heavy GPT smell: repeated “certified trace optimizer / constructive decompiler / semantic
     flow” phrasing.
  4. Overclaim risk: “first mechanized” and “sole culprit” need softer or better-supported
     wording.
  5. Appendix failure: no appendix despite proof-heavy claims.

  Cleared: intro is not lazy, notation is mostly controlled, theorem claims match current Lean
  declarations, and lake build succeeds with exactly the two expected scaffold sorry warnings.

  Verification run: lake build passed; temporary pdflatex build produced a 9-page PDF with
  warnings for missing figure descriptions and one overfull box in the PL dictionary table.

```

# Tue 19 May 19:56
# Source-grounded correction after checking ARCHITECTURE.md, neurips26/verification, and DSeparation

The first pass above was useful as an adversarial writing review, but several
items were too harsh because it had not checked the architecture and NeurIPS
verification sources it named.

## Grounded critiques to keep

- The optimizer/decompiler/semantic-flow slogans are repeated too often. Keep
  the framing, but reduce repeated slogan phrases after the abstract/intro.
- The QIF/security bridge must stay explicitly scoped. In `popl27`, the bridge
  is `InfoTheoryBridge.lean` and still has two intentional scaffold `sorry`s.
- The paper needs an appendix or appendix-like artifact for POPL: theorem
  dependency sketches, proof-status table, and explicit current-vs-planned
  boundary.
- "First mechanized" and "sole culprit" should be scoped carefully as paper
  novelty claims, not treated as Lean facts.

## Corrections to the harsh critique

- The first-order surface calculus is not a dishonesty issue. It is POPL-facing
  future work tied to the original bisimulation design. `paper/main.tex` is the
  POPL 2027 track with 50+ days before the July 9, 2026 deadline; it may carry
  planned architecture if the current-code boundary is explicit. `paper/main_arxiv.tex`
  is the arXiv-facing artifact for immediate release and should describe only
  current assets plus clearly marked future work.
- "QIF is only a scaffold" is incomplete. `popl27` contains the d-separation /
  graph-semantics core and `InfoTheoryBridge.lean` as the integration scaffold.
  `/Users/ostensible_paradox/Documents/neurips26/verification` contains the
  actual QIF/security machinery: finite PMFs, entropy/CMI, conditional DPI,
  cut-set bounds, KKT certificate structure, and the linear-chain case study.
  Its README maps these starting at line 21, including the probe-certificate and
  cut-set/KKT entries around line 31.
- The NeurIPS-to-POPL boundary in `docs/ARCHITECTURE.md` is an integration plan,
  not evidence that the work does not exist. The current missing piece is the
  shared-DAG or explicit-translation layer plus the d-separation-to-CI bridge.
- The "merge Figure 1 and Figure 2" comment is not grounded for the current
  `paper/main.tex`; there is one pipeline figure and one PL dictionary table.

## Current theory split

- `popl27`: endpoint caveat, disjointness repair, trail/moral-graph semantics,
  forward optimizer pipeline, reverse witness extraction pipeline, and
  `InfoTheoryBridge.lean` as the explicit bridge scaffold.
- `neurips26/verification`: finite-discrete information theory and QIF/security
  machinery, including finite PMFs, entropy/CMI, conditional DPI, cut-set
  bounds, KKT certificate structure, and a linear-chain case study.
- POPL 2027 TODO: surface calculus, shared-DAG/translation layer, bridge
  discharge or precise proof-obligation interface, reuse of NeurIPS QIF assets,
  and appendix/status hardening before July 9, 2026.
