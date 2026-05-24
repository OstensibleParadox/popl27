# Supplementary Lean Sources

This directory contains the anonymized Lean sources that support the paper.

Build from this directory with:

```bash
lake build
```

The project files are:

- `DSeparation.lean`
- `DSeparation/`
- `lakefile.lean`
- `lake-manifest.json`
- `lean-toolchain`

---

# TODO before submission (from 2026-05-22 audit)

This list collects items from the 2026-05-22 planning notes
(`20260522--structure.md`, `20260522--reuse.md`) that were *not yet
executed* in `paper/main.tex`, plus the gaps flagged in the post-draft
review. Items are grouped by severity.

## Severity 1 — submission blockers

### S1.1 Necessity theorem proof is informal

`paper/main.tex` §3.1 states the Necessity theorem and gives a
one-paragraph sketch. POPL reviewers expect either a formal proof
(counterexample SCM per dropped field) or an explicit limitation
disclaimer.

Two options:

- **Strengthen.** Add four concrete counterexample SCMs, one per
  field of `SheafMAGWalk`. Each SCM should be a 3–4 node DAG with
  one downstream theorem whose argument type becomes uninhabited
  when that field is dropped. Goes in Appendix.
- **Disclaim.** Insert the line from `20260522--reuse.md` §3.1:
  *"This is a structural typing claim, not a universal complexity
  theorem over all possible frameworks."* Keep informal proof.

Lower-risk choice: disclaim + add one concrete counterexample for
the most visible field (probably `prob`).

### S1.2 Decidability theorem missing

The earlier plan included a Decidability theorem (polynomial-time
checker) and an `Ω(2^|V|)` lower bound for frameworks omitting the
collider-witness component. Both are absent from `paper/main.tex`.

Without these, §3's contribution is "framework + composition" only.
POPL standard wants complexity / decidability characterization.

Minimum action: add a Decidability theorem (polynomial-time
certificate checking is already implicit in §3.3); explicitly cite
the polynomial bound on the certificate-checking algorithm. The
lower bound can be marked future work.

### S1.3 "Zero-sorry verification" claim needs scope clarification

`paper/main.tex` §4 last sentence:

> We achieve a zero-sorry verification of this pipeline in Lean 4.

Ambiguous between (a) syntactic forward-reverse pipeline (current
NeurIPS-level Lean artifact, plausibly zero-sorry) and (b) full
`SheafMAGWalk` (sheaf-realization layer, currently sketched). A
reviewer who reads the artifact will check.

Recommended replacement:

> We achieve a zero-sorry mechanization of the syntactic
> compilation pipeline (`Trail → BayesBallPath → MAGWalk →
> Reachability`) in Lean 4. The sheaf-realization layer is sketched
> in Appendix B; full mechanization is future work.

### S1.4 Appendix B counterexample has `sorry`

`paper/main.tex` Appendix B contains:

```
-- Proof omitted for space, validates topological mismatch
```

This is the §1 textbook bug counterexample — the paper's entire
motivating example. It cannot be `sorry`'d. Complete the proof
(should be reusable from existing NeurIPS Lean artifact).

### S1.5 Appendix C is a stub

`paper/main.tex` Appendix C "Dual Witness Upper Bound" is a single
comment line with no statement or proof. Either delete or fill in.
Recommendation: delete; absorb into main §3 if relevant, or omit.

### S1.6 LaTeX compile risk: missing `hyperref`

`paper/main.tex` uses `\href{...}{...}` inside `\authorsaddresses{}`
but does not `\usepackage{hyperref}`. Compile will fail or `\href`
will not render. Add `\usepackage{hyperref}` to preamble.

## Severity 2 — Quality improvements

### S2.1 Add explicit "three questions" framing to §2

`20260522--structure.md` §2 specifies three concrete consumer
questions that Pearl cannot answer:

```
how many bits can pass through this path?
does this hidden source affect action?
can this cut be logged, controlled, or certified?
```

Currently `paper/main.tex` §2 only has the abstract "qualitative
separator vs quantitative channel" framing. Adding the three
specific questions strengthens the gap argument.

### S2.2 Add "doesn't say Pearl wrong" rhetorical framing to §2

`20260522--structure.md` §2 has this rhetorical move:

> It doesn't say Pearl is wrong. It doesn't say causal inference is
> inadequate. It doesn't say information theory needs a new
> foundation. It says: at the moment of type coercion, there is no
> legal derivation.
>
> This is the most precise failure localization the PL community
> knows how to articulate — precise to a single inference rule's
> existence.

This frame defuses Pearl-defenders preemptively. Currently absent
from paper. Adding as one paragraph in §2.2 closing reduces hostile
review risk.

### S2.3 Add AI Control connection in §9 (Greenblatt-Shlegeris 2024)

`20260522--reuse.md` §9.4 contains:

> The AI Control programme (Greenblatt-Shlegeris et al. 2024) argues
> for treating models as untrusted insiders and controlling channels
> rather than understanding internals. The channel-formation rule
> provides the type-theoretic underpinning for that operational
> stance.

Currently missing from `paper/main.tex` §9. Adding gives AI safety
community a direct citation hook.

### S2.4 Add Composition theorem's independence side-condition formally

`paper/main.tex` §3.2 says "whenever the merge at `t` is
independent" without defining "independent". Reviewer will ask: in
what sense — measure-theoretic product, graph-theoretic absence of
v-structure, conditional independence?

Add one line defining the side condition formally (likely
measure-theoretic product on stalks, since `merge` produces a
joint).

### S2.5 Add Furuya / Nikolaou defense to Related Work

The 2026-05-22 discussion identified that the framework distinguishes
itself from Nikolaou-style "composed function packaged in fancy
language" by following Furuya's stance of explicit boundary
specification. Currently `paper/main.tex` §10 does not cite or
contrast either.

Recommended insertion in §10:

> By contrast with neural-operator approaches that lift Transformer
> layers to infinite-dimensional operator spaces (Nikolaou
> [cite]), we make no expressivity or analytic claim about neural
> networks. Our stance aligns with Furuya [cite], who treats
> injectivity in infinite dimensions only under explicit
> Sobolev/Green's-operator boundary specification.

### S2.6 Add AI-BOM term explicitly in §7

`20260522--reuse.md` §7 introduces the term **AI Bill of Materials
(AI-BOM)**. The paper §7 describes the concept but does not coin or
use the term. Adding the term gives regulators and policy-paper
follow-ups a label.

### S2.7 Markov categories cross-reference in §5

`20260522--reuse.md` §5 last paragraph cross-references Markov
categories (Fritz) as an alternative stalk-typing scheme. Paper §5
omits this. Adding strengthens "internal machinery, swappable"
claim and pre-empts "why not Markov categories?" review question.

### S2.8 Register annotations on §3 theorems

`20260522--reuse.md` adds `Register: structural` /
`Register: type-theoretic / by-definition` lines on each theorem in
§3. These annotations clarify the proof obligation strength to
reviewers. Currently absent from paper. Low-cost addition.

### S2.9 Three-stage labels in §4 pipeline

`20260522--reuse.md` §4 organizes the pipeline as three explicit
named stages (**Normalize**, **Eliminate the collider treaty**,
**Realize on F**). Paper §4 uses a forward/reverse split instead.
Both are valid; the three-stage labeling matches the formation
rule's four obligations more cleanly. Optional restructure.

## Severity 3 — Nice to have

### S3.1 Artifact availability statement

POPL strongly expects artifact evaluation. The paper has no
"Code and proofs available at <URL>" line. Add as footnote on the
first page or to the contributions list.

### S3.2 Conclusion is weak

`paper/main.tex` §11 Conclusion focuses on measure-theoretic
extension as future work. The §7–9 industrial / safety arc is not
echoed. Add one sentence connecting back to governance-topology
audit.

### S3.3 Three-step §3 framing not explicit

`20260522--structure.md` §3 specifies a three-step decomposition:

1. inspection (downstream theorem parameter type vs Pearl cut type)
2. type-theoretic construction (formation rule + admissibility)
3. composition soundness (capacity sum + merge independence)

Paper §3 implements steps 2 and 3 but does not label them
explicitly. Optional restructure for clarity.

## Estimated work

| Severity | Items | Est. time |
|----------|-------|-----------|
| S1 | 6 | ~1–1.5 weeks |
| S2 | 9 | ~3–4 days |
| S3 | 3 | ~1 day |

Total to fully address: ~2 weeks. Minimum (S1 only): ~1 week.
