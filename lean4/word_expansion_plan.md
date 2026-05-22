<proposed_plan>
# SIGPLAN-Scale Expansion Plan: Codes & Maths First, Prose & Framing Second

## Summary
- Target a **20-25 page main body** in the SIGPLAN `acmart` template, not an ACM `sigconf`-style 9-page shape. The goal is **natural density**, not padding.
- Split the work hierarchically:
  - **Blocker: Codes & Maths**  
    Stabilize the proof-story, example choice, and lemma/proof-sketch mapping.
  - **Synthesis: Prose & Framing**  
    Rebuild the manuscript around that stable technical spine, with richer diagrams, examples, and proof sketches.
- Use the older unused proof material in [`/Users/ostensible_paradox/Documents/popl27/DSeparation/`](/Users/ostensible_paradox/Documents/popl27/DSeparation/) and [`/Users/ostensible_paradox/Documents/neurips26/verification/`](/Users/ostensible_paradox/Documents/neurips26/verification/) as **shape reservoirs** for exposition and proof sketching, not as places to invent new foundations.

## 1. Codes & Maths
- Keep theorem names and core statement shapes unchanged.
- Reuse the existing proof skeletons rather than rewriting them:
  - forward Bayes-ball lift / certification / compression from [`DSeparation/Equivalence.lean`](/Users/ostensible_paradox/Documents/popl27/DSeparation/Equivalence.lean)
  - reverse normalization from [`DSeparation/TraceSynthesis/Assembly.lean`](/Users/ostensible_paradox/Documents/popl27/DSeparation/TraceSynthesis/Assembly.lean)
  - alternate-variable skeletons from the older unused trees in `popl27` and `neurips26`
- Build one **worked Bayes-ball example** around `collider3`:
  - show an explicit `outOf -> into -> outOf` state-machine branch
  - show one `RequiredState` certification step
  - show the compression into a `MAGWalk.jump`
- Expand the reverse proof story around the exact lemma chain already present in code:
  - `exists_split`
  - `ancestor_escape`
  - `bad_child_survives`
  - `escape_path_survives`
  - the count-decrease lemmas
  - the final well-founded descent / `Nat.find` wrapper
- Keep the QIF bridge mathematical content intact, but move it out of the compressed architecture prose so its dependency story is explicit.

## 2. Prose & Framing
- Reorder the paper so the body reads like a PL paper, not a compressed artifact report:
  - **Section 2.3 Counterexample**: expand to about **2 pages**
  - **Section 3 Architecture**: expand to about **5-6 pages**
  - **Section 4 Forward Soundness**: expand to about **3-4 pages**
  - **Section 5 Reverse Witness Extraction**: expand to about **5-6 pages**
  - **Section 6 QIF Bridge**: expand to about **3-4 pages**
  - **Section 7 Mechanization Methodology**: expand to about **1-2 pages**
  - **Section 8 Related Work**: expand to about **1.5-2 pages**
  - **Section 9 Conclusion**: expand to about **1 page**
- Treat those numbers as **local ceilings**, not simultaneous maxima. The final body should land around **22-25 pages**, not 30.
- **Counterexample expansion**
  - Add a visual `chain3` diagram.
  - Show which trail the trail-blocking semantics accepts and how moralization deletes an endpoint.
  - State explicitly that textbook treatments often assume disjointness implicitly, while this paper makes it explicit.
- **Architecture expansion**
  - Give one small example for each layer.
  - Show `DisjointSets` on a clean example and show it failing on endpoint-in-`Z`.
  - Add a worked `MAGWalk` compression example.
  - Expand `OpenTrace` with one local non-blocking proof and its meaning.
- **Forward expansion**
  - Add one complete Bayes-ball case analysis on the `collider3` example.
  - Include a short pseudocode or invariant-oriented description of `compress`.
  - Make the `RequiredState` invariant visible as the reason certification works.
- **Reverse expansion**
  - Give `route_improves_of_bad` at least a page of proof sketch.
  - Present the helper lemmas as informal statements, not just names in a footnote.
  - Add a figure showing strict decrease of the bad-collider measure under normalization.
- **QIF Bridge expansion**
  - Move the two-stage factorisation split out of the compressed architecture section into its own standalone section.
  - Add an architectural diagram for upper stage / joint / lower stage.
  - Give the dual KL witness theorem a statement plus proof outline, not only a one-line mention.
- **Mechanization Methodology**
  - Explain what Lean 4 made easy: well-founded recursion and proof-carrying normalization.
  - Explain what was hard: 4+ variable row/column expansion and why the two-stage split is necessary, not cosmetic.
  - Frame this as advice to other formalizers, which PL reviewers usually value.
- **Related Work**
  - Expand the comparison with Anna Zhang's work.
  - Make the contrast with Fritz-Klingler precise: their framework avoids moralization; this work mechanizes the legacy operational/trail definition and its correction.
  - Keep this as a real discussion section, not a citation list.
- **Conclusion**
  - Add a short future-work paragraph on numeric PMF instances, targeted imports, and the possible measure-theoretic lift.

## 3. Section Order
- Use the following manuscript order:
  - Intro
  - Background / Counterexample
  - Architecture
  - Forward Soundness
  - Reverse Witness Extraction
  - QIF Bridge
  - Mechanization Methodology
  - Related Work
  - Conclusion
- That ordering matches the technical dependency graph:
  - graph equivalence first
  - witness extraction second
  - QIF bridge after the graph core is fully established
  - methodology and related work after the core claims are already legible
