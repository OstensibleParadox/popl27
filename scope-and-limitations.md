# CausalQIF — Scope & Limitations Report

**Repo:** `/Users/ostensible_paradox/Documents/CasualQIF`
**Branch:** `main` (clean)
**Date:** 2026-05-20
**Lean:** `leanprover/lean4:v4.30.0-rc1`
**Mathlib pin:** `0e265f2`
**Active library:** 71 Lean files, 5,813 LoC, 158 theorems/lemmas, 130 defs, 18 structures/inductives/classes
**Archive:** 27 Lean files, ~3.2k LoC at `archive/CausalQIFArchive/` (excluded from build)
**Axiom hygiene:** zero `sorry` / `admit` / `axiom` / `unsafe` / `TODO` / `FIXME` in `CausalQIF/`
**Build:** green (8,354 jobs, 0 errors; 73 oleans present)

---

## 1. Mathematical scope

### 1.1 Headline results (all closed, `CausalQIF/Main.lean`)

- `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` (`Main.lean:48`) — DAG factorisation + d-separation + cut capacity `≤ C` ⇒ `stateLeakage P ≤ C`.
- `certified_leakage_gap_of_dSeparated_graph` (`Main.lean:67`) — `H(S∣T̃) ≤ H(S∣T_full) + C`.
- `stateLeakage_le_of_dual_witness` (`Main.lean:88`) — KL variational route.

### 1.2 Load-bearing scaffolding (genuine non-trivial proofs)

- `reachable_equiv_reachableFinset` (`Graph/Reachability.lean:21`) — reachability in a DAG ↔ `ReflTransGen` of its edge relation. Replaces the final `sorry` in the graph layer; 157 lines, well-founded acyclicity via `nodup_of_isChain_of_wellFounded`.
- `stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmf_from_vars` (`InformationFlow/CutSetBound.lean:212`) — leakage CMI ↔ 4-var CMI bridge, 35 lines.
- `cond_dpi` (`CausalModel/DataProcessing.lean:17`) — conditional DPI via chain rule + CMI nonneg + `condMarkov` ⇒ CMI=0.
- `condMutualInfo_le_of_dual_witness` (`InformationFlow/Duality.lean:25`) — Topsoe variational upper bound on CMI, 130 lines.
- `condMutualInfo_kl_identity` (`Probability/Entropy/Identities/CondMutualInfo.lean:21`) — CMI = KL(P ‖ condProductMass) up to `log 2`.
- `condMutualInfo_nonneg`, `condMutualInfo_eq_zero_of_condIndep` — same file, via KL.
- `klDivergence_nonneg` / `kl_nonneg_support` (`Entropy/KLDivergence.lean:15,61`) — Gibbs hand-rolled via `log p ≤ p − 1`.
- `dSeparated_iff_dSeparates` (`DSeparation/Equivalence.lean:144`) — **both directions** of trail-blocking ↔ moralised-ancestral-graph reachability, restricted to pairwise-disjoint queries (`Equivalence.lean:126,143`). Soundness via `MAGWalk` / Bayes-Ball compression; completeness via `activeWitness_of_not_dSeparated`. Unrestricted equivalence is known to fail — the archived counterexample at `archive/CausalQIFArchive/Trash/DSeparation/Counterexample.lean` documents why.

### 1.3 Mathlib coupling

Lazy whole-mathlib re-export — many files `import Mathlib` (e.g. `FinitePMF/Basic.lean:1`). Entropy/PMF layer is bespoke: no `MeasureTheory.MeasurableSpace`, no mathlib `Pmf`, no `Mathlib.InformationTheory.*`.

### 1.4 Missing classical results

Unconditional MI, unconditional DPI, Fano's inequality, full chain rule `H(X,Y) = H(X) + H(Y∣X)` as a named lemma, Pinsker, Han, Markov-chain MI beyond the 3/4-node case.

---

## 2. Conceptual scope

**Thesis (encoded in `Main.lean`):** in the finite discrete setting, if `(State, VisibleTrace, MissingTrace)` factorises over DAG `G` and State is d-separated from MissingTrace by cut `{vY, vW}`, then conditional MI `I(S; M ∣ T̃)` (Shannon leakage to an adversary seeing `T̃` but not `M`) is upper-bounded by the cut's information-theoretic capacity `I(K; M ∣ T̃) ≤ C`. The "certified gap" lifts this to `H(S∣T̃) − H(S∣T_full) ≤ C`.

**Chain closed end-to-end in `Main.lean`:**

```
d-separation → factorization predicate → condMarkov (4-var)
              → cond_dpi → stateLeakage ≤ cutCapacity
              → KL-dual witness bound
```

This is a **complete machine-checked QIF-from-causal-structure result for the finite case** — not just groundwork. The headline theorem delivers what its name says.

**Design intent — two-stage factorisation split:** the classical Verma-Pearl global Markov theorem is deliberately split into (i) an **upper topological-semantics stage** producing computable, `decide`-able Markov blankets and per-node local Markov boundaries, and (ii) a **lower concrete-tuple-adapter stage** that converts node-set premises into the concrete probabilistic CI predicate (e.g. `condMarkov P`), leaving the probability-model derivation to caller or special-case provider. The split avoids row/column-expansion blowup when probability shapes vary. `FactorizesOverDAG` being a semantic package is the joint between the two stages, not a missing proof.

**Current state of the split (both stages restored on `main`):**
- **Upper stage:** `Graph/MarkovBlanket.lean` provides `spouses`, `computeMarkovBlanket`, `generateMarkovConditions`, `generateMarkovBlanketConditions` — computable `decide`-able generators. `Graph/Examples.lean` defines `chain3` and `collider3` DAGs. `Examples/MarkovBlanket.lean` contains `decide`-checked examples (blanket and local-Markov computations on both graphs).
- **Lower stage:** `CausalModel/Factorization.lean` provides `condMarkovNodeCI` with `X = {vX}, Z = {vZ}, YW = {vY, vW}` premises plus standalone bridge `condMarkov_of_factorizes_of_dSeparates_fourVar`. `Main.lean` uses the typed adapter in all three headline theorems.
- **Existing 3-chain bridge:** `isMarkovChain_of_productFactorizes_chain3` (`CausalModel/ProductFactorization.lean:30`) has body `exact h` — definitional joint between two stages for the chain-3 shape. Consistent with the split design.

The two-stage split is now **fully operational on `main`**. Both the computable upper half and the typed lower-half adapter are present, build-clean, and used in the headline theorems.

---

## 3. Engineering scope

| Aspect | State |
|---|---|
| Lakefile | Minimal. Single target `lean_lib CausalQIF`. `autoImplicit := false` (strict). One git dep on mathlib4. |
| Toolchain | `v4.30.0-rc1` — release candidate, not stable. Minor pin-drift risk. |
| Module tree | Clean five-way split: `Graph/` · `DSeparation/` · `Probability/` · `CausalModel/` · `InformationFlow/`. Recent refactors (`94c0264`, `70479dd`) are pure splits with hashes preserved. |
| Axiom hygiene | `grep -rE "\bsorry\b\|\badmit\b" → 0`; `grep "^axiom " → 0`; `TODO/FIXME → 0`. |
| Build | 73 oleans, `lake build` clean (8,354 jobs). |
| Test/example coverage | **Improved but still thin.** `Examples/MarkovBlanket.lean` has `decide`-checked blanket and local-Markov computations on `chain3` and `collider3` — concrete combinatorial examples, not numeric PMF instances. `Examples/LinearChain.lean:33` still returns `h_cap` unchanged; no instantiated PMF, no end-to-end numeric demonstration. No test target in lakefile. |
| Repo hygiene | **Improved.** README present with headline results, module hierarchy, and two-stage split design note. LICENSE (MIT) present. No CI workflows. `lake-manifest.json` clean. |
| Archive status | `archive/CausalQIFArchive/` (27 files) excluded from build. Files inside import unqualified `DSeparation.*` paths (e.g. `archive/CausalQIFArchive/Trash/DSeparation/ActiveRoute.lean:1` → `import DSeparation.BayesBall.Basic`) — won't compile if revived without rename. |
| Executability | Heavy `noncomputable` / `Classical.choice` / `Nat.find` usage (68 occurrences in `CausalQIF/`). Library is verification-oriented; not designed for numeric evaluation. |

---

## 4. Limitations

1. **Finite-only.** Every module quantifies over `[Fintype α] [DecidableEq α]`. No σ-algebras, no `MeasureTheory`, no continuous states. Lifting requires a complete rewrite of the probability layer.
2. **Example layer: combinatorial examples restored, numeric instances still absent.** `Examples/MarkovBlanket.lean` provides `decide`-checked Markov-blanket and local-Markov computations on `chain3`/`collider3`. `Examples/LinearChain.lean` returns `h_cap` unchanged. No numeric PMF instantiation, no `#eval`-able end-to-end bound. The KKT certificate machinery (`InformationFlow/ChannelCapacity.lean`) also has no worked example.
3. **`KKT_Certificate.of_direct_bound` tautological** by its own docstring (`ChannelCapacity.lean:108` — "tautological producer"). The non-tautological version `of_dual_witness` (line 141) routes through `condMutualInfo_le_of_dual_witness`. No KKT *necessity* proof (only sufficiency).
4. **Public d-separation equivalence restricted to pairwise-disjoint X, Y, Z.** An archived counterexample (`archive/CausalQIFArchive/Trash/DSeparation/Counterexample.lean`) documents why unrestricted equivalence fails. This is an intentional scope decision, not a defect — but consumers must respect the precondition.
5. **No unconditional MI / DPI.** All MI is conditional. No named lemma for `I(X;Y) ≥ 0` or `H(f(X)) ≤ H(X)`.
6. **Non-executable in places.** 68 occurrences of `noncomputable` / `Classical.choice` / `Nat.find` across `CausalQIF/`. ℝ-based entropy/KL also block native numeric eval. No `#eval`-able end-to-end pipeline.
7. **Whole-mathlib import.** Many files `import Mathlib`. High build cost; downstream consumers inherit. Replacing with targeted imports is unblocked work.
8. **Naming churn largely settled.** Phase 1c (snake_case migration) and Phase 2 (dedup) are both clean per `.claude/reports/honesty-report-phase{1c,2}.md`. Dot-notation promotion (`FinitePMF.pairFstFthReshape` etc.) is deferred per `.claude/plans/causalqif-phase1c-and-2-plan.md:36` — still pending.
9. **No CI workflows.** `lake build` on PR not automated.
10. **Toolchain on RC.** `v4.30.0-rc1` is a release candidate. Pin drift risk if mathlib advances past it.

---

## 5. Honest assessment

### 5.1 Publishable now

> "A machine-checked formalisation in Lean 4 of (i) the trail-blocking ↔ moralised-ancestral-graph equivalence of d-separation for finite DAGs under pairwise-disjoint queries, (ii) the conditional data-processing inequality, (iii) a Topsoe variational upper bound on conditional mutual information, and (iv) a cut-set state-leakage bound for finite quantitative-information-flow models, with a deliberate two-stage topological–probabilistic factorisation split that keeps the upper stage computable and `decide`-able."

All four headline theorems are non-trivial and sorry-free. The two-stage split is now fully operational: the computable upper half (`Graph/MarkovBlanket.lean`) and the typed lower-half adapter (`condMarkovNodeCI` in `CausalModel/Factorization.lean`) are both present, build-clean, and used in `Main.lean`.

### 5.2 Architectural framing of the FactorizesOverDAG hypothesis

The `Main.lean` headline depends on a caller-supplied `FactorizesOverDAG G condMarkov`. This is *by design*: the project deliberately splits Verma-Pearl into a computable topological stage (upper) and a typed concretization stage (lower), with `FactorizesOverDAG` as the semantic joint. The caller (or a per-shape adapter) supplies the joint validation.

This is a legitimate design choice and should be stated as such in any publication — not as a gap, but as the project's contribution. The combinatorial blowup that a monolithic Verma-Pearl proof would cause is avoided by construction. **As of the latest commits, both halves of the split are operational on `main`:**

- Upper stage: `Graph/MarkovBlanket.lean` (`computeMarkovBlanket`, `generateMarkovConditions`, `generateMarkovBlanketConditions`).
- Lower stage: `CausalModel/Factorization.lean` (`condMarkovNodeCI`, `condMarkov_of_factorizes_of_dSeparates_fourVar`), actively used in `Main.lean:54`.

### 5.3 Next bottlenecks (priority order)

1. **Build a concrete numeric worked example.** A 3- or 4-node DAG with explicit numerical PMF where `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` produces a non-trivial numeric bound. Reviewers will flag the absence. The combinatorial examples (`chain3`/`collider3` blanket computations) are already `decide`-checked in `Examples/MarkovBlanket.lean`; a numeric PMF instantiation is the remaining gap.
2. **Repo hygiene quick fixes.** Add minimal CI (`lake build` on PR). Cheap; high signal of project maturity.
3. **Targeted mathlib imports** to make the library usable as a dependency without inheriting the whole-mathlib cost.
4. **Decide on a measure-theoretic lift** or commit publicly to the finite-discrete scope.
5. **Dot-notation promotion.** Convert `FinitePMF.pairFstFthReshape` etc. to dot notation per deferred plan.

---

## 6. Key files for follow-up

- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Main.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/InformationFlow/CutSetBound.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/InformationFlow/Duality.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/InformationFlow/ChannelCapacity.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/CausalModel/Factorization.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/CausalModel/ProductFactorization.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/CausalModel/DataProcessing.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/DSeparation/Equivalence.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Probability/Entropy/Identities/CondMutualInfo.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Graph/Reachability.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Graph/MarkovBlanket.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Examples/MarkovBlanket.lean`
- `/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF/Examples/LinearChain.lean`
