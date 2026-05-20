# POPL Paper Reframing — 3-Act Structure

**Date:** 2026-05-20
**Status:** Active. Mode C tidy-up complete. Integration of technical debts (Act 3) in progress.
**Companion:** `20260520_debt1_factorization.md`, `20260520_debt2_dual_witness.md`.

---

## Title

> Beyond Boolean Intersections: A Verified Bisimulation and Trace Decompiler
> for Causal Graphs

## Three-Act Structure

### Act 1 — The Bug in the Math Textbook

For decades, two textbook characterizations of d-separation — Pearl's trail-blocking predicate and Lauritzen's moralized ancestral graph — have been treated as unconditionally equivalent. We discovered and formalized a **mechanized counterexample** demonstrating that the unrestricted equivalence is **false**.

### Act 2 — The Compiler & Decompiler

To repair the equivalence, we build two verified transformations:

**Forward compiler (Certified Trace Optimizer):** Compresses a raw operational trace (`Trail`) into a dense reachability IR (`MAGWalk`).
**Reverse decompiler (Exploit Witness Synthesis):** Constructively synthesizes a concrete `Trail` exploit witness from an abstract reachability assertion.

### Act 3 — The Vision: Quantitative Information Flow

The verified graph computation system provides the **zero-sorry foundation** for Shannon-level quantitative security bounds.

The QIF pipeline (fully collapsed into native `condMutualInfo` framework):

```
d-separation
  → conditional independence (Markov bridge)
  → conditional DPI
  → cut-set bound: stateLeakage P ≤ C
  → entropy gap: H(S|T̃) ≤ H(S|T_full) + C
```

Two application-layer debts are currently being closed:
- **Debt 1**: Derive `IsMarkovChain` from explicit product factorization for the showcased instance.
- **Debt 2**: Provide a non-tautological verified upper-bound certificate from a dual KL witness.

---

## Why This Framing

The 3-act framing highlights the **mechanized counterexample** as the hook, the **compiler/decompiler** as the PL core, and the **QIF pipeline** as the quantitative payoff.

---

## Code Inventory

### Proved, zero-sorry — `CausalQIF/DSeparation/`
- `Counterexample.lean`, `Trail/*`, `BayesBall/*`, `MAGWalk/*`, `TraceSynthesis/*`.

### Proved, zero-sorry — `CasualQIF/` core
- `Graph/*`, `Probability/*` (Mode C native), `CausalModel/*`, `InformationFlow/*`, `Main.lean`.

### In Progress
- Debt 1 (Product Factorization) & Debt 2 (Dual KL Witness): Sandbox complete, integration starting.
