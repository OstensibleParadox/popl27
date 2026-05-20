# Debt 1 — Deriving `FactorizesOverDAG` from Product Factorization

**Date:** 2026-05-20
**Status:** In Progress. Tidy-up (Mode C) complete. Sandbox implementation in `scratch_markov.lean` ready for porting.
**Layer:** Act 3 (QIF application layer). Does not affect Acts 1–2 (bisimulation core).
**Companion:** `20260520_paper_repitch.md`, `20260520_debt2_dual_witness.md`.

> **Note (2026-05-20):** Under the 3-act paper reframing, this debt is an
> application-layer hypothesis in the QIF pipeline (Act 3), not a gap in the
> core graph-semantic bisimulation (Acts 1–2). The bisimulation,
> counterexample, and decompiler are self-contained and fully proved regardless
> of whether this debt is closed.

---

## What Debt 1 actually is

*Note: This gap is tracked as an open problem in [README.md:L237](file:///Users/ostensible_paradox/Documents/neurips26/verification/README.md#L237) of the `neurips26/verification` repository.*

Inspecting `CausalQIF/CausalModel/Factorization.lean`:

```lean
def FactorizesOverDAG (G : Graph.DAG V) (CI : CondIndepPredicate Ω V) (P : Probability.FinitePMF Ω) : Prop :=
  ∀ X Y Z : Finset V, DSeparation.dSeparates G X Y Z → CI P X Y Z
```

`FactorizesOverDAG` is **not** product factorization. It **is** the Global Markov Property stated as an assumption. Debt 1 = derive `FactorizesOverDAG` from a recursive product factorization `P(V) = ∏_i P(v_i ∣ parents(v_i))`.

## Why the textbook strategy is the hardest possible route

Step 3 in full DAG generality is the **ordered-Markov / topological-order / moralization metatheorem**. This is a mathlib-scale formalization.

## Representation problem

The **entire downstream zero-sorry chain** is hardwired to flat positional tuples. **Do not retype the QIF core.** It is zero-sorry; perturbing it is pure loss.

## Correct architectural seam

Put product factorization **strictly upstream** of `FactorizesOverDAG`, and provide a marshalling lemma onto the flat tuple PMF the chain consumes.

```
   ProductFactorizes G P       (new module, on Cfg V Ω := (v : V) → Ω v)
            │ prove ⇒
            ▼
   FactorizesOverDAG G CI P    (derived lemma)
            │  unchanged
            ▼
   zero-sorry QIF chain         (untouched)
```

## Two levers

### Lever 1 — Reuse the verified moral-graph engine
Reuse the existing verified moral-graph reachability to discharge Debt 1.

### Lever 2 — Instance escape hatch
For the linear chain `0 → 1 → 2`, *product factorization ⇒ `IsMarkovChain P`* is a **direct computation**.

## Recommended plan

1. Pick **instance-restricted** for POPL submission.
2. Implement `CausalQIF/CausalModel/ProductFactorization.lean`:
   - `ProductFactorizes_chain3 G v0 v1 v2 P`
   - `isMarkovChain_of_productFactorizes_chain3`
3. Marshalling: state directly on the flat `α × β × γ` type.
4. Defer the general theorem to "Future work."

## Honest framing of the closed scope

- Closed: on the showcased instance, explicit product factorization produces the exact CI premise.
- Open: general DAG `FactorizesOverDAG`.
