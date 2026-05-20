# Debt 2 — Capacity Sufficiency via Dual KL Witness

**Date:** 2026-05-20
**Status:** In Progress. Tidy-up (Mode C) complete. Sandbox implementation in `scratch_dual.lean` ready for porting.
**Layer:** Act 3 (QIF application layer). Does not affect Acts 1–2 (bisimulation core).
**Companion:** `20260520_paper_repitch.md`, `20260520_debt1_factorization.md`.

> **Note (2026-05-20):** Under the 3-act paper reframing, this debt is an
> application-layer hypothesis in the QIF pipeline (Act 3), not a gap in the
> core graph-semantic bisimulation (Acts 1–2). The bisimulation,
> counterexample, and decompiler are self-contained and fully proved regardless
> of whether this debt is closed.

> **Validity review (2026-05-20):** The diagnosis is correct:
> `KKT_Certificate.of_direct_bound` is tautological. The dual-witness producer
> is the right replacement. The implementation details below account for the
> **Mode C refactor**: role-based wrappers (like `I_YZ_W`) are replaced by native
> `condMutualInfo` over positional PMF projections (e.g., `pmfMargOutFst`).

---

## What Debt 2 actually is

*Note: The tautological `KKT_Certificate` structure originates from [FiniteQuerySandbox/ChannelCapacity.lean](file:///Users/ostensible_paradox/Documents/neurips26/verification/FiniteQuerySandbox/ChannelCapacity.lean), and its sufficiency metatheorem is marked as Open in [README.md:L240](file:///Users/ostensible_paradox/Documents/neurips26/verification/README.md#L240) of the `neurips26/verification` repository.*

Inspecting `CausalQIF/InformationFlow/ChannelCapacity.lean`:

```lean
def KKT_Certificate.of_direct_bound
    (P4 : FinitePMF (α × β × γ × δ))
    (C : ℝ)
    (h_bound : condMutualInfo (pmfMargOutFst P4) ≤ C) : KKT_Certificate P4 :=
  { C := C
    p_star      := marginalQuad_Snd P4
    per_symbol_I := fun _ => condMutualInfo (pmfMargOutFst P4)
    h_weighted_decomp := …  -- collapses to (Σ p_star) · CMI = 1 · CMI
    h_kkt_condition   := fun _ => h_bound
    … }
```

This constructor is a **tautological wrapper**: it takes the bound as input and packages it. Zero KKT content. `capacity_le_of_kkt` itself is correct algebra, but the library contains **no constructor that produces a non-trivial bound**. Debt 2 is exactly this gap: nothing in `CausalQIF/` derives the bound from a checkable certificate.

## The verified producer — dual KL witness

Standard variational identity (Topsøe / Donsker–Varadhan):

```
I(A; C | B) = E_b E_{a|b} D(P(C | a, b) ‖ P(C | b))
            ≤ E_b E_{a|b} D(P(C | a, b) ‖ ω(C | b))   for any ω(c|b)
```

Quantifying the KL bound uniformly over **all** inputs gives capacity sufficiency: the same witness ω caps the information for any input distribution.

Scaling convention: the entropy definitions use `log₂`, while the KL witness uses Lean's natural `Real.log`. Therefore the natural-log inequality proves `CMI * Real.log 2 ≤ C * Real.log 2`; the final bit-valued bound follows by dividing by `Real.log 2`.

## Framing nit — do not oversell

The math is the Topsøe / DV variational upper bound from `KL ≥ 0`. It does **not** use concavity of the MI functional. Paper-honest framing: *"verified upper-bound certificate from a dual KL witness."*

## The `conditionalPMF` trap — avoid

Phrase the variational bound under-the-integral, with the joint un-normalized; the conditional `P(c|a,b)` only appears implicitly as the ratio inside `log`. `0 · log(0 / x) = 0` falls out of `Real.log` conventions.

Skeleton:

```lean
theorem condMutualInfo_le_of_dual_witness
    (P3 : FinitePMF (α × γ × β))
    (ω : β → γ → ℝ)
    (h_ω_sum : ∀ b, ∑ c, ω b c = 1)
    (h_ω_pos : ∀ b c, 0 < ω b c)
    (C : ℝ)
    (h_bound : ∀ a b,
        ∑ c, marginalTriple_at P3 a c b *
              Real.log (marginalTriple_at P3 a c b /
                        (marginalTriple_FstSnd_swap P3 a b * ω b c)) ≤
        marginalTriple_FstSnd_swap P3 a b * (C * Real.log 2)) :
    condMutualInfo P3 ≤ C
```

## Why this clears the debt

`condMutualInfo_le_of_dual_witness` is the missing producer. Plug into the existing `KKT_Certificate.of_direct_bound` constructor: the `KKT_Certificate` structure suddenly has a real source.

```
   (ω, h_ω_sum, h_ω_pos, h_bound)
            │
            ▼
   condMutualInfo_le_of_dual_witness  →  h_cap : condMutualInfo (pmfMargOutFst P4) ≤ C
            │
            ▼
   KKT_Certificate.of_direct_bound    →  KKT_Certificate P4
            │
            ▼
   capacity_le_of_kkt                 →  condMutualInfo (pmfMargOutFst P4) ≤ C
```

## Action plan (Mode C)

1. **`CausalQIF/Probability/Entropy/KLDivergence.lean`** — add `def klDivergence` and `klDivergence_nonneg` wrapper.
2. **`CausalQIF/InformationFlow/Duality.lean`** (new) — implement `condMutualInfo_le_of_dual_witness` for 3-variable PMFs.
3. **`CausalQIF/InformationFlow/ChannelCapacity.lean`** — add `KKT_Certificate.of_dual_witness` converter.
4. **`CausalQIF/Main.lean`** — corollary `stateLeakage_le_of_dual_witness`.

## Support assumption — strict positivity v1

`h_ω_pos : ∀ b c, 0 < ω b c` is strong but the right v1. Real channels are full-support after ε-smoothing anyway. 

## Honest paper scope after Debt 2

Closed:
- **Sufficiency** — any dual witness `(ω, KL-bound)` mechanically yields a verified Shannon leakage bound.
- Auditor-style certificate: exhibit ω, machine checks KL bound, ship the bound.

Open:
- Converse / tightness.
- Blahut–Arimoto convergence.
- KKT necessity.
