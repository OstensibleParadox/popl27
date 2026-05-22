


# 前言：POPL convention

POPL 历来收的是 **observation + principle + framework + tool** 四件套，不是单纯 bug fix。

- **POPL 不爱**： “我们找了 bug，修了”   → (PLDI / CAV bar)  
- **POPL 爱**： “我们发现 type discipline 缺失，给出 typed framework，证明 soundness，实现 + benchmark，bug 是最小实例”

---

### 典例

**Liquid Types** (Rondon-Kawaguchi-Jhala POPL 2008)  
- **obs**： Hindley-Milner 不够 expressive  
- **principle**： refinement via predicate abstraction  
- **framework**： liquid type system  
- **tool**： DSolve  

**Iris** (Jung-Krebbers-Birkedal POPL 2015)  
- **obs**： sep logic 难复用  
- **principle**： higher-order ghost state + invariants  
- **framework**： Iris connectives  
- **tool**： Coq library  

---

###  New Frame 完美贴合模板

- **obs**： Pearl 的 `cut : Set Vertex` 在 type coercion 时断  
- **principle**： typed boundary certificate (channel-formation rule)  
- **framework**： SheafMAGWalk  
- **tool**： Lean artifact  
- **bug**： POPL d-sep 反例 = 最小实例 (motivating §1)  

---

# Abstract 

"我们重新定位 interpretability 困境的本质：它不是 inscrutability 问题，是 boundary mis-specification 问题"。后者对 PL/security 受众是 deeply familiar 的 move——Dijkstra 1968 对 goto 做的事，Reynolds 对 representation independence 做的事。把一个看起来无法 attack 的问题 reframe 成一个其实是 type discipline 问题的问题。


# §1 ： Motivating example，capability-based security 的 lineage 锚定。

    "Consider this textbook bug in POPL d-separation: ..."
    
- Reynolds-style polymorphic type discipline
- Pierce-style behavioral type
- Wadler-style linearity
- 都在写各自的 boundary identification paper——这一句把 POPL27 paper 放进那个 lineage，而不是放进 Pearl-vs-Rubin 的争论里。
-  OS 安全圈的标准 move：Saltzer-Schroeder 1975 没有说"现有 OS 不安全"，他们说"现有 OS 在 capability transfer 的瞬间没有 well-defined invariant"。整个 capability-based security 是从那个 瞬间 的 type discipline 长出来的。

# §2 的锚定：Pearl fails not at causality, but at boundary formation. 

### 1.1 What Pearl supplies

Pearl fails not at causality, but at boundary formation.

Pearl decides one question: *can this path be causally active?* 

Given a causal DAG `D` and a conditioning set `Z`, Pearl decides:

```text
d-sep(X, Y | Z) :  every path p from X to Y in D
                   is blocked under Z by the collider treaty.
```

This is a Boolean predicate on the syntactic graph. Nothing more.

### 1.2 What downstream consumers need

The question every downstream consumer — NeurIPS-style information-flow
certificates, regulatory audits, QIF leakage bounds, interpretability
claims — actually asks is different:

To use a cut in any of the following theorems, the consumer needs
data Pearl never supplies:

```text
Theorem                       Argument Pearl does not supply
─────────────────────────────────────────────────────────────────
Shannon Cut-set Bound         channel object with rate, capacity
Conditional DPI               Markov kernel + valuation
KKT / Blahut-Arimoto          convex problem on exp-family stalk
Counterfactual identification stalk-level intervention semantics
QIF leakage bound             stateLeakage + cutCapacity as numbers
```
Three observed pathologies all surface the same defect:

```text
(a) NeurIPS  : h_cap : I_cut ≤ C must be imported as external premise.
(b) Lean QIF : condMarkov must be hypothesized, not derived.
(c) POPL d-sep : DisjointSets must be added to repair endpoint-in-Z.
```
```text
how many bits can pass through this path?
does this hidden source affect action?
can this cut be logged, controlled, or certified?
```

Pearl's machinery does not answer these. The failure point is precise:

```text
the moment we ask a qualitative causal separator
to act as a quantitative information channel.
```

- 它不说Pearl 错了。 
- 它 没有 说：causal inference 不够用。 
- 它 没有 说：information theory 需要新基础。
它说的是：在 type coercion 的瞬间，没有合法 derivation。
--------这是 PL 语言里最精确的 failure localization——精确到一个 inference rule 的存在性问题。



# 3的锚定：composition soundness————from CausalQIF 的 QIF ambient elaboration。

分三步走。
1. 第 1 步的工作是 inspection（下游定理参数类型 vs Pearl cut 类型）。不需要新数学，需要把 §6 的 concrete failures（h_cap、condMarkov、DisjointSets、per-edge bound）整理成 type mismatch table。
2. 第 2 步的工作是 type-theoretic construction——formation rule + 它的 admissibility。CausalQIF 在 QIF ambient 是它的 worked elaboration（也就是 paper 的 mechanization backbone）。
3. 第 3 步的工作是 composition soundness——§3.2 那条 capacity 加和 + merge independence 边条件。这是 paper 的真正定理（在 PL register 里，不是数理 register）。三步的工作量都 PL-shaped，都不需要"以防万一"的 hedge。




Sections 7–9 extend the rule to agentic systems
and industrial audit.



 Sections 4–6 record the internal
mechanism (compilation pipeline, sheaf realization, concrete failures of the old boundary). 

# 20260522--reuse.md
# Old Reference Material

