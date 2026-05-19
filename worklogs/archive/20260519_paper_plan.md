> ARCHIVED 2026-05-19 — superseded by docs/ARCHITECTURE.md and CHANGELOG.md.
通过类型论强制（Dependent Typing）揭示概率因果模型核心的隐藏控制流。

### POPL 2027：Title Ideas
> "Beyond Boolean Intersections: A Type-Safe Mechanism for Extracting Certified Shannon Bounds from D-Separated Traces"  
> (超越布尔相交：一种用于从 D-分离轨迹中提取经核证香农上界的类型安全机制)

---

如果想挑战 POPL 27，我们必须把双向等价证明从一个被发现的事实，升级为一个被构建的系统的基础语义。

这是小猫的计划：一个完整的**安全信息审计语言引擎**：

**底层（语法与类型）**：节点就是程序的 Variable 声明，图定义就是程序的 AST。用 `DisjointSets` 规则卡住了语法的正确性。  
**中间层（核心 IR 编译）**：本文重头戏。`TraceSynthesis/` 子模块构成了一个纯血验证的中间语言处理机：正向的 `BayesBallPath.compress` 是 **Certified Trace Optimizer**（经核证的轨迹优化器），逆向的 `StaticRoute → OpenTrace → ActiveRoute` 是 **Decompilation of Semantic Flow**（流的反编译）。  
**上层执行模型（Quantitative Metric Bounds）**：这层不是在 `popl27` 里从零重造信息论，而是把 `neurips26/verification` 中已经存在的 `InfoTheory`、`DualCertificate`、`KKT Certificate` 和熵流边界接到 `popl27` 正在完成的 d-separation 图论地基上。贴合 26 年热点：**"Quantitative Information Flow" (量化信息流安全)**。目标是从绝对通/不通的布尔逻辑（d-sep）升华至具体的比特上界（Shannon Bound ≤ C bits），把"程序流静态分析"接到"信道容量代数上界"。

---

### 第一层：底层（AST 语法与资源控制类型系统）

**你的原意**：节点是 Variable，DAG 是 AST，`DisjointSets` 规则卡住了正确的边界。  
**升级话术**："A Type-Safe Graph Syntax for Conditional Flow"。  
在传统论文里，如果集合相交了还能计算，在计算机看来这是不可达状态，也就是经典的"悬挂指针（Dangling Pointers）"或"非法内存别名（Illegal Aliasing）"。你通过强类型层面的 `Disjoint X Z` 约束，相当于为图灵机建立了一个安全的**所有权模型（Ownership Model）**，保证了作为条件背景的变量 $Z$ 绝对不会被程序的运行态（活跃状态流）二次借用或修改。这个底层的纯净性（Purity），正是形式验证在底层语法检查时所要求的。

**已有资产**（`DSeparation/DAG/`、`DSeparation/Trail/Blocking.lean`）：
- `DAG` 结构：节点 `ℕ`，边 `Finset (ℕ × ℕ)`，无环性 `WellFounded`。
- `DisjointSets X Y Z` 谓词， pairwise-disjoint 前置条件。
- `Trail` 归纳类型与 `isBlocked Z` 阻塞谓词。

**还需构建**：一个真正的 AST 和类型检查器。需要定义一种小型语言（即使只有几个构造），写一个类型检查器函数 `check : AST → Result Type`，并证明 "类型正确 ⇒ `DisjointSets` 成立"。这大约需要 2–3 周的 Lean 开发。

---

### 第二层：中间层核心编解码器 (Trace Bisimulation via Flat IR)

**你的原意**：通过 BayesBall，正向为"经核证的轨迹优化器"，逆向为"流的反编译"，寻找 Existential witness。  
**升级话术**："Verified Bisimulation: Certified Compilation and Decompilation of Information Traces"。  
对于 POPL 来说，"等价性"是一个有点老套的词，但**"双向模拟（Bisimulation）"**与**"逆向工程的计算构造性生成（Constructive Decompilation）"**绝对是顶流。  
你可以自豪地宣称你的 Lean 4 模型不仅仅判定布尔值，而是提取（Extracts）程序的见证（Witnesses）。

**已有资产**：`DSeparation/TraceSynthesis/` 子模块已完成模块化重构，职责清晰：

| 子模块 | 职责 |
|--------|------|
| `TraceSynthesis/StaticRoute.lean` | `StaticStep` / `StaticRoute` IR；从 `dSeparationGraph.Reachable` 反编译到显式证据；`toMAGWalk`、`ofDSeparationGraphAdj`、`ofDSeparationGraphWalk`；通用 `append_nil` / `append_assoc` 结构引理。 |
| `TraceSynthesis/OpenTrace.lean` | `OpenTrace` 编译目标（局部非阻塞证明）；`isStepBad`、`countBadColliders`、`countBadColliders_cons`；`openTrace_of_countBadColliders_zero`（零坏对撞子 ⇒ OpenTrace）；`toActiveRoute`。 |
| `TraceSynthesis/MinimalWitness.lean` | 端点携带的 witness；`minRouteBadCountWitness`（`Nat.find` 包装器）；`normalized_route_exists_of_improves`。 |
| `TraceSynthesis/Split.lean` | `exists_split`：从非零坏对撞子计数中抽取第一处 bad collider；本模块只保留专用 splitter 逻辑。 |
| `TraceSynthesis/Assembly.lean` | 最终拼装；`route_improves_of_bad` 与 `activeWitness_of_not_dSeparated` 已闭合。 |
| `TraceSynthesis/Graph.lean` | `ancestor_escape`、`bad_child_survives`、`escape_path_survives`（rerouting 的核心图论引理）。 |
| `TraceSynthesis.lean` | **聚合入口，只做 import，不声明。** |

- **Forward（编译 / 抽象解释）**：给定操作语义级的凌乱微小轨迹（`Trail`），编译器通过 `BayesBall` 追踪方向状态（Typestate），**消除冗余变量（Colliders）**，优化并投射成更致密的 IR（`MAGWalk`）。关键定理：`dSeparationGraph_reachable_of_active_trail_disjoint`（`Equivalence.lean`）。
- **Backward（反编译 / 漏洞路径重建）**：当抽象层断言连通（存在数据流泄露风险），反编译器必须从被优化后的骨架图（MAG Graph）中**确定性地重构（Deterministically reconstruct）**一条原始代码级别的渗透攻击路线（`Active Trail Witness`）。关键定理链：`Reachable → StaticRoute → NormalizedStaticRoute → OpenTrace → ActiveRoute → ∃ Trail, ¬isBlocked`。在漏洞检测分析界，这就是传说中的"漏洞可利用性证明（Exploitability Certificate Generation）"。

**证明状态**：`TraceSynthesis` 反向 decompiler 已闭合。`route_improves_of_bad` 不再是 proof debt；当前 `lake build DSeparation.TraceSynthesis` 通过且无 `sorry`。新的 proof debt 边界已转移到 `InfoTheoryBridge.lean`，其中两个 `sorry` 是概率语义桥的显式 scaffold。

---

### 第三层：高层量化度量 (Quantitative Information Flow)

**你的原意**：从通/不通升华到具体的比特上限，融合 InfoTheory、KKT Certificate 和切塞边界。  
**升级话术**："From Qualitative Reachability to Algebraic Shannon Bounds in a Unified QIF Engine"。  
很多安全论文做数据流图（Dataflow graph），结论停留在 "0 还是 1"（会不会有信息泄漏），这在安全领域叫做非干涉性（Non-interference）。  
但近三年来，计算机安全和 POPL 最硬核的发展方向是 **量化信息流（Quantitative Information Flow, QIF）**：也就是我们不仅要知道泄露，我们还要知道确切会泄露多少 Bits！  
你的大招来了：通过底层的完全编译（d-sep 双向等价保证图拓扑的严谨度），你把 `neurips26` 已经形式化的信息论上层接到 `popl27` 的图论语义层。你在编译期的终极输出不只是一句 "Type Error: Information Leak"，而是 **"Compiler Warning: Expected Trace Leakage Bound ≤ 1.45 Bits (proven via Sub-modular Flow Bounds)"**！

**已有资产**（不在 `popl27`，而在 `neurips26/verification`）：
- `InfoTheory.lean`：完整的有限离散信息论基础——`FinitePMF`、熵、KL divergence、条件互信息、conditional DPI、chain rule、Markov 前提。全部从 Mathlib 第一原理证明（标 **C**）。
- `DualCertificate.lean`：静态证书（`prop1_static_ub`）与动态证书（`prop2_dynamic_lb`）的结构归约。
- `ChannelCapacity.lean`：KKT certificate 框架。
- `CaseStudy.lean`：线性链 bound 的端到端案例。
- `Screenability.lean` / `InternalImpossibility.lean`：自回归零割不可能性、可预测性路由不可能性。
- `IdentifiabilityGap.lean`：行为等价但审计不等价的有限 PMF 构造（Theorem 1，axiom-free）。

**真正缺的是桥，不是从零开始的信息论**：
- [x] 闭合 `popl27` 的图论双向等价与反向 witness decompiler，包括 `route_improves_of_bad`。
- [ ] 建立共同基础层，消除 `neurips26` 与 `popl27` 中几乎同构但物理隔离的 DAG 定义。
- [ ] 形式化 `d-separation ⇒ conditional independence`，即从图论语义进入概率图模型语义。
- [ ] 用这个桥替换 `neurips26` 中 cut-set capacity inequality 相关的外部 axiom（`neurips26` 中标记 **C/E** 的项）。

**因此第三层的正确定位是**：把 `neurips26` 已经建好的信息论楼层接到 `popl27` 的严格 d-separation 地基上，而不是在 POPL 项目中另起炉灶重写 `FinitePMF` 与熵库。

---

### The PL Dictionary (如何用 POPL 话术改写传统因果图)

为了彻底切入 POPL 的 Scope，你需要对名词进行一场"大换血"：

| 工程术语 | POPL 2027 话术 |
|---------|---------------|
| 因果图 (DAG) | 依赖图语法 (Dataflow AST) |
| 不相交前置条件 (`DisjointSets`) | 资源隔离的线性类型 / 别名控制 (Substructural / Affine Typing constraints against Aliasing) |
| Active Trail | 操作语义的操作轨迹 (Operational Traces of Semantics) |
| `MAGWalk` (道德图行走) | 静态分析的可达性中间件 (Reachability Abstract IR) |
| 对撞子跳转 (`MAGWalk.jump`) | 局部窥孔优化 / 操作宏 (Peephole Optimization / Semantic Fold) |
| `BayesBallPath.compress` | 经核证的轨迹优化器 (Certified Trace Optimizer) |
| `StaticRoute → OpenTrace → ActiveRoute` | 流的反编译器 / 漏洞可利用性证明生成器 (Decompiler / Exploitability Certificate Generator) |
| 互信息 / 切塞边界 (Cut-Set / Mutual Info) | 量化信息流安全容量 (QIF, Quantitative Information Flow Capacity Bounds) |

---

### 现有工程评估（更新版）

#### 第一层：类型安全语法
- **已有资产**：`DisjointSets` 谓词，`DAG` 结构（节点 `ℕ`，边 `Finset (ℕ × ℕ)`，无环性 `WellFounded`）。
- **还需构建**：小型表面语言 + 类型检查器 + "类型正确 ⇒ `DisjointSets`" 的证明。约 2–3 周 Lean 开发。

#### 第二层：中间编解码器
- **已有资产**：`TraceSynthesis/` 子模块已完成职责分离和 Phase 5 模块化清理。
  - 正向：`Equivalence.lean` 已证明 `dSeparated → dSeparates`（`DisjointSets` 下）。
  - 反向：`StaticRoute → OpenTrace → ActiveRoute → Trail` 管线完整，`activeWitness_of_not_dSeparated` 已由 `route_improves_of_bad` 驱动闭合。
- **还需构建**：用 "Bisimulation" 语言包装正向/逆向引理；继续推进 `InfoTheoryBridge.lean` 的概率语义桥（`d-separation ⇒ conditional independence`）。

#### 第三层：高层量化度量
- **已有资产**：`neurips26/verification` 中的完整信息论层（`InfoTheory.lean`、`DualCertificate.lean`、`ChannelCapacity.lean` 等）。
- **真正缺口**：图论到信息论的桥——`d-separation ⇒ conditional independence ⇒ MI 截断`。
- **执行顺序**：已闭合 `popl27` 图论 → 统一 DAG 基础层 → 建桥 → 替换 `neurips26` 的 **C/E** axiom。

---

*Last updated: 2026-05-19. Reflects Phase 5 cleanup: `TraceSynthesis` is closed; current proof debt is isolated to the `InfoTheoryBridge.lean` scaffold.*
