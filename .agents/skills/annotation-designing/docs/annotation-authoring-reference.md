# QCP C Annotation 填写参考

本文件保留 QCP 语言、资源形状、循环不变量与失败分析细节。阶段顺序、命令与报告合同以 workflow 为准。

本文件给唯一 annotation owner 使用。目标是在 main root 内共同修改 spec、C annotation 和 `formal_case_lib` declarations，直到可交给 main-owned `finalize-delivery`。

## 允许修改

只能修改：

- 目标 `.c` 中的 spec、证明真正需要的普通 `Assert` 和每个循环前的 `Inv Assert`。
- 同一正式相对路径下 `formal_case_lib` 中的 mathematical spec declarations。

函数体中不得新增 `by local`、branch-control、普通 `Inv`、multi-inv 或 call `where`。

不得手工修改 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`，不得创建第二个 active Rocq lib。

## Spec 先行

先从题意写自然语言 `Signature`、`Preconditions` 和 `Output`，再写同义的 Rocq `Pre` / `Spec`，最后让 C function spec 和 loop invariant 引用这些性质。

Spec 来源是题目描述、输入输出格式和消除歧义所需的样例说明。C 只用于确认参数、资源和 helper 调用关系。若 current `formal_case_lib` 只有最小 imports seed，在其中填写自然语言 spec 的 Rocq 版本。未由用户提供的 formal spec 由 annotation owner 在当前 attempt 修改。handoff 给出用户 spec 时保持不变；需要修改就停止，在 `agent_output.md` 写明方案并交回 main，用户确认和 `unfreeze` 后继续当前 attempt。

写 declaration 前先搜索已有 `sublist`、`sum`、`Permutation`、单调性、最值、`reachable` 和其他核心接口。只有题目、helper 或循环中独立且重复的数学性质进入 `formal_case_lib`。

核心接口的组合直接写入 spec 或 invariant，不再定义逐层转发的 wrapper。题目输出或跨函数接口需要名称时只保留一层 case predicate，helper 和循环统一引用这一层。

不推荐直接写一份 Rocq 版 C loop body 或完整 C 状态机。快速判断：这个 definition 能否用于说明另一个实现的正确性？如果不能，通常不是合适的 spec。

排序、去重、搜索、优化、图搜索、DP 等功能 case，首轮必须建立数学结果语义。shape、bounds 和 ownership 只是执行条件，不是 functional spec。

### Spec 与 Predicate 复用顺序

每个函数先回答三个问题，再写 annotation：

1. 自然语言 `Output` 和 Rocq `Spec` 是什么？
2. `Ensure` 如何直接连接该输入输出关系？
3. 每个循环维护哪一句数学进度？
4. 已有 predicate 能否直接组合表达；若不能，哪一个重复性质确实需要新 declaration？

隐藏性质不是“把代码换成 Rocq 语法重写”，而是程序状态里真正保留下来的数学事实。典型形态包括：

- 已处理前缀 / 未处理后缀。
- 已归并前缀 / 左右待处理区间。
- 当前候选最大值、最小值、最优值或可行性边界。
- 已写前缀 + 未初始化后缀。
- 当前抽象 queue / graph reachability / DP table meaning。
- 排列关系、有序性、边界、形状保持和分段所有权。

若新定义开始一比一复现 loop locals 和 step transition，改为直接陈述循环维护的数学性质。需要时读取 [算法镜像反例](examples/algorithm-mirror.md)。

### `formal_case_lib` declaration 选型

优先使用短小、稳定、可复用的数学接口：

- 对排序结果，组合 `Permutation` 与 `increasing` / `decreasing`。
- 对 segment sum，普通场景直接用现有 list `sum(sublist lo hi l)`；indexed / finite-set sum 按签名复用 `sum_range` / `sum` / `sum_set_R`，区间枚举使用 `Zrange`，不得递归重写。仅在题目概念确需名称时保留一层业务 predicate，端点与同名接口见[知识规则 §2](spec-and-contract-knowledge.md#2-算术与库接口)。
- 对最大/最小/最优性，必须使用 `MaxMinLib` 的 `min_value_of_subset` / `max_value_of_subset`，不得自定义 `IsMinimum` / `IsMaximum` 等同义接口；题目或跨函数接口需要名称时，保留一层直接引用库语义的 case predicate。
- 对二分答案，定义 `CanX`、`CannotX` 和真实答案 predicate；主循环 invariant 维护答案在当前边界内。先读 [二分答案正例](examples/binary-search-answer.md)，配套 C annotation 见同目录的 `split_array_largest_sum.c`。
- 对 DP，定义 table entry 的数学含义，而不是定义一份递归 DP 程序再追踪它。
- 对 refinement proof，只保留 proof type 所需的 `safeExec` / monad spec；不要把最终 functional correctness 重复塞进 C loop invariant。

新 declaration 的优先形状：

```coq
Definition BusinessPredicate (l : list Z) (args : Z) : Prop := ...
```

与下标无关的逐元素性质使用 `Forall`，两表对应关系使用 `Forall2`；真正依赖位置时才保留带有效域的 `forall`。直接复用 `exists`、`Znth`、`Zlength`、`sublist`、`Permutation`、`sum` 等核心接口。题目或接口需要名称时只增加一层 case predicate。Relation 的零步或多步闭包必须使用 `clos_refl_trans`，不自定义递归执行链；datatype 选型遵循知识规则 §1.4，不为模拟程序循环写 `Fixpoint`。

这一层 case predicate 只用于题目数学语义，不再嵌套其他同义层。结果与进度 predicate 都不包含内存 ownership、输入限制或实现安全范围；题目候选集合、量化有效域和答案区间仍须保留。输入大小、标量/元素值范围和 overflow/safety 条件在 `Require` 或需要它们的中间 annotation 中直接展开，不得定义或调用 `SizeSafe`、`InputValues`、`InputValid`、`InputBound` 一类包装 predicate。`Ensure` 的数学部分只承诺所需最终性质，资源单独归还。

## Annotation 风格

采用“循环 invariant 完整、其他位置最小”：

- 每个循环前写 `Inv Assert`，维护已处理/未处理部分、当前候选状态和仍持有的资源。
- 不要在 `Inv Assert` 前再加普通 `Assert`。
- 普通 `Assert` 在 `if` 前可以按需添加，`return` 前不要添加；其他位置只在 symbolic execution 完全无法确定验证所需状态时添加。
- 普通顺序语句、单步赋值和 symbolic execution 能自动推进的局部转换不加 assertion。
- `n == n@pre` 当且仅当 `n` 从函数入口到当前点没有发生值变化时才写；值发生过变化时禁止写。Bridge 之后同一 assertion 的其他事实全部使用当前名字 `n`。

### Assertion 放置规则

完整 `Assert` / `Inv Assert` 应覆盖以下信息：

- live local store 或能让 QCP 回收 local permission 的等价资源。
- 当前拥有的 heap / array / string / shape resource。
- 抽象列表、segment、前缀、后缀和程序变量之间的桥接等式。
- 当且仅当参数值未变化时使用的 `@pre` bridge。
- 边界、分支条件、循环守卫与数组读取绑定。
- 当前隐藏性质或业务 predicate。

不要在每条赋值后铺满 assertion。普通单步变换让 symbolic execution 推进；普通 `Assert` 只按上面的有限位置使用。

### Loop invariant 形状

循环 invariant 先写“进度 + 资源 + 数学状态”：

```c
Inv Assert
  exists done todo state,
    n == n@pre &&
    l == app(done, todo) &&
    i == Zlength(done) &&
    0 <= i && i <= n &&
    LoopStatePredicate(done, state) &&
    IntArray::full(a, n, l)
```

`IntArray::full(a, n, l)` 已包含 `Zlength(l) == n` 与 `0 <= n`；`IntArray::seg` 等资源同样已包含自己的长度/区间信息。不要在同一 annotation 中重复这些事实。数组访问所需的 `0 <= i < n` 仍按实际需要保留。

`LoopStatePredicate` 只包含数学进度；范围、读取绑定和资源保持在外层，不复制整份入口条件。逐元素范围按知识规则使用 `Forall`，逻辑整数与列表操作统一使用 Z 接口。

数组扫描常见形状：

- 只读扫描：`IntArray::full(a, n, l)` + `i == Zlength(done)` + `l == app(done, todo)`。
- 原地更新：`new_l == replace_Znth(i, v, old_l)`，并保留写回后的 `full`。
- 多游标区间：优先用多个 `seg` 对应 `[lo, mid)`、`[mid, hi)` 等逻辑片段。
- 未初始化缓冲区逐步写入：已写前缀 `seg` / `seg_shape` + 未写后缀 `undef_seg`。
- 二分答案：维护数学答案 `ans` 在 `[left, right]` 内，不维护“二分循环执行器”。

选择 `app` decomposition 只有在 prefix / selected element / suffix 对算法有独立意义时才做。若只是观察一个下标，用 `Znth(i, l, default)` 和 bounds 更清楚。

## 常见错误

- 未变化且需要记录的变量缺少 `n == n@pre` 一类 bridge；已变化的变量错误地写了该 bridge；或写出 bridge 后又在同一 assertion 的范围/资源中继续使用 `n@pre`，而不是当前值 `n`。
- 数组 read 后没有绑定：读 `a[i]` 后若后续需要逻辑列表值，写出 `val == l[i]` 以及 bounds 和数组资源。
- 用 `x == x`、`p == p` 等恒真式假装保变量；只保留后续实际需要的 `local == logical_value`、`new_l == replace_Znth(...)` 或必要的入口值关系。
- refinement case 把最终 functional correctness 塞进 C invariant；C annotation 应暴露 simulation 所需资源、局部值、分支事实、bounds 和当前 `safeExec` 状态。
- invariant 太强，无法初始化或保持；太弱，退出时推不出 `Ensure`。
- full assertion 丢 live local store、array segment 或 shape resource。
- 读数组后把局部值当成自由整数，没有写 `v == Znth(i, l, 0)` 或 case 使用的等价 observation。
- 用 proof-facing predicate 替换业务语义，例如为了证明方便把 `increasing(l)` 换成大量 `mono_*` fact。
- 在 C annotation 中展开 `MaxMinLib` / `SumLib` 细节，导致每个 invariant 都重复复杂 finite-set formula。
- 在 `formal_case_lib` 中新增 unsound shortcut、`Axiom` 或与 seed declaration 同名但内容不同的 definition。

这些错误应在 main root 中修复，不交给 manual VC 硬证。

### 返工判断

以下 proof-side failure 通常应回到 annotation：

- VC premise 中没有 array read binding、loop guard、branch fact 或 `@pre` bridge。
- `safeExec` abstract state 和 goal 对不上，且不是简单 unfold / `prog_nf` 能解决。
- helper lemma 需要的业务前提根本未出现在 invariant / `Ensure`。
- `Ensure` 只说明 shape / bounds，缺少函数真正的 functional spec。

以下 failure 通常不应回到 annotation：

- semantic predicate 已正确暴露，但缺 bridge lemma。
- list arithmetic、`sublist`、`replace_Znth`、`Permutation` 或 `MaxMinLib` 连接事实需要证明。
- worker 需要新增当前 group suffix helper。

## 分阶段自修循环

以下失败默认在同一个 owner 中继续修复：

- `spec-quality`
- `qcp-symbolic-execution`
- `where-instantiation`
- `formal_case_lib-coqc`
- `annotation-design-plan`
- `invariant-too-weak`
- `invariant-too-strong`
- `resource-loss`

唯一 annotation owner 按当前阶段循环推进，直到 completed、stale 或真实 blocker（上下文压缩由运行时处理）：

1. 依次设计自然语言 spec、Rocq spec、function spec、必要 predicate、C annotation、case-lib lemmas 和简洁 plan。
2. 依次运行 handoff 的 design coq-check、canonical symexec 与适用的 post-symexec case-lib check。
3. 根据第一个失败 VC 在当前 attempt 修改对应的 spec、invariant、资源或 lemma；缺口未解决时继续。

若局部修正不能解决缺口，由 owner 重新审视 spec 的抽象层次，以及 function postcondition、loop invariant 与局部 assertion 的连接，决定是否重写 annotation 结构。脚本不计数或发出更大重构提示。

## QCP 失败分析

每次 canonical QCP 失败应在 `agent_output.md` 简要记录：

- `first_failure` 的category、message与 failing file/line/function；command、cwd、target 和 canonical flags 已在 handoff/controller 中时不重复。
- 最近的 `Require` / `Ensure` / `Assert` / `Inv Assert`。
- symbolic state 摘要，特别是 array/list/shape resource。
- 失败分类：pure fact、resource shape、spec mismatch、loop invariant、call instantiation、formal_case_lib mismatch。
- 下一轮修复方式。

不要只改一行就立刻重跑 QCP。先分类，再修一组相关问题。

## 输出

current `agent_report.json` 成功时只写 `{"status":"completed"}`；blocked 时只增加 workflow 规定的完整 blocker。迭代、失败分类、设计选择、branch decisions 和剩余风险写 current `agent_output.md`。`finalize-delivery` 返回 `report-repair-required` 时，同一 owner 在同一 attempt 按 message 修正后重跑原命令。用户 spec 修改方案只写 `agent_output.md`，不执行 `finalize-delivery`。`completed` 前 design coq-check、canonical QCP、VC comparison 与适用的 post-symexec lib check必须通过。
