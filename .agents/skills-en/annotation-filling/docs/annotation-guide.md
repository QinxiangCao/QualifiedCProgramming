# Annotation 规则和同 round 自修

本文件给 annotation-subagent 使用。目标是在 annotation round worktree 内把 C annotation 和 `case_lib` spec declarations 修到可交给 `annotation-checking` 和 main-owned `annotation-check-round`。

## 允许修改

只能修改：

- 目标 `.c` 中的 `Require` / `Ensure`。
- 证明推进所需的 `Assert`。
- 循环中的 `Inv Assert`。
- 函数调用相关的 `where` 子句。
- 同一正式相对路径下 `case_lib` 中的 mathematical spec declarations。

不得手工修改 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`，不得创建第二个 active Rocq lib。

## Spec 先行

先用 `case_lib` 定义数学问题本身，再让 C annotation 说明程序维护并实现这些性质。

如果 handoff 的 `case_lib_seed_evidence.status = created`，说明 controller 已为缺失 `case_lib` 建好最小 seed。本次 spawn 必须直接在这个 `case_lib` 中设计 spec；不得因“没有现成 lib”或“需要用户确认 spec 方向”返回 blocked。`problem_context` 字段为空时，按 C 函数名、参数、返回值、循环结构和题目目录推断一版 conservative candidate spec。

适合进入 `case_lib` 的 declaration 包括：`subarray_sum`、`prefix_sum`、`suffix_sum`、sorted / permutation、reachability、queue coverage、DP table meaning、string matching relation、最优性或可行性关系。

不推荐直接写一份 Rocq 版 C loop body 或完整 C 状态机。快速判断：这个 definition 能否用于说明另一个实现的正确性？如果不能，通常不是合适的 spec。

排序、去重、搜索、优化、图搜索、DP 等功能 case，首轮必须建立数学结果语义。shape、bounds 和 ownership 只是执行条件，不是 functional spec。

### Predicate-first 设计顺序

每个函数先回答三个问题，再写 annotation：

1. `Ensure` 要证明哪个输入输出数学关系？
2. 每个循环在当前 program point 维护哪个局部隐藏性质？
3. 这些性质应由现有 predicate、case-level wrapper，还是一个新 `case_lib` declaration 表达？

隐藏性质不是“把代码换成 Rocq 语法重写”，而是程序状态里真正保留下来的数学事实。典型形态包括：

- 已处理前缀 / 未处理后缀。
- 已归并前缀 / 左右待处理区间。
- 当前候选最大值、最小值、最优值或可行性边界。
- 已写前缀 + 未初始化后缀。
- 当前抽象 queue / graph reachability / DP table meaning。
- permutation、sortedness、bounds、shape-preserved、segment ownership。

若发现新定义开始一比一复现 loop locals 和 step transition，先停止并改成 predicate-first。先读 `docs/incorrect-examples/algorithm-mirror.md`，再查看 `max_sub_array` 反例文件。

### `case_lib` declaration 选型

优先使用短小、稳定、可复用的数学接口：

- 对排序结果，组合 `Permutation` 与 `increasing` / `decreasing`。
- 对 segment sum，普通场景直接用 `sum(sublist lo hi l)`；复杂 indexed sum 用 `SumLib` 包在业务 predicate 里。
- 对最大/最小/最优性，使用 `MaxMinLib` 包在 `Minimized...` / `Maximized...` / `Optimal...` wrapper 中。
- 对二分答案，定义 `CanX`、`CannotX` 和真实答案 predicate；主循环 invariant 维护答案在当前边界内。先读 `docs/correct-examples/binary-search-annotation.md`，配套 C annotation 见 `docs/correct-examples/split_array_largest_sum/`。
- 对 DP，定义 table entry 的数学含义，而不是定义一份递归 DP 程序再追踪它。
- 对 refinement proof，只保留 proof type 所需的 `safeExec` / monad spec；不要把最终 functional correctness 重复塞进 C loop invariant。

新 declaration 的优先形状：

```coq
Definition BusinessPredicate (l : list Z) (args : Z) : Prop := ...
```

优先使用 `forall` / `exists`、`Znth`、`Zlength`、`sublist`、`Permutation`、`sum` 和 case-level wrapper。只有当归纳结构本身就是业务语义时才引入 `Inductive`；不要为了模拟程序循环写 `Fixpoint`。

## Annotation 风格

采用“关键点完整、普通步最小”：

- 在函数入口/出口、循环 invariant、重要分支汇合点、函数调用前后、会改变抽象状态的重要表达式前后写完整 `Assert` / `Inv Assert`。
- 普通顺序语句、单步赋值和 symbolic execution 能自动推进的局部转换，不机械插入 full assertion。
- 循环里维护已处理前缀/后缀、尚未处理区间、当前候选最优值、抽象状态、局部 shape、已写前缀和未写后缀。
- 需要函数入口状态时，显式保留当前变量到 `@pre` 变量的桥接等式。
- 函数调用前确认 `where` / `With` 所需的 list、length、value-level facts 都在当前 assertion 中。

当 C 类型或 local store 已蕴含纯事实，但 witness 没有暴露它时，可在 value materialize 后使用轻量 annotation：

```c
unsigned int __u = u;
/*@ 0 <= u && u <= UINT_MAX by local */
```

`by local` 只导出纯事实，不保留空间资源。

### Assertion 放置规则

完整 `Assert` / `Inv Assert` 应覆盖以下信息：

- live local store 或能让 QCP 回收 local permission 的等价资源。
- 当前拥有的 heap / array / string / shape resource。
- 抽象列表、segment、前缀、后缀和程序变量之间的桥接等式。
- `@pre` 参数桥，例如 `n == n@pre`、`arr == arr@pre`。
- bounds、branch condition、loop guard、array read binding。
- 当前隐藏性质或业务 predicate。

不要在每条赋值后机械铺满全量 assertion。普通单步变换让 symbolic execution 推进；只在资源形态变化、抽象状态变化、分支汇合、函数调用、循环头尾和 QCP 无法自动发现关键纯事实时写完整 assertion。

### Loop invariant 形状

循环 invariant 先写“进度 + 资源 + 数学状态”：

```c
Inv Assert
  exists done todo state,
    l == app(done, todo) &&
    i == Zlength(done) &&
    0 <= i && i <= n@pre &&
    LoopStatePredicate(done, state) &&
    IntArray::full(a, n@pre, l)
```

数组扫描常见形状：

- 只读扫描：`IntArray::full(a, n, l)` + `i == Zlength(done)` + `l == app(done, todo)`。
- 原地更新：`new_l == replace_Znth(i, v, old_l)`，并保留写回后的 `full`。
- 多游标区间：优先用多个 `seg` 对应 `[lo, mid)`、`[mid, hi)` 等逻辑片段。
- 未初始化缓冲区逐步写入：已写前缀 `seg` / `seg_shape` + 未写后缀 `undef_seg`。
- 二分答案：维护数学答案 `ans` 在 `[left, right]` 内，不维护“二分循环执行器”。

选择 `app` decomposition 只有在 prefix / selected element / suffix 对算法有独立意义时才做。若只是观察一个下标，用 `Znth(i, l, default)` 和 bounds 更清楚。

## 常见错误

- 缺 `@pre` 桥：postcondition 使用入口值，但 assertion 只保留当前值。
- 数组 read 后没有绑定：读 `a[i]` 后若后续需要逻辑列表值，写出 `val == l[i]` 以及 bounds 和数组资源。
- 用 `x == x`、`p == p` 等恒真式假装保变量；应改成 `x == x@pre`、`local == logical_value` 或 `new_l == replace_Znth(...)`。
- refinement case 把最终 functional correctness 塞进 C invariant；C annotation 应暴露 simulation 所需资源、局部值、分支事实、bounds 和当前 `safeExec` 状态。
- invariant 太强，无法初始化或保持；太弱，退出时推不出 `Ensure`。
- full assertion 丢 live local store、array segment 或 shape resource。
- `where` 子句只传了 pointer，没传 list、length 或 value-level facts，导致 callee spec 无法实例化。
- 读数组后把局部值当成自由整数，没有写 `v == Znth(i, l, 0)` 或 case 使用的等价 observation。
- 用 proof-facing predicate 替换业务语义，例如为了证明方便把 `increasing(l)` 换成大量 `mono_*` fact。
- 在 C annotation 中展开 `MaxMinLib` / `SumLib` 细节，导致每个 invariant 都重复复杂 finite-set formula。
- 在 `case_lib` 中新增 unsound shortcut、`Axiom` 或与 seed declaration 同名但内容不同的 definition。

这些错误应在 annotation round worktree 中修复，不交给 manual VC 硬证。

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

## 自修循环

以下失败默认是 self-reworkable：

- `spec-quality`
- `qcp-symbolic-execution`
- `where-instantiation`
- `case_lib-coqc`
- `annotation-checking-failed`
- `invariant-too-weak`
- `invariant-too-strong`
- `resource-loss`

每个 annotation spawn 至少按以下循环推进，直到 ready、stale、compact-error 或必要工具重大错误：

1. `design`：列出每个函数 `Ensure` 要表达的数学结果语义。
2. `local-static-review`：检查 live resources、`@pre` 桥、局部变量到数组值绑定、循环退出所需逻辑性质。
3. `case_lib-check`：用 main worktree 的 `coq_tooling.py check --target-kind case_lib` 检查当前 round worktree 的 `case_lib`。
4. `qcp-check`：使用 handoff 中可传 canonical `-I` / `-slp` 的 driver 检查目标 `.c`。
5. `annotation-checking`：把 failed result 转换成下一轮 `repair_actions[]`。
6. `repair`：一次性修复一组同类问题，再进入下一轮检查。

默认 budget：至少 3 次完整 `design/check/repair` cycle，或至少 30 分钟实际 annotation 工作。输入版本失效写 `stale`。context compaction 只写 `compact-error` 事实和可复用 evidence pointer；是否重试或最终 block 由 controller / main agent 判定。只有 canonical QCP driver、`coq_tooling.py` case_lib check 或 annotation-checking 所需脚本完全不可运行并有 command evidence 时，才返回 `blocked`。缺 spec、`case_lib` 暂时不能 coqc、QCP 失败、where instantiation 失败、annotation-checking failed、题目语义需要推断、reference hint 缺失，都应在本次 spawn 内继续修复或给出 candidate。

## QCP 失败诊断

每次 canonical QCP 失败必须记录：

- command、cwd、target `.c`、canonical `-I` 和 `-slp`。
- failing file/line/function。
- 最近的 `Require` / `Ensure` / `Assert` / `Inv Assert` / `where`。
- symbolic state 摘要，特别是 array/list/shape resource。
- 失败分类：pure fact、resource shape、spec mismatch、loop invariant、call instantiation、case_lib mismatch。
- 下一轮修复方式。

不要只改一行就立刻重跑 QCP。先分类，再修一组相关问题。

## Report fields 字段

`agent_result.annotation` 必须记录每轮检查、失败分类、修复动作、剩余风险、self-repair budget 和 blockers。若 `ready_for_annotation_check_round = true`，`self_reworkable_failures` 必须为空，canonical QCP、`case_lib` check 和 `annotation-checking` 必须通过。
