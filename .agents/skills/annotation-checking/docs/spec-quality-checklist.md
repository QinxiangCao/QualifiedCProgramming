# Spec 质量检查清单

检查目标不是证明所有 VC，而是在 `annotation-check-round` 前拦住明显错误的 C annotation 和 `formal_case_lib`。

## `formal_case_lib` 检查

对每个出现在 C annotation 中的 external Rocq predicate / function / relation，确认：

- declaration 存在，名称、参数数量和顺序与 C annotation 一致。
- handoff 的 `controller.py coq-check --target-kind formal-case-lib` 通过；agent不直接调用internal helper，也不自行拼 target/build path。
- 内容是 mathematical spec，不是当前 C 程序的控制流复刻。
- definition 能用于说明另一个合理实现的正确性，而不是只能解释当前实现的 loop locals 和 step transition。
- 强度足以推出函数 `Ensure` 的结果语义，又不把某个具体实现策略写成唯一允许行为。
- 不含 `Admitted.`、extra `Axiom` 或当前 case generated artifact 的 `SimpleC.EE.*` import。

定义不存在、方向错误或 evidence 指向错误路径时，返回 `failed`，要求回到 `annotation-filling` 修正。

direct proof 默认采用 predicate-first annotation；明显的算法镜像 `Fixpoint` / 状态机必须返回 `failed`。refinement proof 可以保留 proof type 要求的 `safeExec` / monad spec，但 loop 的前后缀、已处理区间、候选最优值和其他局部运行时性质仍应直接出现在 C annotation 中。详细判定见 `../annotation-filling/docs/predicate-first-annotation.md`。

### 高阶 existential witness 的轻量审查

只有 spec 出现 `exists f : A -> B, ...` 或等价高阶函数 witness 时才执行本项；其他 existential 不受影响。在当前 `agent_output.md` 记录：

```text
higher_order_witness_review:
  domain:
  finite_contiguous_domain: yes | no
  uniquely_determined_by_input: yes | no
  canonical_definition_available: yes | no
  finite_sequence_representation_available: yes | no
  selected_representation: canonical-value | list | existential-function
  justification:
```

- 唯一确定且有清晰数学闭式时，优先使用透明规范值。
- 对有限连续区间上的序列，若后续主要做长度、下标、前后缀和分段操作，优先考虑带长度约束的 list。
- 数学对象天然是映射，或函数式接口明显简化证明时，可以保留 existential function。
- 不因出现 `exists f` 自动判定失败，也不把它等同于选择公理；保留时必须说明定义域、有效范围及相对规范值或 list 的具体优势。
- 规范定义和 list profile 仍必须描述数学对象，不能成为 C 算法或 loop body 的镜像。
- 若已有透明构造或构造 lemma，不应把同一函数 witness 的搜索重复留给 proof worker。

## Function spec 检查

函数 spec 至少分清三类事实：

- 执行事实：整数范围、下标范围、循环界限、溢出边界。
- 内存事实：数组、链表、结构体、指针和 ownership 资源。
- 逻辑性质：函数数学上完成了什么。

第三类必须回答“结果代表什么”。例如排序需要 sorted / permutation，搜索需要找到/未找到语义，优化问题需要可行性、最优性或极值定义。只有 shape、bounds 和 return range 的 spec 通常不够。

对 `check` / helper 函数，还要确认其 `Ensure` 暴露了调用方真正需要的判定性质；例如返回值只有 `0 <= ret <= 1`，却没有连接 `ret` 与可行 / 不可行语义，不能通过。

### Array / string 内存 predicate 检查

涉及数组、字符缓冲区、C string 或 string literal 时，对照 `../annotation-filling/docs/array-string-guide.md`：

- 优先使用现有 `IntArray` / `UIntArray` / `CharArray` / `PtrArray` 等 array family 与 `store_string` / `store_stringLit` / `GlobalStrings`。
- `store_string` 只表示可读写 C string buffer，其逻辑内容是不含结尾 `0` 的 `list Z`。
- `store_stringLit` 只表示 string literal / 只读全局字符串常量，其逻辑内容是 Rocq `string`。
- 局部 `char a[] = "..."` 或其他可写 buffer 不得误标为 `store_stringLit`。
- 若 `formal_case_lib` 新增 array/string 内存 predicate，先判定是否重复 builtin；case lib 应新增算法数学性质，而不是复制基础内存语义。

## Loop invariant 检查

loop invariant 至少包含：

- 变量范围、下标关系、整数溢出边界。
- 当前持有的数组 / 链表 / buffer 资源。
- 已处理部分与整体目标之间的数学关系。

常见失败：只有 bounds 和数组资源、直接引用 Rocq 版 loop function、退出时推不出 `Ensure`、初始化或保持性不可证、full assertion 缺 `@pre` 桥、局部变量绑定或 live local resources。

## 普通 `Assert` semantic review

重点检查 `Inv Assert` 是否承担循环数学状态；普通 `Assert` 只按连接作用保留。存在普通 `Assert` 时，必须对照 `../annotation-filling/docs/semantic-assert-placement.md` 逐个检查；没有普通 `Assert` 时在当前 `agent_output.md` 记录 `none`。

每个普通 `Assert` 至少记录：

```text
location:
purpose: one or more of function-call-boundary | semantic-phase-transition | path-join | exit-bridge
named_semantic_state: predicate name | none
upstream_paths: qualitative description
downstream_work: qualitative description
redundant_with_invariant_or_postcondition: yes | no
decision: keep | remove | revise
rationale:
```

路径分析是定性的，不要求精确枚举或形式化审核每条路径。检查重点是断言能否把多个具体 symbolic state 收束成后续真正使用的稳定领域性质。

优先删除或改写：

- 循环体入口复制 invariant、只重复 loop guard 的断言。
- 紧邻循环回边、只重新声明下一轮 invariant 的分支末尾断言。
- 简单赋值后重复当前 symbolic state 已蕴含事实的断言。
- 返回前原样复制 `Ensure`、没有独立退出数学步骤的断言。
- 没有稳定语义，只为暂时压住不可证 VC 而堆砌事实的断言。

多条路径汇合且下游仍有复杂分支或调用时，可以保留命名的语义切点。函数调用或资源连接断言没有合适领域 predicate 时，`named_semantic_state` 可以是 `none`，但仍须说明连接用途。删除断言后若数学义务只是移动到 invariant preservation、call boundary 或 return witness，不能把“VC 仍然存在”当作保留理由。

## QCP evidence 检查

exact `controller.py symexec` 必须在 current main root/current round通过。driver、cwd与 canonical include/SLP由 controller code固定，不要求 agent把这些字段复制到 report。

检查controller返回的最终status，而不是只看底层main-root return code或agent自己计算的digest。owner symexec只事务化刷新main-root generated files；独立clean replay由后续main-owned acceptance check执行。连续两次main-root digest相同不能替代该freshness gate。不得手改manual，也不得仅为减少split goals而弱化正确spec/invariant；预期annotation保持不变却重复失败时，把compact first failure交main agent决定controller-owned retry或tooling repair。

若 evidence 指向 stale file、stale line 或 stale directory，返回 `failed`。若 qcp-mcp 交互检查来自共享 stateful session，返回 `failed` 或 `skipped` 并说明原因。

## 教学对照

- 正例 `QCP_examples/LLM_bench/Algorithms/majority_element/majority_element.c` 用 `IsMajorityElement` / `MajorityOnReduced` 直接表达候选、票数和约简状态的数学关系，而不是复现 Boyer-Moore 控制流。
- 二分答案正例见 `../annotation-filling/docs/correct-examples/binary-search-annotation.md` 及其 `split_array_largest_sum/` 材料：`check` 暴露可行性判定，主循环 invariant 维护真实答案位于当前边界内。
- 反例见 `../annotation-filling/docs/incorrect-examples/algorithm-mirror.md` 及其 `max_sub_array` 文件：先定义 Kadane-style Rocq loop，再让 annotation 跟踪该 loop，应判为 spec 方向错误。

案例只提供 annotation/spec 设计对照；不得复制其他 case 的 proof script、generated artifact 或 formal 文件结构。

## 返回

- spec 缺失或方向错误：`failed`，回到 `annotation-filling`。
- spec 是算法镜像，或无理由把有限唯一结果隐藏在高阶 existential function 中：`failed`，回到 `annotation-filling` 重设 spec 表示。
- spec 合理但 C annotation 没使用：`failed`，修正 function spec / loop invariant。
- 普通 `Assert` 无连接用途、与 invariant/postcondition 重复或只为压住 VC：`failed`，在同一 annotation turn 删除或改写后重新检查。
- annotation 和 `formal_case_lib` 合理，但可能需要 helper：`passed`，并记录风险摘要。
- 输入 stale：建议 annotation result 写 `stale`。
- 工具 evidence 不可信、文件边界不清或 spec/annotation 方向错误：返回 `failed`，并在 current `agent_output.md` 写简短 rework plan，让 annotation-filling 在同一 agent turn 内修复。
- annotation-checking 所需必要工具完全不可运行并有 command evidence：建议 annotation result 写 `blocked`。
- context compaction：只记录 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。

`passed` 只表示 candidate 可交给 main agent 执行 `annotation-check-round`；main agent 仍要检查 diff、evidence、`formal_case_lib` contract，在 main root 内运行 canonical symbolic execution，并在独立clean root重放同一symexec、比较四个raw generated files及manual declaration order/names/statements。该early gate也不替代final-check。

## 返工计划说明

`failed` 时在本次 `agent_output.md` 写可直接执行的 rework plan，默认要求同一个 annotation-subagent 在当前 turn 继续修复。每项说明 failure class、repair target、message 与 expected next check；只有确实有助于调度时才补 `self_reworkable`。predicate/spec review、适用时的 higher-order witness review 和普通 `Assert` semantic review也写在这里，不扩展 terminal report JSON。若是 main agent append 的后续迭代，必须先重新完整读取两个 annotation skills、main agent blocker summary和 handoff列出的 Markdown/JSON blocker 原文件。

`spec-quality`、`formal_case_lib-coqc`、`qcp-symbolic-execution`、`where-instantiation`、`invariant-too-weak`、`invariant-too-strong` 和 `resource-loss` 默认可在当前 spawn 修复。这些失败不得建议 terminal `blocked`；notes 可简记已尝试的修复次数，但不把可修问题升级成 hard blocker。

terminal report只写三个 check status；失败 evidence、qcp-mcp交互提示与 rework plan写 `agent_output.md`。
