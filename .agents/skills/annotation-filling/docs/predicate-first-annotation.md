# 谓词优先的 Annotation

本文件深化 `annotation-guide.md` 的 spec-first / predicate-first 设计纪律，专门阻止一种常见但不应继续扩散的做法：

- 先在 Rocq 中把 C 算法重新定义一遍。
- 再让 C annotation 和后续 proof 追踪这份 Rocq 算法镜像。

这种做法会削弱 annotation，把本应在 C 层表达的运行时性质推迟到 Rocq proof；VC 会围绕“算法解释器”组织，并在 C 控制流或 annotation 返工时产生不必要的连锁失效。

## 默认原则

- direct proof 默认采用 predicate-first annotation，优先写人类会先说出的局部隐藏性质。
- refinement proof 可以保留 proof type 要求的 `safeExec` / monad 规格；但局部循环状态、前后缀关系、已处理区间和候选最优值仍应尽量由 C annotation 直接表达。
- 先在 `formal_case_lib` 确认目标 spec 是严格数学性质，再让 C annotation 调用它。spec 缺失、过强、过弱或是算法镜像时，先修 spec，再调整 annotation。

一句话概括：先把程序运行时的局部语义写成 predicate，再决定需要哪些 helper lemma；不要先写 Rocq 算法。

## 什么是隐藏性质

隐藏性质不是把代码换一种语言重写，而是抽取循环每一步真正维护的数学事实。典型形态包括：

- 已处理前缀 / 未处理后缀。
- 已归并前缀 / 左右待处理区间。
- 当前候选最优值或可行性边界。
- 某个边界点对应的 suffix / prefix / subarray 性质。
- 已写前缀 + 未写或未初始化后缀。
- 排列关系、有序性、有界性与形状保持。

这些性质应优先出现在 `Require`、`Ensure`、`Assert` 和 `Inv Assert`，而不是优先藏进新造的 Rocq 递归算法定义。

## 正反例

### 反例：algorithm mirror

先读 `incorrect-examples/algorithm-mirror.md`，再查看同目录的 `max_sub_array.c`、`max_sub_array_lib.v` 和 `max_sub_array_goal.v`。反例先定义追随 Kadane-style C loop 的递归器，再让 spec 和 invariant 追踪该递归器；它把本应直接表达的“当前前缀最大 suffix / 最大 subarray”替换成了算法同步关系。

这条路线的问题不在于递归定义写不出来，而在于它把当前程序点的数学含义隐藏在另一份程序里。

### 正例：majority element

`QCP_examples/LLM_bench/Algorithms/majority_element/majority_element.c` 使用小而直观的性质接口，例如 `IsMajorityElement` 和 `MajorityOnReduced`。loop invariant 直接表达当前 `vote`、`candidate`、剩余列表与全局多数元素之间的关系；定义描述性质，而不是复现 Boyer-Moore 控制流。

### 正例：二分答案

`correct-examples/binary-search-annotation.md` 及其 `split_array_largest_sum/` 配套材料展示“二分答案 + check 函数”的设计：

- `check` 的 `Ensure` 暴露 `CanSplit` / `CannotSplit` 判定语义。
- 主循环 invariant 维护真实数学答案位于 `[left, right]`。
- proof helper 连接可行性判定与最优值边界，但不把二分过程定义成 Rocq 程序。

## 优先使用显式 witness 表示

设计 `formal_case_lib` spec 时，不要无理由地把有限且由输入唯一确定的结果包装成高阶 existential witness，例如 `exists f : Z -> Z, ...`。这会扩大后续 proof 的 witness 搜索空间：worker 需要猜测 lambda、有效域外取值、点态等价方式，以及是否需要函数外延性。

按以下顺序选择表示：

1. witness 由输入唯一确定且存在清晰数学闭式时，优先定义透明的规范值。
2. witness 表示有限连续区间上的序列，且证明主要使用长度、下标、前后缀或分段操作时，优先使用带 `Zlength` 约束的 `list`。
3. 只有数学对象天然是函数，或现有函数式代数接口能明显简化证明时，才保留 existential function。

透明规范值和 list profile 仍必须描述数学对象，不能借机重写 C loop body。`exists f` 本身不等于使用选择公理，也不是一律禁止；若保留 existential function，应说明定义域、有效范围、它相对规范值或 list 的具体优势，以及是否已有透明构造或构造 lemma，避免把同一 witness 搜索重复留给 proof worker。

例如，有限数组上每个位置的派生值若由输入唯一决定，优先直接定义规范值，或使用与输入等长的结果 list，而不是默认使用 `exists value_at : Z -> Z, ...`。图着色、顶点势函数和变量赋值等天然映射对象则可以继续使用函数 witness。

## 向现有案例学习什么

可以参考：

- `QCP_examples/QCP_demos_LLM/int_array_merge_rel.c`
- `QCP_examples/QCP_demos_LLM/sll_merge_rel.c`

重点观察区间分解、已处理进度以及 pure / spatial / `safeExec` 信息如何并列组织。只复用 annotation 风格，不复制其他 case 的 proof script、generated artifact 或 formal 文件结构。

## 允许、警惕与阻止

允许：

- 为性质接口引入 `subarray_sum`、`suffix_sum`、`prefix_sum` 或简单最优性 predicate。
- 为连接 annotation step 编写小型数学 lemma。
- 保留 refinement proof 必需的 `safeExec` / monad 规格。

警惕：

- 新定义开始一比一复现 loop locals 和状态推进。
- invariant 的核心语义依赖先运行 Rocq 算法才能得到的结果。
- proof 工作变成证明 Rocq 算法与 C 算法同步前进，而不是证明 annotation 的局部性质。

直接阻止：

- 在 direct proof 中仅为弥补 annotation 未表达局部性质而引入算法镜像 `Fixpoint` 或状态机。
- 把 annotation 写成 Rocq 算法定义的投影，而不是程序运行时状态的说明。

## 设计检查

开始写或重构 annotation 前，依次回答：

1. 函数 `Ensure` 要表达哪个输入输出数学关系？
2. 每个循环每轮真正维护的局部事实是什么？
3. 这些事实能否写成 prefix / suffix / segment / shape / optimality predicate？
4. 若要引入新 definition，它描述的是独立数学性质，还是在重放算法？
5. proof 失败应由 helper lemma 连接已有性质，还是暴露出 annotation 本身不够好？
6. 若 spec 使用 existential function，规范值或有限 list 能否更显式地表达同一 witness并减少后续搜索？

第 4 个问题的答案接近“重放算法”时，立即回退到 spec 与 annotation 设计，不要把该候选交给后续 VC proving。
