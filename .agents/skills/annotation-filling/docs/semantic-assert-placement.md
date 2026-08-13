# 语义 Assert 的放置

本文件说明如何在 QCP C annotation 中放置普通 `Assert`。目标不是机械追求最少断言，而是在保持 C 文件可读的同时，用少量稳定的语义切点控制 symbolic execution 的路径和后续 VC 形状。

## 默认结构

- 循环头使用稳定的 `Inv Assert`，描述变量范围、空间资源以及已处理 / 未处理部分的核心数学关系。
- 普通 `Assert` 不是每个 `if` 或赋值后的固定步骤；只有承担明确连接作用时才保留。
- 优先让函数规格、循环不变量和已有分离逻辑规则承担能够自然表达的事实。

## 适合保留普通 `Assert` 的位置

普通 `Assert` 至少应满足以下一种用途：

- **函数调用边界**：把当前状态整理成 callee 的 `Require`，或在调用后显式恢复调用方使用的抽象状态。
- **语义阶段转换**：程序从一个稳定领域状态进入另一个稳定领域状态，例如从“frontier maximum”转换为“inclusive maximum”。
- **路径汇合**：多条上游路径得到同一个领域性质，且汇合后还有复杂分支、函数调用或较长公共后继；断言让后续 symbolic execution 忘记无关的路径历史。
- **退出桥接**：循环退出状态到函数 `Ensure` 的转换本身是重要、可复用的数学步骤。若返回点能直接由 invariant 推出 `Ensure`，退出断言可以省略。

语义阶段转换或路径汇合断言应优先调用有名字的领域谓词，例如 `PhaseSummary`，而不是复制大量低层算术条件。领域谓词必须描述数学性质或稳定的局部观察，不能把 C loop body 重写成 Rocq 状态机。

## 通常应删除的普通 `Assert`

- 在循环体入口完整复制 `Inv Assert`，只额外重复当前 loop guard。
- 紧邻循环回边、仅重新声明下一轮 invariant 的分支末尾断言。
- 简单赋值后重复 symbolic state 已经直接蕴含的等式或范围。
- 返回前原样重复函数 `Ensure`，且没有独立的退出数学步骤。
- 为暂时压住不可证 VC 而加入、但没有稳定语义含义的断言。

删除普通 `Assert` 不等于删除数学义务。若断言只是中转，义务会移动到循环保持、函数调用或 return witness；应比较新的 VC 结构，而不是只比较 C 文件行数或 VC 是否仍然存在。

## 路径收束判断

在候选位置做定性判断：

1. 上游是否已有多条路径，例如连续条件更新形成多种状态组合？
2. 下游是否还有新的复杂分支、函数调用或较长公共后继？
3. 上游路径能否共同推出一个比各自 symbolic state 更稳定的领域谓词？
4. 加入断言后，后续证明是否只依赖该领域谓词，而不再依赖具体路径历史？

若四项大多成立，普通 `Assert` 通常是有价值的语义切点。不要要求精确计算路径数量；路径乘积只用于识别潜在 VC 膨胀。若断言后立即回到循环头或直接返回，loop invariant 或 function `Ensure` 往往已经是自然汇合点。

## 与 Rocq helper lemma 的关系

- 对稳定的语义切点，优先准备阶段转换 lemma，例如 `LoopState -> StepState`。
- 对左右分支等不同后继，可以分别准备 branch-progress lemma。
- 只有多个 witness 确实重复整轮推导时，才考虑组合成 full-iteration lemma。
- 不要求 full-iteration lemma 采用固定 statement，也不要求 manual witness 使用固定 tactic 模板。
- manual witness 只承担当前 VC 特有的实例化、路径条件和空间连接；可跨 witness 复用的数学推导才适合提取为 helper lemma。

Rocq helper 可以缩短单个 witness，但不能事后合并 symbolic execution 已经展开的路径。因此，语义 `Assert` 与 helper lemma 是互补手段，不能机械地互相替代。

## 检查记录

对每个普通 `Assert` 在当前 attempt 的 `agent_output.md` 记录以下信息；没有普通 `Assert` 时明确写 `none`：

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

`upstream_paths` 和 `downstream_work` 只需给出定性描述，不要求逐路径形式化证明。一个断言可以同时承担多种用途。函数调用或资源连接断言没有合适的领域谓词时，`named_semantic_state` 可以写 `none`；若无法说明任何连接用途，或断言与 invariant / postcondition 重复，应优先删除或改写。

## 对照片段

- `QCP_examples/LLM_bench/Algorithms/rmq/rmq.c` 构建表时，在两个写入分支之后建立 `STLevelPrefix(..., i + 1)`，属于把不同路径收束成统一数学状态。
- `QCP_examples/LLM_bench/Algorithms/quicksort_lomuto_index/quicksort.c` 的 partition 扫描以 `partition_scan_inv` 作为循环头语义；分支结束后若立即回到循环头，应直接证明 invariant preservation，不需要为每个分支机械增加普通 `Assert`。

这些案例只用于比较断言承担的连接作用，不表示其现有 spec、helper 布局或 formal 文件结构都应原样复制。
