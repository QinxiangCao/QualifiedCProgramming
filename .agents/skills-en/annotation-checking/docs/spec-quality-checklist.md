# Spec 质量检查清单

检查目标不是证明所有 VC，而是在 `annotation-check-round` 前拦住明显错误的 C annotation 和 `case_lib`。

## `case_lib`

对每个出现在 C annotation 中的 external Rocq predicate / function / relation，确认：

- declaration 存在，名称、参数数量和顺序与 C annotation 一致。
- `coq_tooling.py check --target-kind case_lib` 通过，target file 指向 Rocq formal `case_lib`，不是 C source directory。
- 内容是 mathematical spec，不是当前 C 程序的控制流复刻。
- 强度足以推出函数 `Ensure` 的结果语义，又不把某个具体实现策略写成唯一允许行为。
- 不含 `Admitted.`、extra `Axiom` 或当前 case generated artifact 的 `SimpleC.EE.*` import。

定义不存在、方向错误或 evidence 指向错误路径时，返回 `failed`，要求回到 `annotation-filling` 修正。

## Function spec 检查

函数 spec 至少分清三类事实：

- 执行事实：整数范围、下标范围、循环界限、溢出边界。
- 内存事实：数组、链表、结构体、指针和 ownership 资源。
- 逻辑性质：函数数学上完成了什么。

第三类必须回答“结果代表什么”。例如排序需要 sorted / permutation，搜索需要找到/未找到语义，优化问题需要可行性、最优性或极值定义。只有 shape、bounds 和 return range 的 spec 通常不够。

## Loop invariant 检查

loop invariant 至少包含：

- 变量范围、下标关系、整数溢出边界。
- 当前持有的数组 / 链表 / buffer 资源。
- 已处理部分与整体目标之间的数学关系。

常见失败：只有 bounds 和数组资源、直接引用 Rocq 版 loop function、退出时推不出 `Ensure`、初始化或保持性不可证、full assertion 缺 `@pre` 桥、局部变量绑定或 live local resources。

## QCP evidence 检查

`canonical_symexec_evidence` 必须来自当前 annotation round worktree，并匹配当前 `source_version`。evidence 记录实际 QCP driver、cwd、target `.c`、`-IQCP_examples/QCP_demos_LLM/` 和 `-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM`。

若 evidence 指向 stale file、stale line 或 stale worktree，返回 `failed`。若 qcp-mcp 交互检查来自共享 stateful session，返回 `failed` 或 `skipped` 并说明原因。

## Generated VC 语义预检

canonical QCP 生成当前 case 的 generated/proof artifacts 后，可以读取当前 round 中允许的 generated context，检查 witness 形状是否暴露 annotation/spec 方向错误。不得读取其他 case 的 generated/proof artifact 作为依据。

危险信号：

- destructive array write 后，post 仍要求整个 mutable logical list 与旧输入保持 `Permutation` / `sorted_permutation`。
- invariant 没有区分 immutable source、mutable destination、已处理 prefix 和未约束 suffix。
- loop body 覆盖或移动元素后，assertion 继续使用旧 full-list 等式或旧 full-list multiset。
- postcondition 要求 suffix/multiplicity 不变，但 C 代码允许覆盖 suffix。

这一步不要求证明所有 manual VC，只判断是否语义上明显不可证。

## 返回

- spec 缺失或方向错误：`failed`，回到 `annotation-filling`。
- spec 合理但 C annotation 没使用：`failed`，修正 function spec / loop invariant。
- annotation 和 `case_lib` 合理，但可能需要 helper：`passed`，并记录风险摘要。
- 输入 stale：建议 annotation result 写 `stale`。
- 工具 evidence 不可信、文件边界不清或 spec/annotation 方向错误：返回 `failed` + `rework_plan[]`，让 annotation-filling 在同一 spawn 内修复。
- annotation-checking 所需必要工具完全不可运行并有 command evidence：建议 annotation result 写 `blocked`。
- context compaction：只记录 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。

`passed` 只表示 candidate 可交给 main agent 执行 `annotation-check-round`；main agent 仍要检查 diff、evidence、`case_lib` contract，并在 round worktree 内运行 canonical symbolic execution。

## Rework plan 输出

`failed` result 必须给出 `rework_plan[]`，默认要求 annotation-subagent 同 round 继续修复。每项包含：

- `failure_class`
- `repair_target`
- `self_reworkable`
- `message`
- `expected_next_check`

`spec-quality`、`case_lib-coqc`、`qcp-symbolic-execution`、`where-instantiation`、`invariant-too-weak`、`invariant-too-strong` 和 `resource-loss` 默认 `self_reworkable = true`。这些失败不得建议 terminal `blocked`；`self_repair_budget` 只记录本次 spawn 已经做过多少修复尝试，不把可修问题升级成 hard blocker。

QCP evidence 字段必须拆分为 `canonical_symexec_evidence`、`qcp_mcp_interactive_evidence` 和 `case_lib_coqc_evidence`；不要用 legacy flag 混淆 direct symexec 与 qcp-mcp interactive evidence。
