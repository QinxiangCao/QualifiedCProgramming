---
name: vc-checking
description: 由 vc-checking-subagent 直接只读 main root cleaned manual/generated/formal_case_lib，判断 manual VC 语义可证性并输出绑定 source_goal_version 的 group_plan.json。
---

# VC Checking

完整读取 startup message 指定的 `agent_input.md`；main root current files和 handoff version 是唯一 context。parent transcript 不允许。

## 文档

- `docs/vc-checking-guide.md`：proofability、per-witness plan、group plan。
- `docs/natural-language-analysis.md`：自然语言 `P |-- Q` 分析。
- `../verification-orchestrator/docs/path-configuration.md`：root/group path roles。

## 允许工作

- 只读 main root manual、goal、auto、diagnostics、snapshot 与 `formal_case_lib`。
- 只写 declared `agent_report.json`、`group_plan.json`、`agent_output.md`。
- 不改 formal files、witness statements 或 generated files。

## 判断与分组

每个 target witness 分析 pre/post spatial resources、pure facts、existentials、refinement state、witness instantiation 和 helper premises。

- `proofable`：现有事实/lemmas 足够。
- `needs-helper`：语义成立，group-worker 可在 `group_worker_lib` 证明 current-suffix helper。
- `annotation-bug`：当前 C annotation 或 `formal_case_lib` spec 缺失/错误，必须回 annotation。
- `blocked`：VC 语义确实不可证或必要读取/解析工具重大错误。

返回 `annotation-bug`/`blocked` 时，`agent_output.md` 必须写足以让 main agent分析并让 annotation owner修正的具体 witness、缺失 premise/resource、对应 C function/loop/assertion 与建议重新审视的 spec 边界；`agent_report.json` 的 blocker保持 machine-minimal。main agent会读取这两个原文件，按 blocker-summary模板总结原因与反思，再把 summary和原文件路径一起 append 到 run 内唯一的 annotation agent，不会重新 spawn annotation。

优先减少 group 数量：同一函数/pattern/helper family可由一个 worker 连续处理时放同组；仅在真实 dependency、strategy 差异或上下文过大时拆分。每个 target witness 恰好一次，dependency graph 无环，遵守 grouping bound。

shared helper 若必须跨 group 使用，应建议回 annotation 把数学事实提升为 `formal_case_lib` spec declaration；不要让 group 修改正式 lib。

## 输出

详细 per-witness judgment与自然语言 proof analysis写 `agent_output.md`。`group_plan.json` 只保留 current version和 `groups[{id,witnesses,depends_on,strategy?,helpers?}]`；`agent_report.json` 只保留 terminal status、version与 blockers。controller 才给 plan 添加 `verified: true` 并在 state记录 acceptance。

proof route 不确定、helper 未证明、diagnostics hint 缺失或 witness 较难不是 blocked。版本失效写 stale；compaction 只写 compact-error fact。不要直接修改 annotation，也不要请求新的 annotation agent。
