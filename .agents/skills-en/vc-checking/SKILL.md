---
name: vc-checking
description: 由 vc-checking-subagent 在 vc-checking round worktree 中检查 generated manual VC 是否语义可证，并输出与当前 source_goal_version 绑定的 proof group plan。
---

# VC Checking

本 skill 固定由 `vc-checking-subagent` 使用。它只读 `agent_input.json` 和 vc-checking round worktree，判断当前 generated manual VC 是否语义可证，并输出 proof group plan。

`spawn.fork_context == false`、`fork_turns == "none"`、`parent_context_allowed == false`；不得依赖 main agent 聊天历史。

## 文档

- `docs/vc-checking-guide.md`：`P |-- Q` 分析流程、judgment、group plan 模板和 annotation/spec blocker 信号。
- `docs/natural-language-analysis.md`：自然语言证明分析 group 的规范化输出、blocked 规则和与 proof group plan 的连接。

## 输入

- accepted annotation round worktree
- 当前 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`
- 当前 `case_lib`
- `source_version`
- `source_goal_version`
- diagnostics 文件和 snapshot，仅作为 planning hint
- `problem_context` 和 `annotation_design_summary`，用于理解题目语义和 annotation 设计，不需要读取 parent chat。

## 输出

写入 `agent_report.json.agent_result.vc_checking.group_plan`。计划必须绑定当前 `source_goal_version`，并列出：

- target witnesses
- `proof_groups`
- 每组 `group_id`
- `witness_names`
- `representative_witness`
- dependencies
- likely helper declarations
- natural-language proof strategy
- `natural_language_analysis`，建议包含每个 witness 的自然语言可证性分析和用于分组的 analysis groups；该字段是 vc-checking 的结构化辅助，不是 controller acceptance gate
- blockers

vc-checking 应先用自然语言分析每个 target VC 的证明思路，再用这些分析辅助分组。若某个 VC 在语义上无法证明，返回 `blocked` 并说明应回到 annotation/spec 的原因，不交给 vc-proving-preparing / group-worker 硬证。若 VC 语义可证但需要 helper、证明较难或 proof route 不确定，应输出 proof plan 并交给 group-worker，不得 blocked。controller 不因缺失 `natural_language_analysis` 字段拒绝本轮；基本流程仍以 `group_plan.proof_groups`、版本和 witness 覆盖为准。

group plan 必须遵守 `agent_input.json.grouping_policy`。默认策略是 bounded witness groups：每组最多放入 `max_witnesses_per_group` 个 witness；当 target witness 数超过该上限时必须拆成多个 group。分组参考自然语言 analysis group、proof pattern、helper family、loop/refinement phase 和依赖关系，manual witness order 只作为确定性 tie-breaker。不得为了减少 spawn 数把大量 witness 无约束塞进一个组。

同时写 `agent_output.txt` 作为 `non-authoritative reuse note`。第一行必须是 `# Reuse Note`，正文包含 `Note kind: non-authoritative reuse note` 和 `This file is not acceptance evidence.`。

## Blocking 原则

vc-checking-subagent 的 `blocked` 只用于两类情况：

- 发现某个 target VC 语义上不可证，即当前 `P` 确实无法推出 `Q`，并且缺口必须回到 C annotation 或 `case_lib` spec 修正。
- 必要检查工具发生重大错误：无法读取当前 generated/manual VC、无法解析 witness、或固定检查脚本完全不可运行，并已记录具体 evidence。

以下情况不得 `blocked`，必须自行处理并输出 group plan：helper 尚未证明、proof route 不确定、diagnostics hint 缺失、annotation design summary 缺字段、某些 witness 较难、需要把多个相关 witness 在 group size 上限内放进同一 group 由 worker 顺序证明。输入版本失效写 `stale`。context compaction 只写 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。

## Main-owned 检查

main agent 调用 `vc-checking-check-round`，确认 source versions 匹配、target witness 集合与 cleaned `*_proof_manual.v` 完全一致、没有重复分配、dependency graph 无环，满足 controller grouping policy，且 group plan 不要求修改 generated files 或 witness statements。
