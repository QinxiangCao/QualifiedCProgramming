# 自然语言证明分析指南

## 目标

`vc-checking-subagent` 应先用自然语言判断每个 target VC 是否可证，再用这些分析结果辅助生成 proof group plan。自然语言分析是 vc-checking 内部判断 proofability 和分组边界的结构化辅助，不是 controller acceptance gate；controller 的基本验收仍以版本、target witness 覆盖、proof group 合法性和后续 parent verify 为准。

每个 target witness 至少要回答：

1. 当前 VC 写成 `P |-- Q` 后，是否在现有 annotation / `case_lib` spec 下语义成立。
2. 若成立，`Q` 中每个空间资源、纯命题和存在 witness 如何从 `P` 构造出来。
3. 若需要 helper lemma，lemma 的数学陈述、premise、premise discharge 来源，以及它属于哪个 analysis group / proof group。
4. 若不成立，缺口来自 C annotation、`case_lib` spec、输入 stale、generated/manual skeleton mismatch，还是 witness 结构本身。

自然语言证明阻塞就是 vc-checking blocker。不得把自然语言上无法说明的 VC 交给 group-worker 硬证。

## 先读什么

1. `agent_input.json`：确认 `target_witnesses`、`source_goal_version`、`target_files`、`grouping_policy`、report 路径和 diagnostics hint 位置。
2. `*_proof_manual.v`：读取 cleaned manual witness statements，确认 target witness 集合和顺序。
3. `*_goal.v` / `*_proof_auto.v` / `*_goal_check.v`：只读 VC theorem 展开形状，不修改 generated files。
4. 当前 case 的 `case_lib`：区分 annotation-approved spec declarations 和已存在 helper lemma。
5. diagnostics 文件和 `diagnostics_snapshot.json`：只作为 planning hint，不作为 target witness 来源。

参考 Rocq 风格时优先看 `SeparationLogic/examples/LLM_bench` 和 `QCP_demos_LLM`，不得参考 `QCP_demos_human`。

## Witness 分析规范

建议在 `agent_report.json.agent_result.vc_checking.natural_language_analysis.witnesses` 中按 target witness 顺序记录每个 witness：

```json
{
  "witness_name": "proof_of_xxx_entail_wit_N",
  "judgment": "proofable | needs-helper | annotation-bug | blocked",
  "vc_shape": {
    "pre_spatial": "...",
    "pre_pure": "...",
    "pre_exists": "...",
    "post_spatial": "...",
    "post_pure": "...",
    "post_exists": "..."
  },
  "witness_instantiation": "...",
  "space_plan": "...",
  "pure_plan": "...",
  "refinement_plan": "...",
  "used_existing_lemmas": [],
  "candidate_helper_declarations": [],
  "premise_discharge": [],
  "failure_signal": "",
  "recommended_next_phase": "vc-proving-preparing | annotation",
  "analysis_group_candidate": "group_id",
  "grouping_reason": ""
}
```

`vc_shape` 应把 `P` 与 `Q` 分开写。`witness_instantiation` 要说明右侧 `EX` 的值来自旧逻辑列表、`replace_Znth`、`sublist`、`app`、当前 loop variable、abstract state，还是某个 case-specific spec relation。`premise_discharge` 应逐项对应当前 VC 的前条件，不允许只写“显然”或“lia”。

Judgment 规则：

- `proofable`：自然语言证明完整，现有 facts / existing lemmas 足够。
- `needs-helper`：自然语言证明完整，但需要 group-worker 在 group-local `case_lib` 中新增当前 group suffix helper。
- `annotation-bug`：当前 annotation 或 `case_lib` seed spec 缺失/错误，导致 `P` 无法推出 `Q`。
- `blocked`：VC 读取/解析/版本检查等必要前提失败，或自然语言 proof obligation 无法闭合且不是可由 group-local helper 修复。

只要存在 `annotation-bug` 或 `blocked` witness，本轮 vc-checking 必须返回 `blocked`，不得输出可进入 proving 的完整 group plan。

## Analysis Group 规范

`natural_language_analysis.analysis_groups` 是 proof grouping 的辅助依据。每个 analysis group 应只包含自然语言证明已通过的 witnesses，即 judgment 为 `proofable` 或 `needs-helper`。

```json
{
  "group_id": "dp_transition",
  "witness_names": ["proof_of_..."],
  "representative_witness": "proof_of_...",
  "shared_proof_pattern": "...",
  "shared_space_plan": "...",
  "shared_pure_plan": "...",
  "shared_refinement_plan": "...",
  "candidate_helper_declarations": [],
  "dependencies": [],
  "grouping_reason": "same invariant expansion and same recurrence helper family",
  "proof_group_ready": true
}
```

`agent_result.vc_checking.group_plan.proof_groups` 应参考这些 analysis groups 派生：

- 每个 proof group 的 `group_id`、`witness_names`、`representative_witness`、`dependencies` 尽量与对应 analysis group 一致；若受 `agent_input.json.grouping_policy.max_witnesses_per_group` 限制而拆分，在 `grouping_reason` 中说明。
- 不得把自然语言分析失败的 witness 混入 proof group。
- 不得为了减少 spawn 数把 proof pattern 不同、helper family 不同或上下文明显不同的 witnesses 放入同一 group。
- 当 target witness 数超过 controller 上限时，先按 analysis group 拆分，再用 manual witness order 作稳定 tie-breaker。

## Helper 审计

若 judgment 为 `needs-helper`，必须说明：

```json
{
  "name_hint": "helper_name_without_group_suffix",
  "statement_shape": "...",
  "used_by_witnesses": [],
  "premises": [
    {
      "premise": "...",
      "discharged_by": "...",
      "needs_unfold": [],
      "arithmetic": "...",
      "spatial_resource": "..."
    }
  ],
  "destination": "group-local case_lib with helper_namespace.suffix"
}
```

vc-checking 不修改 `case_lib`。候选 helper 只进入 group plan；group-worker 若使用它，必须在自己的 group worktree 中证明带当前 group suffix 的 declaration。若 helper 必须跨 group 共享，vc-checking 应返回 annotation/spec blocker，建议把该事实提升为 annotation-approved seed `case_lib` declaration。

## Blocked 信号

出现以下情况时，返回 `blocked` 并推荐回 annotation/spec 或报告工具问题：

- `Q` 要求的数据结构资源在 `P` 中不存在。
- 分支 proof 需要的 pure fact 没有来自 guard、invariant 或 local assertion。
- witness 需要的逻辑 array/list value 没有在 C read 后绑定。
- postcondition 使用 pre-state 值，但 assertion 缺少桥接等式。
- refinement 目标中的 `safeExec` program state 与当前 abstract state 对不上。
- candidate helper lemma 需要额外假设，而这些假设不能由当前 `P` 推出。
- proof 需要修改 generated files、witness statements 或 seed `case_lib` spec。
- `source_goal_version` mismatch、manual skeleton 与 target witnesses 不一致、或必要 VC 文件无法读取/解析。

输入版本失效写 `stale`。context compaction 只写 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。

## 反例

- 不要把 C 循环直接翻译成 Rocq 函数后就声称 VC 可证；spec 必须描述数学性质，例如最大值、可达性、prefix/table relation、queue coverage。
- 不要把 `lia` 当作 proof plan。必须写出 `lia` 依赖哪些 bound、guard、length fact 和等式。
- 不要用“现有 invariant 足够”代替展开分析；要写明 invariant 的具体 conjunct 和实例化参数。
- 不要建议在 `*_proof_manual.v` 中新增 helper lemma。
- 不要在目标 stale、hash 不匹配、manual skeleton 与 goal witness 不一致时继续分组证明。
