# VC Checking 指南

本文件给 vc-checking-subagent 使用。目标是在写 Rocq proof 前判断每个 manual VC 是否语义可证，并输出绑定当前 `source_goal_version` 的 group plan。

## 分析流程

1. 把每个 witness 看成 `P |-- Q`。
2. 拆出 `P` 中的空间资源、纯命题和 existential witnesses。
3. 拆出 `Q` 需要的空间资源、纯命题和 existential witnesses。
4. 判断缺口属于 shape / ownership resource、pure fact、witness instantiation、refinement state、loop invariant 信息，还是 stale generated files。
5. 为每个 witness 做自然语言证明分析，用它辅助判断 proofability 和 grouping；若分析发现语义缺口，返回 annotation/spec blocker，不进入 group-worker。
6. 若 `P` 无法推出 `Q`，返回 annotation/spec blocker。
7. 若语义成立但证明需要 helper，给出 helper statement shape、premise 和 discharge 来源，并交给 group-worker；不要因为 helper 尚未证明而 blocked。
8. 参考已经通过自然语言分析的 witnesses 形成 analysis groups，再结合 controller grouping policy 生成 `group_plan.proof_groups`。

## Judgment 分类

每个 witness 使用一个 judgment：

- `proofable`：现有 facts 和 library lemmas 足够。
- `needs-helper`：语义成立，但需要在 `case_lib` 中新增 proved helper declaration。
- `annotation-bug`：当前 annotation/spec 缺少或写错。
- `blocked`：当前 `P` 语义上无法推出 `Q`，必须回到 annotation/spec；或必要 VC 读取/解析/检查工具发生重大错误并有 evidence。

输入版本失效写 `stale`，不写 `blocked`。context compaction 只写 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。

`annotation-bug` 的 witness 不得混入 proving group。

## 单个 witness 模板

每个 witness 至少输出：

```text
witness_name:
judgment: proofable | needs-helper | annotation-bug | blocked
vc_shape:
  pre_spatial:
  pre_pure:
  pre_exists:
  post_spatial:
  post_pure:
  post_exists:
witness_instantiation:
space_plan:
pure_plan:
refinement_plan:
used_existing_lemmas:
candidate_helper_declarations:
premise_discharge:
failure_signal:
recommended_next_phase:
proof_group_candidate:
grouping_reason:
```

`vc_shape` 必须分开写 `P` 和 `Q`。`witness_instantiation` 说明右侧 `EX` 的值来自旧逻辑列表、`replace_Znth`、`sublist`、`app`、当前 loop variable 或 abstract state。

## Space / pure / refinement plan 写法

space plan 说明哪些资源可直接 `cancel`，哪些 array segment 要 split / merge，哪些 list / struct predicate 需要 `sep_apply`，以及 side conditions 从哪里来。

pure plan 说明 `pre_process` / `split_pures` 后可得到哪些 facts。`lia` 不是 proof plan；必须列出它依赖的 bounds、guards、length facts 和等式。

refinement plan 说明哪个 hypothesis 携带 `safeExec` fact，目标 abstract program state 是什么，是否需要 `prog_nf in H`、`unfold_loop in H`、`safe_choice_l H` / `safe_choice_r H`，或因 abstract state 对不上而回到 annotation/spec。

## Helper 审计

若 judgment 为 `needs-helper`，必须说明：

- helper lemma 的 statement shape。
- 使用它的 witnesses。
- 所有 premise。
- 每个 premise 如何从当前 VC 的 `P` 中 discharge。
- helper destination 是 `case_lib`，不是 `*_proof_manual.v`。

如果 premise 不能从当前 `P` 推出，不能判为可证。

## 分组

`group_plan` 参考自然语言 analysis group / proof pattern 分组，不按 witness 编号机械切块。常见分组依据：

- 相同 invariant 展开。
- 相同 helper lemma family。
- 相同 array/frame transformation。
- 相同 refinement transition pattern。

每组至少包含 `group_id`、`witness_names`、`representative_witness`、dependencies、candidate helper declarations 和 proof strategy。每个 target witness 只能出现一次。

必须遵守 `agent_input.json.grouping_policy`。默认 controller policy 是 bounded witness groups：每组最多 `max_witnesses_per_group` 个 witness；target witness 数超过该上限时必须拆分，controller 会拒绝超大单组。分组依据仍是 proof pattern、共享 helper family、loop/refinement phase 和依赖关系，manual witness order 只作为确定性 tie-breaker。不要为了减少 spawn 数把所有 witness 放进一个组；每个 group 在 `grouping_reason` / group entry 中说明其边界。

## 回 annotation/spec 的信号

出现以下信号时，不进入 vc-proving：

- `Q` 要求的数据结构资源在 `P` 中不存在。
- 分支 proof 需要的 pure fact 没有来自 guard、invariant 或 local assertion。
- witness 需要的逻辑 array/list value 没有在 C read 后绑定。
- postcondition 使用 `@pre` 值，但 assertion 缺少桥接等式。
- refinement 目标中的 `safeExec` program state 与当前 abstract state 对不上。
- annotation 修改后重新 symbolic execution，VC 基本没变化，可能 generated files 不是最新。
- candidate helper lemma 需要额外假设，而这些假设不能由当前 `P` 推出。
- proof 需要修改 generated files 或 witness statements。

报告必须写明 witness 名称、缺少的 resource / pure fact / abstract state、推荐回到 C annotation 还是 `case_lib` spec，以及当前 `source_version` / `source_goal_version` 是否匹配。不要用全局“annotation insufficient”代替 witness-local analysis。
