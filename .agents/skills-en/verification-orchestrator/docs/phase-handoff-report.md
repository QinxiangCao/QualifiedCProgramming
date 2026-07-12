# Phase、Handoff 和 Report 合同

本文件汇总 `verification-orchestrator` 需要的 run 级规则。AGENTS.md 是更完整的 source of truth；此处只保留执行时必须快速读取的内容。

## Phase 和 worktree lineage

每个 run 按固定顺序推进：

1. `intake`：记录 target C file、main worktree、run root、report root 和初始 `source_version`。
2. `annotation`：annotation round worktree 从 main worktree snapshot 创建。
3. `vc-checking`：round worktree 从 accepted annotation round worktree 创建。
4. `vc-proving-preparing`：controller 在 run root 下创建普通 container 目录 `worktrees/<run>/<case>-vc-proving-rN/`，并在 report root 下创建同名 preparing report directory；它不是 Git worktree，也没有 agent input/report/output。
5. group worktree：从 accepted vc-checking worktree 创建，并放在 `worktrees/<run>/<case>-vc-proving-rN/group_XX__<group_id>/`。
6. `vc-proving-verify`：parent verify 读取 group reports，写 `group_merged_result.json`，并准备 final candidate。
7. `final-candidate-apply`：main worktree 只从 controller accepted final candidate 采用正式文件。
8. `final-check` / `done`：main agent 完成最终一致性检查后由 `controller` 写入终态。

若 `vc-checking` 要求回到 annotation，新 annotation round 从当前 accepted annotation round worktree 创建，并携带对应 `source_goal_version` 下的 blocker context。

## 写入边界

- `controller`：写 run 状态、round acceptance、group acceptance、retry transition、`run_logs.json` 和 main-owned verification result；不启动 agent，不编辑 proof 内容。
- main agent：调用 `controller`，启动 fixed phase subagents / group-worker，执行 controller-owned `vc-proving-preparing` 和 parent verify step，等待 group report，执行 final candidate 采用。
- annotation-subagent：只在 annotation round worktree 修改目标 `.c` 和同一正式相对路径的 `case_lib`。
- vc-checking-subagent：只读 generated VC、diagnostics 和 `case_lib`，只写 `agent_result.vc_checking`。
- vc-proving-preparing：controller-owned action，只准备 manifest、普通 container 目录、group worktree 和 group-worker handoff，不证明 witness；不写 `agent_input.json`、`agent_report.json` 或 `agent_output.txt`。
- group-worker：只证明 assigned witness blocks，只在 group-local `case_lib` 新增当前 group suffix 的 helper declarations，或为这些 helper/proofs 所需的 Rocq 官方库 import。
- parent verify：只能通过 `controller` 的 `vc-proving-verify` 进入，失败必须 rollback parent files，并把失败作为 controller command error 返回 main agent 裁决，不写 vc-proving round blocker。

main agent 启动 owner 后默认等待。长时间运行本身不是 retry、stale 或 blocker 的 evidence。

## Handoff 文件

annotation / vc-checking subagent 的运行时消息由 controller `spawn-instructions` 生成，固定包含：

```text
Read <agent_input.json>.
The goal is to complete the workflow task assigned by the input JSON; <agent_report.json> is only the final report file recording the result.
Before acting, read the input JSON completely and read every skill or rule file listed in handoff.rules_source.
The input JSON, declared round worktree, declared source versions, and current files are the source of truth.
Do not rely on parent chat history or unstated assumptions as task context or evidence.
Minimize respawns: perform repair, retry, missing-file bootstrap, and alternative attempts inside this same spawn whenever the input versions are still current.
Do not stop for confirmation about optional context, missing bootstrap files, future proof difficulty, or recoverable tool feedback; make a conservative local choice and continue.
Work only in the declared round worktree; write only the declared report/output files and formal files allowed by allowed_write_paths.
No compromise operations: do not weaken specifications, bypass required checks, fake evidence, change generated files by hand, change witness statements to fit a proof, add Admitted/Axiom, use forbidden tools/tactics, or edit paths outside the handoff.
Task completion means the assigned phase work is completed under the strict workflow, with a terminal agent_result, required evidence, changed-files or blocker details, applicable source_version/source_goal_version, and an output note satisfying output_contract.
Controller acceptance is separate; do not mark yourself accepted or claim acceptance unless the controller writes it.
Reuse only previous_attempts, required_lessons, prior_failure_summaries, and output notes declared in the JSON; previous outputs are non-authoritative and lose conflicts to JSON, manifests, source versions, and current files.
Compact-error is not your blocked judgment; report it only as a compaction fact and let controller/main decide retry or final blocker.
If the strict workflow cannot be completed, write a blocked, stale, or compact-error result with concrete evidence instead of improvising around the process.
```

group-worker 的运行时消息由 vc-proving handoff helper 生成，固定包含：

```text
Read <group_worker_input.json>.
The goal is to complete the group-worker task assigned by group_worker_input.json; <group_worker_report.json> is only the final report file recording the result.
Before acting, read group_worker_input.json completely and read every skill or rule file listed under handoff.detailed_rules.skill_docs.
The group_worker_input.json, group_workers_manifest.json, declared group worktree, declared source_goal_version, and current files are the source of truth.
Do not rely on parent chat history or unstated assumptions as task context or evidence.
Minimize respawns: solve every assigned witness in this group inside this same spawn whenever the source_goal_version and helper namespace are still current.
Do not stop for confirmation about proof uncertainty, missing optional hints, or a failed tactic; inspect the proof state, try an alternate route, add current-suffix helpers when useful, and re-run the fixed group check.
Work only in the declared group worktree; write only the declared group_worker_report.json, group_worker_output.txt, assigned witness proof bodies, current group-suffixed case_lib helpers, and official Rocq library imports needed by those proofs.
No compromise operations: do not weaken specifications, bypass required checks, fake evidence, change generated files by hand, change witness statements, edit unassigned witnesses, edit seed case_lib declarations, add unsuffixed or foreign-suffix helpers, add non-Rocq/project/generated case_lib imports, add Admitted/Axiom, or use forbidden tools/tactics.
Task completion means the assigned group proof work is completed under the strict workflow, with a terminal group status, solved/unsolved witnesses, blockers or errors, changed-files details, helper/import declarations, source_goal_version-bound Coq evidence, and an output note satisfying output_contract.
Controller/parent verification acceptance is separate; do not claim group acceptance or final proof acceptance unless the controller writes it.
Reuse only references explicitly declared in group_worker_input.json; previous output notes are non-authoritative and lose conflicts to JSON, manifests, source versions, and current files.
Compact-error is not your blocked judgment; report it only as a compaction fact and let controller/main decide retry or final blocker.
If the strict workflow cannot be completed, write a blocked, stale, or compact-error result with concrete evidence instead of improvising around the process.
```

`vc-checking` handoff 必须隔离 parent transcript：

```json
{
  "spawn": {"fork_context": false, "fork_turns": "none", "parent_context_allowed": false},
  "context_policy": {
    "source_of_truth": "agent_input_json_and_round_worktree",
    "main_agent_transcript_allowed": "no"
  }
}
```

`vc-proving-preparing` 的并发上限由 main agent / `controller` 写入 preparing attempt state，默认 4；manifest 可生成 `dependency_ready_order` 作为 difficulty-first scheduling hint，但它不是 acceptance evidence。vc-checking 应优先减少 group 数量，避免把可由一个 worker 处理的 witnesses 机械拆成多个 spawn。

每个 group handoff 必须包含：

```json
{
  "helper_namespace": {
    "policy": "group-id-suffixed",
    "group_id": "<group_id>",
    "suffix": "__<sanitized_group_id>",
    "required": "yes"
  }
}
```

suffix 只允许字母、数字和下划线；非法字符替换为 `_`，sanitized 为空则拒绝该 group。

## Report layout 文件

run level:

- `run_logs.json`
- `timing_summary.json`

annotation / vc-checking round report directory:

- `agent_input.json`
- `agent_report.json`
- `agent_output.txt`

vc-proving-preparing report directory:

- `group_workers_manifest.json`
- `group_merged_result.json`，仅 parent verify 后产生
- `groups/`，包含 group-worker report directories

group report directory:

- `group_worker_input.json`
- `group_worker_report.json`
- `group_worker_output.txt`

所有 JSON input/report 必须有 `schema_version`。`run_logs.json` 是 append-only JSONL，记录 controller event 和 state snapshot；legacy `run_status.json` / `run_events.json` 只可作为只读兼容输入，新 run 不写。

`agent_output.txt` 和 `group_worker_output.txt` 只是 `non-authoritative reuse note`，第一行必须是 `# Reuse Note`，正文必须包含：

```text
Note kind: non-authoritative reuse note
This file is not acceptance evidence.
```

如果 output note 与 JSON report、handoff、manifest、source version 或当前 worktree 文件冲突，忽略 output note。

## Acceptance 和 stale

annotation / vc-checking round 只有同时满足以下条件才可由 `controller` 标记 accepted：

- phase owner 已写 `agent_result`，且不是 `pending`、`stale` 或 compact error。
- 当前 `source_version` / `source_goal_version` 与 handoff 一致。
- worktree diff 只包含该 phase 允许修改的 formal files。
- required QCP / `coqc_check` evidence 和 phase main-owned check 通过。
- `case_lib` contract 通过。
- `agent_report.json.status == "accepted"`，且 `run_logs.json` 最新 state snapshot 记录 accepted round worktree。

`vc-proving-preparing` acceptance 不是 agent round acceptance；它只在 `vc-proving-verify` 成功、`group_merged_result.json.merge_vc_ready == "yes"`、parent full fixed `coqc_check` 通过且 final candidate 已记录后由 controller 写入 `accepted_rounds.vc-proving-preparing`。

上游 accepted round worktree 被替换后，所有 downstream round/group report 立即 stale。stale 目录只能作为只读参考，不得作为当前 conclusion 或 dependency evidence。

`source_version` mismatch 使 annotation-derived downstream evidence 失效；`source_goal_version` mismatch 使 vc-checking、vc-proving-preparing 和 group-worker evidence 失效。group-worker 的 `coqc_check` evidence 必须直接记录当前 `source_goal_version`。

## Group acceptance 和 parent verify

accepted group report 只表示该 group 可交给 parent verify；最终 proof acceptance 只来自 `vc-proving-verify` 写入的 `group_merged_result.json`，以及后续 `final-candidate-apply` / `final-check`。

parent verify 按 manifest 顺序恢复 solved assigned witness proof blocks，并按 top-level declaration block 合并带 suffix 的 helper declarations；group-local 新增的 Rocq 官方库 import 会去重后合入 merge 结果。以下情况直接 reject 并 rollback：

- unsuffixed helper 或 foreign suffix helper。
- duplicate helper names。
- 非 Rocq 官方库 import。
- seed `case_lib` declaration 修改。
- forbidden declaration。
- generated file edits。
- witness statement changes。
- unassigned witness edits。
- failed Coq evidence。

若多个 group 需要同一个数学事实，允许各自新增同构但带各自 suffix 的 helper。若必须共享 helper，回到 annotation，将该事实提升为 annotation-approved seed `case_lib` declaration。

## Retry 和 compact error

retry、stale 和 blocker transition 必须基于 durable evidence：written report、run log/error state、explicit cancellation、compact error、stale source version 或 machine-checkable failure。

compact error 不是 proof failure，也不是 owner 自己作出的 `blocked` 判断。owner 只报告 `compact-error` 事实和可复用 evidence pointer；controller / main agent 根据 attempt_control、run log 和最大重试次数决定重启同 role attempt 或在耗尽后写 `compact-error-retry-exhausted` blocker。默认最多 3 次 compact attempt，并把 previous attempt 的 round/group directory 作为只读参考。
