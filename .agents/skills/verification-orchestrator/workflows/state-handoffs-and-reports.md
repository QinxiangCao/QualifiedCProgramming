# 状态、交接与报告

## 一份任务事实

`reports/<run>/controller_state.json` 使用 **schema 4**。固定输入包括 roots、`target_files`、库策略、
问题与 spec 约束；`attempts` 保存任务事实。`current` 只有 `annotation`、`vc-checking`、`vc-proving`
三个当前任务指针，group owner 的任务记录位于相应 proving attempt 的 `groups` 中。

Owner 任务使用同一生命周期：

```text
prepared → claim → running → finalize 开始 → returned → accepted / blocked
                                                 ↘ 同 owner repair → prepared
```

`returned` 表示 owner 已停止写入，接纳可能尚未完成。`finalize-delivery` 可从这个状态继续。
修复保留 attempt、owner 和文件目录，更新 feedback 与 `repair_index`，再领取 append action。Phase attempt id 同时
就是 CLI 的 round id；group delivery id 为 `<round>:<group_id>`。

Controller 每次根据事实派生 `next_actions` 和 `waiting_for`。它们只出现在响应中，不持久化。
没有第二份 `rounds`、`accepted_rounds` 或 session 状态。`pending_retry` 只记录已确定的重试
目的、原因与来源；group annotation-gap 的批次处理直接从当前 group 终态计算。

Main 顺序提交业务状态；group 工具检查不为计时改业务状态。不得手改 state 伪造接纳。Schema 3
及更早 run 不迁移：用创建它的代码恢复，或从当前 formal 文件初始化新 run。

## 路径与文件

```text
verification_runs/<run>/
  dependency_plan.json
  annotation_history/annotation-attemptN/{before,after}/...
  <case>-vc-proving-rN/
    groups/group_NN__<id>/<case>_proof_manual.v
    groups/group_NN__<id>/<case>_lib.v       # active lib 时
    proving_merged/...                    # 当前候选
  _coq_builds/...
reports/<run>/
  controller_state.json
  controller_control.json
  run_logs.json                           # JSON Lines
  timing_summary.json
  annotation-attempts/annotation-attemptN/
    agent_input.md / agent_report.json / agent_output.md
    annotation_plan.json
  rounds/<case>-vc-checking-rN/
    agent_input.md / agent_report.json / agent_output.md
    group_plan.json
    <case>_proof_manual.v                  # VC debug copy
  rounds/<case>-vc-proving-rN/
    groups/group_NN__<id>/
      group_worker_input.md / group_worker_report.json / group_worker_output.md
      tool_calls.jsonl
      proof_reuse.md                      # 可选
  final-check/backup/...
```

无 manual VC 时空 `group_plan.json` 位于 run 的 report root。Group assignment、目录及 candidate
由当前 plan/manual/lib 加 round identity 派生；不另写 base manifest、worker manifest 或 merged-result
镜像。`final_candidate` 只保存 round，消费时重新读取候选文件。

Annotation before/after history 保存原 bytes，作为 failed-VC 解释和模型复用的只读参考。
`failed_vcs` 项包含 `source_attempt`、`name`、`parent`、`annotation_location`、`manual`、`message`。
Group id 使用 ASCII 字母、数字与下划线；新增 helper 使用 exact `__<group_id>` suffix。

## Claim 与 owner 交接

Main 执行 owner action 的 `claim_invocation`，保存 owner→agent target 映射，把返回的
`handoff.prompt` 原样发送。首次 spawn，append action 则联系同一 target。每个 run 的 annotation
owner 不变；其他任务的同 attempt 修复也不换 owner。

Owner 读取 handoff 中的角色 skill、当前 assignment、写入边界和结构化 Commands。终态报告最后
写入，之后停止修改并通知 main。Main 使用返回的 `finalize_invocation`；不自行构造接纳命令。

## 报告与 plan

成功报告恰为：

```json
{"status": "completed"}
```

阻塞报告恰含 `status` 和一个 `blocker`：

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "annotation-gap",
    "kind": "missing-premise",
    "vcs": [{"name": "vc_name", "parent": null, "annotation_location": "function/loop boundary"}],
    "message": "已有前提、缺失结论和原因",
    "repair_boundary": "C annotation"
  }
}
```

Blocker 和 VC 项字段固定。语义缺口必须列实际 VC；工具/报告问题可用空 `vcs`。
VC-checking 的 gap 类为 `annotation-gap`、`specification-gap`、`dependency-gap`；另允许
`plan-defect`、`report-defect`、`infrastructure`。Group 的语义缺口统一用 `annotation-gap`，VC 必须
属于本组，并在 `group_worker_output.md` 写非空解释。调度读取结构化字段，不从 prose 提取 VC。

`annotation_plan.json` 为 version 2，字段为 `version`、`status`、`function_specs`、`loop_invariants`、
`new_predicates`、`vc_comparisons`。设计摘要由 owner 负责；脚本检查必要结构、VC 身份和comparison
覆盖，不根据推测的函数/循环数量判断数学质量。Group plan 的当前覆盖和数组顺序由 VC owner 负责。

## 暂停、恢复与诊断

Pause 更新 run control 并写 control signal，任务、owner 和文件保持原样，不保存一份 suspended
动作列表。工具响应 signal 并清理进程树。明确 resume 后运行 `step`：running owner 继续原任务，
returned 交付重新 finalize，prepared 任务继续 claim。

Run/group 日志记录命令、耗时和退出情况；`timing_summary.json` 含 `run`、`commands`、
`annotation_attempts`、`rounds`，其中耗时总和不等于并行墙钟时间。日志失败只是诊断，不是证明
是否成立的证据。Symexec progress 只记录实际输出、耗时和文件尺寸，不猜测当前函数或数学进展。
