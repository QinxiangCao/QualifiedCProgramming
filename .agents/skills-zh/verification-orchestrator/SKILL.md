---
name: verification-orchestrator
description: 为单个验证 case 定义 controller、main agent、fixed phase subagents、controller-owned vc-proving-preparing container、JSON handoff files、case_lib、group-worker deterministic merge 和 final-check 的协作合同。
---

# Verification Orchestrator

本 skill 只由 main agent 使用。`controller` 是唯一 run 状态和 acceptance 写入口；main agent 调用 `controller`、启动 fixed phase subagents / group-worker、执行 controller-owned preparing / verify step，并在 owner 写出 report 或 controller step 成功后继续推进。

## 文档

- `docs/phase-handoff-report.md`：phase 顺序、worktree lineage、写入边界、handoff/report、stale / retry / compact error 规则。
- `docs/forbidden-lemma.md`：manual proof 和 `case_lib` 禁用 lemma 列表。

## 必守边界

- fixed phase subagents 只能由 main agent 按 `controller` 的 spawn instruction 启动；脚本不得启动 subagent 或 group-worker。
- main agent 启动 owner 后默认等待；只有 report、compact error、stale、blocked、explicit error、用户取消或 `controller` 已落盘 evidence 能证明 attempt 失效时，才 retry 或替换。compact error 不是 owner 的 `blocked` 判断；owner 只报告事实，controller / main agent 决定重试或最终 blocker。
- `controller` 发现的问题如果不改变 formal source 语义、不绕过版本 / freshness / fixed check / `case_lib` contract，且可由 main agent 或 controller 的 main-owned 简单补正解决，应记录补正并继续流程，不升级成 terminal `blocked`。例如报告形态缺口、inline artifact 需要落盘、非权威 output note 缺失或警告、可重新传入正确参数的 main-owned check，都不应阻断证明流；真正语义不可证、版本失效、必要工具不可用或验收 evidence 不可信仍按 `blocked` / `stale` 处理。
- `annotation`、`vc-checking`、controller-owned `vc-proving-preparing`、group-worker 和 `final-check` 必须沿 AGENTS.md 的目录和 worktree lineage 推进。
- `vc-proving-preparing` 和 parent merge/verify 不是独立 agent round，不创建 Git worktree，不生成 `agent_input.json`、`agent_report.json` 或 `agent_output.txt`。`worktrees/<run>/<case>-vc-proving-rN/` 是普通 container 目录，只用于容纳 group-worker Git worktrees。
- `vc-proving-preparing` 或 parent merge/verify 失败时，controller command 直接非零返回给 main agent 裁决；不得把这类 controller step 失败写成 vc-proving round blocker。
- `case_lib` 是唯一 active Rocq lib；annotation 写 seed spec declarations，group-worker 只新增带当前 group suffix 的 proved helper declarations。
- `coq_tooling.py` 是唯一 Coq feedback 与 verification 入口；JSON 操作不依赖 `jq`。

## Controller 调用入口

统一入口：

```bash
python3 .agents/skills/verification-orchestrator/scripts/controller.py \
  --main-worktree-root <main-worktree-root> <command> ...
```

所有入口只推进 controller state、写 handoff/report/run log，或执行 main-owned check；它们不得启动 fixed phase subagent 或 group-worker。

- `init-run`：创建本次 run 的 run root、report root、初始 `run_logs.json` state snapshot、`source_version`、problem context、reference policy 和 compact retry budget。
- `step`：按当前 phase 串行推进 controller state；创建缺失 round attempt 或 `vc-proving-preparing` container、写 next action、为 ready attempt 写 main-owned action，并在 preparing phase 调度 dependency-ready group-worker 或 parent verify action。
- `spawn-instructions`：根据 `next_actions[].id` 输出 subagent / group-worker 启动消息和 handoff 路径；main agent 读取后自行启动 owner。
- `mark-attempt-started`：记录 attempt 已由 main agent 启动，更新 attempt 状态和 timing。
- `mark-attempt-returned`：记录 owner 返回事实和 result status；不做 acceptance。
- `review-attempt`：读取 `agent_report.json` 或 `group_worker_report.json`，按当前版本、phase contract、compact/stale/blocker 规则做 controller review；对可 main-owned 简单补正的报告形态问题记录 `controller_simple_repairs` 并继续。
- `retry-round`：基于 previous attempt 创建同 phase 或 annotation retry round，携带只读 previous_attempt、required lessons 和 prior failure summaries。
- `verify-round`：显式验证 vc-checking group plan 与 manual witnesses / `source_goal_version` 一致，并给 group plan 写入 `controller_verified`。
- `annotation-check-round`：annotation accepted 前的 main-owned 检查入口；运行 canonical symbolic execution、diagnostics split、清理 manual diagnostic goals、计算 `source_version` / `source_goal_version`，并接受 annotation round。
- `vc-checking-check-round`：验证 group plan 覆盖 cleaned manual obligations、依赖合法且绑定当前 `source_goal_version`，并接受 vc-checking round。
- `vc-proving-preparing`：controller-owned preparing step；调用 vc-proving scripts 初始化 manifest、准备 group worktrees 和 group-worker handoff，并把 preparing container 推进到 ready-for-groups。兼容入口 `vc-proving-setup` 只作为旧命令别名保留。
- `vc-proving-verify`：parent verify 唯一入口；调用 deterministic group merge，恢复 solved witness blocks，合并 suffixed helpers，运行 parent full fixed `coqc_check`，并写 `group_merged_result.json` / final candidate。
- `annotation-preflight`：检查 annotation subagent 记录的 canonical QCP evidence 和 `case_lib` Coq evidence 是否满足最低要求。
- `final-apply`：把 controller accepted final candidate formal files 复制回 main worktree；失败时回滚并写 blocker。
- `final-check`：final-candidate-apply 后的最终一致性检查，覆盖 symbolic execution freshness、fixed `coqc_check`、manual proof structure、`case_lib` contract、forbidden lemma 和 cleanup scan。
- `validate-artifact`：轻量校验 `agent-input`、`agent-report`、`group-worker-input`、`group-worker-report`、`manifest` 或 `run-log` 的 schema / 必要字段。
- `render-output`：从 structured report 渲染 `agent_output.txt` 或 `group_worker_output.txt` 非权威复用笔记。
- `check-output-note`：检查 output note 是否满足非权威复用笔记格式；该检查结果不是 acceptance evidence。

## 正常推进

1. `intake` 创建 run root、report root 和初始 `source_version`。
2. `annotation` 由 annotation-subagent 修改目标 `.c` 和 `case_lib`；`annotation-check-round` 刷新 generated files、写 diagnostics，并生成 `source_goal_version`。
3. `vc-checking` 由 vc-checking-subagent 只读检查 manual VC，并输出绑定当前 `source_goal_version` 的 group plan。
4. `vc-proving-preparing` 由 controller/main-owned step 准备 manifest、普通 container 目录、group worktree 和 group-worker handoff；group-worker 证明 assigned witnesses。
5. `vc-proving-verify` 由 `controller` 调用 parent verify，确定性合并 solved witness blocks 和 suffixed helpers，写 `group_merged_result.json`。
6. `final-candidate-apply` 后由 main agent 执行 `final-check`，确认 freshness、fixed `coqc_check`、manual proof structure、`case_lib` contract 和 cleanup。
