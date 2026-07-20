---
name: verification-orchestrator
description: 为单个验证 case 控制 controller 状态机、唯一持续 annotation agent、逐 attempt annotation reports、根目录 annotation/vc-checking、三级 lib、copied group directories、deterministic proving_merged 与 final-check。
---

# Verification Orchestrator

只由 main agent 使用。以 `AGENTS.md` 为完整合同；按需读取：

- `docs/phase-handoff-report.md`：phase、轻量 Markdown/JSON 文件和 acceptance。
- `docs/path-configuration.md`：controller-owned symexec/Coq path。
- `docs/forbidden-lemma.md`：manual 与三级 lib 禁用 lemma。

## 边界

- 只通过 `scripts/controller.py`；internal modules不提供 agent CLI。
- controller 写 state、event、acceptance、retry/stale，并创建 handoff；不启动 agent、不写 proof。main agent每个 run只 spawn一次 annotation agent，之后只向保存的 target append。
- annotation 直接修改 main root target C/`formal_case_lib`；vc-checking 对 main root formal files只读。
- group-worker 只改 fixed group copied manual/`group_worker_lib`；`proving_merged_lib` 只由机械 merge 生成。
- agent-facing handoff 是 Markdown；terminal JSON 保持扁平，不复制规则、manifest、tooling evidence 或 controller state。
- preparing/parent verify 不是 agent round，不创建 phase-agent files。

## Controller 顺序

1. `init-run` / `step`：创建 run；首轮使用 `reports/<run>/annotation-attempts/annotation-attempt1/`，并建立唯一 annotation session state。
2. `spawn-instructions` 首次返回 spawn message。后续 annotation retry创建新的 `annotation-attempts/annotation-attemptN/agent_input.md` 主总结模板并停在 `awaiting-main-summary`；main agent阅读原始 blocker、完成模板并调用 `annotation-summary-ready` 后，controller才返回 append message。main agent必须保留首次 annotation target并复用；attempt lifecycle、`review-attempt`照常由 controller记录。
3. `annotation-check-round`：重跑 symexec、diagnostics split、`formal_case_lib` check，接受 current version。
4. `vc-checking-check-round`：验证 v3 group plan exact coverage/dependency/version。
5. `vc-proving-preparing`：写 compact base/worker manifests，copy group files，创建 group Markdown handoff。
6. group lifecycle/review：controller 重跑 fixed group-check后才接受 group。
7. `vc-proving-verify`：机械 merge、parent full check，写 compact `proving_merged_result.json`。
8. `final-apply` / `final-check`：backup、写回；controller只清除current target case与run非build区域的旧Coq side products，保留前置全量make的基础`.vo`；fresh symexec 后在 refresh directory diagnostics split raw manual，再做 full check、结构/lib 与检查后 cleanup 扫描，完成后写 done。失败且 rollback 成功则回到 `final-candidate-apply`，必须重新 apply 后再 check。

每次agent delivery/return都必须用`mark-attempt-started`/`mark-attempt-returned`建立真实墙钟边界。annotation handoff另含配对`timing-stage`命令，owner在annotation-checking完整review/repair loop前后执行。controller据此生成按annotation attempt及vc-checking/vc-proving round组织的`qcp-timing-summary/v4`；summary优先整体生命周期，只下钻重要stage，不记录单witness时间或全局command累计。

## 操作规则

- main agent 只执行 controller 返回的 action/command，不自行拼 path、flags、overlay 或 build directory。
- 首轮 annotation action只 spawn一个 agent；以后 `append-annotation-agent` action必须发给同一 target。每次 retry的 `agent_input.md` 由 main agent按五段模板总结 blocker cause、evidence、previous-attempt reflection、required repair与scope decision，并保留原始 Markdown/JSON路径；模板未完成时controller拒绝append。每次 append都要求重新完整读取两个 annotation skills、主总结和原始证据；第三次及以后还要求从更大范围重构 spec/contract/invariant。
- vc-checking/group-worker 使用不含 parent transcript 的独立会话；handoff Markdown/current files 是 source of truth。
- 长时运行不是 retry evidence。annotation compact repair继续 append同一 target；其他 agent compact error按 state 中 bounded policy重启；version变化使 downstream stale。
- final-check 失败后只按 controller state 恢复：rollback 成功时 `step` 返回 `final-apply`；rollback 失败时没有后续 action。cleanup evidence 保持 compact，不保存全部副产物路径。
- acceptance只读 `controller_state.json`、event log、current files和 controller-generated merge result；owner report不由 controller改写。
