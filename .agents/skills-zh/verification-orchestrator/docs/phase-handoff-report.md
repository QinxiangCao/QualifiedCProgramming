# Phase、Handoff 和 Report

`AGENTS.md` 是完整合同；本文件只列执行时最小接口。

## 文件职责

| 文件 | 读写者 | 只保存 |
|---|---|---|
| `reports/<run>/annotation-attempts/annotation-attemptN/agent_input.md` | attempt 1: controller；later: controller template + main agent summary → 唯一 annotation owner | 首轮背景；后续 blocker因果总结/反思、原始 evidence路径、version、exact commands、linked rules与annotation-checking timing边界 |
| `reports/<run>/annotation-attempts/annotation-attemptN/agent_report.json` | annotation owner | 本次 terminal status、check summary、changed files或 blockers |
| `reports/<run>/annotation-attempts/annotation-attemptN/agent_output.md` | annotation owner | 本次人类分析与 repair notes；非 acceptance evidence |
| `rounds/<round>/agent_input.md` | controller → vc-checking owner | 当前任务、路径、version、linked rules |
| `rounds/<round>/agent_report.json` | vc-checking owner | terminal status、version与 blockers |
| `rounds/<round>/agent_output.md` | vc-checking owner | 人类可读分析与 retry/annotation feedback；非 acceptance evidence |
| `group_plan.json` | vc-checking/controller | group id、witnesses、dependencies、短 strategy/helper hints |
| `base_manifest.json` | preparing | formal paths、seed/witness hashes、version |
| `group_workers_manifest.json` | preparing/controller | group copies、assignment、namespace、commands、order |
| `group_worker_input.md` | controller → group-worker | 单组任务和 exact commands |
| `group_worker_report.json` | group-worker | terminal status、version、blockers |
| `group_worker_output.md` | group-worker | 可选人类 proof notes |
| `proving_merged_result.json` | parent verify | compact candidate/check/merge trace |

不要在 JSON 中重复 Markdown 规则、完整 plan/manifest、parent transcript、command argv/cwd/flags、pending evidence template或 controller state。

## 顺序

`intake → annotation → annotation-check-round → vc-checking → vc-checking-check-round → vc-proving-preparing → group-worker/review → vc-proving-verify → final-apply → final-check`。annotation main-check失败、vc-checking或group-worker返回 annotation/spec blocker 时，controller/review先在 `next_actions` 排入main-owned `retry-round` transition。main agent执行后，controller使 downstream stale、创建下一次 `annotation-attempts/annotation-attemptN` 和 blocker-summary模板，但状态停在 `awaiting-main-summary`。main agent阅读原Markdown/JSON和controller main-check evidence，完成模板的五段分析；`annotation-summary-ready`验证并封存 input 后才产生发给原 annotation target的 append action，然后重新走 annotation-check-round。final-check 失败且 rollback 成功时回到 `final-candidate-apply`，`step` 只返回 `final-apply`；重新 apply 后才能再次 final-check。rollback 失败时不产生后续 action。

每个 annotation iteration 的三文件直接保存在总目录下独立且不覆盖的 `reports/<run>/annotation-attempts/annotation-attemptN/`。input在delivery前记录digest，report/output在`mark-attempt-returned`时记录digest；review和feedback拒绝封存后的修改。`verification_runs/<run>/annotation_history/<attempt-id>/` 只保存 formal `before/after`；agent不写 history。新 annotation acceptance 使旧 downstream plan/group/merge stale。

所有owner在实际交付/返回边界执行`mark-attempt-started`/`mark-attempt-returned`。annotation owner在annotation-checking完整review/repair/recheck之前和之后执行handoff的配对`timing-stage` start/finish。`timing_summary.json`由controller写成`qcp-timing-summary/v4`：`annotation_attempts`和`rounds`中的每项都明确绑定attempt/round，先给created-to-finished整体时间，再给少量重要stage。vc-checking的所有witness分析合为一个`witness-analysis`；vc-proving的并行groups只给整体墙钟区间以及Coq/review合计，不产生单witness timing或旧式全局command计数。

## Main agent blocker summary

后续 `agent_input.md` 的 controller-owned sections 固定 assignment、target、原始 blocker Markdown/JSON、controller evidence、skills、writable paths与exact commands。main agent只替换五个 `MAIN_AGENT` 注释：

1. `Main-agent blocker conclusion`：主失败、被阻塞的 witness/check、回 annotation 的理由。
2. `Evidence and causal analysis`：决定性证据及 spec/contract/invariant/assertion/call instantiation 根因链。
3. `Reflection on the previous annotation attempt`：前次错误假设、应保留内容、不得重复的策略。
4. `Required annotation repair`：修改目标/位置、保持条件和三个 check 的成功标准。
5. `Scope decision`：局部修复或整体重构及理由；iteration 3+必须响应 broader-redesign requirement。

所有区段必须具体，不能只复制原 report、写“继续尝试”或删除 controller事实。`annotation-summary-ready` 检查模板 marker、必需区段、原始来源、skill路径、commands和 repeated-repair instruction，并记录 input digest；封存后修改 input会阻止 agent delivery/review。

## Acceptance

- owner report `completed` 只声明 owner work结束；controller main-owned check 另行决定 acceptance。
- annotation controller 重跑 canonical symexec、diagnostics split与`formal_case_lib` fixed check。
- vc-checking controller校验 v3 plan的 current version、exact witness coverage、唯一 assignment、group bound与无环 dependency，然后加 `verified: true`。
- group controller先重验 preparing 时钉入 state 的 base/worker manifest digests并重新派生 current versions，再检查 copied manual的 assigned/unassigned blocks、statement、Admitted/Abort、seed lib、helper namespace/import/declaration与 forbidden lemma，最后从 state/manifest派生 overlay并重跑 group-check；不读取 worker粘贴的 evidence。
- parent verify再次检查 group directory、assigned/unassigned blocks、helper suffix、seed lib、forbidden lemma并运行 full goal check。Coq build复用前置全量make已有的基础`.vo`，但删除并重编译current target case五个module；缺少required基础`.vo`时失败，不回退重编译基础源码。
- passed merge仍须 final-apply/final-check。final freshness 对 raw refresh manual 先 diagnostics split，再比较 cleaned witness names/statements；cleanup 由 controller 只删除current target与run非build旧副产物、检查后重扫同一边界并保留基础`.vo`，state只保存删除/错误/残留数量和首个失败信息。

## Retry

retry只基于 terminal report、explicit cancellation、version mismatch、machine-check failure或 compact error。对 annotation，`--previous-attempt` 是 feedback来源：可以是 annotation、vc-checking或 `<vc-proving-round>:<group-id>`；controller提取对应 Markdown与JSON原路径，创建新的 attempt/template。旧文件只读。main agent完成总结门禁后，必须把 controller message追加到首次保存的 annotation target，禁止新 spawn。长时运行不是 retry依据。

每次 annotation append都明确要求重新完整读取 annotation-filling与annotation-checking skills；iteration 3及以后还明确要求考虑整体重构数学 spec、function contracts和 invariants。compact error不是 proof failure；annotation未耗尽次数时仍append同一 agent，vc-checking/group-worker才重启同 role，耗尽后记录 `compact-error-retry-exhausted`。
