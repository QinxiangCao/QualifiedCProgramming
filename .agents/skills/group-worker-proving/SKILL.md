---
name: group-worker-proving
description: 由 group-worker 读取 group_worker_input.md，只编辑 fixed group directory 的 copied manual 和 group_worker_lib，证明 assigned witnesses 并写 compact terminal result。
---

# Group Worker Proving

完整读取 startup message 指定的 `group_worker_input.md` 和 linked rules；不得依赖 parent transcript。manifest是 controller machine file，不需要整份载入上下文。

## 文档

- `docs/coq-tooling-policy.md`：scripted Coq、overlay 与 group-check evidence。
- `../verification-orchestrator/docs/path-configuration.md`：group path teaching。
- 其他 linked tactic/reference guides。

## 允许工作

- 只编辑 handoff `Copied manual` 中 assigned witness proof bodies。
- 只在 handoff `group_worker_lib` 新增 proved `Lemma`/`Theorem`/`Fact`/`Remark` 与必要 Rocq official imports。
- debug script只写 handoff `Debug script` 给出的 exact `_coq_builds` path。
- machine output只写 declared compact group report；可选 proof notes写 `group_worker_output.md`。

`formal_case_lib` read-only；generated files和unassigned witness blocks不可修改。group directory 最终只能有 copied manual 与 `group_worker_lib`。

## Helper namespace

每个新 helper 名必须以 `helper_namespace.suffix` 结尾。禁止 unsuffixed、foreign-suffix、seed declaration修改、project/generated imports。多个 groups需要同构事实时各自写 suffix helper；必须共享时回 annotation 提升为 `formal_case_lib` spec。

无需在 worker report重复新增 declaration metadata；parent merge直接解析 `group_worker_lib` 并记录 name/kind/statement hash。

## Coq feedback

- 原样执行 handoff `Commands` 代码块中的 debug/check commands；两者必须进入 controller，禁止直接调用 internal `coq_tooling.py`。
- 不拼 `--workspace-root`、build path、overlay、flags 或 cwd。
- `completed` 前 exact group-check 必须通过并绑定 current `source_goal_version`；controller review会从 state/manifest派生相同 overlay并重跑，不把完整 evidence复制进 worker report。
- 禁止 raw Coq、Dune、Rocq MCP、`coqc -o`。

## Blocking 与 report

single spawn 内尽量完成全部 assigned witnesses；failed tactic、missing optional hint、需要 suffix helper、多轮 debug 都应 local repair/retry。

blocked 只用于经过 concrete proof-state/helper/scripted checks 后确认 premise 不可从当前 VC/`group_worker_lib` 推出，或 exact tooling 完全不可运行。版本失效 stale；compaction 只写 compact-error fact。

返回 `blocked` 时，在 `group_worker_output.md` 写清 assigned witness、无法推出的 premise/resource、已尝试的 suffixed helper 与为何指向 annotation/spec 缺口；compact JSON report只保留 blocker。main agent会读取 Markdown与JSON原文件，按固定模板总结原因、反思和修复范围，再把 summary及原文件路径 append到 run 内唯一 annotation agent，不会为修正另开 annotation agent。

`group_worker_report.json` 使用 `qcp-group-worker-report/v2`，只含 terminal status、current `source_goal_version` 与 blockers。assignment、candidate paths与namespace已在 handoff/manifest，不重复记录。不得 claim controller/parent acceptance。
