---
name: group-worker-proving
description: 由 group-worker 使用，读取 group_worker_input.json，在 group worktree 中证明 assigned witness blocks，并只在 group-local case_lib 中新增带当前 group_id suffix 的 helper declarations 和必要 Rocq 官方库 import。
---

# Group Worker Proving

只读取 startup message 指定的 `group_worker_input.json`。其结构化字段是唯一 source of truth；不得依赖 parent chat context。
`problem_context`、`annotation_design_summary` 和 `vc_checking_plan` 若存在，必须优先作为 proof strategy 起点；缺失时在本次 spawn 内直接分析 assigned witnesses，不返回确认请求。

## 文档

- `docs/coq-tooling-policy.md`：固定 Coq tooling 和 group-check evidence。
- `docs/separation-logic-whole-proof-tactics.md`：separation logic proof tactic 操作规则、side goal 形态和常见证明骨架。
- `docs/refinement-proof-tactics.md`：refinement / `safeExec` proof 规则、`prog_nf` 工作流和禁止的低层 reconstruction。
- `docs/pure-proposition-proof-patterns.md`：annotation-facing pure predicate 的 proof-side bridge、rewrite 和 helper 规则。
- `docs/reference-cases.md`：允许参考的 case 范围。

## 允许工作

- 只编辑 group worktree 中 assigned witness proof bodies。
- 只在 group-local `case_lib` 新增已证明的顶层 `Lemma`、`Theorem`、`Fact` 或 `Remark`。
- 允许在 group-local `case_lib` 新增证明所需的 Rocq 官方库 import，例如 `Require Import Coq...` 或 `From Coq... Require Import ...`。
- 不修改 generated files、witness statements、unassigned witness blocks 或 seed `case_lib` declarations。
- formal output 只写 group worktree；machine output 只写声明的 `group_worker_report.json`。
- 必须在单次 spawn 内尽量完成本 group 的所有 assigned witnesses。失败 tactic、proof route 不确定、缺少 optional hint、或需要当前 group suffixed helper，都应在本次 spawn 内调试、改 proof、补 helper、重跑 fixed group-check。

## Blocking 原则

group-worker 的 `blocked` 只用于两类情况：

- 某个 assigned witness lemma 在当前 `source_goal_version` 下完全不可证：经过 proof state 分析、必要 helper 尝试和 fixed group-check/debug 后，确认缺少的 premise 不能从当前 VC、当前 `case_lib` 或允许新增的当前 suffix helper 中推出，必须回到 annotation/spec。
- 必要工具发生重大错误：fixed `coq_tooling.py debug` / `check` 或 group-check workspace 完全不可运行，且已记录具体 command evidence。

以下情况不得 `blocked`，必须在本次 spawn 内自行解决：单个 tactic 失败、proof route 不确定、需要新增当前 group suffix helper、vc-checking plan 缺字段、optional reference 缺失、同构 helper 可能被其他 group 也需要、或某个 witness 需要多轮 debug。输入版本失效写 `stale`。context compaction 只写 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。

## Helper namespace

每个新 `case_lib` helper 名称必须以 `group_worker_input.json.helper_namespace.suffix` 结尾。

- policy 必须是 `group-id-suffixed`。
- suffix 形如 `__<sanitized_group_id>`。
- 不新增 unsuffixed helper。
- 不使用其他 group 的 suffix。
- 如果 helper 必须跨 group 共享，停止并报告 blocker，让该事实回到 annotation 成为 seed `case_lib` declaration。
- 不要把“多个 group 可能需要同构 helper”作为 blocker；当前 group 可以新增带自己 suffix 的 helper 并证明。

每个新增 helper 和新增 Rocq 官方库 import 都要写入 `agent_result.vc_proving.group.case_lib_added_declarations`，包含 `name`、`kind` 和 `statement_hash`。import 的 `kind` 写 `Import`，不得记录或新增非 Rocq 官方库 import。

## Coq feedback

- 只使用 handoff 声明的 `coq_tooling.py debug` 和 `coq_tooling.py check`。
- 不手写 Coq flags，不调用 Dune，不调用 Rocq MCP，不使用 `_CoqProject` derived command，不使用 `coqc -o`。
- final group evidence 必须满足 `target_kind == "group-check"`，并记录当前 `source_goal_version`。
- JSON 检查使用 `python3` 或 shell builtins，不使用 `jq`。

## Report 输出

`group_worker_report.json` 必须设置 `agent_result.vc_proving.group.status` 为 `completed`、`blocked`、`stale` 或 `compact-error`。`completed` report 包含 solved/unsolved witness lists、blockers/errors、candidate file paths、helper namespace、added helper declarations 和 Coq evidence。`compact-error` report 只记录 compaction 事实和可复用 evidence pointer，不声明 witness 不可证。

不得遗留 `Admitted.`、`Abort.`、extra `Axiom`、debug commands，或在 `*_proof_manual.v` 中新增 helper declarations。

同时写 `group_worker_output.txt` 作为 `non-authoritative reuse note`。第一行必须是 `# Reuse Note`，正文包含 `Note kind: non-authoritative reuse note` 和 `This file is not acceptance evidence.`。如果 output note 与 structured/current sources 冲突，以 `group_worker_report.json`、`group_worker_input.json`、`group_workers_manifest.json`、source versions 和当前 worktree files 为准。
