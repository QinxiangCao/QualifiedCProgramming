# 仓库定位

本仓库验证 C 程序：补充 annotation、运行 symbolic execution、检查 manual VC、证明 Rocq obligations，并完成最终一致性检查。

系统由 controller、main agent、每个 run 唯一且持续复用的 annotation-subagent、按轮创建的 vc-checking-subagent、controller-owned vc-proving-preparing、group-worker、机械 merge 和 final-check 组成。正式 C、generated files 与 Rocq formal files 始终以仓库根目录为当前状态；phase 不创建 Git 隔离目录。

外界只调用 `.agents/skills/verification-orchestrator/scripts/controller.py`。agent 不直接执行 controller 内部模块；controller handoff 提供完整的 `symexec`、`coq-check`、`coq-debug` 命令。

# 简化文件原则

- 给 agent 阅读的交接使用 Markdown；JSON 只保存 controller 必须解析的状态、terminal result、plan、manifest 与 merge result。
- 同一事实只记录一次。可由 controller state、固定目录或文件内容推导的信息，不复制进 report/manifest。
- JSON 不保存整份规则、parent transcript、完整 manifest 副本、预填 evidence、命令 argv/cwd/flags 副本或 state snapshot。
- 成功 evidence 只保存 status、版本与必要摘要；失败时保留首个 diagnostic 或 blocker。完整检查可通过同一 controller 命令重跑。
- final-check cleanup 只记录删除数量；失败只记录错误数、残留数以及首个错误或残留路径，不保存整份副产物路径列表。
- `controller_state.json` 是 current authority；agent report 只属于 owner，controller acceptance 写入 state/log，不反写 report。
- `run_logs.json` 是 append-only JSONL，只含事件，不重复整个 state。
- 所有机器读取的 JSON 都含 `schema_version`。Markdown 不使用伪 schema。
- `agent_output.md` / `group_worker_output.md` 用于简短的人类分析与 retry 参考，不是 acceptance evidence；没有固定套话模板。每次 annotation attempt 的 input/report/output 从创建起就位于独立 report directory，不覆盖前次文件；formal before/after 另存 run root history。

# Skill routing

- `verification-orchestrator`：main agent 使用；控制单个 run、唯一 annotation 会话、round、group、merge、stale 与 final-check。
- `annotation-filling`：run 内唯一的 `annotation-subagent` 使用；首次读取相关示例并修改 main root target C annotation 与 `formal_case_lib` spec，后续接收 append feedback 继续修正。
- `annotation-checking`：唯一 annotation owner 的当前 turn 内使用；判断 candidate 是否可交 main-owned check。
- `vc-checking`：`vc-checking-subagent` 使用；只读 current formal files，输出 group plan。
- `group-worker-proving`：group-worker 使用；只证明 assigned witnesses，只改 group copies。
- `final-check`：main agent 使用；accepted merge 写回后检查 freshness、Coq、结构、三级 lib 与 cleanup。

role 执行 controller command 前按需读取 `.agents/skills/verification-orchestrator/docs/path-configuration.md`；详细 proof/annotation 规则由各 skill 链接。

`vc-proving` 不是 phase subagent round。main agent 调用 controller preparing，按 next actions 启动 group-worker，再调用 controller verify。

# 核心术语与三级 lib

- `main root`：用户仓库根目录。
- `run root`：`verification_runs/<run>/`，保存 build、annotation formal history、group copies 与 merge candidate。
- `report root`：`reports/<run>/`，保存 state、event log、timing、每次 annotation attempt 的独立 input/report/output、其他 round handoff 与 result。
- `round`：annotation 会话的一次修改迭代、一次 vc-checking attempt 或 controller-owned vc-proving-preparing attempt。新 annotation round 不代表新 agent。
- `formal_case_lib`：main root `SeparationLogic` 中的正式 `<case>_lib.v`。annotation 维护数学 spec；final-apply 才能用 accepted merge 替换它。
- `group_worker_lib`：group directory 中对 `formal_case_lib` 的 copy。当前 group 可新增带本组 suffix 的 proved helper 与必要 Rocq 官方 import。
- `proving_merged_lib`：controller 按 manifest 机械合并 accepted `group_worker_lib` 得到的 candidate；parent full check 通过后才可写回为 `formal_case_lib`。

三级 lib 是唯一 lib 角色。不得引入第四种 active/scratch/helper lib。

# 固定目录

```text
verification_runs/<run>/
  _coq_builds/
  annotation_history/<attempt-id>/
    before/
    after/
  <case>-vc-proving-rN/
    base_manifest.json
    groups/group_NN__<group-id>/
      <case>_proof_manual.v
      <case>_lib.v                 # group_worker_lib
    proving_merged/
      <case>_proof_manual.v
      <case>_lib.v                 # proving_merged_lib

reports/<run>/
  controller_state.json
  run_logs.json                    # append-only JSONL events
  timing_summary.json
  annotation-attempts/
    annotation-attemptN/           # 同一 annotation agent 的第 N 次迭代
      agent_input.md
      agent_report.json
      agent_output.md
  rounds/<round-id>/
    agent_input.md                 # vc-checking only
    agent_report.json              # vc-checking only
    agent_output.md                # vc-checking only
    group_plan.json
    group_workers_manifest.json
    proving_merged_result.json
    groups/<group>/
      group_worker_input.md
      group_worker_report.json
      group_worker_output.md
```

首轮 `reports/<run>/annotation-attempts/annotation-attempt1/agent_input.md` 是 controller 生成的 annotation 背景与执行 handoff。后续 `annotation-attempts/annotation-attemptN/agent_input.md` 是 controller 提供固定事实与模板、main agent 阅读原始 blocker 后填写的阻塞总结和反思；input在交给agent前封存 digest，report/output在owner returned时封存 digest，后续 feedback/review重验。每次 attempt 的三文件均保留在原目录，不复制或被后续 attempt 覆盖。`verification_runs/<run>/annotation_history/<attempt-id>/` 只保存 formal `before/after`。每个其他 round 只创建适用文件。preparing/verify 不创建 phase agent files。group directory 最终只能有 copied manual 与 `group_worker_lib`；report 和 debug/build 文件分别放 report root 与 `_coq_builds`。

`timing_summary.json` 使用 `qcp-timing-summary/v4`，首要用途是供人类专家分析整体流程。顶层只按 `annotation_attempts` 和 `rounds` 展示；每项明确写出所属 `attempt`/`round`、status、created/finished time、整体 `elapsed_seconds` 与少量 `stages`，不再按 controller command 做全局计数。annotation stages包括整段 annotation work、所有 symexec、`formal_case_lib` Coq check、annotation-checking、controller review/acceptance；vc-checking只把全部 witness 的分析作为一个 `witness-analysis`，不记录单 witness 时间；vc-proving记录 preparing、全部 group-worker 的并行墙钟区间、group Coq/review合计和 parent verify，不展开单 witness。agent交付前后必须执行 controller 的 `mark-attempt-started`/`mark-attempt-returned`；annotation owner还必须按handoff在annotation-checking前后执行`timing-stage` start/finish，禁止估算或事后伪造内部阶段时间。

# 轻量 JSON 合同

## Fixed phase report

`agent_report.json` 使用 `qcp-agent-report/v3`，保持扁平。
未列出的扩展字段会被 controller 拒绝；长分析必须写 Markdown notes。

annotation terminal result 只需；每次迭代写入自己的 `annotation-attempts/annotation-attemptN/agent_report.json`：

```json
{
  "schema_version": "qcp-agent-report/v3",
  "status": "completed",
  "changed_files": [],
  "checks": {
    "symexec": "passed",
    "formal_case_lib": "passed",
    "annotation_checking": "passed"
  },
  "blockers": []
}
```

vc-checking terminal result 只需 status、current `source_goal_version` 与 blockers。详细 witness 自然语言分析写 `agent_output.md`；机器 plan 单独写 `group_plan.json`。

## Group plan

`group_plan.json` 使用 `qcp-vc-checking-group-plan/v3`：

```json
{
  "schema_version": "qcp-vc-checking-group-plan/v3",
  "source_goal_version": "<digest>",
  "groups": [
    {
      "id": "core",
      "witnesses": ["proof_of_x"],
      "depends_on": [],
      "strategy": "short optional hint",
      "helpers": []
    }
  ]
}
```

controller 验证 exact coverage、唯一 assignment、group size、dependency 后添加 `verified: true`。target witness 全集已在 current `source_goal_version`，不在 plan 重复。

## Group report

`group_worker_report.json` 使用 `qcp-group-worker-report/v2`，只含 status、`source_goal_version` 与 blockers。`completed` 表示全部 assigned witnesses 已解决且 exact handoff group-check 已通过；controller review 会自行重跑 group-check，不要求 worker 把整份 Coq evidence 复制进 report。
未列出的字段会被拒绝。

## Manifest 与 merge result

- `base_manifest.json` (`qcp-vc-proving-base-manifest/v2`)：round、version、两个 formal relative paths、seed hashes、witness statement hashes。
- `group_workers_manifest.json` (`qcp-vc-proving-group-workers-manifest/v3`)：version、base manifest、每组 id/copies/report directory/witnesses/dependencies/helper namespace、controller commands 和调度顺序。preparing 把 base/worker manifest digests钉入 controller state，group review与parent verify均重验，worker不得改写 assignment。不得嵌套 plan、规则全文或 tooling argv/evidence 模板。
- `proving_merged_result.json` (`qcp-vc-proving-proving-merged-result/v2`)：`status`、version、candidate paths、compact group/parent-check summary、可追踪的 added declaration metadata、blockers/errors。`status == passed` 才是 accepted merge candidate。

# 路径与工具

agent 不手写 executable、cwd、include/search path、`-slp`、Coq `-R` flags、overlay 或 `_coq_builds` path。

- symbolic execution 唯一外部入口是 handoff 的 `controller.py symexec`。
- Coq 唯一外部入口是 handoff 的 `controller.py coq-check/coq-debug`。
- internal `symexec_tooling.py` / `coq_tooling.py` 只由 controller 调用。
- debug script 只写 handoff 给出的 `_coq_builds/.../.coq_debug/...` path。
- 禁止 raw symexec、raw `coqc`/`coqtop`、`coqc -o`、Dune、Rocq MCP、`_CoqProject` derived command 与 `jq`。

Coq checks以仓库已完成一次全量make为前提，条件信任main root现有的基础库`.vo`。这项信任属于整个验证系统而不是单个run：annotation owner/main check、group worker/review、parent verify、final-check和debug在任意run中都从同一main root full-make产物复用全部Makefile load path下的基础`.vo`，并按各自check需要stage到该run的`_coq_builds`。controller从`SeparationLogic/CONFIGURE`和Makefile的`COQC=$(COQBIN)coqc$(SUF)`约定取得可执行文件；不按基础源码digest、Coq版本或fixed flags另建cache，也不为check重编译基础库。此信任不覆盖current target case：`<case>_lib.v`、`<case>_goal.v`、`<case>_proof_auto.v`、`<case>_proof_manual.v`和`<case>_goal_check.v`对应的旧产物必须排除并在每个适用check中从本轮source/overlay重编译；缺少被依赖的基础`.vo`时check明确失败，不能回退为隐式基础源码编译。

canonical symexec 必须保留：

```text
-IQCP_examples/QCP_demos_LLM/
-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM
```

# 版本、acceptance 与 stale

`source_version` digest 只绑定 relative path、sha256、state 与可选 role，不含 absolute path。`source_goal_version` 绑定 generated file digests、target witnesses 与 witness statement hashes。

annotation acceptance 前，controller 在 main root 重跑 canonical symexec、diagnostics split、clean manual check 与 `formal_case_lib` fixed Coq check，再计算 current versions。vc-checking、preparing、group review 与 parent verify 都重新从 current root 派生 versions，并拒绝与 accepted annotation digest 不同的文件；不能只比较 state 中已保存的字符串。final-check 另以 freshness skeleton、main-path Coq check及 accepted target C digest处理 applied proof/lib 的预期变化；freshness 的 raw manual 必须先在 refresh directory 内执行同样的 diagnostics split，再比较 cleaned witness names/statements。

phase acceptance 要求：owner terminal report；input/current version 匹配；写入边界正确；controller main-owned checks 通过。controller 只在 `controller_state.json` 与 event log 记录 accepted round，不修改 owner report。

group acceptance 要求 terminal report、current version、合法 group files/helper namespace，以及 controller review 重跑 group-check 通过。group acceptance 只允许进入 parent verify；最终 proof acceptance 还要求 passed `proving_merged_result.json`、final-apply 和 final-check。

同一 annotation 会话的新迭代取代 accepted annotation 时，downstream plan/group/merge 全部 stale。旧 annotation attempt report、formal history、downstream report 与 group directory只读复用。

# Main agent 阻塞总结模板

annotation 首轮不使用阻塞模板。后续 `retry-round --phase annotation` 先创建下一次 `reports/<run>/annotation-attempts/annotation-attemptN/agent_input.md`，状态为 `awaiting-main-summary`，不会立即产生 append action。main agent 必须完整阅读其中列出的原始 Markdown/JSON blocker 与 controller-recorded main-check evidence，只替换所有 `MAIN_AGENT` 注释并保留 controller-owned 路径、版本、命令和规则：

```markdown
# Annotation blocker summary and repair handoff

## Main-agent blocker conclusion
<!-- MAIN_AGENT: 说明主失败、被阻塞的 witness/check，以及为何需要回 annotation。 -->

## Evidence and causal analysis
<!-- MAIN_AGENT: 引用决定性证据，从表象追到具体 spec/contract/invariant/assertion/call instantiation 根因。 -->

## Reflection on the previous annotation attempt
<!-- MAIN_AGENT: 反思前次假设或修复为何不足；说明应保留什么、不得重复什么。 -->

## Required annotation repair
<!-- MAIN_AGENT: 给出可执行修复目标、位置、必须保持的约束，以及三个 annotation checks 的成功标准。 -->

## Scope decision
<!-- MAIN_AGENT: 决定局部修复还是整体重构并说明理由；第三次及以后必须显式重新审视整体设计。 -->
```

每个区段都必须有具体内容，不能只复制 blocker JSON、agent 原话或写“重试”。main agent 填完后执行 controller action 指定的 `annotation-summary-ready --attempt <attempt-id>`；controller 验证模板已完成并封存 input digest，之后才给出 `append-annotation-agent`。主总结用于因果判断、反思与修复优先级，不替代原始证据；annotation agent仍须读取两者。

# Agent 调度

每个 run 只能 spawn 一次 `annotation-subagent`。main agent 保存首次 spawn 返回的 target；annotation accepted 或暂时 returned 后不得关闭、替换或再次 spawn。controller 后续给出 `append-annotation-agent` action 时，main agent必须向这个 target追加任务。scripts 不启动 agent。

vc-checking 与 group-worker 必须使用无 parent transcript 的新会话（`fork_context: false`, `fork_turns: none`）；它们只依赖 handoff Markdown、current formal/group files 与 linked skills。annotation 是唯一持续会话，但仍以本次 immutable attempt handoff、feedback 原文件和 main root files 为准。

annotation 首轮必须完整读取 annotation skills、linked rules 与当前算法相关的 correct/incorrect examples。以后每次 append 都必须先重新完整读取 `annotation-filling` 与 `annotation-checking` skills，再读取 main agent 完成的 blocker summary 与其中列出的 Markdown/JSON 原文件。main agent必须先做独立的因果总结与反思，不能只转发原文件；annotation agent也不能只依赖总结。第三次及以后迭代必须提醒 agent从数学 spec、function contract、loop invariant、assertion/call instantiation 的整体关系考虑重构。

每个 agent turn 内完成可恢复分析、修改、retry 与检查。长时间运行、missing optional hint、一次工具失败、bootstrap spec 或未来 proof 难度不是 retry/blocker evidence。

compact error 只记录 compaction 事实。annotation compact retry 仍 append 到唯一会话，不得创建第二个 annotation agent；vc-checking/group-worker 可按 current run 配置重启，耗尽后才记录 `compact-error-retry-exhausted`。

# Phase 合同

## annotation

1. 首轮读 problem context、target C、两个 annotation skills、linked guides 与当前例子相关示例；以后每轮先重新加载两个 skills，并读取 main agent blocker summary 与其列出的 Markdown/JSON blocker 原文件。
2. 设计或重新审视数学 spec，先修改 `formal_case_lib`。
3. 修改 C function spec、invariant、assertion/call instantiation；多轮仍卡住时优先考虑整体重构而非局部补丁。
4. 原样执行 handoff symexec 与 `formal_case_lib` Coq command。
5. 原样执行handoff中的`timing-stage ... start`，在同一个 annotation agent turn 内运行annotation-checking并完成其repair loop，再执行配对的`timing-stage ... finish`；修复后重跑必要检查。

只允许写 target C、`formal_case_lib`、scripted symexec generated files、declared report/notes。generated files 不得手改。不得弱化 spec、加入 `Admitted.`/extra `Axiom` 或 generated import。

## vc-checking

formal files全部只读。以 cleaned manual obligations 为 target source；diagnostics 只作 hint。每个 witness 判断 proofable、needs-helper 或 annotation-bug，并优先形成少量 coherent groups。group-local helper 进入 `group_worker_lib`；必须跨 group 共享的数学事实应回 annotation 提升为 `formal_case_lib` spec。

## vc-proving

preparing copy current manual/`formal_case_lib`。group-worker 只改 assigned proof bodies 与自己的 `group_worker_lib`；新 helper 必须使用本组 suffix，禁止修改 seed declaration、foreign/unsuffixed helper、非官方 import、unassigned witness 或 statement。

controller review 重跑 group-check。parent verify 按 manifest 恢复 solved blocks、按 top-level declaration 合并 `group_worker_lib`，检查 unassigned edits、seed edits、helper namespace、forbidden lemmas，并运行 full fixed goal check。

## final-check

final-apply 只从 accepted `proving_merged` directory复制 manual 与 `proving_merged_lib`，先 backup，失败 rollback。target C/generated files不从 group/merge copy。

final-check 开始时由 controller 删除current target case五个formal modules及current run非`_coq_builds`区域中的旧`.vo/.vos/.vok/.glob/.aux`，只记录删除数量；全量make产生的基础`.vo`必须保留并继续复用。所有检查结束后再次扫描相同target/run边界，新产生或无法删除的target副产物使cleanup失败，失败 evidence只保留数量和首个错误或残留路径。agent不手工清理这些副产物。

freshness symexec 输出到 `reports/<run>/final-check/symexec-refresh/`，不得覆盖 proved manual；raw fresh manual 先在该目录内 diagnostics split，只有 cleaned witness names/statements 与正式 proved manual 比较。final-check 要求 target C digest 仍等于 accepted annotation source、main-path full check 通过；manual 只有 current witness proofs；manual/`formal_case_lib` 无 `Admitted.`、extra `Axiom`、forbidden lemma；`formal_case_lib` digest 等于 accepted `proving_merged_lib`；正式target路径无current-case Coq side products，基础库`.vo`不属于cleanup违规。

final-check 任一项失败时 rollback final-apply。rollback 成功后 controller 回到 `final-candidate-apply`，main agent 必须先执行 `step` 返回的 `final-apply`，不得直接重跑 final-check；rollback 失败时不产生新的 apply/check action，保留 blocker 等待人工处理。

# Formal 边界与完成标准

main root formal state只有 target C、`*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v` 与 `formal_case_lib`。generated files只允许 scripted symexec 刷新。

最终 manual 不得新增 top-level `Definition`、`Fixpoint`、`Inductive`、`Notation`、`Axiom` 或 helper。`formal_case_lib` 只含 annotation-approved mathematical spec 与 merge 后可追踪的 suffixed proved helpers；不得含 `Admitted.`、extra `Axiom` 或 current generated artifact import。

任务完成要求：symbolic execution fresh；所有 target VC 证明完成；fixed goal check 通过；manual/lib 结构合法；三级 lib 一致且 merge 可追踪；只采用 controller accepted candidate；唯一 annotation 会话的所有 `annotation-attempts/annotation-attemptN` reports 与 formal before/after history 完整；final-check 通过并由 controller state/event log 记录 done。
