# 仓库定位

这是一个用于验证 C 程序的仓库。Agent 围绕目标 C 文件完成端到端验证：补充 annotation、运行 symbolic execution、证明 Rocq 生成的 manual VC，并完成最终一致性检查。

当前系统采用 controller + main agent + fixed phase subagents + controller-owned vc-proving-preparing container + group-worker + worktree chain + JSON handoff/report files。

# Windows / PowerShell 约定

本文件是 Windows 入口文档。除本节列出的平台差异外，Windows 与 Linux/macOS 使用同一套 `.agents/skills/`、同一个 controller 状态机、同一组 JSON handoff/report files、同一个 `case_lib` contract，以及同一条 worktree / vc-proving-preparing container 链。

- 默认 shell 是 PowerShell；命令示例可用 PowerShell 语法表达。
- 进入 workflow 前，先在仓库根目录执行 `. .\scripts\setup-windows-env.ps1`。该脚本应让 `win-binary\symexec.exe`、`win-binary\StrategyCheck.exe`、`win-binary\lsp.exe`、`win-binary\mcp.exe`、`coqc.exe` 和 `coqtop.exe` 可被后续脚本找到。
- 如需在 PowerShell 下启用 `qcp-mcp`，再执行 `. .\scripts\setup-windows-mcp-env.ps1`。`qcp-mcp` 只用于 C annotation / symbolic execution 交互检查，不用于证明 Rocq manual VC。
- Coq feedback 与 verification 仍只允许通过 `.agents\skills\vc-proving\scripts\coq_tooling.py check` 和 `.agents\skills\vc-proving\scripts\coq_tooling.py debug` 间接执行；不得在 Windows 文档中恢复手写 `coqc.exe` flags、Dune、Rocq MCP 或 `_CoqProject` derived command。
- Python 命令可写为 `python` 或 `py -3`；JSON 操作使用 Python、controller helper 或 shell builtin，不依赖 `jq`。
- 路径可以使用 `/` 或 `\`。PowerShell 中含空格路径必须加单引号，并用调用运算符 `&` 执行。
- Windows 只保留执行环境差异；不得恢复旧 lib/scratch 术语、legacy scratch flow、旧 worker runner、旧独立证明 round 流程或下划线形式的旧 forbidden lemma 路径。

# Skill Routing

- `verification-orchestrator`
  固定由主agent使用，定义单个 run 的 controller 状态机、round worktree chain、JSON handoff files、`case_lib` contract、group-worker 调度和 stale 传播规则。
- `annotation-filling`
  固定由 `annotation-subagent` 使用，在 annotation round worktree 中补充或修正 C annotation，并维护同一正式相对路径下的 `case_lib` spec declarations。
- `annotation-checking`
  固定由 `annotation-subagent` 在每轮 filling 后调用，检查 candidate annotation 和 `case_lib` 是否值得交给 main agent 执行 `annotation-check-round`。
- `vc-checking`
  固定由 `vc-checking-subagent` 使用，判断 generated manual VC 是否语义可证，并输出绑定当前 `source_goal_version` 的 proof group plan。
- `group-worker-proving`
  固定由 group-worker 使用，只证明 assigned witness blocks，并只在 group-local `case_lib` 中新增带当前 `group_id` suffix 的 proved helper declarations。
- `final-check`
  只由 main agent 使用，执行 final-candidate-apply 后的 symbolic execution freshness、fixed `coqc_check`、manual proof structure review、`case_lib` contract review 和 cleanup。

`vc-proving` 不是 subagent skill，也不再是独立 agent round；controller/main agent 执行 `vc-proving-preparing` main-owned step，复用 `.agents/skills/vc-proving/scripts/` 下保留的脚本准备 manifest、group worktrees 和 group-worker handoff。`vc-proving-preparing` 和 parent merge/verify 不生成 `agent_input.json`、`agent_report.json` 或 `agent_output.txt`，不创建 Git worktree。

# 核心术语

只使用以下术语描述文件系统、报告和证明流：

- `run`：一次针对单个验证 case 的端到端验证执行，覆盖 annotation、symbolic execution、VC 检查、证明、合并和 final-check。
- `controller`：单点状态机和 report 状态写入口，负责推进 controller step、维护 run 状态、写入接受结果并判定 stale / retry / blocker。
- `controller step`：controller 串行执行的一个状态推进动作，例如 intake、goal-frozen、annotation-check-round、vc-proving-verify、final-candidate-apply、done。
- `run root`：本次 run 在 main worktree 的 `worktrees/` 下创建的根目录，包含本 run 的 round / group worktree 和 `_coq_builds/`。
- `report root`：本次 run 在 main worktree 的 `reports/` 下创建的根目录，集中保存 run、round 和 group 的 JSON/text handoff 与 report 文件。
- `round`：一个固定 phase 的一次尝试，例如 annotation round 或 vc-checking round；每个 fixed phase round 有自己的 worktree 和 report directory。
- `main worktree`：用户仓库的主工作区；在 `final-candidate-apply` 前不得采用 round 或 group 的 formal file 修改。
- `round worktree`：annotation / vc-checking round 专用的 Git worktree，phase owner 只能在其中按 phase 合同编辑允许的 formal files。
- `vc-proving-preparing container`：controller 在 run root 下创建的普通目录 `worktrees/<run>/<case>-vc-proving-rN/`，不是 Git worktree，只用于容纳 group-worker Git worktrees。
- `group worktree`：某个 group-worker 专用的 Git worktree，从 accepted vc-checking worktree 创建，放在 `vc-proving-preparing container` 下，只允许证明 assigned witness blocks 并新增带当前 group suffix 的 case_lib helper declarations 和必要 Rocq 官方库 import。
- `round report directory`：annotation / vc-checking round 在 report root 下的报告目录，包含 `agent_input.json`、`agent_report.json`、`agent_output.txt`。
- `vc-proving-preparing report directory`：`reports/<run>/rounds/<case>-vc-proving-rN/`，包含 `group_workers_manifest.json`、parent verify 后的 `group_merged_result.json` 和 `groups/` 子目录；不得包含 vc-proving `agent_input.json`、`agent_report.json` 或 `agent_output.txt`。
- `group report directory`：某个 group-worker 在 report root 下的报告目录，包含 `group_worker_input.json`、`group_worker_report.json`、`group_worker_output.txt`。
- `group-worker`：由 main agent 调度的证明 worker，只处理分配给自己的 witnesses，并只在 group worktree 和 group report directory 内产生结果。
- `agent_input.json`：main agent / controller 写给 fixed phase subagent 的机器可读 handoff，声明输入、上下文策略、允许路径、版本和验收要求；不得为 vc-proving-preparing 或 merge 生成。
- `agent_report.json`：fixed phase round 的机器可读报告，由 phase owner 写入 `agent_result`，并由 controller 写入或更新 acceptance status；不得为 vc-proving-preparing 或 merge 生成。
- `agent_output.txt`：round 的非权威复用笔记，只用于 retry/downstream 阅读，不作为机器验收依据。
- `group_workers_manifest.json`：vc-proving-preparing 生成的 group-worker 清单，记录 group 划分、依赖、handoff 路径和 parent verify 所需顺序。
- `group_worker_input.json`：main agent / vc-proving-preparing 写给 group-worker 的机器可读 handoff，声明 assigned witnesses、允许路径、helper suffix、版本和验收要求。
- `group_worker_report.json`：group-worker 的机器可读报告，记录 assigned witnesses 的证明结果、coqc_check evidence、changed files 和 blocker。
- `group_worker_output.txt`：group-worker 的非权威复用笔记，只用于 retry/downstream 阅读，不作为机器验收依据。
- `run_logs.json`：run 级 append-only JSONL，包含 controller event 和最新 state snapshot；新 run 不写 legacy `run_status.json` / `run_events.json`。
- `agent_result`：`agent_report.json` 中由对应 fixed phase owner 写入的 round 结果对象，包含 status、evidence、changed files、blockers 等验收输入。
- `group_merged_result`：controller 在 `vc-proving-verify` 后写入 `group_merged_result.json` 的 parent verify 合并结果，表示 accepted group reports 已按 manifest 合并并通过父级检查。
- `source_version`：main agent 为当前 formal source files 记录的版本标识，至少绑定目标 `.c` 和 annotation-approved `case_lib` seed 内容。
- `source_goal_version`：controller 在 accepted annotation round 完成 canonical symbolic execution 和 diagnostics split 后记录的目标版本，至少绑定 generated files、target witnesses 和 witness statements。
- `case_lib`：唯一 active Rocq lib，保存 annotation-approved mathematical spec declarations 和 vc-proving 合并后的 proved helper declarations。
- `<case>_proof_diagnostics.v`：由 deterministic diagnostics splitter 生成的诊断文件，用于 vc-checking planning hint，不作为 target witness 来源。
- `diagnostics_snapshot.json`：diagnostics split 的结构化快照，记录 split 结果和诊断信息，用于检查与 planning hint。
- `timing_summary.json`：run 级 timing 汇总文件，记录各 controller step、round 或 group 的耗时信息。
- `final-check`：main agent 在 final-candidate-apply 后执行的最终一致性检查，覆盖 symbolic execution freshness、fixed `coqc_check`、manual proof structure、`case_lib` contract 和 cleanup。

`case_lib` 是唯一 active Rocq lib。annotation 在 annotation round worktree 中维护 seed spec declarations；group-worker 在各自 group worktree 的正式相对路径新增 suffixed proved helpers / allowed Rocq imports；parent verify 合并后形成最终 `case_lib`。不存在额外 active lib。

# 版本与接受规则

`source_version` 由 main agent 为当前 formal source files 记录，至少绑定目标 `.c` 和 annotation-approved `case_lib` seed 内容。若使用 deterministic file digest，hash input 只允许包含 `relative_path`、`sha256`、`state` 和可选 `role`；absolute path 只能作为 metadata。

`source_goal_version` 由 controller 在 accepted annotation round worktree 内完成 canonical symbolic execution 和 diagnostics split 后记录，至少绑定 generated files、target witnesses 和 witness statements。`vc-checking`、`vc-proving-preparing`、parent verify 和 group-worker report 都必须与当前 `source_goal_version` 一致。group-worker 的 `coqc_check` evidence 必须直接记录当前 `source_goal_version`。

`accepted` 只能通过 controller command 写入。annotation / vc-checking round 只有同时满足以下条件才算 accepted：

- `agent_result` 已由对应 fixed phase owner 写入，且不是 `pending`、`stale` 或 compact error。
- 当前 `source_version` / `source_goal_version` 与 handoff 一致，若该字段适用。
- worktree diff 只包含该 phase 允许修改的 formal files。
- required QCP / `coqc_check` evidence 和 phase main-owned check 通过。
- `case_lib` contract 通过。
- `agent_report.json.status == "accepted"` 已由 controller 写入，且 `run_logs.json` 最新 state snapshot 的 `accepted_rounds` 已记录该 round worktree。

`vc-proving-preparing` 不是 agent round；它只在 `vc-proving-verify` 成功、`group_merged_result.json.merge_vc_ready == "yes"`、parent full fixed `coqc_check` 通过且 final candidate 已记录后由 controller 写入 `accepted_rounds.vc-proving-preparing`。

accepted group report 只表示该 group-worker 的 assigned witnesses 可交给 parent verify；最终 proof acceptance 只来自 controller `vc-proving-verify` 写入的 `group_merged_result.json`，以及后续 `final-candidate-apply` 和 `final-check`。

如果上游 accepted round worktree 被替换，所有 downstream round/group report 立即 stale。被替换的目录只能作为只读参考，不得再作为当前 conclusion 或 dependency evidence。

# Agent 角色

controller 是单点状态机和 report 状态写入口，负责 `run_logs.json`、main-owned `agent_report.json.status`、group acceptance、vc-proving-preparing state 和 retry transition。main agent 调用 controller、启动 subagent / group-worker、执行 controller-owned preparing / verify step，并保留最终采用决策。

fixed phase subagent 只有两个：

- `annotation-subagent`
- `vc-checking-subagent`

main agent 在进入 `annotation`、`vc-checking` 前必须通过 controller 获取 spawn instruction，再启动对应 subagent。`vc-proving-preparing` 由 controller 生成 `vc-proving-preparing` main-owned action，main agent 调用对应 controller command 完成 manifest / group handoff 准备。兼容命令 `vc-proving-setup` 只作为旧入口别名；新流程和文档使用 `vc-proving-preparing`。`intake`、`goal-frozen`、`final-check`、`done` 由 main agent 调用 controller 串行推进。

main agent 启动 subagent 或 group-worker 后，默认必须主动等待其完成并写出对应 report；等待期间可以保持静默。除非 subagent / group-worker 已返回 compact error、stale、blocked、explicit error、用户明确取消，或 controller 依据已落盘 evidence 判定 attempt 已失效，否则 main agent 不得主动打断、关闭或替换仍在工作的 subagent / group-worker。controller 只根据已落盘 report、run log 记录和明确错误状态推进 retry / stale / blocker；不得把“运行时间较长”本身当作打断依据。

系统目标是尽量减少 spawn 次数。fixed phase subagent 和 group-worker 在一个 attempt 内必须主动完成可恢复问题的分析、修复、重试和验证；不得因为缺少可推断的题目语义、缺少 bootstrap 文件、工具一次失败、未来证明难度不确定或需要补 helper 就提前返回 blocked 请求外层确认。controller 只在 owner 返回后做版本、边界、QCP / `coqc_check`、`case_lib` 和 parent verify 的最终验收。

subagent 只在自己的 round worktree 中编辑 formal files，并只在对应 round report directory 的 `agent_result` 中写结果。group-worker 只在自己的 group worktree 中编辑 formal files，并只在对应 group report directory 写结果。`vc-proving-preparing` 和 merge/verify 不得生成 fixed phase agent files；失败时 controller command 直接非零返回给 main agent 裁决，不写 vc-proving blocker。main worktree 只在 `final-candidate-apply` 前保持不变；`final-candidate-apply` 是唯一把最终 candidate 写回 main worktree 的步骤，失败时必须回滚。

fixed phase subagents 必须由 main agent 新开独立 subagent 会话并交付 round handoff；controller 和脚本不得启动 `annotation-subagent`、`vc-checking-subagent` 或 group-worker。

fixed phase subagent attempt 的聊天消息必须由 controller `spawn-instructions` 生成，内容包含 `Read <agent_input.json>`、最终目的为完成 input JSON 指派的 workflow task、`agent_report.json` 只是记录结果的最终报告文件、读取 handoff/rules source、single-spawn 内部修复策略、只按声明 worktree 和 allowed paths 工作、不得使用父聊天作为 evidence、不得为完成任务妥协流程、完成条件、controller-only acceptance、previous attempt / output note 复用优先级，以及按各 phase skill 原则区分 `blocked` / `stale` / `compact-error`：输入版本失效只写 `stale`，context compaction 只写 `compact-error` 事实，是否重试或最终 block 由 controller / main agent 判定。详细规则仍以 `agent_input.json`、`handoff.rules_source` 和 round worktree 为 source of truth。

group-worker 由 main agent 直接调度。脚本只准备 group worktree、写 group report directory 中的 handoff files、检查 report 和执行 parent verify；脚本层不提供启动 subagent/group-worker 的入口。默认最多同时运行 4 个 dependency-ready group-workers；该调度上限由 controller 写入 vc-proving-preparing attempt state，不由 group worktree preparation script 生成，也不写入任何 vc-proving `agent_input.json`。

group-worker attempt 的聊天消息必须由 vc-proving handoff helper 生成，内容包含 `Read <group_worker_input.json>`、最终目的为完成 `group_worker_input.json` 指派的 group-worker task、`group_worker_report.json` 只是记录结果的最终报告文件、读取 detailed rule docs、single-spawn 内部 proof retry 策略、只按声明 group worktree / assigned witnesses / suffixed helpers 工作、不得使用父聊天作为 evidence、不得为完成任务妥协流程、完成条件、controller/parent verification-only acceptance、复用优先级，以及按 group-worker skill 原则区分 `blocked` / `stale` / `compact-error`：输入版本失效只写 `stale`，context compaction 只写 `compact-error` 事实，assigned witness 完全不可证或必需工具重大错误才写 `blocked`。详细规则只在 `group_worker_input.json`、`group_workers_manifest.json` 和 `handoff.rendered_instructions_compact` 中读取。

如果 subagent 或 group-worker 遇到 compact error，owner 只报告 `compact-error` 事实和可复用 evidence pointer，不把它写成自身 `blocked` 判断。main agent / controller 必须主动新开一轮同名 agent/worker，并把 previous attempt 的 round/group directory 作为只读参考目录交给新一轮继续任务。默认最多允许 3 次 compact attempt；超过后由 controller / main agent 写入 `compact-error-retry-exhausted` blocker。

# Worktree Lineage

每个 fixed phase 和 group-worker 按以下目录 / Git worktree 链推进：

1. `annotation` round worktree 从 `main worktree` snapshot 创建。
2. `vc-checking` round worktree 从已接受的 `annotation` round worktree 创建。
3. `vc-proving-preparing` 在 run root 下创建普通 container 目录 `worktrees/<run>/<case>-vc-proving-rN/`；该目录不是 Git worktree。
4. `group worktree` 从已接受的 `vc-checking` round worktree 创建，并放在 `worktrees/<run>/<case>-vc-proving-rN/group_XX__<group_id>/` 下。
5. `vc-proving-verify` 写 `group_merged_result.json` 并记录 final candidate。
6. `main worktree` 只在 `final-candidate-apply` 前从 controller accepted final candidate 采用正式文件。

每个 run 必须在 main worktree 根目录的 `worktrees/` 下创建独立 run root，目录名必须包含当前 case 名和时间戳，例如 `worktrees/<case>-YYYYMMDDHHMMSS/`。该 run root 下固定包含 `_coq_builds/`。本 run 的 annotation / vc-checking round worktrees 和 group worktrees 放在 run root 下；group worktree 必须位于对应 `vc-proving-preparing container` 下，不得直接落到 run root 或 main worktree 的 `worktrees/` 顶层。本 run 的 report root 固定为 main worktree 根目录下的 `reports/<case>-YYYYMMDDHHMMSS/`，所有 JSON/text handoff 和 report 文件放在该 report root 下。

# Report Layout

Run level files:

- `<main-worktree-root>/reports/<case>-YYYYMMDDHHMMSS/run_logs.json`
- `<main-worktree-root>/reports/<case>-YYYYMMDDHHMMSS/timing_summary.json`

Annotation / vc-checking round level files:

- `agent_input.json`
- `agent_report.json`
- `agent_output.txt`

vc-proving-preparing report directory:

- `group_workers_manifest.json`
- `group_merged_result.json`，仅 parent verify 后产生
- `groups/`，包含各 group-worker report directory

Group-worker level files:

- `group_worker_input.json`
- `group_worker_report.json`
- `group_worker_output.txt`

所有 JSON input/report 必须包含 `schema_version`。`agent_output.txt` 和 `group_worker_output.txt` 是 `non-authoritative reuse note`，第一行必须是 `# Reuse Note`，正文必须声明 `Note kind: non-authoritative reuse note` 和 `This file is not acceptance evidence.`；它们只给 retry/downstream agent 复用方法、失败路径和 evidence pointer，不参与 acceptance、blocker、stale、group acceptance、final-check、`source_version` 或 `source_goal_version`。`run_logs.json` 使用 append-only JSONL，每条记录是 controller event 或 state snapshot。legacy `run_status.json` / `run_events.json` 只作为只读兼容输入，不是新 run 输出。

# Phase 合同

## annotation

- `annotation-subagent` 在 annotation round worktree 中编辑目标 `.c` 和同一正式相对路径下的 `case_lib`。
- 如果当前 case 没有 `case_lib`，controller 在 annotation round worktree 中创建最小 seed；annotation-subagent 必须在同一次 spawn 内根据 `problem_context` 和 C 代码 bootstrap 数学 spec declarations。缺少现成 `case_lib` 或题目字段为空不是 terminal blocker。
- `agent_result.annotation.file_access_summary` 应是 object，包含 `must_log_file_reads`、`read_categories`、`searches` 和 `denied_globs_touched`。schema 小错误不应导致停工；命中 `QCP_demos_human` 或 handoff 明确 denied 的参考输入才是 blocker。
- annotation-subagent 必须记录 `canonical_symexec_evidence`、`qcp_mcp_interactive_evidence`、`case_lib_coqc_evidence`、`annotation_checking_evidence`、changed files、`source_version`、iteration/failure/repair fields、self-repair budget 和 blockers。
- 第一轮 annotation 的生产顺序是：读 `problem_context` -> 推断/设计 spec -> 编辑 `case_lib` -> 编辑 C annotation -> QCP / `case_lib` check -> annotation-checking；这些循环应在单次 spawn 内完成到 ready candidate、stale/compact-error，或必要工具重大错误。
- controller `annotation-check-round` 顺序固定为：review annotation report；运行 canonical symbolic execution；对 refreshed `<case>_proof_manual.v` 执行 deterministic diagnostics splitter；写 `<case>_proof_diagnostics.v` 和 `diagnostics_snapshot.json`；确认 manual 不含 `_split_goal_` 或 `Proof. Abort.`；计算 `source_goal_version`；写 accepted annotation round。
- split goals 是 diagnostics，不是 target witness；它们可作为 vc-checking planning hint，但不得进入 `source_goal_version.target_witnesses`。

## vc-checking

- `vc-checking-subagent` 是 read-only semantic planning agent，输入只来自 `agent_input.json` 和 round worktree。
- `agent_input.json.spawn.fork_context == false`，`fork_turns == "none"`，`parent_context_allowed == false`。
- `agent_input.json.context_policy.source_of_truth == "agent_input_json_and_round_worktree"`，`main_agent_transcript_allowed == "no"`。
- `group_plan.target_witnesses` 必须与 cleaned `<case>_proof_manual.v` 中 manual obligations 完全一致。diagnostics 文件和 snapshot 只能作为 planning hint。
- vc-checking 应使用自然语言证明分析辅助判断 proofability 和分组；该分析不是 controller acceptance gate，controller 不因 `natural_language_analysis` 字段缺失而拒绝 group plan。基本流程仍由 `group_plan.proof_groups`、版本绑定、target witness 覆盖和依赖合法性驱动。
- vc-checking 应优先减少 group 数量：同一函数、同一 proof pattern 或可由一个 worker 连续处理的 witnesses 默认放入同一 group；只有真实依赖顺序、明显不同 proof strategy 或上下文过大时才拆分，并写明原因。

## vc-proving

- `vc-proving-preparing` 由 controller/main-owned step 初始化 `group_workers_manifest.json`、准备普通 container 目录、准备 group worktrees、写每个 group 的 `group_worker_*` handoff files；该 step 不证明 witness，不创建 vc-proving Git worktree，不写 vc-proving `agent_input.json` / `agent_report.json` / `agent_output.txt`。
- `reports/<run>/rounds/<case>-vc-proving-rN/` 只放 `group_workers_manifest.json`、`group_merged_result.json` 和 `groups/`；`worktrees/<run>/<case>-vc-proving-rN/` 只作为 group worktree container。
- group-worker 使用 `group-worker-proving`，只编辑 assigned witness proof bodies，并只在 group-local `case_lib` 新增 proved helper declarations 和必要 Rocq 官方库 import。
- group-worker 必须在单次 spawn 内尽量证明本 group 的所有 assigned witnesses；失败 tactic、缺少 optional hint 或需要当前 group suffixed helper 时，应在同一 spawn 内调试、补 helper、重跑 group-check，不应立即返回 blocked。
- 每个 group handoff 必须包含：

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

suffix 从 `group_id` 生成，只允许字母、数字和下划线；非法字符替换为 `_`；sanitized 为空则拒绝该 group。

- group-worker 新增 helper declaration 名称必须以当前 suffix 结尾；不得新增 unsuffixed helper，不得使用 foreign suffix，不得修改 seed `case_lib` declaration；新增 import 只能是必要 Rocq 官方库 import。
- group-worker 的 `coqc_check` 必须使用 `--target-kind group-check`，目标为 build-workspace-only `.coq_group_checks/<case>_group_<gid>_check.v`；evidence 必须记录当前 `source_goal_version`。
- controller `vc-proving-verify` 是 parent verify 的单一入口：在所有 target groups accepted completed 后调用 `verify_group_results.py`，按 manifest 顺序恢复 solved assigned witness proof blocks，按 top-level declaration block 合并带 suffix 的 helper declarations 和允许的 Rocq imports，运行 parent full `coqc_check`，并写 `group_merged_result.json`。
- parent verify 不创建人工审查分支，不自动重命名 helper。同名 helper、unsuffixed helper、foreign suffix、seed declaration 修改、forbidden declaration 都直接 reject 并 rollback。parent verify 或 `vc-proving-preparing` 失败时，controller command 直接向 main agent 返回错误，由用户裁决；不要写成 vc-proving blocker。

若多个 group 需要同一个数学事实，允许各自添加同构但带各自 suffix 的 helper。若确实需要共享 helper，必须回到 annotation，将该事实提升为 annotation-approved seed `case_lib` declaration。

## final-check

- main agent 执行 `final-candidate-apply`，把最终 `.c`、generated files、`*_proof_manual.v` 和 `case_lib` 从 controller accepted final candidate 复制到 main worktree。
- apply 后运行 canonical fixed `coqc_check` 和 `final-check`。final-check 的 symbolic execution freshness 检查必须输出到 report root 下的 temp directory，再与 main worktree generated files 和 witness statements 比对；不得直接覆盖已证明的 `*_proof_manual.v` 来刷新 skeleton。
- cleanup 可以清理本 run 创建的 round/group worktree、临时产物、Coq 编译副产物和 Python/test 临时目录；不得删除正式交付文件。

# Formal 文件边界

main state files:

- 目标 `.c`
- `*_goal.v`
- `*_proof_auto.v`
- `*_proof_manual.v`
- `*_goal_check.v`
- `case_lib`

生成文件只允许 symbolic execution 刷新，不允许手工修改。

最终 `*_proof_manual.v` 只允许包含当前 case 的 manual witness theorem proofs；不得新增顶层 `Definition`、`Fixpoint`、`Inductive`、`Notation`、`Axiom` 或 helper lemmas，不得遗留 `Admitted.`。

`case_lib` 允许包含 annotation-approved mathematical spec declarations 和 vc-proving 合并后的 proved helper declarations。`case_lib` 不得包含 `Admitted.`、extra `Axiom`、当前 case generated artifact 的 `SimpleC.EE.*` import、与 seed declaration 同名但内容不同的新增 declaration。

# 全局约束

- 只参考 `QCP_demos_LLM` 版本的示例，不参考 `QCP_demos_human`。
- `QCP_examples/LLM_bench` 下复用 `QCP_demos_LLM` 公共头文件的 C case 统一使用裸 include。
- symbolic execution 必须使用 `-IQCP_examples/QCP_demos_LLM/`，并保留 `-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM`。
- main agent 和 annotation-subagent 交付或记录 QCP evidence 时，必须记录实际 driver、working directory、`-I` 参数和 `-slp` 参数。不能传递 canonical 参数的 wrapper 必须标记为 `skipped` 或 `forbidden`，不得写成 `passed`。
- `qcp-mcp` 只用于 C annotation / symbolic execution 交互检查，不用于证明 Rocq manual VC。
- main agent、fixed phase subagent 和 group-worker 都不得手写 Coq flags、使用 `coqc -o`、调用 Dune、调用 Rocq MCP 或 `_CoqProject` derived command；`coq_tooling.py` 是唯一 Coq feedback 与 verification 入口。
- Coq 批量检查统一通过 main worktree 的 `coq_tooling.py check` 执行 fixed `coqc` argv；交互/调试反馈统一通过 `coq_tooling.py debug` 执行 fixed `coqtop -batch` argv。
- `jq` 不在当前环境中。JSON 操作说明必须使用 `python3`、controller helper 或 shell builtin。
- 禁止使用仓库规则禁用的黑盒 entailment tactic。
- 如果 manual VC 语义上不可证，应回到 annotation 或规格层修正，不要硬写 Rocq proof。

# 完成标准

任务只有在以下条件同时满足时完成：

1. symbolic execution 已到文件尾，且 generated files 是最新的。
2. 所有 target manual VC 都已完成证明，或已明确退回 annotation 修正。
3. 对应 `*_goal_check.v` 通过 canonical fixed `coqc_check`。
4. `*_proof_manual.v` 和 `case_lib` 没有 `Admitted.` 或 extra `Axiom`。
5. `*_proof_manual.v` 只含 witness proofs，没有 helper lemmas 或 forbidden top-level declarations。
6. `case_lib` 满足 contract，合并记录可追踪到 group-worker report。
7. main worktree 只采用了 controller accepted final candidate。
8. final-check 完成 freshness、forbidden lemma 和 cleanup 检查，并通过 `run_logs.json` 记录结果。
