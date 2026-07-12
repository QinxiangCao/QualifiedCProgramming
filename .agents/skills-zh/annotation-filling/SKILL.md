---
name: annotation-filling
description: 由 annotation-subagent 在 annotation round worktree 中填写或修正 C annotation，并在同一正式相对路径的 case_lib 中维护数学 spec declarations；完成后交给 annotation-checking。
---

# Annotation Filling

本 skill 固定由 `annotation-subagent` 使用。annotation-subagent 只在 annotation round worktree 中工作，不写 main worktree；脚本只能提供 deterministic checks 或 file helpers，不能启动 subagent。

## 文档

- `docs/annotation-guide.md`：允许修改范围、spec 设计、annotation 风格、常见错误和同 round 自修。
- `docs/array-string-guide.md`：builtin array / string 谓词和选型。
- `docs/branch-control-annotation.md`：复杂 if/else、多路径 assertion、branch naming、`Destruct`、`Branch join`、`Branch clear` 和 multi-inv case 映射。
- `docs/pure-proposition-predicates.md`：annotation-facing pure proposition predicate 的选择和书写规则。
- `docs/qcp-reference-guide.md`：canonical symbolic execution、QCP evidence、reference policy 和 resource reclaim 错误。
- `docs/correct-examples/binary-search-annotation.md`：二分答案正例解析，并指向 `split_array_largest_sum` 配套 C annotation。
- `docs/incorrect-examples/algorithm-mirror.md`：`max_sub_array` 反例解析，说明 algorithm-mirror spec 为什么应回退。

## 输入

- target `.c`
- 当前 `case_lib`
- `problem_context`，作为题目语义的结构化 source of truth；字段为空时按 C 程序、函数名和 headers 推断 candidate spec。
- `case_lib_seed_evidence`，若 status 为 `created`，本次 spawn 必须尝试 bootstrap 数学 spec declarations。
- handoff 中的 `source_version`
- canonical QCP driver / qcp-mcp config
- 从 vc-checking 或 vc-proving 回流的 blocker context

## 流程

1. 读取 handoff、目标 `.c`、headers、允许的当前 round generated context、正反例提示和 `case_lib`。
2. 先设计 strictly mathematical spec declarations，需要新增时写入同一正式相对路径的 `case_lib`；若发现自己在 Rocq 中复写 C loop，先回到 predicate-first 设计。
3. 填写或修正 C annotation：关键点写完整 assertion，普通单步依赖 symbolic execution；数组、二分答案、DP、字符串和 refinement case 先读取对应 example analysis docs。
4. 使用能传 canonical `-I` / `-slp` 的 QCP driver 检查目标 `.c`；qcp-mcp 只作独立交互检查，不作为不能传参 wrapper 的 formal evidence。
5. 每轮 candidate 后运行 `annotation-checking`。
6. 若 QCP、`case_lib` check 或 `annotation-checking` 未通过，按 `docs/annotation-guide.md` 在同一 spawn 和同一 annotation round worktree 中继续修复，直到 ready、stale、compact-error 或必要工具重大错误；self-repair budget 只作为工作量 evidence，不是自动 blocked 条件。
7. 写 `agent_report.json.agent_result.annotation`，再写 `agent_output.txt` 作为 `non-authoritative reuse note`。

## Blocking 原则

annotation-subagent 的 `blocked` 只用于必要工具发生重大错误：canonical QCP driver、`coq_tooling.py` case_lib check 或 annotation-checking 所需脚本完全不可运行，且已记录具体 command evidence。输入版本失效写 `stale`。若 context compaction 使本 attempt 无法严格继续，只写 `compact-error` 状态和已完成 evidence；是否重试或最终 block 由 controller / main agent 判定。

以下情况不得返回 `blocked`，必须在本次 spawn 内自行解决：无现成 `case_lib`、`problem_context` 字段为空、spec 方向不确定、`case_lib` 暂时不能 coqc、QCP 报 annotation 错、where instantiation 失败、annotation-checking failed、reference hint 缺失或未来 proof 难度不确定。除非必要工具本身不可用，否则最终应产出 ready candidate 或带具体未解证据的非 ready report。

## 输出

`agent_result.annotation` 至少包含：

- `status`: `completed` | `blocked` | `stale` | `compact-error`
- `source_version`
- changed files、candidate `.c` path、candidate `case_lib` path
- `canonical_symexec_evidence`
- `qcp_mcp_interactive_evidence`
- `case_lib_coqc_evidence`
- `annotation_checking_evidence`
- `iteration_log[]`、`failure_diagnosis[]`、`repair_actions[]`
- `self_reworkable_failures[]`
- `self_repair_budget` 和 `self_repair_budget_exhausted`
- `reference_policy_compliance`
- `file_access_summary` object，包含 `must_log_file_reads`、`read_categories`、`searches`、`denied_globs_touched`
- blockers

`agent_output.txt` 第一行必须是 `# Reuse Note`，正文包含 `Note kind: non-authoritative reuse note` 和 `This file is not acceptance evidence.`。它只记录复用说明和 evidence pointer，不声明 controller accepted。

若 `annotation_checking.status = failed` 或 canonical QCP failed 且必要工具仍可运行，必须继续本次 spawn 内自修，不得返回 terminal `blocked`。缺少现成 `case_lib`、缺少父聊天确认、spec 不确定但可从 C 代码推断，都不是 terminal blocker。
