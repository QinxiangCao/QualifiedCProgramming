---
name: annotation-checking
description: 由 annotation-subagent 在 annotation-filling 后检查 annotation round worktree 中的 C annotation 和 case_lib spec declarations，判断是否可交给 main agent 执行 annotation-check-round。
---

# Annotation Checking

本 skill 是 annotation-subagent 的同 round 质量检查步骤。它只判断 candidate 是否值得交给 main agent 执行 `annotation-check-round`；它不写 acceptance。

## 文档

- `docs/spec-quality-checklist.md`：`case_lib`、函数规格、loop invariant、QCP evidence 和 generated VC 语义预检。

## 必查项

- `case_lib` 能由 main worktree 的 `coq_tooling.py check --target-kind case_lib` 加载；`--workspace-root` 必须是当前 annotation round worktree，`--target-file` 指向 Rocq formal `case_lib`。
- `case_lib` 不含 `Admitted.`、extra `Axiom` 或当前 case generated artifact 的 `SimpleC.EE.*` import。
- C annotation 引用的 external Rocq predicates 都在 `case_lib` 中有 mathematical definition。
- spec declaration 描述数学性质，不复刻 C 控制流。
- function spec 和 loop invariant 既足够推出结果语义，也不过强到掩盖 annotation 错误。
- `canonical_symexec_evidence` 来自当前 annotation round worktree，匹配当前 `source_version`，并记录可参数化 QCP driver、cwd、canonical `-I` 和 `-slp`。
- 不能传 canonical 参数的 wrapper 不得写成 formal `passed`；只能在 `qcp_mcp_interactive_evidence` 中写 `skipped`、`failed` 或 `forbidden`。

## 输出

在 `agent_result.annotation.annotation_checking` 中写：

- `status`: `passed` | `failed`
- `case_lib_coqc_status`
- `canonical_symexec_status`
- `qcp_mcp_interactive_status`
- accepted spec declarations
- rejected or suspicious declarations
- `rework_plan[]`
- required rework

## Blocking 原则

annotation-checking 自身不把 spec 质量、annotation 不充分、`case_lib` 声明缺失或 QCP 诊断失败判成 terminal blocker；这些都应输出 `failed` + `rework_plan[]`，交给 annotation-filling 在同一 spawn 内继续修。只有 annotation-checking 所需必要工具完全不可运行且有 command evidence 时，才建议 annotation result 使用 `blocked`。输入版本失效应建议 `stale`，不是 `blocked`。context compaction 只写 `compact-error` 事实；是否重试或最终 block 由 controller / main agent 判定。
