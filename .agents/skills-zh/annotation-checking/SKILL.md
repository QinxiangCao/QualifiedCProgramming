---
name: annotation-checking
description: 由 annotation-subagent 检查 main root 当前 C annotation 与 formal_case_lib specs，判断是否值得交给 main agent 执行 annotation-check-round。
---

# Annotation Checking

annotation owner必须在进入本skill前执行当前handoff的`timing-stage ... start`，把本轮完整review、feedback repair与recheck纳入同一interval；只有本skill结论稳定后才执行配对的`timing-stage ... finish`。本skill不自行估算耗时，也不把耗时写入agent report。

本 skill 在 run 内唯一 annotation agent 的当前 turn 中使用，不启动额外 agent。每次 main agent append 新 blocker summary handoff 后，annotation owner 必须先重新完整读取本 skill 与 annotation-filling skill，再读取主总结及其列出的原始 Markdown/JSON evidence，然后开始修正和检查。

## 文档

- `docs/spec-quality-checklist.md`：`formal_case_lib`、function spec、invariant、scripted QCP/Coq evidence 与 generated VC 预检。
- `../verification-orchestrator/docs/path-configuration.md`：path assembly 规则。

## 必查

- `formal_case_lib` 定义业务数学语义，C annotation 引用的 external predicates 均有声明。
- `formal_case_lib` 不含 `Admitted.`、extra `Axiom`、current generated artifact import。
- exact handoff `controller.py coq-check --target-kind formal-case-lib` passed。
- function spec 描述计算结果，不仅 bounds/shape。
- loop invariant 覆盖 initialization/preservation/exit，连接 processed state 与 postcondition。
- exact handoff `controller.py symexec` passed；canonical include/SLP由 controller code固定。
- generated files只由 scripted symexec 刷新。
- changed files 不超出 handoff allowed paths。

## 输出

把最终判断写入 annotation report 的 `checks.annotation_checking`。需要返工时在 `agent_output.md` 简述 findings、repair target与 residual risk；不要在 JSON 嵌套 evidence或 rework template。

`passed` 只表示 candidate 可交 controller main-owned check，不表示 accepted。可修 spec/QCP/`formal_case_lib` 问题返回 `failed + rework_plan`，让 filling 在同一 agent turn 修复；必要工具完全不可用才建议 blocked。版本失效建议 stale；compaction 只记 compact-error fact，不请求创建第二个 annotation agent。
