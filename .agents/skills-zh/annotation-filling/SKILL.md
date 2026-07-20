---
name: annotation-filling
description: 由 run 内唯一且持续复用的 annotation-subagent 在 main root 补充或修正 C annotation，并维护 SeparationLogic 中的 formal_case_lib spec declarations；完成后调用 annotation-checking。
---

# Annotation Filling

本 run 只允许一个 annotation-subagent。首次 startup 完整读取 `annotation-attempts/annotation-attempt1/agent_input.md`、本 skill、annotation-checking skill、linked rules和当前算法相关的 correct/incorrect examples；返回后保持同一 agent target 可继续接收 append，不得要求 main agent另开 annotation agent。

每次收到 append，先重新完整读取本 skill 与 annotation-checking skill，再完整读取本次 `annotation-attempts/annotation-attemptN/agent_input.md` 中 main agent的 blocker conclusion、causal analysis、previous-attempt reflection、required repair和scope decision，并读取其中列出的 blocker Markdown 与 JSON 原文件。handoff总结用于定位与确定优先级，原始 evidence 与 main root current files用于核验事实；不要只依赖任何一方或旧会话记忆。

## 文档

- `docs/annotation-guide.md`：spec、invariant、external declaration、repair loop。
- `docs/qcp-reference-guide.md`：QCP syntax、reference policy、scripted symexec evidence。
- `../verification-orchestrator/docs/path-configuration.md`：symexec/Coq path configuration。
- 其他 linked guides：array/string、branch control、pure predicates 与 correct/incorrect examples。

## 允许写入

- main root 目标 `.c` annotation。
- main root `formal_case_lib` 中 annotation-approved mathematical spec declarations。
- handoff `Commands` 中 `controller.py symexec` 刷新的 generated files。
- declared `agent_report.json`/`agent_output.md`。

不得编辑其他正式文件、manual proof bodies 或 group/proving files。generated files 不得手改。

## 生产顺序

1. 读 `problem_context` 与 target C。
2. 推断业务数学语义，设计/补全 `formal_case_lib` specs。
3. 写 C function specs、loop invariants、assertions/call instantiations。
4. 原样执行 handoff `Commands` 中的 symexec command；该命令必须进入 controller，不得直接调用 internal helper 或拼 driver/cwd/include/`-slp`/output paths。
5. 原样执行同一代码块中的 `formal_case_lib` Coq command；该命令必须进入 controller，不得直接调用 internal helper 或拼 Coq flags/build path。
6. 紧接annotation-checking前原样执行handoff的`timing-stage ... start`；调用annotation-checking并根据feedback在同一个agent turn内完成修复/recheck；整体checking结束后原样执行配对的`timing-stage ... finish`。不得用估计值代替这两个边界。

缺失现成 `formal_case_lib`、空 problem context、一次 tool failure、where 不完整或 spec 尚不理想都不是 terminal blocker；controller 已提供 seed/path，owner 应在当前 turn 内 bootstrap/修复。若已进入第三次或更晚的 annotation 迭代，必须从数学 spec、function contracts、loop invariants、assertions/call instantiations 的整体关系重新评估设计，不能只叠加局部补丁。

## 禁止妥协

- 不弱化 postcondition/invariant 只为减少 VC。
- 不把 C algorithm 镜像成数学定义来伪装 functional spec。
- 不加 `Admitted.`、extra `Axiom`、unsound shortcut 或 generated artifact import。
- 不调用 raw symexec/raw Coq/Dune/Rocq MCP。
- qcp-mcp 只用于 C annotation/symexec 交互，不用于 Rocq proof。

## Result

本次 `annotation-attempts/annotation-attemptN/agent_report.json` 使用扁平 `qcp-agent-report/v3`，只记录本次迭代的 terminal status、exact changed files、`symexec`/`formal_case_lib`/`annotation_checking` 三个 check status 与 concrete blockers。失败过程、branch-control 解释和 repair 摘要写同目录 `agent_output.md`，不要把完整 command evidence、规则或迭代日志复制进 JSON；returned后controller封存report/output digest，三文件不会被后续attempt覆盖，formal before/after由controller另存。

`blocked` 只用于必要 scripted tool 完全不可运行，或在充分 local attempts 后确认任务无法在当前输入完成。版本失效写 `stale`；compaction 只写 `compact-error` fact。owner 不写 accepted。
