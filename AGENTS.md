# Agent 入口

在本仓库执行单个 C 验证任务时，main agent 必须调用
[`verification-orchestrator`](.agents/skills/verification-orchestrator/SKILL.md)，完整读取该 skill
指定的 workflow/docs，并持续按 controller action 工作，直到 run 为 `done` 或 controller 给出明确 blocker。

不要从本文件推断阶段、命令或 subagent 规则；`final-check` 和 Windows 适配等后续阅读由
`verification-orchestrator` 指引。
