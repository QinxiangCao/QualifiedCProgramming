---
name: final-check
description: main agent 在 final-apply 发布当前 proving_merged 后使用；检查当前 C 对应的义务、完整 Rocq 证明、manual/lib 边界与副产物清理，失败时安全恢复。
---

# 最终检查

只由 main agent 在 controller 完成 `final-apply` 后调用，不创建 subagent。使用当前 action 的完整 argv/cwd；action 根据当前任务状态派生，不沿用旧报告中的命令。

完整读取[执行流程](workflows/final-check.md)，并遵循 orchestrator 的[路径与命令](../verification-orchestrator/workflows/paths-and-commands.md)及[公共接口](../verification-orchestrator/docs/controller-cli.md)。不要改 proof、手动清理目录或自行调用 raw Coq/Dune/Make。

`final-check` 检查当前源码的形式义务、全部 proof routes、case library、安全约束与清理结果。全部通过后 controller 才把 run 置为 `done`。失败并安全回滚后，先执行 controller 给出的 `final-apply`，再做下一次终检；发布冲突保留现状并交回用户处理。
