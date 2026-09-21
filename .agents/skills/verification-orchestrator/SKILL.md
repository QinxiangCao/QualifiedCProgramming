---
name: verification-orchestrator
description: main agent 控制本仓库单个 C 验证 case 时使用；从 init-run 开始，按 controller 当前 action 管理 annotation、VC checking 和 group owner，完成接纳、合并、写回和 final-check，直到 done 或明确 blocker。
---

# 验证编排入口

只由 main 使用。完整阅读以下四份文档，再执行单个 case：

- [总流程](workflows/verification-workflow.md)
- [状态、交接与报告](workflows/state-handoffs-and-reports.md)
- [路径与命令](workflows/paths-and-commands.md)
- [公共 CLI](docs/controller-cli.md)

Windows 上另读 [Windows 运行规则](docs/windows.md)。进入 `final-check` 时读取
[`final-check/SKILL.md`](../final-check/SKILL.md) 及其要求的 workflow。

Main 维护 controller owner 到实际 agent target 的映射，执行返回的结构化 invocation。
Owner action 先 claim，再把 claim response 的 `handoff.prompt` 原样交给对应 agent。
每个 run 只创建一个 annotation agent；修复和后续 annotation attempt 都交回这个 agent。
每个 VC-checking attempt 和每组首次领取使用独立 owner；同任务修复继续原 owner。
`vc-proving` 的准备、调度、合并和 parent check 由 main 执行 controller action，不另设 phase agent。

Owner 写完终态报告并停止修改后，main 执行 `finalize-delivery`。这个命令直接完成对应角色的
全部接纳检查；报告写了 `completed` 本身不代表已接纳。下一步始终由当前任务事实重新派生。
持续推进到 `phase: done`；有运行中的 owner 时等待，出现没有可执行动作的明确 blocker 时报告。

Main 不代替 owner 修改 annotation、plan 或 proof，也不主动读取、摘要或重述 owner 的角色技能。
Owner 根据自己的 handoff 阅读角色知识。此阅读分工用于控制上下文；验收依据是当前文件、报告
和实际检查结果，不把偶然多读文件当作失败。

冻结的用户 spec 需要修改时，owner 先写清修改方案并停止。Main 暂停 run，将方案交用户确认；
取得明确批准后恢复 run，执行当前 annotation round 的 `unfreeze`，交回同一 owner 继续。
未冻结的模型编写 spec 可在当前 annotation attempt 内修正。

用户要求暂停或停止时执行当前 action 的 `cancel-action`；没有准确 action id 时用 `pause-run`。
等待正在运行的工具完成进程清理，再停止推进。只有用户明确要求恢复才调用 `resume-run`，随后
运行 `step`；任务和 owner 保持原样，动作从当前状态重新计算。
