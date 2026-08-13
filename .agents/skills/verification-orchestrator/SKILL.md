---
name: verification-orchestrator
description: main agent 控制本仓库单个 C 验证 case 的完整 run 时使用；从 init-run 起依照 controller action 管理唯一 annotation agent、需要时的 vc-checking 与全部 group-worker、统一 annotation 缺口反馈、机械合并、final-apply 和 final-check，直到 done 或明确 blocker。
---

# 验证编排

只由 main agent 使用。以 `controller_state.json` 和 controller 返回的 action 为准，不直接调用内部
模块，不自行实现状态转移，也不代替 owner 修改其文件。

main 负责原样执行 action 自带的 invocation，维护 controller owner 到 agent target 的映射，并把
claim response 的固定 `handoff.prompt` 原样发送给对应 agent。每个 run 只 spawn 一次 annotation
agent，后续修正 append 到同一 target；vc-checking 和每组首次 group-worker 使用独立会话。

main 的主动阅读边界只有：

- 本 skill 及下列全部 workflow/docs；
- controller action 明确给出的当前 blocker、state 摘要和交接文件；
- controller 进入 `final-check` 时，[`final-check/SKILL.md`](../final-check/SKILL.md) 及其 workflow；
- Windows 上另读仓库根 [`AGENTS_WIN.md`](../../../AGENTS_WIN.md) 和它指向的
  [Windows 适配说明](docs/windows.md)。

main 不读取、摘要或重新解释 `annotation-filling`、`annotation-checking`、`vc-checking`、
`group-worker-proving` 等 owner skill。每个 owner 只根据原样 claim message 读取自己的 skill 和本次
交接文件；main 只编排，不代替 owner 学习角色知识。`vc-proving` 不是 phase subagent，group 的准备、
汇总、merge 与 parent verify 都由 controller 驱动。

没有 manual VC 时跳过 vc-checking 和 group-worker，但仍执行 controller 选择的 dependency
preparation（公共 action 名保留为 `dune-build`）、parent check、写回和终检。有 group 时，即使已有
group 报告 annotation 缺口，也继续派发本轮所有 group；全部 group
到终态后才统一进入一次 annotation retry，本轮不 merge、不 verify。

## 需要阅读

- [总流程](workflows/verification-workflow.md)
- [状态与交接](workflows/state-handoffs-and-reports.md)
- [路径与命令](workflows/paths-and-commands.md)
- [Controller 公共接口](docs/controller-cli.md)

`SKILL.md` 只做入口和阅读路由；状态转移与写入边界放在 `workflows/`，公共接口和稳定知识放在
`docs/`。本仓库不跟踪 skill 回归测试，不得在 `.agents/skills/**/scripts/test/` 或语言镜像中加入
测试脚本。
