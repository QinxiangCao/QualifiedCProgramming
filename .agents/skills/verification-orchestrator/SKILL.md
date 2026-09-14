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

若 annotation agent 返回用户 spec 修改方案而未执行 `finalize-delivery`，main 暂停 run，把方案交给用户确认。用户同意后恢复 run，对当前 annotation round 执行 `unfreeze`，再把确认方案交回同一 annotation agent；不创建 attempt 或更换 owner。

用户明确要求停止/暂停时，立即执行当前 action id 对应的 `cancel-action`（没有精确 active action 时用
`pause-run`），等待 controller-owned process group 清理完成后停止推进。paused `step` 只报告状态；不得
自行调用 `resume-run`。只有用户后来明确要求恢复时才 resume，并继续原 suspended action。

main 的主动阅读边界只有：

- 本 skill 及下列全部 workflow/docs；
- controller action 明确给出的当前 blocker、state 摘要和交接文件；
- controller 进入 `final-check` 时，[`final-check/SKILL.md`](../final-check/SKILL.md) 及其 workflow；
- Windows 上另读 [Windows 适配说明](docs/windows.md)。

main 不读取、摘要或重新解释 `annotation-designing`、`vc-checking`、
`group-worker-proving` 等 owner skill。每个 owner 只根据原样 claim message 读取自己的 skill 和本次
交接文件；main 只编排，不代替 owner 学习角色知识。`vc-proving` 不是 phase subagent，group 的准备、
汇总、merge 与 parent verify 都由 controller 驱动。

上述阅读边界用于保持角色清晰和减少上下文，不是 controller 的交付 gate。owner 偶然多读一个文件本身不使 attempt 失败，也不要求重开；controller 只根据实际写入、固定输入、报告、plan、formal bytes 和机器检查推进流程。

没有 manual VC 时跳过 vc-checking 和 group-worker，但仍执行 controller 选择的 dependency
preparation（公共 action 名保留为 `dune-build`）、parent check、写回和终检。有 group 时，首次
proving 正常并行派发全部 group。annotation retry 后先派发 comparison 对应的优先 group；优先
group 再次报告 annotation 缺口时立即回 annotation，不派发剩余 group。statement、proof mode、
case lib、dependency snapshot 或 public helper snapshot 是否变化都不参与跨轮复用判断；有上一 proving
round 时，每个实际领取任务的 group worker 在上一轮各组 manual/lib中搜索当前 witness/helper、只读候选 proof block，并可按需写简短 `proof_reuse.md`。该文件缺失或为空不阻断 finalize；当前 round 的完整 group check 始终验收其自行复用或重写的证明。

## 需要阅读

- [总流程](workflows/verification-workflow.md)
- [状态与交接](workflows/state-handoffs-and-reports.md)
- [路径与命令](workflows/paths-and-commands.md)
- [Controller 公共接口](docs/controller-cli.md)

`SKILL.md` 只做入口和阅读路由；状态转移与写入边界放在 `workflows/`，公共接口和稳定知识放在
`docs/`。本仓库不跟踪 skill 回归测试，不得在 `.agents/skills/**/scripts/test/` 或语言镜像中加入
测试脚本。
