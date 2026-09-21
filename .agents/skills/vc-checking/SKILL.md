---
name: vc-checking
description: controller 已领取 vc-checking attempt、当前 backend 的依赖 plan 已准备且主仓库 manual 至少含一个 top-level VC 时，由独立 vc-checking owner 使用；直接检查当前 manual，先完成廉价 top-level structural blocker scan，再对无确定 blocker 的输入完成全量 split-first 可证性判断、proof_mode 决策和严格 group plan，并完成本 attempt 的报告交付或原地报告修复。
---

# VC 检查

你是当前 attempt 的 `vc-checking` owner，只完成 VC 分析、分组和本次交付。每个 attempt 都是独立新会话；只以 controller claim/handoff、当前 `agent_input.md` 和交接绑定的文件为准，不依赖 parent transcript，也不推测或推进 annotation、group proving、merge、final apply 等后续阶段。

## 阅读顺序

1. 完整阅读 [VC 分析与分组流程](workflows/vc-analysis-and-grouping.md)。它是当前角色的流程、写入、命令和输出合同。
2. 按流程需要阅读 [VC 分析指南](docs/vc-checking-guide.md) 与 [自然语言分析](docs/natural-language-analysis.md)。两者只提供证明分析知识；若其旧流程描述与 workflow 冲突，以 workflow 为准。
3. 完整阅读 claim message 指定的 `agent_input.md`，再读取当前主仓库 formal files、列出的前次 vc-checking 结果和 controller blocker。

根 `AGENTS.md`、verification-orchestrator、其他角色 skill、controller state/event 或未列出的历史都不是本角色所需输入，不应用它们替代当前 handoff。偶然多读文件本身不是 blocker；只要没有越界写入或把非当前内容当作 plan 依据，就继续按当前 manual 完成工作。

## 交付目标

- 先扫描全部 top-level VC，并优先检查无 split goal 的 whole goal 是否缺 resource address、scalar equality 或 current/`@pre` bridge；确定 countermodel 可立即返回。
- 读取 annotation 的 VC comparison，但把它当作优先复核线索；在当前 manual 中独立检查新增 premise 的来源和 related VCs。
- structural scan 无确定 blocker 后，全部 top-level VC 严格执行全量 split-first 分析和唯一 `proof_mode` 决策。
- 仅对所选正式目标写可执行策略；不做 witness reuse 分析。
- 自行评估风险并安排 plan 顺序，把依赖新重型数学 lemma 的 current/related VCs 尽量放在一起。Controller 保留包含 comparison `current` 的组为首批，各批次都按 plan 顺序派发，不按难度分数重排。
- 最后写 `agent_report.json`，停止所有写入并把 delivery 交回 main/controller；`finalize-delivery` 完成当前报告与 plan 的全部验收；若要求修复，只在同一 owner、attempt 和允许边界内继续。
