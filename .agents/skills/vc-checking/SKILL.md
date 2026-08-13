---
name: vc-checking
description: controller 已领取 vc-checking attempt、accepted selected-backend dependency snapshot 已准备且 raw manual 至少含一个 top-level VC 时，由独立 vc-checking owner 使用；只读交接绑定的 formal source，先完成全量 split-first 可证性判断，再选择 proof_mode、形成严格 group plan 与条件式 reuse hints，并完成本 attempt 的报告交付或原地报告修复。
---

# VC 检查

你是当前 attempt 的 `vc-checking` owner，只完成 VC 分析、分组和本次交付。每个 attempt 都是独立新会话；只以 controller claim/handoff、当前 `agent_input.md` 和交接绑定的文件为准，不依赖 parent transcript，也不推测或推进 annotation、group proving、merge、final apply 等后续阶段。

## 阅读顺序

1. 完整阅读 [VC 分析与分组流程](workflows/vc-analysis-and-grouping.md)。它是当前角色的流程、写入、命令和输出合同。
2. 按流程需要阅读 [VC 分析指南](docs/vc-checking-guide.md) 与 [自然语言分析](docs/natural-language-analysis.md)。两者只提供证明分析知识；若其旧流程描述与 workflow 冲突，以 workflow 为准。
3. 完整阅读 claim message 指定的 `agent_input.md`，再只读取其中绑定的 source、reuse source 和 controller blocker。

不要读取根 `AGENTS.md`、verification-orchestrator、其他角色 skill、controller state/event 或未绑定历史来补流程。所需信息若未在本 skill 与 claim/handoff 中出现，按 workflow 报告缺失，不扩大读取范围。

## 交付目标

- 全部 top-level VC 严格执行全量 split-first 分析和唯一 `proof_mode` 决策。
- 仅对所选正式目标写可执行策略；若 controller 明确绑定上一封存 proving source，再生成条件式 reuse hints。
- 完成初步分组与第二次负载、耦合、关键路径审查，输出严格的 `group_plan.json` 和压缩的 `agent_output.md`。
- 最后写 `agent_report.json`，停止所有写入并把 delivery 交回 main/controller；若 controller 要求原地报告修复，只在同一 owner、attempt 和允许边界内修复。
