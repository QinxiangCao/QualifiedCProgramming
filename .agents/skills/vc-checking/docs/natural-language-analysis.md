# 自然语言证明分析

自然语言分析写入 `agent_output.md`，用于解释 proofability、proof-mode、策略、helper ownership 和 group 边界。controller 的接纳依据是 `group_plan.json` 与后续证明检查，不解析这些说明文字。

## 读取顺序

1. 当前 `agent_input.md`；
2. 主仓库当前 `*_proof_manual.v`；
3. goal/auto 和当前 `formal_case_lib`；
4. 第二轮及以后 handoff 明确列出的前次 vc-checking 结果。

当前 manual 是权威。需要展开 goal 时，只在交接的调试副本对应 proof body 中加入 `Show.`，运行 handoff 给出的 controller 命令；除 `Show.` 外不要修改任何 proof 或非 proof token，也不要生成额外 manual、debug script 或历史比较文件。

## 分析顺序

先对全部 top-level VC 做 structural scan，并优先检查 no-split whole goals 的 resource address、scalar equality、existential 与 current/`@pre` bridge。简短说明扫描结论；找到 P 可成立而 Q 失败的具体 countermodel 时立即报告 annotation/spec/dependency 缺口，不先消耗全部 split 分析。

structural scan 通过后，完成全部 split goals 的可证/不可证判断，不分析 top-level VC，也不规划 helper。某个 VC 有 split 且全部可证时选择 `aggressive_pre_process`；否则才判断整个 top-level VC，整体可证时选择 `LLM_pre_process`，整体仍不可证才报告 annotation/spec/dependency 缺口。

全部 mode 确定后再写策略：

- aggressive 只分析 split goals；
- LLM 只分析 top-level goal；
- 不做 witness reuse 判断。

第二轮可以参考前次结论，但每个决定都要用当前 manual 复核，并简短说明本轮保留或改变了什么。

## 每个目标回答

- `P |-- Q` 是否成立？
- pre/post spatial、pure、existential 分别是什么？
- 右侧 witness 取什么值？
- 哪些资源直接 cancel，哪些 list/segment 需要转换？
- arithmetic 依赖哪些 bounds、guards、length facts和等式？
- refinement 的 source/target state 是什么？
- helper 的 statement、premises、premise 来源和 destination 是什么？
- 若失败，缺口位于 C annotation、case lib、当前 manual 还是工具环境？

内容应具体到 group worker 或 annotation owner 可以直接继续工作。

## Helper 与 group

本轮新证或实质修改的 helper 才进入 plan，并使用 owner suffix。只供本组时用 `local`；稳定、纯数学且预计未来 round 可用时用 `public`。无法从当前 VC discharge 的 premise 是 annotation/spec 缺口，不能用 helper 掩盖。

策略完成后先按 invariant、proof pattern、resource transformation、refinement transition 和 helper family 初分组，再做负载、耦合与关键路径复查。split goal 不独立分组。通常每组 2 到 6 个 top-level VC；独立 final-result、特殊 route 或独立 helper family 可以单独成组。

最终 plan 只保存 group id、proof mode、aggressive `split_strategies`、LLM `strategy`、`estimated_difficulty` 和 planned helpers。不要加入 controller metadata、acceptance、dependency 或 reuse 字段。

split goal 不可证只触发父 VC 的整体分析。只有整体仍不可证时才交付 `blocked`；`agent_output.md` 必须保留具体失败形状和修正位置。
