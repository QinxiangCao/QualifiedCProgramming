# 自然语言证明分析

自然语言分析用于判断 proofability和 group边界，写入 `agent_output.md`；controller不解析其固定 schema，机器 acceptance仍来自 current version、v3 group plan、group checks、parent verify与 final-check。

## 读取顺序

1. `agent_input.md`：version、target witnesses、group bound和输出路径。
2. cleaned `*_proof_manual.v`：obligation source与顺序。
3. goal/auto/check：只读 theorem展开。
4. current `formal_case_lib`。
5. diagnostics/snapshot：只作 planning hint。

优先参考 `SeparationLogic/examples/LLM_bench` 与 `QCP_demos_LLM`；human cases只作非权威思路提示。

## 每个 witness 回答

- `P |-- Q` 是否语义成立？
- pre/post spatial、pure、existential分别是什么？
- 右侧 witness取什么值？
- 哪些资源直接 cancel，哪些 segment/list需要转换？
- arithmetic依赖哪些 bounds、guards、length facts与等式？不要只写“lia”。
- refinement hypothesis/目标 state是什么，需哪些 unfold/choice step？
- helper若需要，其 statement、premises、premise来源和 destination是什么？
- 若失败，缺口位于 C annotation、`formal_case_lib`、stale files还是 malformed VC？

可使用简洁 Markdown 小节，不要为了模拟旧 JSON template填空。内容要具体到能指导 group-worker或 annotation repair。

## Helper

`needs-helper` 必须说明 helper的 statement shape、used witnesses、每个 premise如何从当前 VC discharge，以及 destination为`group_worker_lib` + current group suffix。不能 discharge的 premise意味着 annotation/spec缺口。跨 group共享则回 annotation。

## Group analysis

在 witness分析后列出 proposed groups、共同 proof pattern、dependencies和拆分理由。最终 `group_plan.json` 只保留 group id/witnesses/dependencies与短 hints，不复制长分析。

只要有 `annotation-bug` 或真正 blocked witness，本轮不得输出可进入 proving 的完整 plan；terminal report写相应 status/blocker。`agent_output.md` 同时保留具体 witness分析；之后 main agent读取它与 JSON report，完成下一次 annotation `agent_input.md` 的 blocker总结与反思，并把 summary及原文件路径 append到唯一 annotation会话。
