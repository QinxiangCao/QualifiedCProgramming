# VC Checking

目标是在写 proof 前判断每个 cleaned manual VC 是否语义可证，并形成少量 coherent proof groups。

## 分析

对每个 `P |-- Q`：

1. 分开列出 pre/post spatial resources、pure facts与 existentials。
2. 说明右侧 witness实例来自旧逻辑值、`replace_Znth`、`sublist`、`app`、loop variable或 abstract state。
3. 说明 space cancellation/split/merge、pure premise来源与 refinement transition。
4. 若需要 helper，写 statement shape、所有 premises及每个 premise如何由当前 `P` discharge。
5. `P` 不能推出 `Q` 时回 annotation/spec；不得交 group-worker硬证。

Judgment：

- `proofable`：现有 facts/lemmas足够。
- `needs-helper`：语义成立，group-worker可在`group_worker_lib`证明 current-suffix helper。
- `annotation-bug`：annotation或`formal_case_lib` spec缺失/错误。
- `blocked`：必要文件/解析工具重大错误，或语义缺口不能由 annotation/group-local helper修复。

版本失效写 `stale`；compaction写 `compact-error`。proof route不确定、helper尚未证明或 VC困难不是 blocker。

## 分组

按同一 invariant展开、helper family、array/frame transformation、refinement transition或相近上下文分组。只有真实 dependency、strategy明显不同或 group超过 handoff上限才拆分。每个 target witness恰好一次，dependency graph无环。

必须跨 group共享的数学事实应回 annotation提升为`formal_case_lib` declaration；不要让 group修改正式 lib。

## 输出

- `agent_output.md`：按 manual顺序写自然语言分析。每个 witness至少包含 judgment、P/Q shape、instantiation、space/pure/refinement plan、helper premise或 failure signal。该文件面向人和 retry，不是 controller acceptance evidence。
- `group_plan.json`：只写 machine-minimal v3 plan：

```json
{
  "schema_version": "qcp-vc-checking-group-plan/v3",
  "source_goal_version": "<digest>",
  "groups": [
    {
      "id": "array-frame",
      "witnesses": ["proof_of_x"],
      "depends_on": [],
      "strategy": "split array, instantiate EX, cancel",
      "helpers": ["optional short helper hint"]
    }
  ]
}
```

不要在 plan复制 target witness全集、grouping policy、per-witness长分析或 controller metadata；这些分别存在 current version、handoff、`agent_output.md`和 controller state。

- `agent_report.json`：terminal status、current version、blockers。

若 terminal status 是 `blocked` 或 blocker 属于 `annotation-bug`，main agent会读取本轮 `agent_output.md` 和 `agent_report.json`，在下一次 annotation `agent_input.md` 中按固定模板总结 failure cause、evidence、previous-attempt reflection、required repair与scope decision，再把 summary及两个原文件路径 append到唯一 annotation agent。为此 VC Markdown 必须给出具体 failure shape和 repair location，JSON只保留 compact blocker；vc-checking owner不要替 main agent写总结，也不要建议另开 annotation agent。

## 回 annotation 的信号

- `Q`要求的 ownership/resource不在`P`。
- guard/invariant/local assertion没有必要 pure fact。
- array/list observation或`@pre`桥缺失。
- `safeExec` abstract state对不上。
- helper需要当前`P`无法提供的额外 premise。
- proof需要修改 generated file、witness statement或正式 spec。
