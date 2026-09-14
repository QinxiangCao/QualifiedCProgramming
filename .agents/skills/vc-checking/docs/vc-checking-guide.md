# VC 检查

目标是在写 proof 前先快速扫描全部 top-level VC 的致命结构缺口，再对无确定 blocker 的输入判断全部 split goals 的可证性，仅在必要时判断整个 top-level VC，据此选择`aggressive_pre_process`或`LLM_pre_process`；随后分析对应目标的证明思路并形成少量coherent proof groups。`<vc>_split_goal_*` declarations是raw obligation source的一部分，不做预处理或删除。

## 分析

严格按以下顺序分析：

1. 先扫描所有 top-level VC，no-split whole goals 优先，检查 resource/current-`@pre`/scalar/existential 结构；确定 countermodel 可立即回 annotation/spec。
2. 对 annotation comparison 的 current/related VCs 独立复核新增 premise/resource 的来源；缺来源直接回 annotation，有新重型数学义务则标高风险。
3. structural scan 通过后，遍历所有top-level VC的全部split goals，只记录“可证”或“不可证”，忽略top-level VC，不规划helper或证明路线。
4. 某个top-level VC至少有一个split goal且全部可证时，选择`aggressive_pre_process`，不再分析该top-level VC的可证性。
5. 任一split goal不可证或没有split goal时，只判断整个top-level VC的可证性；整体可证时选择`LLM_pre_process`，整体仍不可证时回annotation/spec。
6. 全部mode确定后，再分析证明思路：aggressive只分析split goals，`LLM_pre_process`只分析整个top-level VC。
7. 所有证明思路完成后才分组；comparison current/related 的高风险 witness 单独组成第一组，其余 split goals 随所属top-level VC进入对应group。

对每个实际分析的split goal或整个top-level VC：

1. 分开列出 pre/post spatial resources、pure facts与 existentials。
2. 说明右侧 witness实例来自旧逻辑值、`replace_Znth`、`sublist`、`app`、loop variable或 abstract state。
3. 说明 space cancellation/split/merge、pure premise来源与 refinement transition。
4. 若需要 helper，写 statement shape、所有 premises及每个 premise如何由当前 `P` discharge。
5. `P` 不能推出 `Q` 时，split goal进入整体top-level分析；整个top-level VC仍失败时回annotation/spec，不得交group-worker硬证。

第一遍 split-goal 判断只有：

- 可证：结论语义成立。
- 不可证：当前 split goal 的前提不能推出结论。

mode确定后的详细分析才区分现有facts/lemmas是否足够、是否需要`group_worker_lib`中的current-suffix helper，以及整个top-level VC失败时属于annotation/spec缺口还是工具阻塞。split goal不可证本身不是blocker。

主仓库文件在分析期间变化时保存证据并交给 controller；compaction写 `compact-error`。proof route不确定、helper尚未证明或 VC困难不是 blocker。

## 分组

证明思路完成后，按同一invariant展开、proof pattern、array/frame transformation、refinement transition、helper family和相近上下文对top-level VC形成初步groups，再做一次负载、耦合与预计关键路径审查。split goal不独立分组；aggressive top-level VC按其全部split-goal思路的整体负担与共享关系分组：

- 同时考虑top-level witness数、aggressive split-goal数、预计helper family数、数学库、proof mode差异、程序阶段和需要持续保留的proof context；`max_witnesses_per_group`只是hard upper bound。
- 通常形成少量、每组约2到6个top-level witnesses的coherent groups。单witness group必须是final result、独立特殊route或独立helper family等合理边界；超过6个witnesses必须在`agent_output.md`说明为何不能合理拆分。
- 同一function内的初始化、核心语义转换、简单控制流投影和最终结果若没有不可分割的helper family，应拆组。对预计tail group，若final-result与transition/safety可独立证明必须拆开；不可拆时在`agent_output.md`说明helper/context耦合，并规划可提前提供的permutation、sum/length、mask-clear等formal/public helper。
- manual seed只决定最终manual witness declaration顺序；accepted plan顺序决定group编号与helper merge顺序。程序阶段、实际负载与helper ownership优先决定group边界。

所有groups在机器调度上独立，plan不含dependency字段。若多个witnesses必须使用同一组紧耦合、证明专用的helper family，应留在同一group，由一个`group_worker_lib`维护current-suffix helpers。structured `helpers`只列本组新证/改写且带owner suffix的helper；public snapshot中已有且不需修改的helper不是新plan item。只供本组时写`visibility: local`；稳定数学性质预计可在后续round使用时写`visibility: public`。controller在该group通过validation后，把public candidate及必要依赖append到run-root pool；本轮所有groups只见preparing时冻结的同一`public_helper_snapshot.txt`。snapshot/pool都不能import、不能成为第四种lib或group dependency。不得读取/import sibling `group_worker_lib`。

类似`sieve_of_euler`的case可在helper ownership允许时使用如下自然语言分组示例；具体witness名称不得硬编码进controller：

- `initialization`：初始化prefix、`replace_Znth` step和初始化循环退出。
- `semantic-transitions`：当前composite/prime分类、prime append和product mark，共享prime/least-factor/flag-state重型helper family。
- `control-and-exits`：inner divide/non-divide、下标归一化、stored exit implication和outer exit等projection、rewriting与算术witnesses。
- `final-result`：从最终outer state推出公开result spec。

只有共享数学事实已经合法进入`formal_case_lib`后，才考虑把`semantic-transitions`继续拆为outer-entry与inner-product groups。

## 输出

- `agent_output.md`：先按 manual顺序记录全部split goals的二元可证性判断，再写mode确定后实际分析目标的P/Q shape、instantiation、space/pure/refinement plan、helper premise或failure signal；同时记录所属top-level VC的mode。第二轮可以引用前次vc-checking结论，但要说明本轮保留或改变了什么。该文件面向人和retry，不是controller acceptance evidence。
- `group_plan.json`：只写最小 plan：

```json
{
  "groups": [
    {
      "id": "array-frame",
      "witnesses": [
        {
          "name": "proof_of_x",
          "proof_mode": "aggressive_pre_process",
          "split_strategies": {
            "proof_of_x_split_goal_1": "instantiate the old list and discharge the length fact",
            "proof_of_x_split_goal_2": "rewrite the update and cancel the unchanged segment"
          }
        }
      ],
      "helpers": [
        {
          "name": "decimal_comparator_transitive__array_frame",
          "strategy": "prove the comparator order is transitive independently of C locals",
          "visibility": "public"
        }
      ],
      "estimated_difficulty": 5
    }
  ]
}
```

每个top-level VC恰好在一个group，其split goals随它进入同一group。顶层只允许`groups`；group object只允许`id`、`witnesses`、`helpers`和`estimated_difficulty`，不得保留acceptance或dependency字段。difficulty必须是1到5的整数，供controller在不改变plan/merge顺序的前提下生成dispatch order。aggressive witness只含`name`、`proof_mode`和`split_strategies`；keys必须与raw manual的names/order完全一致，每个值非空。`LLM_pre_process` witness只含`name`、`proof_mode`和整体`strategy`。`helpers`只列本轮由本组新证或改写的helper；每项严格包含`name`、`strategy`、`visibility`，name全局唯一，visibility只能是`local`或`public`。public candidate在owner validation通过后进入pool。不要复制target witness全集、grouping policy、per-witness长分析或controller metadata。

- `agent_report.json`：成功只含completed status，blocked时增加唯一完整`blocker`，不复制controller checks。

split goal不可证时先分析所属top-level VC，不直接返回blocker。只有整个top-level VC仍不可证，terminal status才写`blocked`。JSON `vcs` 精确列出失败 top-level/split goal 及 annotation location；controller 直接把 sealed manual、report 和 comparison history写入下一次 annotation handoff，不需要 main 重写总结。

## 回 annotation 的信号

- `Q`要求的 ownership/resource不在`P`。
- guard/invariant/local assertion没有必要 pure fact。
- array/list observation或`@pre`桥缺失。
- `safeExec` abstract state对不上。
- helper需要当前`P`无法提供的额外 premise。
- proof需要修改 generated file、witness statement或正式 spec。
