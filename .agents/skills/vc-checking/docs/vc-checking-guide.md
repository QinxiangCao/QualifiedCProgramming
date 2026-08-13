# VC 检查

目标是在写proof前先判断全部split goals的可证性，仅在必要时判断整个top-level VC，据此选择`aggressive_pre_process`或`LLM_pre_process`；随后分析对应目标的证明思路并形成少量coherent proof groups。`<vc>_split_goal_*` declarations是raw obligation source的一部分，不做预处理或删除。

## 分析

严格按以下顺序分析：

1. 遍历所有top-level VC的全部split goals，只记录“可证”或“不可证”，忽略top-level VC，不规划helper、证明路线或复用。
2. 某个top-level VC至少有一个split goal且全部可证时，选择`aggressive_pre_process`，不再分析该top-level VC的可证性。
3. 任一split goal不可证或没有split goal时，只判断整个top-level VC的可证性；整体可证时选择`LLM_pre_process`，整体仍不可证时回annotation/spec。
4. 全部mode确定后，再分析证明思路和复用：aggressive只分析split goals，`LLM_pre_process`只分析整个top-level VC。
5. 所有证明思路完成后才分组；只分配top-level VC，split goals随所属top-level VC进入同一group。

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

版本失效写 `stale`；compaction写 `compact-error`。proof route不确定、helper尚未证明或 VC困难不是 blocker。

## 分组

证明思路完成后，按同一invariant展开、proof pattern、array/frame transformation、refinement transition、helper family和相近上下文对top-level VC形成初步groups，再做一次负载、耦合与预计关键路径审查。split goal不独立分组；aggressive top-level VC按其全部split-goal思路的整体负担与共享关系分组：

- 同时考虑top-level witness数、aggressive split-goal数、预计helper family数、数学库、proof mode差异、程序阶段和需要持续保留的proof context；`max_witnesses_per_group`只是hard upper bound。
- 通常形成少量、每组约2到6个top-level witnesses的coherent groups。单witness group必须是final result、独立特殊route或独立helper family等合理边界；超过6个witnesses必须在`agent_output.md`说明为何不能合理拆分。
- 同一function内的初始化、核心语义转换、简单控制流投影和最终结果若没有不可分割的helper family，应拆组。对预计tail group，若final-result与transition/safety可独立证明必须拆开；不可拆时在`agent_output.md`说明helper/context耦合，并规划可提前提供的permutation、sum/length、mask-clear等formal/public helper。
- manual seed只决定最终manual witness declaration顺序；accepted plan顺序决定group编号与helper merge顺序。程序阶段、实际负载与helper ownership优先决定group边界。

所有groups在机器调度上独立，plan不含dependency字段。若多个witnesses必须使用同一组紧耦合、证明专用的helper family，应留在同一group，由一个`group_worker_lib`维护current-suffix helpers。structured `helpers`只列本组新证/改写且带owner suffix的helper；历史snapshot/reuse helper不是新的plan item。只供本组时写`visibility: local`；稳定数学性质预计可在后续group/round复用时写`visibility: public`，具体潜在消费者留在notes。controller在该group通过validation后，把public candidate及其必要本地helper依赖闭包append到run-root durable pool；本轮所有groups只见preparing时冻结的同一`public_helper_snapshot.txt`，所以晋升只供未来round，不能改变当前调度结果。snapshot/pool都不能import、不能成为第四种lib或group dependency。不得读取/import sibling `group_worker_lib`或让多个groups重复证明同一大型helper family。

类似`sieve_of_euler`的case可在helper ownership允许时使用如下自然语言分组示例；具体witness名称不得硬编码进controller：

- `initialization`：初始化prefix、`replace_Znth` step和初始化循环退出。
- `semantic-transitions`：当前composite/prime分类、prime append和product mark，共享prime/least-factor/flag-state重型helper family。
- `control-and-exits`：inner divide/non-divide、下标归一化、stored exit implication和outer exit等projection、rewriting与算术witnesses。
- `final-result`：从最终outer state推出公开result spec。

只有共享数学事实已经合法进入`formal_case_lib`后，才考虑把`semantic-transitions`继续拆为outer-entry与inner-product groups。

## 封存 source 的证明复用

仅当handoff明确绑定正好上一轮sealed vc-proving source时执行，并与mode确定后的详细strategy分析放在同一步。source可以是failed round，也可以是verified后因annotation/freshness retry而stale的round；manifest、base、reuse local build与accepted dependency artifact digest由controller钉住，若已产生parent merge result则对应failed/passed result也必须封存。未绑定时不扫描历史目录、不运行comparison、不创建hint files。

先按“全部helper → 全部aggressive split goals → 全部`LLM_pre_process` top-level VC”的三段顺序分析复用。aggressive top-level VC和`LLM_pre_process` split goals不建立复用行。结构非法的failed group由controller跳过。只有曾通过controller group validation的accepted group可提供`direct copy`；未accepted failed/blocked group中的proof最多是partial idea，其helper只能from scratch。helper只做二元判断。使用handoff声明的current/reference debug scripts及exact commands，在各自build中print generated goals：

- current和previous都为`aggressive_pre_process`时，只比较相应split goals。
- current和previous都为`LLM_pre_process`时，只比较top-level whole goals。
- mode不同、名称/goal不够相似或proof state不支持复用时，标为from scratch。

split goal从`P |-- Q`变为`P' |-- Q'`时，不要只比较文本。若可证明`P |-- P'`与`Q' |-- Q`，旧proof可用前后adapter包裹；若变化等价于增加/重排共同spatial frame，例如`P ** F |-- Q ** F`，可标为`partial proof-idea reuse`。`direct copy`要求accepted source、完整兼容proof span/route，以及current/previous generated-goal语义指纹相同；该指纹绑定传递本地Definition闭包与`formal_case_lib`，只忽略generated declaration自身改名。Reason中的adapter/frame分析是worker提示，不是controller机器证明。

debug不是可选参考：handoff列出raw targets供选择，final current script必须exact覆盖全部aggressive split proof rows和全部`LLM_pre_process` top-level proof rows；final reference scriptexact覆盖每个direct/partial实际引用的previous goal。对每个comparison unit写`Goal <active_case_theory>.<case>_goal.<symbol>.`，下一个可执行命令必须是`Show.`，之后可运行proof tactics和额外`Show.`，最后`Abort.`。全from-scratch时不创建/运行reference script。controller封存script/build/round/version receipt；既有build digest是机械绑定local tree与reachable-base aggregate的combined seal，receipt不增加base字段。controller复验sealed `reuse-source` combined seal；额外未选target、覆盖不足或seal漂移都会失败。

每个proposed group写一个`reuse_hints/<group-id>.md`，table固定五列并按全部helper、全部aggressive split、全部`LLM_pre_process` top-level排列。helper direct引用accepted source `group_worker_lib`中的完整proved declaration；split/top-level direct或partial引用compatible copied manual完整proof declaration。所有非from-scratch range的start/end必须与parser识别的完整declaration边界精确相等，不能只引用其中的statement、`Proof`段或若干tactic；from-scratch的file/lines均为`—`。helper复用只由自己的行表达，不虚构它与每个witness的依赖。controller验证row order、mode、semantic fingerprint、path/range、source kind、completion与receipts并封存同次读取的bytes；hint不替代current group check。

## 输出

- `agent_output.md`：先按 manual顺序记录全部split goals的二元可证性判断，再写mode确定后实际分析目标的P/Q shape、instantiation、space/pure/refinement plan、helper premise或failure signal；同时记录所属top-level VC的mode。该文件面向人和retry，不是controller acceptance evidence。
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

每个top-level VC恰好在一个group，其split goals随它进入同一group。顶层只允许`groups`；group object只允许`id`、`witnesses`、`helpers`和`estimated_difficulty`，不得保留version、verified或dependency字段。difficulty必须是1到5的整数，供controller在不改变plan/merge顺序的前提下生成dispatch order。aggressive witness只含`name`、`proof_mode`和`split_strategies`；keys必须与raw manual的names/order完全一致，每个值非空。`LLM_pre_process` witness只含`name`、`proof_mode`和整体`strategy`。`helpers`只列本轮由本组新证或改写的helper；每项严格包含`name`、`strategy`、`visibility`，name全局唯一，visibility只能是`local`或`public`。public candidate在owner validation通过后进入pool。历史snapshot/reuse helper是机会性exact copy，不作为新的unsuffixed planned helper重复声明。不要复制target witness全集、grouping policy、per-witness长分析、reuse proof内容或controller metadata；这些分别存在current accepted inputs、`agent_output.md`、`reuse_hints`和controller state。

- `agent_report.json`：成功只含completed status，blocked时增加唯一完整`blocker`，不复制current version或checks。

split goal不可证时先分析所属top-level VC，不直接返回blocker。只有整个top-level VC仍不可证，terminal status才写`blocked`或`annotation-bug`。main agent会读取本轮`agent_output.md`和`agent_report.json`，在下一次annotation `agent_input.md`中按固定模板总结failure cause、evidence、previous-attempt reflection、required repair与scope decision，再把summary及两个原文件路径append到唯一annotation agent。为此VC Markdown必须给出具体failure shape和repair location，JSON只保留compact blocker；vc-checking owner不要替main agent写总结，也不要建议另开annotation agent。

## 回 annotation 的信号

- `Q`要求的 ownership/resource不在`P`。
- guard/invariant/local assertion没有必要 pure fact。
- array/list observation或`@pre`桥缺失。
- `safeExec` abstract state对不上。
- helper需要当前`P`无法提供的额外 premise。
- proof需要修改 generated file、witness statement或正式 spec。
