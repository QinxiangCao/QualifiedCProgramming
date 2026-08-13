# 自然语言证明分析

自然语言分析用于记录proofability、proof-mode理由、具体proof strategy、第二次负载/耦合审查、public-helper ownership和group边界，写入`agent_output.md`；controller不解析其固定结构，机器acceptance来自current version、group plan、conditional reuse hints、group validation、parent verify与final-check。

## 读取顺序

1. `agent_input.md`：version、target witnesses、group bound和输出路径。
2. raw `*_proof_manual.v`：top-level VC与其`<vc>_split_goal_*` obligation source、mapping与顺序。
3. goal/auto/check：只读 theorem展开。
4. current `formal_case_lib`。

不读取或生成额外manual preprocessing artifact。

优先参考 `Rocq/examples/LLM_bench` 与 `QCP_demos_LLM`；human cases只作非权威思路提示。

## 顺序

先遍历全部split goals，只记录“可证”或“不可证”，不分析任何top-level VC，也不规划helper、具体证明路线或复用。某个top-level VC至少有一个split goal且全部可证时，选择`aggressive_pre_process`；任一split goal不可证或没有split goal时，才只判断整个top-level VC的可证性，整体可证则选择`LLM_pre_process`，整体仍不可证才返回annotation/spec缺口。

全部`proof_mode`确定后，再写证明思路，并在handoff绑定正好上一轮sealed vc-proving source时同时完成reuse comparison。`aggressive_pre_process`只分析和比较split goals，忽略top-level VC；`LLM_pre_process`只分析和比较整个top-level VC，忽略split goals。使用current/reference debug commands逐comparison unit执行`Show.`、取得controller script/combined-build-seal/version receipts；combined build digest机械绑定local tree与accepted dependency artifact digest。source可以failed，也可以verified后因annotation/freshness retry而stale。未绑定时直接写证明思路，不扫描历史或创建reuse hints。

## 每个被分析目标回答

- `P |-- Q` 是否语义成立？
- pre/post spatial、pure、existential分别是什么？
- 右侧 witness取什么值？
- 哪些资源直接 cancel，哪些 segment/list需要转换？
- arithmetic依赖哪些 bounds、guards、length facts与等式？不要只写“lia”。
- refinement hypothesis/目标 state是什么，需哪些 unfold/choice step？
- helper若需要，其 statement、premises、premise来源和 destination是什么？
- 若失败，缺口位于 C annotation、`formal_case_lib`、stale files还是 malformed VC？

可使用简洁 Markdown 小节，不要为了模拟旧 JSON template填空。内容要具体到能指导 group-worker或 annotation repair。

## Helper 判定

`needs-helper` 必须说明 helper的 statement shape、used witnesses、每个 premise如何从当前 VC discharge，以及 destination为owner的`group_worker_lib`。只有本轮新证或改写的helper进入当前plan并使用owner suffix；上一轮或public snapshot中声明/proof token一致的helper只是机会性复用。只供本组的helper写`visibility: local`；稳定且不依赖具体C局部变量、预计可在后续group/round复用的数学性质写`visibility: public`，具体潜在消费者写notes。controller在owner group通过validation后把public helper及必要本地helper依赖闭包append到durable pool，供未来round。不能discharge的premise意味着annotation/spec缺口；正式spec本身缺失时仍回annotation，不能把public pool当作spec替代品。

## Group 分析

证明思路完成后，按invariant、proof pattern、array/frame transformation、refinement transition和helper family对top-level VC形成初步groups，再逐组做第二次负载、耦合与预计关键路径审查。split goal不单独分组，始终随所属top-level VC进入同一group；aggressive top-level VC按其全部split-goal思路的整体负担分组。至少记录top-level witness数、aggressive split-goal负担、预计helper family数量/复杂度、数学库、proof mode差异、程序阶段、需持续保留的上下文、helper owner和最终拆分/合并理由。对likely tail group判断final-result与transition/safety能否独立；能则拆组，不能则说明不可分割helper/context，并规划可提前提供的formal/public helper。通常以2到6个witnesses为合理区间；manual seed只控制final witness order，plan控制group/helper merge order。这些prose是human review/worker输入，不是controller acceptance parser的输入。

最终`group_plan.json`只保留group id、逐VC proof mode、aggressive `split_strategies`、`LLM_pre_process`整体`strategy`、1到5的`estimated_difficulty`和带owner suffix/visibility的planned helpers。aggressive witness不写top-level `strategy`，`LLM_pre_process` witness不写`split_strategies`。plan不保存version、verified或dependency字段。所有groups必须能从正式seed与preparing时冻结的同一个public candidate snapshot独立证明：不可分割的proof-specific helper family决定合组；本轮producer晋升不会改变任何sibling输入。不得规划读取/import sibling `group_worker_lib`、等待pool更新、直接helper注入或重复证明大型helper family。

若启用了sealed-source reuse，每个group的`reuse_hints/<group-id>.md`只放固定五列comparison table，按全部helper → 全部aggressive split goals → 全部`LLM_pre_process` top-level VC排序。每个非from-scratch `Lines` 必须从首行到末行精确覆盖source中的完整helper/proof declaration，声明内部子范围即使含全部tactic也无效。helper direct引用accepted source group的完整proved declaration，不做partial；split/whole direct或partial引用compatible previous copied-manual proof block。proof direct还要求accepted source、完整route与current/previous semantic goal fingerprint一致；rename-only可direct。fingerprint变化只能partial并分析adapter/common-frame思路，或者from scratch。结构非法failed groups不出现；未accepted group不能提供direct。agent_output可总结判断，但不要复制整张table或previous proof。

split goal单独不可证只触发所属top-level VC的整体分析，不直接阻塞。只有整体分析后仍为`annotation-bug`或真正blocked的top-level VC，才不得输出可进入proving的完整plan；terminal report写相应status/blocker。`agent_output.md`同时保留具体分析；之后main agent读取它与JSON report，完成下一次annotation `agent_input.md`的blocker总结与反思，并把summary及原文件路径append到唯一annotation会话。
