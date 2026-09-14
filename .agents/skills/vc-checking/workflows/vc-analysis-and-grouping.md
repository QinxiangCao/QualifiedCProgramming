# VC 分析与分组流程

本流程只由已经 claim 的 `vc-checking` owner 执行。主仓库当前 formal files 是唯一工作版本；manual 缺失或没有 top-level VC 时，controller 会直接接纳空 plan，不创建本角色。

## 一、开始工作

1. 核对 claim 中的 role、owner 和 CWD。
2. 完整读取本 skill、当前 `agent_input.md`，以及其中列出的当前 formal files。
3. 读取 handoff 中的 annotation VC comparisons，记录每个 source、current、related VCs、fact sources 和 judgement；这些只是优先复核线索。
4. 第二轮及以后可以读取 handoff 列出的前次 vc-checking `agent_output.md`、`group_plan.json` 和 blocker，避免重复分析；旧结果只是参考，当前主仓库 manual 始终为准。
5. 不读取 controller state、event、其他角色 skill 或未列出的历史。

每个 attempt 使用独立会话。不要自行 claim、推进 phase、启动 annotation/group worker 或修改 controller 文件。

## 二、文件边界

可读取：

- 当前主仓库 `*_proof_manual.v`、`*_goal.v`、`*_proof_auto.v`；
- 当前存在的 `formal_case_lib`；
- handoff 明确列出的前次 vc-checking 结果和 controller blocker。

可写：

- 当前主仓库 `*_proof_manual.v`，仅在 proof body 内临时插入 `Show.` 检查原始 goal；
- 当前 attempt 的 `group_plan.json`；
- `agent_output.md`；
- `agent_report.json`。

除插入 `Show.` 外，不修改 manual 的任何 proof 或非 proof token，也不修改其他 C、goal、auto、goal-check、lib 和历史文件。不创建 debug script、reuse hint、parser 输出或行号清单。

VC-checking 完成后，controller 会删除主仓库 manual 并重新运行 symbolic execution。group worker 收到的是重新生成的干净 manual，因此这里的临时 `Show.` 不需要手工清理。

## 三、观察 goal

需要 Rocq 展开结果时，直接在目标 proof body 中加入 `Show.`，然后原样运行 handoff 给出的 `coq-debug --round <current-round>`。该命令读取当前主仓库 manual；不要另建脚本、复制 goal、修改其他 manual token 或手拼 Coq 命令。

controller 命令必须保持 argv、cwd、解释器、参数和顺序不变。命令退出码为 0 且 JSON `status: passed` 才算通过。失败时保存第一个诊断，不用 raw Coq、Dune、Make、`coqdep` 或自写脚本绕过。

## 四、structural blocker scan 与全量 split-first

先对 manual 中全部 top-level VC 做一次廉价 structural scan，并优先查看没有 split goal 的 whole goals。此阶段只找会让 entailment 明确为假的结构缺口：antecedent 中的 current pointer/scalar 与 consequent 的 `@pre` 参数是否有等式桥、所需 resource address 是否存在、existential 是否能由当前资源实例化。不要在此阶段规划 tactic/helper，也不要把“看起来困难”当 blocker。

在 `agent_output.md` 的 `Structural Blocker Scan` 精确填写 status、已扫描 top-level 数、优先检查的 no-split 数和 definite blocker 数。若得到具体 countermodel，写明 P 可成立而 Q 失败的赋值/资源形状，立即交付 annotation/spec/dependency blocker；此时不必先分析全部 split goals。若没有确定 blocker，再进入下面的严格全量 split-first。

全量分析有两个不可跨越的顺序边界：

1. 所有 split goal 完成可证/不可证判断前，不分析任何 top-level VC；
2. 所有 top-level VC 的 mode 或 blocker 确定前，不写详细策略、helper 或 group。

先按 manual declaration 顺序列出全部 top-level VC 和各自的 `<vc>_split_goal_*`。名称或映射有问题时报告当前输入问题，不猜测、不改 statement。

对每个 split goal 只做二元判断：

- 可证：当前前提能够推出结论；
- 不可证：当前前提不能推出结论。

这一轮不分析 top-level goal，不写策略，也不因一个失败就停止后面的 split。

随后按 manual 顺序决定每个 top-level VC：

- 有 split 且全部 split 可证：选择 `aggressive_pre_process`，不再分析 top-level 可证性；
- 没有 split，或至少一个 split 不可证：分析整个 top-level VC；整体可证时选择 `LLM_pre_process`；
- 整体仍不可证：报告 annotation/spec/dependency blocker，不把它塞进 proving plan。

`aggressive_pre_process` 的正式目标是全部 split goals；`LLM_pre_process` 只证明 top-level VC，其 split blocks 保持生成状态。

完成 structural scan 后，独立复核 annotation comparison：在 current manual 中检查每个新增 premise/resource 的实际来源，以及 related VC 是否承担了建立责任。`provable` 不等于已经证明；缺少来源时直接返回结构化 annotation blocker。需要新重型数学 lemma、但没有明确反例或 premise 缺失时，标记为高风险。

## 五、策略与 helper

所有 mode 确定后才写策略：

- aggressive：只为每个 split goal 写策略；
- LLM：只为整个 top-level VC 写策略。

策略至少说明：

- entailment 两侧的 spatial resources、pure facts 和 existentials；
- witness 如何实例化；
- cancellation、frame、split/merge、list/array/permutation 变换；
- bounds、guard、length、等式等前提来自哪里；
- refinement 的 source/target state 和 transition；
- helper 的 statement、premises、使用位置和证明路线。

重复路线先抽成一个公共 proof pattern；单个 VC 只记录实际差异。

`formal_case_lib` 不存在时不得规划 helper。存在时，`helpers` 只列本轮由该 group 新证或实质修改的 helper，名称带 group suffix，`visibility` 只能是 `local` 或 `public`。所有 premise 必须能从当前 VC 给出；缺 premise 是 annotation/spec 信号。

## 六、分组

只分配 top-level VC；split goals 始终跟随父 VC。

先按 invariant、proof pattern、resource transformation、refinement transition、helper family 和持续上下文形成初步组，再做一次负载、耦合和关键路径审查。逐组检查：

- top-level witness 数；
- aggressive split 数；
- helper 数量和复杂度；
- proof mode、program stage 和库上下文；
- 是否会成为尾部关键路径；
- 是否能把独立 final-result、transition 或 safety 工作拆开。

通常每组 2 到 6 个 top-level VC。单 witness group 只用于真正独立的结果、route 或 helper family。每组给出 1 到 5 的 `estimated_difficulty`。handoff 的组大小是硬上限，不替代负载判断。各组独立，不读 sibling output，也不写 `depends_on`。

包含 comparison current/related VCs 的高风险 witness 单独组成最先运行的 group；不要把它与大量轻量 projection/lia witness 混在一起。其余 group 只在该优先 group 通过后才会被 controller 派发。

## 七、输出合同

### `group_plan.json`

顶层只含 `groups`。成功 plan 必须非空并精确覆盖当前 manual 的全部 top-level VC。

每个 group 只含：

- `id`；
- `estimated_difficulty`；
- `witnesses`；
- 可选 `helpers`。

aggressive witness 只含 `name`、`proof_mode`、`split_strategies`；split keys 与 manual 名称和顺序一致。LLM witness 只含 `name`、`proof_mode`、`strategy`。helper 只含 `name`、`strategy`、`visibility`。

不要加入版本、digest、acceptance、dispatch、dependency 或 reuse 字段。

### `agent_output.md`

保持简短，包含：

1. Outcome；
2. Structural Blocker Scan（四个机器读取字段）；
3. Annotation Comparison Review；
4. Proof-Mode Decisions；
5. Common Proof Patterns；
6. VC Deltas；
7. Grouping Decisions；
8. Risks or Blockers。

每个公共 pattern 只写一次；每个 VC 只写 pattern reference 和真实差异。第二轮引用前次结论时，只指出保留或改变了什么。

### `agent_report.json`

成功只写：

```json
{"status": "completed"}
```

blocked 时增加唯一 `blocker`，字段为 `failure_class`、`kind`、`vcs`、`message`、`repair_boundary`。annotation/spec/dependency blocker 的 `vcs` 非空，每项严格包含当前 manual 中的 `name`、`parent` 和 `annotation_location`；plan/report/infrastructure blocker 使用空列表。合法 failure class：

- `annotation-gap`；
- `specification-gap`；
- `dependency-gap`；
- `plan-defect`；
- `report-defect`；
- `infrastructure`。

前三类回 annotation，后三类留在 vc-checking。不要在 report 复制命令输出、digest 或 controller 检查结果。

## 八、交付

先写 plan 和 `agent_output.md`，确认停止修改后最后写 report。然后通知 main owner 已停止写入；main 才能执行 `finalize-delivery`。

若 controller 返回 `report-repair-required`，继续使用同一 owner 和 attempt，只修指出的 plan、说明或 report。不要新建 round。若 controller 已接受本 attempt，它会自动删除临时 manual 并重新 symbolic execution；不要再修改任何文件。
