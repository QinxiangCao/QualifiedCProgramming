# VC 分析与分组流程

本流程只由 controller 已领取的 `vc-checking` owner 执行，且 raw manual 至少含一个 top-level VC。零 manual VC（manual 缺失，或只含 generated import 与作用域命令）由 controller 直接接纳 `{"groups": []}`；owner 不得为它虚构 witness、manual、plan 或 group。

本文件是 vc-checking 的流程与机器合同。`docs/` 只提供证明分析知识；其中涉及旧读取范围、旧报告布局或旧交接方式的文字不扩大本流程的权限。

## 一、从 claim/handoff 开始

main 已执行 controller 给出的 `claim_invocation`，随后把 claim response 中的 prompt 原样交给当前 owner。prompt 固定包含 `Role`、`Owner`、`CWD` 和逐字的 `Claim message`。开始工作时：

1. 确认 role 是当前 `vc-checking` 工作，owner 与 claim message 一致，并在给定 `CWD` 工作。
2. 完整读取 claim message 指定的当前 `agent_input.md`。不要凭目录名、case stem 或旧 attempt 猜路径、版本、命令或输出位置。
3. 只使用交接给出的当前 attempt、source version、target witnesses、group 上限、输入路径、输出路径、可选 reuse binding 和 exact controller commands。
4. 若 prompt 缺段、role/owner 冲突、必须路径未绑定或必要文件状态与交接冲突，停止扩展读取，按第九节报告 blocker 或 stale。

不要自行运行或重领 `claim-attempt`，不要换 owner。每个新 attempt 使用独立会话；只有 controller 明确要求同一 delivery 原地修复时，才在这个 owner target 继续工作。

## 二、读取和写入边界

除本 skill 的 workflow/docs 与当前 claim/handoff 外，只可读取交接精确绑定的：

- raw `*_proof_manual.v`；
- `*_goal.v`；
- `*_proof_auto.v`；
- present 的 `formal_case_lib`；
- 启用 reuse 时的 sealed source、frozen helper snapshot、已有 group seal/result 与 controller blocker；
- controller command 返回的当前 attempt receipt 或诊断。

只可写交接精确给出的：

- `group_plan.json`；
- `agent_output.md`；
- `agent_report.json`；
- 启用 reuse 时的 `reuse_hints/<group-id>.md`；
- 交接给出的 current/reference debug script 路径。

始终遵守以下边界：

- main-root formal files 全部只读；不修改 C annotation、generated files、raw manual、goal、auto、proof body 或任何 lib。
- 不创建缺失的 manual、`formal_case_lib`、helper lib 或占位文件。
- 不读取根 `AGENTS.md`、verification-orchestrator、其他角色 skill、controller state/event、sibling owner 输出、未绑定 run 或 repository examples。
- 不扫描历史寻找复用机会；只有 handoff 明确绑定的正好上一封存 proving source 可读。
- 不替 main/controller 做 phase transition，也不启动 annotation owner、group-worker、merge、verify、final apply 或 final check。

## 三、controller 命令边界

handoff 给出的 `coq-debug` 或其他 controller 命令必须原样执行：argv、`argv[0]`、cwd、flags、路径和顺序都不能改。优先直接调用系统终端；若当前运行时仅通过 `functions.exec` 暴露终端操作，允许透明桥接：每个 cell 只 `await` 一次 `tools.exec_command` 来启动命令，或只调用一次 `tools.write_stdin` 来续接同一 live session（也可使用运行时为同一终端操作公布的规范化等价名称），并仅转发结果。启动时原样传入完整命令/argv、全部参数和 cwd，续接时保留同一 session id；不得把 argv 序列化为 shell 字符串、重新解析命令或增添引号。

禁止：

- 在桥接 cell 中调用第二个工具、构造、修改、串联、并行或解释命令；
- 使用其他 JavaScript/Python 编排、自建 shell/PowerShell/Python 脚本或另一层 `uv run`；
- 使用 `sh -c`、管道、命令替换、后台进程或自行拼接环境；
- 直接调用 controller 内部模块、raw Coq/Rocq、symexec、Dune、Make 或相似替代命令。

保留并继续等待任何外层 cell 和内层 session/process id，直到实际命令退出；透明桥接若返回仍在运行的 `functions.exec` cell，只用 `functions.wait` 恢复同一 cell，直到其中唯一一次终端操作返回。空输出、首次让出和 `Script completed` 都不表示通过。只有最终退出码为 `0` 且 controller JSON 的 `status` 为 `passed`，该 controller check 才通过；否则保存精确失败证据并按第九节处理，不用替代命令绕过。

## 四、全量 split-first 与 `proof_mode`

分析必须有两个全局顺序边界：在全部 split-goal 二元判断完成前，不分析任何 top-level VC；在全部 VC 的 mode 或失败结论确定前，不写详细策略、helper、reuse 判断或 group。

### 1. 核对正式目标

按 raw manual declaration 顺序列出全部 top-level VC 及其 `<vc>_split_goal_*` declarations，并与 handoff 的 target witnesses 和 mapping 核对。名称、顺序、statement 或 target coverage 不一致属于 stale/malformed input，不自行改 manual 或猜映射。

split declaration 是 `aggressive_pre_process` 的正式子目标，不是预处理噪声。没有 split declaration 的 top-level VC 要明确记为“无 split”，但不要伪造一个 split。

### 2. 先完成所有 split goals 的二元判断

遍历所有 top-level VC 的全部 split goals，完整走完 raw manual 后才进入下一步。此阶段每个实际 split goal 只记录一种结论：

- **可证**：当前前提在语义上可以推出结论。
- **不可证**：当前 split goal 的前提不能推出结论。

此阶段禁止：

- 判断、展开或记录任何 top-level VC 的整体可证性；
- 把单个 split 不可证直接诊断为 annotation/spec 缺口；
- 写 proof strategy、helper、reuse decision 或 grouping；
- 因前面某个 split 不可证而提前停止尚未判断的 split goals。

`aggressive_pre_process` 可能丢掉整体证明所需信息，因此 split 不可证只决定所属 top-level VC 下一步必须做整体判断。

### 3. 为全部 top-level VC 确定唯一 mode

完成全部 split 二元判断后，再按 raw manual 顺序处理每个 top-level VC：

- 至少有一个 split goal，且该 VC 的全部 split goals 都可证：选择 `aggressive_pre_process`，不得再分析该 top-level VC 的整体可证性。
- 任一 split goal 不可证，或该 VC 没有 split goal：只判断整个 top-level VC。整体可证时选择 `LLM_pre_process`；整体仍不可证时记录 annotation/spec 缺口或真实基础设施 blocker。

继续完成所有需要的整体判断，以便 `agent_output.md` 给出本 attempt 的完整反馈。若任一 top-level VC 整体不可证，本 attempt 不得输出可进入 proving 的完整 plan，也不得把它交给 group-worker 硬证；按第九节写一个 terminal report。

`LLM_pre_process` 只证明 top-level VC；其原始 split proof token 保持不动。`aggressive_pre_process` 的正式 proving targets 是该 VC 的全部 split goals，top-level 仅在后续由既定预处理路线组合。

## 五、详细策略与 helper 规划

只有全部 top-level VC 都取得可进入 proving 的 `proof_mode` 后，才写详细策略。分析对象必须与 mode 一一对应：

- `aggressive_pre_process`：只分析该 VC 的全部 split goals；不分析或比较 top-level VC 的证明思路，也不为 top-level 建 reuse 行。
- `LLM_pre_process`：只分析整个 top-level VC；不分析其 split-goal 证明思路，也不为 split 建 reuse 行。

对每个实际分析目标，具体说明：

- `P |-- Q` 的 pre/post spatial resources、pure facts 和 existentials；
- 右侧 witness 的实例及来源；
- resource cancellation、split/merge、frame、数组/list/permutation 变换；
- bounds、guards、length facts、等式等 pure premise 的来源；
- refinement 的 source/target state 与 transition；
- helper 的 statement shape、全部 premises、每个 premise 如何由当前 VC discharge、使用位置和证明路线。

先把重复路线抽成公共 proof pattern，每个 pattern 只定义一次；每个 VC 只引用 pattern 并写 binder、边界、分支、witness、rewrite 或 helper 等真实差异。详细领域方法使用本 skill 的两个 `docs/`，但不要按 docs 中的示例去读取未绑定 repository 文件。

`helpers` 只规划本轮由所属 group 新证或实质修改的 helper：

- `formal_case_lib` missing 时不得规划任何 helper；controller 不会为它创建 `group_worker_lib`，也不能把 shared/异名 lib 当作当前 case 的可编辑 lib；
- 名称必须带该 owner group suffix，且在 plan 内全局唯一；
- `visibility` 只能是 `local` 或 `public`；
- `local` 仅供本组；稳定、纯数学且预计供未来 group/round 使用时才标 `public`；
- frozen snapshot 或 accepted reuse 中 declaration/proof token 一致的 helper 不作为新的 planned helper；
- 无法从当前 `P` discharge 的 helper premise 是 annotation/spec 信号，不能靠把 premise 塞进 helper 或 public pool 掩盖。

所有 group 在本轮调度上独立。不能规划读取/import sibling `group_worker_lib`、等待本轮 public helper 晋升或使用 `depends_on`；紧耦合的 proof-specific helper family 应与消费者留在同一 group。

## 六、条件式 sealed-source reuse

只有 `agent_input.md` 明确绑定“正好上一轮封存的 vc-proving source”时才执行 reuse。未绑定时：

- 不扫描 `verification_runs/`、reports、Git history 或其他目录；
- 不创建 `reuse_hints`；
- 不运行 reference comparison；
- 直接按当前目标从头规划策略。

启用 reuse 时，在 mode 和当前详细策略确定后完成单元比较，再在最终分组确定后为每个 group 写恰好一个 hint。比较顺序固定为：

1. 全部 planned helpers；
2. 全部 `aggressive_pre_process` split goals；
3. 全部 `LLM_pre_process` top-level VC。

对每个 mixed-mode group，`group_plan.json` 的 witnesses 也必须把全部 `aggressive_pre_process` witnesses 放在全部 `LLM_pre_process` witnesses 之前，并保持两个分段各自的相对顺序。这样 plan traversal、固定类别顺序与实际 hint 行序三者一致；不能只重排 hint 表。

不要为 aggressive top-level VC 或 `LLM_pre_process` split goals 建比较单元。来源可由 controller 绑定为 parent check 失败的 round、含结构合法 blocked group 的失败 round，或曾 verified 后因 annotation/freshness retry 变 stale 的 round。

复用判定：

- 只有曾通过 controller group validation 的 accepted group 可提供 `direct copy`。
- 未 accepted 的 proof 最多是 `partial proof-idea reuse`；其中 helper 一律 `from scratch`。
- helper 只允许 `direct copy` 或 `from scratch`。
- proof 允许 `direct copy`、`partial proof-idea reuse`、`from scratch`。
- proof `direct copy` 还要求完整 proof declaration/route 兼容，且 current/previous generated-goal 语义指纹一致；只改 generated declaration 名可 direct。
- `P |-- Q` 变成 `P' |-- Q'` 时，只有可解释的前后 adapter 或共同 frame 思路才可 partial；hint 中的解释不是机器证明。

helper 只依据交接绑定的 frozen snapshot 或 sealed source 比较完整 declaration/proof token，不写进 goal debug script。使用 handoff 给出的 current/reference debug script 路径和 exact commands；每个 proof comparison unit 使用交接给出的完整目标：

```coq
Goal <active_case_theory>.<case>_goal.<symbol>.
Show.
Abort.
```

允许在该目标内加入实际调试 tactic 和额外 `Show.`，但不增加 local declaration、`Load`、load-path 命令或封装。current script 精确覆盖全部 proof 比较单元，即 aggressive split goals 与 `LLM_pre_process` top-level VC；reference script 只覆盖 direct/partial 实际引用的 previous proof goals。若所有 proof 都 `from scratch`，不创建或运行 reference script。

每个最终 group 的 `reuse_hints/<group-id>.md` 只含固定五列表格：

```text
Current goal | Decision | Previous file | Lines | Reason
```

行仍按“全部 helper → 全部 aggressive split goals → 全部 LLM top-level VC”的相对顺序排列，并只放属于该 group 的项。非 `from scratch` 的 file/path 和 start/end lines 必须精确覆盖 parser 识别的一个完整 helper 或 proof declaration；不能只引用 statement、内部 tactic 或 `Proof` 子段。`from scratch` 的 file/lines 写 `—`。helper 复用只由 helper 自己的一行表达，不虚构它对每个 witness 的依赖。

## 七、初步分组与第二次审查

全部策略完成后，按共享 invariant、proof pattern、array/frame transformation、refinement transition、helper family 和相近持续上下文形成初步 groups。只分配 top-level VC；一个 aggressive VC 的全部 split goals 始终随它进入同一 group。

初步分组完成后，必须进行一次独立的负载、耦合和预计关键路径审查。逐组重新检查：

- top-level witness 数；
- aggressive split-goal 数；
- helper family 的数量与复杂度；
- 数学库与持续 proof context 负担；
- 是否混杂不同 `proof_mode` 或不相干 program stage；
- 哪一组预计成为尾部关键路径，以及是否仍可拆分。

初始化、核心语义转换、简单控制流投影和最终结果若不共享不可拆 helper/context，应拆开。可独立证明的 final-result 与 transition/safety 必须拆组；不能拆时，在 `agent_output.md` 说明具体 helper/context 耦合，并提前规划稳定的 permutation、sum/length、mask-clear 等 helper。

通常每组约 2 到 6 个 top-level witnesses。单 witness group 只用于独立 final result、特殊 route 或独立 helper family。不要把重型 aggressive/helper 工作与大量只需投影、rewrite 或算术的轻量 VC 堆成尾部大组。超过 6 个 witnesses 或预计尾部仍不可拆时说明原因。

每组给出 `1` 到 `5` 的整数 `estimated_difficulty`。handoff 的 `max_witnesses_per_group` 是硬上限，不代替上述负载判断。accepted plan 顺序决定固定 group 编号与 helper merge 顺序；controller 另算的 dispatch order 只影响并发调度。

## 八、严格输出合同

可进入 proving 的成功 attempt 先完成 `group_plan.json`、可选 reuse/debug artifacts 和 `agent_output.md`，确认不再修改它们后，最后写 `agent_report.json`。terminal blocked/stale/compact-error 路径不要为满足成功合同补造 plan、hint 或 debug artifact；只保留交接允许且在失败前已形成的诊断材料，先在 `agent_output.md` 保存完整证据，再把对应 terminal report 作为最后写入。任何路径都不要在 report 写完后继续修改 owner 文件。

### `group_plan.json` 文件

成功 plan 的顶层只含 `groups`。本流程的 `groups` 必须非空，并精确覆盖 raw manual 的全部 top-level VC；空 plan 只由 controller 在零 manual VC 时生成。

```json
{
  "groups": [
    {
      "id": "array-frame",
      "estimated_difficulty": 4,
      "witnesses": [
        {
          "name": "proof_of_x",
          "proof_mode": "aggressive_pre_process",
          "split_strategies": {
            "proof_of_x_split_goal_1": "instantiate the old list and discharge the bound",
            "proof_of_x_split_goal_2": "rewrite the update and cancel the unchanged frame"
          }
        }
      ],
      "helpers": [
        {
          "name": "list_update_frame__array_frame",
          "strategy": "prove the unchanged prefix and suffix frame from the index bounds",
          "visibility": "local"
        }
      ]
    }
  ]
}
```

机器字段必须严格满足：

- group 只含 `id`、`estimated_difficulty`、`witnesses` 和可选 `helpers`；group id 唯一。
- 每个 top-level VC 恰好出现一次；witness 名精确匹配 raw manual。
- aggressive witness 只含 `name`、`proof_mode`、`split_strategies`。split keys 与 raw manual names/order 完全一致，每个 strategy 非空；不得写 top-level `strategy`。
- `LLM_pre_process` witness 只含 `name`、`proof_mode`、整个 top-level 的非空 `strategy`；不得写 `split_strategies`。
- 启用 reuse 时，mixed-mode group 的 witnesses 必须先列全部 aggressive witnesses、再列全部 LLM witnesses，并保持每段内部相对顺序。
- helper 只含 `name`、非空 `strategy`、`visibility`；名称带 owner group suffix且全局唯一，visibility 只能是 `local` 或 `public`。
- `estimated_difficulty` 是 `1..5` 的整数；每组 witness 数不超过 handoff 上限。
- 不增加 source/version、digest、`verified`、`depends_on`、dispatch order、负载统计、notes 或其他字段。

### `agent_output.md` 文件

只保留六个决策区段：

1. `Outcome`：能否进入 proving、witness/group 数与预计关键路径。
2. `Proof-Mode Decisions`：按 manual 顺序压缩记录每个 VC 的全部 split 二元结果、是否需要整体判断、最终 mode 与原因。
3. `Common Proof Patterns`：公共证明模式，每个模式只定义一次。
4. `VC Deltas`：每个 VC 对所选实际目标的 pattern reference、相对差异、helper premise/归属与可选 reuse 结论。
5. `Grouping Decisions`：初步共享关系、第二次负载/耦合/关键路径审查、为何拆分或不能继续拆分。
6. `Risks or Blockers`：真实风险；若失败，给出完整 annotation/spec 或工具 blocker 证据。

该 Markdown 面向人和下一次修正，不控制机器接纳。不要重复 handoff 合同、skill 原文、完整 plan/schema、controller 命令、完整 reuse table、previous proof 或每个 VC 都相同的步骤。新证据可以写充分；公共套路只写一次。

### `agent_report.json` 文件

成功时只能写：

```json
{
  "status": "completed"
}
```

不要复制 version、digest、changed files、checks、command output、receipt 或“verified”声明；controller 自己计算并接纳这些事实。

## 九、blocked、stale 与 annotation 反馈边界

以下情况不是 blocker：proof 困难、尚未证明 helper、策略需要 group-worker 探索、复用为 `from scratch`、单个 split goal 不可证但整个 top-level VC 可证。

只有整个 top-level VC 仍不可证、输入/命令真实损坏、必要文件或授权路径缺失等无法在本角色边界内继续的情况，才写 terminal report。`blocked` report 顶层只含 `status` 与唯一完整 `blocker`：

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "<handoff/controller 允许的分类>",
    "kind": "<具体问题类型>",
    "location": "<witness、formal symbol 或文件位置>",
    "message": "<当前前提为何不能推出目标的完整而紧凑说明>",
    "repair_boundary": "<必须修复的精确边界>"
  }
}
```

字段一个不能少，也不增加其他字段。`failure_class` 只能是
`annotation-gap`、`specification-gap`、`dependency-gap`、`source-version`、`plan-defect`、
`report-defect` 或 `infrastructure`；`kind` 和 `repair_boundary` 使用 handoff/controller 给出的
现行枚举，不自行发明同义值。controller 只按 `failure_class` 决定恢复阶段：前四类回到 annotation，
后三类保留 accepted source 与 selected dependency snapshot，修复对应 controller/plan/report 边界后重试 vc-checking，
不从 `kind`、`message` 或自然语言猜测。若多个 top-level VC 都暴露 annotation 缺口，JSON 仍只有
一个完整 blocker：在 `location/message` 汇总涉及的 witnesses，并在 `agent_output.md` 逐项保存证据。

annotation/spec 缺口反馈必须具体说明：

- 失败 witness 与实际分析的 whole-goal shape；
- `Q` 所需但 `P` 缺失的 ownership/resource、pure fact、array/list observation、`@pre` bridge、refinement state 或 helper premise；
- 能定位时对应的 C function、function contract、loop invariant、assertion、call instantiation 或 present `formal_case_lib` 数学规范；
- 为什么修复边界不属于 vc-checking 或 group proof。

不要修改 annotation/spec，不要把不可证目标硬塞进 plan，不要联系或启动 annotation agent，也不要替 main 写 annotation summary。main/controller 会引用本 attempt 的原始 Markdown/JSON blocker，在后续创建一次正式 annotation feedback；当前 owner 到报告交付即停止。

source version 或 seal 在工作期间失效时，使用交接规定的 `stale` terminal status，不读新版本混做同一 attempt。发生上下文压缩且无法保证已完成全量分析时，使用交接规定的 `compact-error`，不要靠猜测补完。两种状态的 JSON 形状以 claim message 的精确合同为准；不得伪装成 `completed` 或用旧 plan 推进。

## 十、停止写入、finalize 与原地修复

完成或 blocked 后，关闭所有 owner 文件并确认不再有 formal/report/debug 写入，再把结果返回 main。main 使用 claim response 或 `step.waiting_for` 中 controller 给出的完整 `finalize_invocation`；owner 不自行拼接、改写或提前执行 finalize。finalize 先运行适用的 owner-candidate preflight；若它通过，才封存 owner 文件并直接运行 `vc-checking-check-round`，机械检查 current version、exact VC coverage、proof mode、difficulty、helper 合同与条件式 reuse hints。preflight 若返回同 attempt repair，则按下述边界返修后重跑同一命令。

finalize 之后：

- 接纳成功：本角色工作结束。不要读取 state 猜下一步，不运行 proving preparing 或其他 phase。
- controller 返回 `report-repair-required` 或同 attempt 的可修复 handoff：delivery 仍是 `running`；只有收到 main 原样追加到同一 owner target 的 controller repair prompt 后才继续。只读取该 handoff 明确给出的 blocker/文件，按 repair boundary 修改允许的 owner outputs；不创建新 round、不换 owner、不重做未被否定的 formal analysis。
- 若只开放 report 修复，保持 `group_plan.json`、reuse hints、debug scripts 和全部 formal source 不变；只修 `agent_report.json`/`agent_output.md` 中 controller 指出的合同错误。若 handoff 开放某个 plan/hint 输出，也只修改列明路径。
- 修复完成后再次停止全部写入并返回 main，由 main 原样重跑同一 delivery 的 `finalize_invocation`。
- 若 controller 判断 source/seal 漂移、修复越界或不可接纳，按它给出的 terminal handoff 报告，不绕过 check，不自行进入 annotation 或后续 phase。

交付前最后核对：

- 所有 split goals 在任何 top-level 分析之前都已完成二元判断；
- 每个 top-level VC 的 mode 符合唯一决策规则；
- strategy 只覆盖该 mode 的正式目标；
- 成功时 plan 精确覆盖且无扩展字段，并已完成第二次负载、耦合和关键路径审查；terminal 路径没有伪造 plan；
- 启用 reuse 时来源确为明确绑定 source，hint/debug coverage 与顺序正确；
- report 是最后写入且符合最小 JSON 合同；
- 未修改 formal source，未读取其他角色流程，也未推进后续阶段。
