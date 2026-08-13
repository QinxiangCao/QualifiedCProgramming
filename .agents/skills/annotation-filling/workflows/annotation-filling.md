# Annotation 填写与修正流程

本流程由一个 run 内唯一且持续复用的 annotation owner 执行。你直接修改 main root 当前 annotation 候选，并在同一 agent 工作中完成 `annotation-checking`。本文件已经包含本角色需要的流程合同；不要为了解“下一步”读取 orchestrator 或其他角色 skill。

## 一、认领后的角色边界

main agent 已经使用 controller 返回的 `claim_invocation` 认领 delivery。你收到的启动或追加消息应包含 `Role`、`Owner`、`CWD` 和逐字保留的 `Claim message`：

- 始终在给出的 `CWD` 工作，不猜测仓库、run 或 attempt 路径。
- 把 `Claim message`、它指向的当前 `agent_input.md` 以及其中列出的原始材料作为本 attempt 的权威输入。
- owner 名和 attempt 已由 controller 绑定；不要运行 `claim-attempt`、`step` 或 `finalize-delivery`，不要换 owner，也不要另建 annotation agent。
- 只执行交接明确给出的本角色命令。不要根据状态猜测缺少的命令、参数、解释器、路径或下一阶段动作。
- main root 当前目标 C、可选 formal files 和 controller 刷新的 generated files 才是当前候选。旧会话记忆、旧 attempt snapshot 或 group copy 都不是编辑基线。

若启动消息缺少上述四段，或其中引用的当前交接文件不存在，停止写入并把缺失项报告给 main agent；不要自行扫描 run state 或 orchestrator 文档来重建交接。

## 二、完整读取当前 attempt

### 首次 attempt

按以下顺序读取：

1. 本 skill 与本 workflow；
2. `annotation-checking/SKILL.md` 与其 workflow；
3. 当前 `agent_input.md`；
4. 交接列出的 `problem_context`、目标 C、存在的 `formal_case_lib`、当前 generated files 和必需的原始阻塞材料；
5. 两个 annotation skill 直接导航的知识文档，以及交接明确选出的本 skill 示例。

从 `agent_input.md` 记录 exact target 路径、哪些可选角色为 present/missing、允许的报告路径和 Commands。路径、case stem 与 C stem 可能不同；只使用交接给出的 exact 路径，不从文件名或目录名推导其他 formal 文件。

### 后续 retry

每次追加都仍由同一 agent target 处理，并重新完整读取：

1. 两个 annotation skill 及其 workflow；
2. 新 attempt 的完整 `agent_input.md`；
3. 其中五段反馈总结：阻塞结论、因果分析、前次反思、必需修正、范围决定；
4. 总结逐项引用的原始 `group_worker_report.json`、`group_worker_output.md` 或其他当前 attempt Markdown/JSON blocker；
5. main root 当前目标文件。

原始 blocker 与当前文件优先于旧会话记忆。不要只根据摘要或上次 diff 继续修改。只有 controller
handoff 明确给出 `consider_broader_refactor: true` 时，才必须重新审视数学规范、function contract、
loop invariant、assertion 和调用实例之间的整体关系，避免继续叠加互相冲突的局部补丁；不要从
annotation iteration 的目录序号自行推断该要求。

### 一次处理多个 group 的 annotation 缺口

一次 retry 可能汇总同一 proving round 中多个 group 报告的 annotation 缺口。它们属于同一次完整反馈，必须在本 attempt 中逐项闭环：

1. 从五段总结建立覆盖清单；每项保留原始 group、witness、location、message、repair boundary，以及对应 `group_worker_report.json` / `group_worker_output.md` 路径。
2. 完整读取清单中每个被引用的原始 blocker。不得只读第一项，也不得把措辞相近的不同 witness 当作已经覆盖。
3. 把每项缺口映射到需要复核的数学规范、function contract、loop invariant、assertion 或调用实例。多个缺口可以共享一个根因和一次修正，但来源引用必须分别保留。
4. 先形成覆盖全部条目的整体修正，再编辑候选；不得修完第一个 group 就结束 attempt。
5. 完成检查循环后，重新对照每一条原始 blocker，确认它已由哪项修正覆盖。把逐项引用、共同根因和处理结论简洁写入 `agent_output.md`。

这些 blocker 只是 annotation 修正输入。其原始报告、group manual/lib、副本与已封存证明全部只读；不要进入 group 目录继续证明，不要判断 proof reuse，也不要推断 controller 接下来如何调度或合并。若反馈本身缺少某项声称存在的原始引用，或引用之间存在无法从当前文件核实的冲突，应先停止相应编辑并向 main agent 准确指出缺失或冲突，不能扫描未授权报告来补齐。

## 三、写入边界

只允许写入：

- 交接指定的 main root 目标 `.c` 中的 annotation；不得改 C 算法实现。
- 交接开始时已经存在的 main root `formal_case_lib` 中与 annotation 配套的数学规范。
- 由当前 attempt 的交接 `symexec` 命令事务化刷新的 exact generated roles；generated files 不得手改。
- 当前 attempt 的 `agent_report.json` 和可选 `agent_output.md`。

`formal_case_lib` 若标记为 missing，就保持 missing：不得创建 placeholder、同名或异名 lib，也不运行仅适用于该 lib 的检查。可选 generated role 在开始时 missing 不代表失败；只允许 controller 的 `symexec` 决定刷新后的 present/missing 状态。

以下内容全部只读，且不得借“修 annotation”越界修改：

- `agent_input.md`、annotation history、`before/`、`after/`、controller state/event 与原始 blocker；
- manual proof body、group 文件、public helper、`proving_merged` 和其他 formal/shared lib；
- controller 与任一 skill 的脚本、workflow 或知识文档。

不得增加 `Admitted.`、额外 `Axiom`、禁用 lemma、不安全捷径或对本 run current generated artifact 的 import。changed files、digest、版本、命令结果和接纳结论由 controller 计算，不要复制到 owner JSON。

## 四、形成完整候选

### 1. 理解计算目标

先读 `problem_context`、目标 C、已有规范和真实调用关系，明确输入、输出、会改变的资源，以及必须跨循环、分支和函数调用保留的纯事实。背景简短、初始 annotation 不完整或 `formal_case_lib` 缺失都不是终止理由；在允许边界内形成最小而充分的候选。

### 2. 先审数学规范

若 `formal_case_lib` present，先确认其中 specification 可以脱离当前 C 控制流独立理解，再设计 predicate 和 annotation：

- 不把 loop、状态机或单步转移翻译成 Rocq 算法来伪装功能规范。
- 对有限且由输入唯一确定的结果，优先使用透明规范值或有限 list。
- 使用 `exists f : A -> B, ...` 等函数 witness 前，确认它确实代表数学对象或 proof interface，而不是把可避免的搜索留给 proof worker。
- 稳定的业务数学事实放进已有 `formal_case_lib`；局部运行时性质放在 C annotation。

若 `formal_case_lib` missing，不创建新 lib；直接使用当前允许且已有的规范接口完成 C annotation，并在 `agent_output.md` 说明此可选角色缺失，而不是把它作为 blocker。

### 3. 联动修改 C annotation

依次检查并补全：

1. function contracts；
2. loop invariants；
3. 分支、循环与退出需要的纯事实；
4. 函数调用实例与存在量词 witness；
5. 必要的普通 `Assert`。

invariant 必须同时连接初始化、保持和退出，并表达前缀、后缀、区间、候选最优值、可行性、shape 等算法隐藏性质。不得为了减少 VC 而弱化 postcondition、contract 或 invariant。

普通 `Assert` 只服务于函数调用边界、语义阶段转换、路径汇合或退出桥接。对每个新增、保留或修改的普通 `Assert`，按知识文档审查并在 `agent_output.md` 记录 `keep`、`remove` 或 `revise`；没有普通 `Assert` 时记录 `none`。

### 4. 整体复核

确认数学规范、function contract、loop invariant、assertion 和调用实例描述同一功能关系；修正一处接口时同步检查所有调用者与退出桥接。对 retry，再逐项核对本次五段总结和全部原始 blocker 的覆盖清单。

## 五、controller 命令合同

`agent_input.md` 的 Commands 会给出已经绑定解释器、cwd、case、路径、flags 和 build/overlay 的完整 controller 命令。每条命令都必须：

- 原样执行，并使用交接给出的 `CWD`；优先直接调用系统终端；若终端操作仅能通过 `functions.exec` 使用，允许每个 cell 只 `await` 一次 `tools.exec_command` 来启动命令，或只调用一次 `tools.write_stdin` 来续接同一 live session（也可使用运行时为同一终端操作公布的规范化等价名称），并仅转发结果；
- 启动时原样传入完整命令/argv、全部参数、解释器和 `CWD`，续接时保留同一 session 标识；规范化等价工具只有在输入形态能原样接收这些值时才可使用，不得把 argv 序列化为 shell 字符串、重新解析命令或增添引号；
- 保持返回 argv 的解释器和所有参数不变，不另包一层 `uv run`；
- 不在桥接 cell 中调用第二个工具、构造、修改、串联、并行或解释命令，不使用其他 JavaScript/Python 编排、自建 shell/PowerShell/Python 脚本、`sh -c`、管道、命令替换、后台进程或封装；
- 不改 cwd、环境、flags、include、SLP 参数、driver、overlay、build path 或输出路径；
- 不替换为 controller 内部模块、raw symbolic execution、raw Coq、Dune、Make、Rocq MCP 或自拼等价命令。

保留并继续等待任何外层 cell 和内层 process/session 标识，直到实际命令明确退出；透明桥接若返回仍在运行的 `functions.exec` cell，只用 `functions.wait` 恢复同一 cell，直到其中唯一一次终端操作返回。空输出、首次 yield 或 `Script completed` 均不单独代表成功。只有退出码为 0 且 controller 最终 JSON 的 `status` 为 `passed`，该命令才通过。

按以下次序工作：

1. 原样运行当前 attempt 的 `symexec`。它是刷新 generated roles 的唯一方式；失败时只修允许的 annotation/规范，再重跑同一命令。
2. 仅当 `formal_case_lib` present 且交接提供对应 invocation 时，原样运行 `coq-check --target-kind formal-case-lib`。不得自行补造该 invocation。
3. 进入 `annotation-checking`，按其 workflow 执行候选检查以及交接提供的 checking timing invocations。

进入 checking 本身不要求重复刚刚通过、且此后没有 formal/generated 写入的同一组命令；checking 发现问题并修改候选后，才按其 workflow 重跑受影响的命令。

命令失败后先根据完整输出定位允许边界内的原因。一次 tactic 失败、可修的规范问题或可重跑的 controller 命令都不是 `blocked`。不得手改 generated 文件、弱化功能规范或修改 proof 来让命令变绿。

## 六、annotation-checking 修正循环

形成候选并完成上述最新 owner 检查后，在当前 agent 中调用 `annotation-checking`，不 spawn 新 agent。checking 若发现可修问题：

1. 回到本 workflow 对应的数学规范或 C annotation 层修正；
2. 原样重跑受影响的 `symexec`，以及 present `formal_case_lib` 的检查；
3. 重新执行完整 annotation-checking 清单；
4. 对 retry 再核对全部汇总 blocker，而非只确认最新错误消失。

重复直到当前候选满足 checking 条件或形成真实且无法在允许边界内修复的 blocker。owner 的 checking 结论只说明候选可交付，不代表 controller 已接纳。

## 七、报告、停止写入与 finalize 修正

成功时，`agent_report.json` 只含：

```json
{
  "status": "completed"
}
```

确实不能继续时写 `blocked`，并增加唯一完整 `blocker`，且只含本合同要求的 `failure_class`、`kind`、`location`、`message`、`repair_boundary`。版本失效使用 `stale`，上下文压缩使用 `compact-error`。不要把多个诊断伪装成多个 JSON blocker；详细来源和逐项分析写在 `agent_output.md`，唯一 blocker 必须完整说明真正阻止本 attempt 继续的边界。

`agent_output.md` 可记录问题理解、数学规范理由、高阶 witness 判断、分支控制、普通 `Assert` 审查、修正摘要，以及 retry 对每个原始 blocker 的引用与覆盖结论。它供人和后续修正阅读，不控制接纳。

写完报告后停止修改所有 formal/generated/report 文件，并通知 main agent 可以执行 claim response 或 `waiting_for` 中原样给出的 `finalize_invocation`。该 invocation 由 main agent 执行；owner 不运行、不改写。

若 controller 返回 `report-repair-required`：

1. 当前 delivery 仍是 `running`，当前 attempt、owner 和 agent target 全部不变；不要创建新 attempt 或重新 claim。
2. 读取 main agent 追加的精确 mismatch 和它引用的当前 attempt 材料；不要从 orchestrator 或 state 猜测原因。
3. 只在本 workflow 的写入边界内修正 mismatch。若只要求报告修正，不触碰已经停止写入的 formal/generated 候选；若允许文件确需修正，重新执行受影响的 owner 检查后再更新报告。
4. 再次停止写入并通知 main agent。main agent 重跑原 `finalize_invocation`；owner 仍不执行 finalize。

`report-repair-required` 不创建 `after/`，不开始新的 annotation round，也不是更换 owner 或启动下游工作的理由。finalize 被 controller 接受后，本角色工作结束；不要自行运行接纳检查、proof、merge、apply、cleanup 或 final check。
