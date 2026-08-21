# Annotation 候选检查流程

本流程由 run 内唯一 annotation owner 在同一 agent 工作中执行。它检查当前候选、把可修问题送回 `annotation-filling`，并在修正后重复检查；不创建新 agent，不决定 controller 接纳，也不需要读取 orchestrator 或其他角色 skill。

## 一、开始条件与当前输入

开始前必须同时满足：

- 已重新完整读取两个 annotation skill 及其 workflow。
- 已完整读取当前 attempt 的 `agent_input.md`、交接指定的原始材料和 main root 当前目标文件。
- `annotation-filling` 已形成一版候选，或已按当前 retry 的五段总结完成一版整体修正。
- 当前 attempt 的 exact `symexec`，以及 present `formal_case_lib` 对应的检查 invocation，均来自交接的 Commands；missing 可选角色不需要也不得补造命令。

首次 attempt 与 retry 都以当前 main root 为准。retry 不得依赖旧会话记忆；若反馈汇总多个 group 的 annotation 缺口，先确认已经完整读取每项交接列出的全部 evidence 路径，并保留 group、witness、location、message 与 repair boundary 的逐项覆盖清单。交接只列出 owner 实际交付并被封存的文件；未列出的文件不存在，不得去找。

若 controller 交接所需字段、当前输入或被明确引用的原始 blocker 缺失，停止检查并准确报告缺失项；不要扫描 controller state、其他 reports、group 目录或 orchestrator 文档来重建上下文。

## 二、共同写入与命令边界

checking 期间仍只允许写：目标 C 的 annotation、开始时已存在的 `formal_case_lib` 数学规范、由交接 `symexec` 刷新的 generated roles，以及当前 attempt 的报告/notes。不得改 C 算法、手改 generated files、创建 missing lib、修改 manual proof、group 文件、annotation history、controller 文件或其他 formal/shared lib。

交接中的 checking timing、`symexec` 和 `coq-check` invocations 必须原样执行，并使用交接给出的 `CWD`。优先直接调用系统终端；若当前运行时仅通过 `functions.exec` 暴露终端操作，允许透明桥接：每个 cell 只能 `await` 一次 `tools.exec_command` 来启动命令，或只调用一次 `tools.write_stdin` 来续接同一 live session（也可使用运行时为同一终端操作公布的规范化等价名称），并且只能透传结果。启动时必须原样传入完整命令/argv、全部参数、已绑定解释器和 `CWD`；续接时必须保留同一 session 标识。规范化等价工具只有在输入形态能原样接收这些值时才可使用；不得把 argv 序列化为 shell 字符串、重新解析命令或增添引号。

不得在桥接 cell 中调用第二个工具、加入其他 JavaScript/Python 编排、构造、修改、串联、并行或解释命令；不得另包 `uv run`、自建 shell/PowerShell/Python 脚本、使用 `sh -c`、管道、命令替换、后台进程或其他封装；不得自行拼 cwd、flags、include、SLP、overlay、build path 或 target，也不得改用内部模块、raw symexec、raw Coq、Dune、Make 或 Rocq MCP。

保留并继续等待任何外层 cell 和内层 process/session 标识，直到实际命令明确退出；透明桥接若返回仍在运行的 `functions.exec` cell，只用 `functions.wait` 恢复同一 cell，直到其中唯一一次终端操作返回。空输出、首次 yield 或 `Script completed` 不单独表示成功。只有退出码为 0 且 controller 最终 JSON 的 `status` 为 `passed`，对应检查才通过。

交接若提供 annotation-checking 的 timing invocations，只在本次 checking 实际开始时运行 start，在本次 checking 确实结束时运行 finish，并分别原样执行。timing 不控制候选结论；不得估算、补写时间或为了计时增加 agent 往返。

## 三、检查清单

### 1. 数学规范质量

若 `formal_case_lib` present，检查其 specification 是否描述独立于当前 C 控制流的业务数学语义：

- function contract 的输入输出关系足以表达真正结果，而不只是范围或 shape。
- declaration 没有把 loop locals、单步转移或控制流照搬成 Rocq 算法。
- direct proof 遇到算法镜像 specification 时必须返工；不能把难证当作保留镜像规范的理由。
- refinement proof 可以保留 proof type 需要的 `safeExec` 或 monad spec，但局部运行时事实仍应写在 annotation。
- 不含 `Admitted.`、额外 `Axiom`、禁用 lemma、不安全捷径或 current generated artifact import。

若出现 `exists f : A -> B, ...` 或同类高阶 witness，比较透明规范值、有限 list 与函数表示。只有函数表示在定义域、有效范围或 proof interface 上确有优势时才保留，并在 `agent_output.md` 说明理由。

若 `formal_case_lib` missing，确认候选没有创建 placeholder 或异名替代物；继续检查现有规范接口与 C annotation，不把角色缺失本身判为失败。

### 2. Annotation 的端到端连接

逐项检查：

- C function contract 引用了正确且当前允许的 specification declaration。
- helper/check 函数的 `Ensure` 给出调用方真正需要的判定性质，而不是仅给返回值范围。
- loop invariant 覆盖初始化、保持与退出，并把已处理状态连接到 postcondition。
- 分支条件、循环边界、调用实例、存在量词 witness、资源变化和退出状态能够闭合。
- 修改 callee contract 后，所有 caller 的实例、前置条件和退出桥接都已同步复核。
- 数组与字符串优先复用已有 `IntArray`、`UIntArray`、`CharArray`、`PtrArray`、`store_string`、`store_stringLit`、`GlobalStrings` 等谓词；可写缓冲区、只读 literal 与局部 `char[]` 的选择一致。

不得以弱化 postcondition、contract 或 invariant 的方式隐藏 VC，也不得把本应属于 annotation 的局部事实转移到 proof body。

交接含 `## Frozen specification` 时，其中列出的函数 spec 与已存在的 `Extern Coq`、`Import Coq`、case lib 声明都不得改动；复核只确认它们逐字未变，任何修改都会在接纳前被 controller 比对拦截。

### 3. 普通 `Assert`

对每个非 invariant、非 postcondition 的普通 `Assert` 逐一给出 `keep`、`remove` 或 `revise`：

- 只保留服务于函数调用边界、语义阶段转换、路径汇合或退出桥接的断言。
- 删除机械重复 invariant、postcondition 或当前 symbolic state 的断言。
- 断言位置必须处于其语义事实刚建立且后续仍需要的位置。
- 没有普通 `Assert` 时，在 `agent_output.md` 记录 `none`。

### 4. 汇总 retry 的逐项覆盖

若当前 retry 含一个或多个 annotation blocker，逐项核对覆盖清单：

1. 每个原始 group/witness/location 都能指向本次复核过的 contract、invariant、assertion、调用实例或数学规范。
2. 共享根因可以合并修正，但每条原始 evidence 引用仍有单独结论。
3. 当前 generated 结果没有只消除第一个 blocker、却遗漏同轮其他 group 的缺口。
4. `agent_output.md` 能简洁说明每项来源、共同根因、对应修正与复核结果。

只检查交接明确引用的 blocker，不进入 group 副本补证明，不编辑原报告，不扫描历史寻找额外来源，也不判断 proof reuse、下一轮分组或调度。

### 5. Controller owner 检查的新鲜性

首次进入本流程时，确认 `annotation-filling` 已在最后一次 formal/generated 写入后，按交接顺序原样运行并通过：

1. 当前 attempt 的 `symexec`；
2. 仅在 `formal_case_lib` present 时运行其 `coq-check --target-kind formal-case-lib` invocation。

若两项已经针对当前候选通过，不要仅因进入 checking 重复执行。若 checking 期间修改了目标 C annotation 或 present `formal_case_lib`，必须回到 `annotation-filling`，重新运行 `symexec` 与适用的 lib 检查，再从本检查清单开头复核。`symexec` 是 generated roles 的唯一刷新方式；失败时只在允许边界内修正，不得手改生成结果。owner 检查只证明当前候选能在 main root 由 controller 稳定刷新，不代表 controller 已接纳。

### 6. 写入边界复核

最后确认修改只落在当前 attempt 允许的目标 C annotation、present `formal_case_lib`、controller 刷新的 exact generated roles 和报告文件中。不要在 JSON 中声明 changed files、digest、version、检查输出或接纳结论；controller 会从封存的 before/current 状态机械计算。

## 四、返修循环与结论

任一检查项发现可修问题时：

1. 把问题定位到 `annotation-filling` 的数学规范或 C annotation 层；
2. 在共同写入边界内完成联动修正；
3. 原样重跑 `symexec` 与适用的 `formal_case_lib` 检查；
4. 从本文件检查清单开头重新检查，包括全部汇总 blocker 的覆盖情况。

一次 tactic 失败、规范仍可改善、普通工具失败或可重跑的 controller invocation 都不能直接写成 `blocked`。只有问题确实无法在本角色允许的文件和命令边界内继续解决时，才形成真实 blocker。

全部项目通过后，按 `annotation-filling` workflow 写 `agent_report.json` 与可选 `agent_output.md`，结束 timing（若交接提供），停止修改 formal/generated/report 文件，并通知 main agent 可以执行原 `finalize_invocation`。成功 JSON 只能是 `{"status":"completed"}`；blocked JSON 只能增加一个含 `failure_class`、`kind`、`location`、`message`、`repair_boundary` 的完整 blocker。

## 五、finalize 返回报告修正时

`finalize-delivery` 由 main agent 执行，不由 annotation owner 执行。若 controller 返回 `report-repair-required`：

- delivery 保持 `running`；沿用同一 attempt、owner、agent target 和原 finalize invocation。
- 读取 main agent 追加的精确 mismatch，只在共同写入边界内修正。
- 若 mismatch 仅涉及报告，保持 formal/generated 候选不变；若允许文件确需修正，重新执行受影响命令与本检查清单。
- 再次停止写入，由 main agent 重跑原 finalize；不要自行 claim、finalize、创建新 round 或运行任何下游检查。

通过本流程仅表示候选可以交回 main agent。finalize 是否接受以及此后的状态转移都由 controller 决定，本角色不预测也不代行。
