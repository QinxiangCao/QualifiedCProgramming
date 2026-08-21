# Controller 公共接口

本文给 main agent 和 controller 维护者说明公开入口。正常 run 中，main 以 action 返回的 invocation 为准，不靠本文或 `--help` 临时拼命令。

## 一、统一调用合同

唯一入口：

```text
.agents/scripts/verification-orchestrator/controller.py
```

人类从仓库根同步并首次启动：

```text
uv sync --frozen --python 3.12
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py ...
```

公共入口会在 parser 和任何业务写入前拒绝非 Python 3.12。通过门禁后，controller 返回的 action 继续以当前 uv 环境中已验证的绝对 `sys.executable` 作为 `argv[0]`；agent 原样直接执行该数组，不替换 Python，也不再次嵌套 uv。

controller 返回的可执行命令统一为：

```json
{
  "argv": [
    "/workspace/qcp-binary-democases/.venv/bin/python",
    "/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py",
    "--main-root",
    "/workspace/qcp-binary-democases",
    "step",
    "--run",
    "demo-20260729000536"
  ],
  "cwd": "/workspace/qcp-binary-democases"
}
```

执行规则：

- `argv` 是字符串数组，直接交给终端执行，不拼成 shell 字符串。
- `cwd` 是绝对路径；终端工作目录必须使用它。
- `argv[0]` 是 controller 已验证为 Python 3.12 的当前 uv 环境解释器。
- controller、root、run、round、attempt、owner 和文件参数都已完整展开。
- 不替换 Python，不增删参数，不加 `sh -c`、管道、后台或二次封装。
- action 的人类可读字段用于理解；`argv` 才是执行依据。

main-owned action 使用 `invocation`。spawn/append action 使用 `claim_invocation`。claim 成功后使用 `handoff.prompt` 启动或追加 agent，并保存 `finalize_invocation`。owner 停止写入后才 finalize；上下文丢失时从下一次 `step.waiting_for` 取回。

任何公开入口在首次读取、写入、删除、复用或验证 phase artifact 前，都从 current run/report roots、round、attempt id 与 exact target mapping 重新推导固定 topology，并要求 state 中的 directory/report/input/output/manifest/candidate/reuse path 逐项相等。persisted path 不能把另一 run、错 round、absolute alias 或 symlink/reparse tree 变成合法来源。

固定交接只有四段：

```text
Role: <controller role>
Owner: <controller owner>
CWD: <controller cwd>
Claim message (verbatim):
<controller claim message 原文>
```

main 不摘要、不翻译、不补充。owner 自己读取 claim message 指定的角色 skill 和交接文件。

下文示例使用固定演示值：

```text
Python: /workspace/qcp-binary-democases/.venv/bin/python
Root: /workspace/qcp-binary-democases
Run: demo-20260729000536
```

这些只是文档示例。真实执行必须使用当前 action 返回的值。

## 二、18 个公共入口

### 1. `init-run` 命令

**调用者与时机：** main；一个 case 开始时调用一次。目标 C 必须已存在于 main root。

**参数：**

| 参数 | 必需 | 含义 |
|---|---:|---|
| `--case` | 是 | run id stem 与唯一 authoritative Rocq/generated formal stem；必须是合法 Rocq identifier |
| `--target-c-file` | 是 | main root 的 `QCP_examples/**` 内目标 C，可为相对或绝对路径；stem/目录名可与 case 不同 |
| `--timestamp` | 否 | 固定 run 时间串；省略时由 controller 生成 |
| `--max-compact-attempts` | 否 | compact retry 上限，默认 3，必须为正数 |
| `--max-witnesses-per-group` | 否 | 单组 witness 硬上限，默认 12，必须为正数 |
| `--max-parallel-group-workers` | 否 | group 并发上限，默认 5，必须为正数 |
| `--problem-statement` | 否 | 题目文字 |
| `--problem-statement-file` | 否 | 题目文件 |
| `--target-function` | 否 | 目标函数 |
| `--expected-behavior` | 否 | 预期行为 |
| `--input-output-contract` | 否 | 输入输出合同 |
| `--spec-hint` | 否，可重复 | spec 提示 |
| `--preferred-hidden-property` | 否，可重复 | 希望保留的隐藏性质 |
| `--forbidden-pattern` | 否，可重复 | 禁止实现模式 |
| `--reference-case-hint` | 否，可重复 | 参考 case |
| `--freeze-spec` | 否，可重复或逗号分隔 | 冻结指定 C 函数的 specification；省略时 annotation agent 可自由编写 spec |

**返回与成功：** exit 0，JSON 给出 `run_id`、`run_root`、`report_root` 和 `controller_state`。controller 把 target parent 镜像到 `Rocq/examples/<collection>/**`，以 `--case` 命名 generated/formal modules，并持久化只含 C/formal paths、case 与 active theory 的九字段 exact `target_files`；同目录可有多个互不混淆的程序。run/report roots 成对分配，任一同名遗留目录都不能被新 run 接管。init 还以 O_EXCL 一次写入 `reports/<run>/controller_target_topology.json`，严格只含 `run_id`、`case` 和 `target_files`，后续不重写；每次加载 state 都从 current run identity、fixed C path 与 authoritative case 重算，并要求 state、anchor、重算结果逐项一致。include/SLP/profile 在每次 canonical symexec 时从 sealed C path 重算，不成为额外 state mapping。随后调用 `step`。

**`--freeze-spec`：** 把 specification 当作本 run 的固定输入而非可重新设计的对象。给出函数名后，该函数的 `With` / `Require` / `Ensure` 块（含具名 spec 与 `<= other_spec` refinement 子句）必须在 annotation 阶段保持 token 一致；注释、空白与行尾属于格式，不算修改。

只要使用该 flag，已存在的 `Extern Coq` 条目、`Import Coq` module 和 case lib 顶层声明也一并冻结——冻结的 spec 其含义依赖这些定义，否则文本不变而语义漂移。**新增**不受限制：可以新增 `Extern Coq` 条目、新增 import、在 case lib 中新增 definition/lemma，也可以为未列出的函数编写 spec。`Inv Assert` 与 `Assert` 始终完全可编辑。

init 时抽取 baseline 并存入 `controller_state.json` 的 `spec_freeze`；`annotation-check-round` 重新抽取并逐条比对，任何被修改或删除的条目都会使该 attempt 失败，并以 `annotation-main-check-spec-freeze` 退回 annotation agent，附带具体条目名。省略该 flag 时不做任何比对，行为与之前完全一致。

**重复与失败：** 不把它当成恢复入口。路径越界、目标缺失、非法 Rocq case identifier、配置值非法或 run 目录冲突时停止；修正输入后创建明确的新 run。禁止手工创建 state、从 C stem 重算 formal 名或复用另一个 case 的 run root。后续所有 action 只消费 persisted `target_files`。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","init-run","--case","demo","--target-c-file","QCP_examples/LLM_bench/Algorithms/demo/demo.c","--timestamp","20260729000536","--max-compact-attempts","3","--max-witnesses-per-group","12","--max-parallel-group-workers","5"],"cwd":"/workspace/qcp-binary-democases"}
```

### 2. `step` 命令

**调用者与时机：** main；init 后、每个 action 完成后、等待恢复后都调用。

**参数：** `--run` 必需。

**作用与返回：** 根据权威 state 推进纯 controller 状态，返回 `phase`、hydrated `next_actions`、hydrated `waiting_for` 和可选 blocker。main-owned action 有完整 `invocation`；spawn/append 有 role、owner、cwd 和完整 `claim_invocation`；running/returned delivery 有完整 `finalize_invocation`。非空 group plan 中，即使已有 group 以 `blocker.failure_class: annotation-gap` 到达本轮终态，scheduler 也不把它加入提前停止集合；只要仍有未终态 group 和 `max_parallel_group_workers` 下的可用 slot，`step` 就继续 hydrate 尚未领取的 group action，不能只等待当时 running 的 delivery。

**成功与重复：** exit 0 即表示 step 本身完成，不表示整个 run 通过。相同状态重复调用必须稳定，不应制造重复 attempt。`next_actions` 为空时必须有 `waiting_for`、blocker 或 `phase: done`。

**失败后：** 修复 controller 报告的 state/path 问题。禁止 main 自己推断下一 phase、扫描 state 后手拼命令或用 `--help` 猜 action。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","step","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 3. `claim-attempt` 命令

**调用者与时机：** main；收到 spawn/append action 后，在启动或追加 agent 前执行 action 自带的 `claim_invocation`。

**参数：**

| 参数 | 必需 | 含义 |
|---|---:|---|
| `--run` | 是 | 当前 run |
| `--next-action` | 是 | action 原始 `id` |
| `--owner` | 是 | action 给出的稳定 owner |

**返回与成功：** `status` 为 `claimed` 或同 owner 的 `already-claimed`，并返回 `attempt`、`owner`、原 `message`、固定 `handoff` 和完整 `finalize_invocation`。main 只使用 `handoff.prompt` 交接。group 汇总产生的 annotation retry 在首次 claim、重复 claim 和重新渲染 handoff 前，都重验全部 `feedback_sources` 的固定路径与 sealed digests；漂移时不返回旧 handoff。

**重复与失败：** 同 owner 重复 claim 幂等；不同 owner、过期 action、错误 manifest 或非 delivery action 被拒绝。annotation retry 复用 annotation owner，group repair 复用 group owner。禁止 main 改 owner、改 prompt 或先 spawn 后 claim。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","claim-attempt","--run","demo-20260729000536","--next-action","spawn-demo-vc-checking-r1-attempt-1","--owner","vc-checking/demo-vc-checking-r1-attempt-1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 4. `finalize-delivery` 命令

**调用者与时机：** main；owner 已真正停止写 formal/report 后，执行 claim response 或 `step.waiting_for` 给出的 invocation。

**参数：** `--run`、`--attempt`、`--owner` 都必需。

**作用与返回：** 校验 owner，封存交付，并直接运行 annotation/vc-checking phase validation 或 group validation。返回值可能是 `ready-for-main-check`、`returned`、`report-repair-required`、`invalid-report`、group validation 结果或幂等结果；按 JSON 和下一次 `step` 处理。finalize 封存 owner 实际交付的每个文件；group 的合法 `failure_class: annotation-gap` blocker 还要求交付固定路径上非空 UTF-8 的 `group_worker_output.md`。controller 以 `require_complete=False` 检查 structure/ownership/route/helper/import/safety，不跑 exact/full group Rocq，结构合法才成为本轮 blocked 终态和 reuse source。它不要求 owner 越界修改 annotation，也不阻止 sibling 调度。

**成功与重复：** 同 owner、同 seal 的重复 finalize 幂等。一次 controller 命令完成 group validation；不发布 in-flight execution，也不并发调用同一 action。

**失败后：** 首次 group preflight 返回 `report-repair-required` 前，用 `repair_formal_sha256` 冻结 manual/可选 lib；同一 owner 只能修 report/Markdown，formal 漂移返回 `invalid-report`，成功 finalize 清理临时 seal。`failure_class: annotation-gap` 不是原地 proof repair；controller 等全部计划 group 到终态后统一处理。其他 blocker 仍按原有 repair、耗尽或终止 action 执行。禁止换 owner、先 finalize 后继续写、另跑公开“检查交付”命令或手工标记 accepted。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","finalize-delivery","--run","demo-20260729000536","--attempt","demo-vc-proving-r1:group1","--owner","group-worker/demo-vc-proving-r1/group1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 5. `retry-round` 命令

**调用者与时机：** main-owned action；controller 已明确要求 annotation 或 vc-checking retry 时调用。

**参数：**

| 参数 | 必需 | 取值 |
|---|---:|---|
| `--run` | 是 | 当前 run |
| `--phase` | 是 | `annotation` 或 `vc-checking` |
| `--reason` | 是 | action 给出的机器原因 |
| `--previous-attempt` | 是 | action 给出的 blocker 来源 |

**返回与成功：** 创建合法 retry attempt，更新 state 并返回新 attempt/action 摘要。annotation retry 先进入 main 总结，vc-checking retry 进入新的独立 delivery。vc-checking blocked 的 phase 由固定 `failure_class` 映射产生：annotation/spec/dependency/source-version 类回 annotation，plan/report/infrastructure 类留在 vc-checking；不读取 blocker 自然语言。本轮多个 group 报告 annotation 缺口时，controller 只在全部 group 都为 accepted 或结构合法 annotation-gap blocked 后发布一次 `--phase annotation --reason group-worker-annotation-gaps --previous-attempt <vc-proving-round>`；attempt 的 `retry_previous_attempt` 绑定整个 proving round，phase、reason 和 source 必须与 current action 逐项一致。retry 按 plan/source 顺序把全部原始 group Markdown/JSON 展开为同一 input 的 `feedback_sources`。annotation attempt 另存因果 retry count；只有机器分类的 annotation/spec/dependency 缺口增加该值，目录序号和 infrastructure/tool/report/compact 等原因不增加。

**重复与失败：** 相同调用在 attempt 已存在时先重验 feedback sources，再只返回 `already-retried` 并复用原 attempt，不能创建第二个 attempt。旧 action、phase/reason/source 不匹配、版本或来源 seal 漂移会拒绝或写 blocker。禁止 main 自选参数、把同一 delivery 的报告修正升级成 retry、或跳过原始 blocker。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","retry-round","--run","demo-20260729000536","--phase","annotation","--reason","vc-proving-parent-failed","--previous-attempt","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

多组 annotation-gap 汇总时，同一入口的 action 形如：

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","retry-round","--run","demo-20260729000536","--phase","annotation","--reason","group-worker-annotation-gaps","--previous-attempt","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 6. `annotation-summary-ready` 命令

**调用者与时机：** main-owned action；main 已按模板填写 annotation retry 的五段 blocker 总结后调用。

**参数：** `--run`、`--attempt` 必需。

**作用与返回：** 检查模板 marker、全部原始 blocker 路径与 sealed digests、固定事实和 input digest，封存输入并发布 `append-annotation-agent`。返回 `status` 和下一 action id。group 汇总来源要求五段总结覆盖每个列出的缺口；任一 feedback Markdown/JSON 缺失或漂移都拒绝 summary-ready。

**重复与失败：** 已封存内容不得再改。摘要空泛、marker 未替换、来源消失或固定区段被改时失败；修正文档后重跑同一 action。禁止 main 读取 subagent skill 来补规则，只能总结 controller 指定的当前 blocker。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","annotation-summary-ready","--run","demo-20260729000536","--attempt","demo-annotation-r2-attempt-1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 7. `timing-stage` 命令

**调用者与时机：** annotation owner；按交接在人工 annotation-checking 开始和结束时调用。

**参数：** `--run`、`--round`、`--stage` 和 `--event` 必需；`--stage` 只能是 `annotation-checking`，`--event` 只能是 `start` 或 `finish`。

**返回与成功：** 记录计时事件并返回 JSON。它只做观测，不接纳 annotation。

**重复与失败：** 必须按交接的 round 和事件执行；错误 phase、无 current attempt 或不合法的 start/finish 顺序会失败。禁止把它当检查命令或伪造其他 stage。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","timing-stage","--run","demo-20260729000536","--round","demo-annotation-r1","--stage","annotation-checking","--event","start"],"cwd":"/workspace/qcp-binary-democases"}
```

### 8. `annotation-check-round` 命令

**调用者与时机：** main-owned action；annotation delivery 已封存并完成 controller phase validation 后调用。

**参数：** `--run`、`--round` 必需。

**作用与返回：** 在 main root 按 persisted `target_files` 重跑 canonical symexec，解析 present raw manual；`formal_case_lib` present 时先用 selected backend 准备其 exact `.vo` target，再执行本地 `coqc`；随后做独立 clean replay 与 generated role presence/digest 稳定性比较。manual/lib 候选路径允许 missing，不 seed lib、不创建 placeholder。通过时接纳 annotation、写 source versions，并发布 `dune-build`。

run 若使用了 `--freeze-spec`，本命令还在 `formal_case_lib` contract 检查之后、接纳之前重新抽取 specification surface，与 `spec_freeze.baseline` 逐条比对。被修改或删除的条目使 attempt 以 `main-check-failed` 结束，`main_check.spec_freeze` 记录 `mismatch_count` 与 `first_mismatch`（含 `section`、`entry`、`kind`），并以 `annotation-main-check-spec-freeze` 退回同一 annotation agent。未使用该 flag 时跳过此比对。

**成功与重复：** 以 exit 0 和 JSON 接纳状态为准。相同已接纳输入可返回稳定结果；输入漂移会路由 retry，不得把 owner 自检当成替代。

**失败后：** 执行返回的 retry action或处理 blocker。禁止直接进入 vc-checking、手改 accepted state 或跳过 clean replay。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","annotation-check-round","--run","demo-20260729000536","--round","demo-annotation-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 9. `vc-checking-check-round` 命令

**调用者与时机：** main-owned action；vc-checking delivery 已封存后调用。

**参数：** `--run`、`--round` 必需；`--group-plan` 可选，通常由 action 在需要时完整给出。

**作用与返回：** 严格验证 current version、全部 witness coverage、proof mode、aggressive split 顺序、strategy、difficulty、helper、组上限和可选 reuse/debug 证据。helper reuse mode 机器门禁只接受 `from scratch`，拒绝 `direct` 或 `partial`。接纳时返回 `status: accepted`、plan 路径、group 数和 `agent_output_metrics`。

**重复与失败：** 同一 sealed plan 可稳定复验；非法 plan 进入 controller 指定的 retry。禁止通过缩短 `agent_output.md` 放宽 `group_plan.json`，也禁止 main 指向另一 plan 文件。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","vc-checking-check-round","--run","demo-20260729000536","--round","demo-vc-checking-r1","--group-plan","/workspace/qcp-binary-democases/reports/demo-20260729000536/rounds/demo-vc-checking-r1/group_plan.json"],"cwd":"/workspace/qcp-binary-democases"}
```

### 10. `dune-build` 命令

**调用者与时机：** main-owned action；annotation 接纳后、vc-checking/preparing 前调用。

**参数：** `--run` 必需。

**作用与返回：** 从 persisted arbitrary-depth target path 构造 exact goal-check `.vo`。若 main root 的 `_build` 是目录，执行原有 exact Dune build 并写 `dune_dependency_snapshot.json`；否则执行 lock-free Makefile preparation：breadth-batched `coqdep` 只解析 exact closure，生成只含 `trusted-base` goal 的 run 根 `Makefile`，拒绝聚合 target，并写 `makefile_dependency_snapshot.json`。state 的历史字段 `dune_preparation` 保存 `build_mode`（Makefile 时）、snapshot path/digest、dependency/source/artifact/configuration digests、current/dependency counts、重编计数和耗时；Makefile 模式另有 dependency batch/process/node metrics、current cleanup 与 Make 耗时。

**成功标准：** `status: passed`，snapshot 与 receipt digests 一致，所有 dependency sources/artifacts 与 selected configuration 可重验，`source_goal_version` 等于 accepted annotation，exact target 与 current case identity 一致。Makefile 模式还要求 run `Makefile` digest、tool paths 和 batched-resolution metrics 一致。

**重复与失败：** 相同 accepted input 可重跑 selected exact preparation 并覆盖同路径 snapshot/Makefile；annotation retry 产生新 version 后旧 receipt 失效。同一 action 的无副作用区间复用一次完整校验返回的 snapshot/摘要；经过会改写已校验输入的 build/Rocq 步骤、state reload 或独立后置接纳边界时重新校验。不保留 snapshot 历史、dependency fragment 或额外 freshness database。失败只修首个 selected-build/Rocq/source/configuration 问题并重跑相同 action；禁止扩大为 whole-workspace Dune target、仓库 Make aggregate target或手工伪造 snapshot。一个 run 内不得新增或删除 `_build` 来切换模式。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","dune-build","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 11. `vc-proving-preparing` 命令

**调用者与时机：** main-owned action；VC plan 已接纳，或零 manual VC 的空 plan 已由 controller 接纳。

**参数：** `--run`、`--round` 必需。

**作用与返回：** 重验 plan/source/accepted selected dependency snapshot，创建固定 base manifest、适用的 group copies、public snapshot、可选 reuse source、group manifest 和 handoff。stale proving source 的 manifest 显式使用 source round sealed `reuse_source_raw` seed 解析，不能读取 annotation 更新后的 main root。manual absent 等价零 witnesses；group 只在 present manual 含 witnesses 时创建。`formal_case_lib` absent 时不创建 `group_worker_lib`、不得声明 helper。base/merged optional role absent 时 digest 为 `null`。返回 `status: groups-ready`、manifest 及 hydrated group actions；空 plan 直接发布 verify action。

**重复与失败：** 已准备且 seal 未变时不得创建第二套同 round workspace。source/plan/dependency snapshot 漂移时停止并按 action 修复。禁止 main 手建 group 目录、调整 assignment 或在 preparing local build 运行 Dune/重编 dependency source。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","vc-proving-preparing","--run","demo-20260729000536","--round","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 12. `vc-proving-verify` 命令

**调用者与时机：** main-owned action；plan 为空，或本轮没有 annotation 缺口且全部 group accepted。

**参数：** `--run`、`--round` 必需。

**作用与返回：** 重验全部 seal，按 accepted plan 机械合并实际 present 的 manual/lib，只运行一次 parent goal-check/full Coq，写 `proving_merged_result.json`。manual/lib 都 absent 时仍强制该检查，不制造 candidate 文件。通过后发布 `final-apply`；失败发布 annotation 或 vc-checking retry。本轮只要有一个结构合法的 annotation-gap blocked group，就不发布或调用本入口：controller 统一创建 annotation retry，不做 mechanical merge；全部 group seal 保留在 `reuse_group_artifacts.groups`，其中 accepted proof 满足语义指纹时可 direct，结构合法 blocked proof 最多 partial，helper 从头证明。

**重复与失败：** 已完成结果由 state 与结果 seal 识别，不再次运行相同 candidate。parent 失败不能直接重跑同一 candidate，必须走 controller 返回的 retry。禁止 main 手工 merge、逐 group 代替 parent 或绕过 failed result。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","vc-proving-verify","--run","demo-20260729000536","--round","demo-vc-proving-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 13. `symexec` 命令

**调用者与时机：** annotation owner；只在当前 claimed/running annotation round，按 handoff 调用。

**参数：** `--run`、`--round` 必需。

**作用与返回：** 重验 before seal，使用 init 持久化的 exact `target_files` 和 active theory，并从 sealed C path 重新解析显式 collection/target profile、quoted include 与 annotation strategy graph，生成有序 include/SLP 参数，再事务式刷新 generated roles；失败恢复调用前 presence 与 exact bytes。不得从 C stem 猜 formal identity，也不得使用全局固定 `QCP_demos_LLM` 配置。返回 driver 结果、freshness/transaction 证据和 `status`。

**成功标准：** exit 0 且 JSON `status: passed`。空输出、会话首次让出或外层 `Script completed` 不算通过。

**重复与失败：** 修正允许的 annotation/spec 后原样重跑。禁止 raw symexec、手改 generated files、换 include/logic path、删除已证明 manual 或绕开事务。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","symexec","--run","demo-20260729000536","--round","demo-annotation-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 14. `coq-check` 命令

**调用者与时机：** annotation owner 或 group owner；只执行 handoff 给出的目标。

**参数：**

| 参数 | 必需 | 取值 |
|---|---:|---|
| `--run` | 是 | 当前 run |
| `--round` | 是 | 当前 claimed round |
| `--target-kind` | 是 | `formal-case-lib`（仅 lib present）、`group-development`、`group-check` |
| `--group` | 条件必需 | 两个 group target 必须使用 handoff group |

**作用与返回：** 通过统一 local plan stage/编译 current closure，直接读取 accepted selected snapshot 指定的 dependency `.vo`（Dune `_build/default` 或 Makefile main-root base）。formal-case-lib 模式先执行一次 selected exact lib preparation；proving/group 模式只重验既有 snapshot，不运行 Dune、Make 或 `coqdep`。返回 `status`、Rocq结果、mode-specific `dependency_mode`、复用计数和 `current_compile_seconds`。

**成功标准：** exit 0 且 `status: passed`。development/exact 只是 owner 提前反馈；最终 group acceptance 仍由 finalize validation 决定。

**重复与失败：** 修改当前 owner 允许的 formal 文件后原样重跑。若 group import 不在 snapshot 中，返回 annotation 形成新 accepted version；不得原地扩展依赖。禁止 raw `coqc`、内部模块、换 build、复制/重编 dependency source、使用另一 group 或把 development 当 acceptance。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","coq-check","--run","demo-20260729000536","--round","demo-vc-proving-r1","--target-kind","group-check","--group","group1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 15. `coq-debug` 命令

**调用者与时机：** vc-checking owner 或 group owner；已按 handoff 写好唯一允许的 debug script 后调用。

**参数：** `--run`、`--round` 必需；group 场景使用 `--group`。

**作用与返回：** 重验 script、target、manifest、版本、accepted selected dependency snapshot 和 build seal，在 controller-owned build 中运行 Rocq debug。controller 把唯一授权 script 规范化为 build 内的 fixed absolute path；同一绝对路径同时用于普通文件/digest 校验和 `coqtop -l`，并在 child 退出后重验 digest。返回 `status`、授权路径、实际 load argument、解析路径、script digest、目标覆盖、build receipt 和 current 编译计时；三条路径不一致时在启动前失败，script 运行中漂移时不接纳。debug 不重新运行 Dune、Make、`coqdep` 或解析依赖。

**重复与失败：** debug script 不变时可重复；修改只限交接指定路径。禁止额外目标、`Load`、手工 load path、扫描未绑定历史或把 `Show.` 结果当 proof acceptance。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","coq-debug","--run","demo-20260729000536","--round","demo-vc-checking-r1"],"cwd":"/workspace/qcp-binary-democases"}
```

### 16. `final-apply` 命令

**调用者与时机：** main-owned action；parent verify 已接纳 candidate。

**参数：** `--run` 必需。

**作用与返回：** 重验 annotation、manifest、已有 group、parent result 和 candidate seal，通过持久事务备份并原子写回实际 present 的 manual 和/或 `formal_case_lib`。两个 optional candidate 都 absent 时，零 target transaction 合法，仍完成来源重验和 phase 转移。成功后 phase 进入 final-check。fixed path、backup digest 与原子替换约束每个 exact target。

**重复与失败：** 同一事务只继续或回滚，不覆盖最初 backup。每次 recovery/rollback 都要求 transaction records 与本次 exact 0/1/2 个 candidate、accepted original seals、固定 target 和 `reports/<run>/final-check/backup/<transaction-id>/` 完全一致；零 target 只能有空 records。任何额外/缺失 record、路径或 digest 注入都停止而不执行 rollback。来源漂移时在写 root 前停止；部分写入时用同一 backup 恢复。禁止从 group/stale report 手工复制、建立另一 backup 或跳过来源检查。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","final-apply","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 17. `final-check` 命令

**调用者与时机：** main-owned action；`final-apply` 成功后。

**参数：** `--run` 必需。

**作用与返回：** 执行独立 symexec freshness、main-root full Rocq、present manual/适用三级 lib/禁用规则和副产物清理。present `formal_case_lib` 即使未被 goal-check 引用，也作为独立 root 审计 import；只禁止触达本 run 四个 exact generated identities，包含当前 missing leaf，其他 project import 必须属于 accepted dependency snapshot。该审计只读 source 与 snapshot，不运行 Dune、Make、`coqdep`、`coqc` 或编译。manual absent 时 freshness/full Coq 仍强制，goal-check 导入 missing manual 必须失败。cleanup 覆盖所有 exact current module identities 的同名副产物，即使 optional source absent；broken symlink/非普通 leaf 不能按 missing 放过。全部通过后写 `phase: done`。

**重复与失败：** 已完成的 final result 由 state/seal 判断。失败会尝试 rollback；rollback 成功后必须先执行新的 `final-apply` action，不能直接重跑 final-check。禁止手工清理、运行 Dune 或自行重编 dependency source。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","final-check","--run","demo-20260729000536"],"cwd":"/workspace/qcp-binary-democases"}
```

### 18. `validate-artifact` 命令

**调用者与时机：** 维护者或诊断工具；验证一个公开 JSON artifact，不推进 run。

**参数：**

| 参数 | 必需 | 取值 |
|---|---:|---|
| `--kind` | 是 | `agent-report`、`group-worker-report`、`manifest`、`group-plan`、`merge-result`、`controller-state`、`run-log` |
| `--path` | 是 | 待验证文件 |

此入口不使用 `--run`。

**返回与成功：** JSON `status: valid|invalid`、`errors`、`path`；valid exit 0，invalid exit 1。

**重复与失败：** 纯验证，可重复。只能用于诊断，不能替代 `finalize-delivery`、phase check、parent 或 final，也不能把 valid artifact 自动写入 state。

```json
{"argv":["/workspace/qcp-binary-democases/.venv/bin/python","/workspace/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py","--main-root","/workspace/qcp-binary-democases","validate-artifact","--kind","group-plan","--path","/workspace/qcp-binary-democases/reports/demo-20260729000536/rounds/demo-vc-checking-r1/group_plan.json"],"cwd":"/workspace/qcp-binary-democases"}
```

## 三、维护与防漂移

`controller.py` 的 parser 是命令名、required/optional 参数、choices 和默认值的代码权威。`public_command_schema()` 可供外部回归导出 schema；回归必须检查：

- parser 的 18 个 subcommand 在本文全部出现；
- required/optional 与 choices 一致；
- action builder 能为所有 main-owned action 生成完整 invocation；
- spawn/append、claim 和 waiting delivery 能生成完整 claim/finalize invocation；
- 新增或删除入口时，文档覆盖测试先失败。

main 的正常执行仍不调用 schema，也不依赖 `--help`。维护者更新 parser、统一 invocation builder、本文和外部回归时，四者必须在同一个改动中完成。
