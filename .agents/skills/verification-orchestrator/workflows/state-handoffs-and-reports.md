# 状态、交接与报告

`controller_state.json` 是当前唯一状态权威。Markdown 负责给人和 agent 说明任务；JSON 只保存 controller 必须读取的状态、计划、封存和最终结果。

## 核心术语与权威来源

| 术语 | 含义 |
|---|---|
| `main root` | 仓库根目录；正式 C、generated files 和 Rocq formal files 的当前状态 |
| `run root` | `verification_runs/<run>/`；build、annotation history、group copies 与 merge candidate |
| `report root` | `reports/<run>/`；state、event、timing、交接和结果 |
| `round` | 一次 annotation 修改迭代、一次 vc-checking attempt 或一次 controller-owned proving preparing |
| `split goal` | raw manual 中的 `<vc>_split_goal_*` declaration；aggressive 路线的正式子目标 |
| `proof_mode` | 只能是 `aggressive_pre_process` 或 `LLM_pre_process` |
| `source_version` | 按 relative path 与 digest 绑定 annotation 源文件，不保存 absolute path |
| `source_goal_version` | 绑定四个 raw generated records、目标与 split mapping、statement hash、goal symbol 和 `formal_case_lib` 相关语义指纹 |
| `case` | `--case`；run id stem 与唯一 authoritative Rocq/generated formal stem，必须是合法 Rocq identifier，不能从 C stem 或目录名替代 |
| `target_files` | `init-run` 一次解析的九字段 C/formal path、case 与 active theory mapping；同时写入不可重写的 `controller_target_topology.json` anchor，每次加载都从 fixed C/case 重算并三方核对 |

`formal_case_lib` 和 `proof_manual_file` 是候选角色，可以 missing；optional role 的 version/digest 用
present/missing 与 `null` 表示，不能创建 placeholder。main root `formal_case_lib`、适用时的
`group_worker_lib`、适用时的 `proving_merged_lib` 是三级 active lib；共享/异名 lib 属于 selected backend
dependency。`public_helper_lemma_lib.v` 只是 controller-owned、append-only 的跨轮候选目录，不是第四种
active lib。

## 一、固定目录

```text
verification_runs/<run>/
  dune_dependency_snapshot.json       # `_build/` present 的 Dune 模式
  makefile_dependency_snapshot.json   # `_build/` absent 的 Makefile 模式
  Makefile                            # 仅 Makefile 模式；exact trusted-base plan
  _coq_builds/
    current/
  public_helper_lemma_lib.v
  annotation_history/<attempt-id>/
    before/
    after/
  <case>-vc-proving-rN/
    base_manifest.json
    public_helper_snapshot.txt
    reuse_source_raw/
    groups/group_NN__<group-id>/
      <case>_proof_manual.v
      <case>_lib.v                 # 仅 formal_case_lib present
    proving_merged/
      <case>_proof_manual.v        # 仅 proof_manual_file present
      <case>_lib.v                 # 仅 formal_case_lib present

reports/<run>/
  controller_state.json
  controller_target_topology.json
  run_logs.json
  timing_summary.json
  group_plan.json
  annotation-attempts/annotation-attemptN/
    agent_input.md
    agent_report.json
    agent_output.md
  rounds/<round-id>/
    agent_input.md
    agent_report.json
    agent_output.md
    group_plan.json
    reuse_hints/<group-id>.md
    group_workers_manifest.json
    proving_merged_result.json
    groups/<group>/
      group_worker_input.md
      group_worker_report.json
      group_worker_output.md
      proof_reuse.md
```

report root 的 `group_plan.json` 只在零 manual VC 时由 controller 写为 `{"groups": []}`；manual absent 也属于零 manual VC。普通 plan 仍位于 vc-checking round。annotation attempt 目录还可有 controller-owned `clean-output-freshness/`。它不是新阶段或新的 formal 角色。

## 二、文件职责

| 文件 | 负责者 | 内容 |
|---|---|---|
| `annotation-attemptN/agent_input.md` | attempt 1 由 controller；以后由 controller 模板加 main agent 五段总结 | 当前任务、原始 blocker 路径、允许写入、技能和 exact 命令 |
| annotation `agent_report.json` | 唯一 annotation owner | 最终状态；`blocked` 时唯一完整 blocker |
| annotation `agent_output.md` | annotation owner | 可选分析、反思与修正说明；不控制接纳 |
| `annotation_history/.../before/` | controller | agent 启动前 target C 与 persisted formal/generated roles 的不可变前态；optional role 保存 present/missing |
| `annotation_history/.../after/` | controller | finalize 预检通过时同一 role 集合的结果和聚合 seal |
| `dune_dependency_snapshot.json` | controller `dune-build`；Dune 模式 | exact goal-check 的固定 Dune dependency graph、dependency source/artifact digests、Dune configuration、case identity 与 `source_goal_version`；后续只读 |
| `makefile_dependency_snapshot.json` 与 run 根 `Makefile` | controller `dune-build`；Makefile 模式 | batched `coqdep` 的 exact graph、main-root base source/artifact digests、Make/Coq tool 与 configuration seal，以及唯一 `trusted-base` exact plan；后续检查不再解析依赖或运行 Make |
| vc-checking `agent_input.md` | controller | current version、raw targets、技能、允许写入和可选复用来源 |
| vc-checking `agent_report.json` | vc-checking owner | 最终状态 |
| vc-checking `agent_output.md` | vc-checking owner | 决策摘要：proof-mode、公共模式、VC 差异、关键路径、分组和 blocker |
| `group_plan.json` | vc-checking owner；零 manual VC 时为 controller | groups、路线、策略、difficulty 与 helper visibility；零 manual VC 时只含空 groups |
| `reuse_hints/<group-id>.md` | vc-checking owner | 仅 controller 绑定来源时的完整 declaration 复用判断 |
| `base_manifest.json` | controller preparing | current version、optional manual/lib 候选 relative paths、presence 和 seed digests；absent digest 为 `null` |
| `group_workers_manifest.json` | controller preparing | base/plan/snapshot seals、compact groups、可选 reuse seals 与 `dispatch_order` |
| `group_worker_input.md` | controller | 本组 assignment、写入边界、命令和追加修正 |
| `group_worker_report.json` | group-worker | 最终状态 |
| `group_worker_output.md` | group-worker | 通常为可选证明说明；annotation-gap 时必须是固定路径上的非空 UTF-8 普通文件，逐项记录受影响 witness 与证据，其 digest 进入 finalized `artifact_sha256` |
| `proof_reuse.md` | controller 复制 | accepted per-group reuse hint；worker 只读 |
| `public_helper_lemma_lib.v` | controller | 跨轮 helper 候选目录；不 import |
| `public_helper_snapshot.txt` | controller preparing | 当前 round 开始时 pool 的不可变 bytes |
| `reuse_source_raw/` | controller | 历史结构和语义指纹所用 present raw goal/manual/lib；stale source manifest 必须以本 round sealed bytes 为 seed，不能读取更新后的 main root |
| `proving_merged_result.json` | controller parent verify | per-role candidate digests（absent optional role 为 `null`）、group count、added declarations、可选复用统计或首个失败；annotation-gap 汇总分支不创建 |

同一事实只保存一次。可以从 state、固定目录、plan 或文件内容推导的内容，不复制到 report 或 manifest。

group 因 annotation 缺口 blocked 时，每个 `group_worker_report.json` 仍只描述自己的唯一 blocker，且
`failure_class` 必须精确为 `annotation-gap`。controller 只按该字段分类；具体缺 premise 时 `kind`
可以是 `missing-annotation-premise`，但不能用 `kind` 或自然语言替代 failure class。
controller 从 accepted plan 与本轮固定报告派生整轮汇总，按 manifest order 保留每个 group、witness、
location、message、repair boundary 以及原始 Markdown/JSON 路径；不把这些来源覆盖回 owner report，
也不只保存第一个缺口。annotation retry input 引用原文件，不复制或改写它们。

JSON 不保存：

- 整份规则；
- parent transcript；
- 完整 state 副本；
- 持久化的命令 argv、cwd 与 flags 副本；
- 预填检查结果；
- 整份 manifest 再复制；
- optional notes；
- 全部清理路径列表。

## 三、机器合同

所有机器读取的 JSON 都直接按当前字段集合校验。

### Owner 报告

成功只写：

```json
{
  "status": "completed"
}
```

`blocked` 时增加唯一 `blocker`，字段固定为：

- `failure_class`
- `kind`
- `location`
- `message`
- `repair_boundary`

版本、digest、changed files、检查结果、命令输出和 receipt 都由 controller 计算，不由 owner 复述。

对 group 而言，合法的 `failure_class: annotation-gap` blocker 是该 group 的本轮终态，不是要求 owner 在原目录
修 annotation 的 repair action。多个 group 可以各自有一个这样的 blocker；“owner report 只含一个
blocker”与“controller 汇总本轮全部 blocker”并不冲突。

### Group annotation-gap 汇总

全部计划 group 到终态后，state 的 `current_blockers` 按 manifest `order` 保存扁平记录。每条只含：

- owner 原字段：`failure_class`、`kind`、`location`、`message`、`repair_boundary`；
- controller 来源字段：`round`、`group_id`、`witnesses`、`markdown`、`json`。

`witnesses` 来自 accepted plan 中该 group 的完整 assignment；owner 的 `location` 必须命名精确
affected witness。`markdown` 与 `json` 指向本组原始报告，不能复制成 controller-owned owner report。
retry 以 proving round 为唯一 `previous_attempt`，按 plan/source 顺序把全部记录展开到同一 annotation
attempt 的 `feedback_sources`。

annotation-gap finalize 把 `group_worker_output.md` 与 JSON/manual/可选 lib 一起视为来源 artifact：文件
必须位于固定 report path、不是 symlink 或其他特殊 leaf、非空且可按 UTF-8 解码，其 digest 写入
finalized `artifact_sha256`。后续 group validation、`reuse_group_artifacts`、feedback 汇总、
`annotation-summary-ready`、首次或重复 annotation claim、重复 handoff 和 `already-retried` 返回都重验
同一路径与 digest；任何缺失、替换或内容漂移都不能继续复用或交接。

所有 group 的 report/Markdown/manual/lib seal 保存在现有 `reuse_group_artifacts.groups`；只有通过
`require_complete=False` 的 structure、ownership、route、helper/import/safety 检查者进入
`structurally_valid_groups`。annotation-gap validation 不跑 exact/full group Rocq，也不要求 unfinished
proof。previous accepted group 在 generated-goal 语义指纹一致时才可 `direct`；结构合法 blocked group
最多 `partial`。helper 的 reuse mode 必须为 `from scratch`；controller 在 reuse hint 接纳和后续消费时
机械拒绝 helper 的 `direct` 或 `partial`，不能只依赖 owner 自述。

### Group 计划

顶层只含 `groups`。

零 manual VC（包括 manual absent）时，唯一合法内容是：

```json
{
  "groups": []
}
```

此文件由 controller 写入，不属于 owner report，也不创建 vc-checking attempt。只要 present manual 中存在一个 VC，`groups` 就必须精确覆盖全部 top-level VC，不能用空数组跳过证明。group 只在 manual 有 witnesses 时出现；`formal_case_lib` absent 时 plan 不得声明 helper。

每个 group 只含：

- `id`
- `estimated_difficulty`
- `witnesses`
- 可选 `helpers`

每个 witness 必须有 `name` 和 `proof_mode`。`aggressive_pre_process` 只增加 `split_strategies`；`LLM_pre_process` 只增加整个 top-level VC 的 `strategy`。

helper 只含 `name`、`strategy`、`visibility`，其中 `visibility` 只能是 `local` 或 `public`。

不得出现 `source_goal_version`、`verified`、`depends_on` 或未定义的扩展字段。

### 合并结果

成功结果只保存：

- `status`；
- `source_goal_version`；
- manual/lib candidate digest；对应 optional role absent 时值为 `null`；
- `group_count`，零 manual VC 时为 0；
- `added_declarations`；
- 适用时的 `proof_reuse`。

失败结果再保存 `error_count`、`blocker_count` 和首个结构化 `failure`。固定路径可由 round 和目标文件推导，不重复写入。

## 四、领取与交付

state 中的 action 保持精简；controller 输出前统一 hydrate，不把绝对 argv 永久写入 `controller_state.json`。

- `main-owned-action` 增加完整 `invocation`。
- spawn/append action 增加 `role`、稳定 `owner`、绝对 `cwd` 和完整 `claim_invocation`。
- claim response 增加固定 `handoff` 和完整 `finalize_invocation`。
- running/returned delivery 在 `step.waiting_for` 中重新导出 `finalize_invocation`。

main 不根据 action 名、state 字段或文档示例拼命令。接口字段与全部入口见 [Controller CLI](../docs/controller-cli.md)。

### `claim-attempt` 命令

spawn/append action 已包含 `role`、稳定 `owner`、绝对 `cwd` 和完整 `claim_invocation`。main 直接执行该 invocation，不选择另一 owner，也不拼参数。controller 在同一次 state commit 中：

1. 确认 action 仍有效；
2. 绑定 owner；
3. 记录 started 时间；
4. 更新计时；
5. 返回原始 claim message、固定 `handoff` 和完整 `finalize_invocation`。

state 只保存 action id/kind、owner 和时间。重复消息从当前 attempt/manifest 重新渲染，不复制进 state。

group 汇总产生的 annotation retry 在首次 claim、同 owner 重复 claim 和 handoff 重新渲染前，都重验
`feedback_sources` 中每个原始 Markdown/JSON 的固定路径与 sealed digest；重验失败时不返回可发送的
handoff。该要求同样适用于 retry 已创建后重新领取，而不只适用于 `annotation-summary-ready`。

state 中的 `target_files`、attempt/report/manifest/candidate/reuse 路径都不是独立授权。init 以 O_EXCL 一次写入 `reports/<run>/controller_target_topology.json`，严格只保存 `run_id`、`case` 和九字段 `target_files`，以后不重写。加载 state 时，controller 先从 current run id、authoritative case、fixed C path、round 与 attempt id 重算对应 exact topology，再要求 state、target anchor 与重算值逐项相等。跨 run 或错 round 的同源目录、absolute alias、symlink/reparse parent 和特殊目录项不能因 digest 相同而被读取、写入、删除或复用。

同 owner 重复 claim 返回同一工作；不同 owner 被拒绝。

controller 的默认 owner 为：

```text
annotation/<run-id>
vc-checking/<attempt-id>
group-worker/<round-id>/<group-id>
```

annotation retry 复用 `annotation_session.owner`，group repair 复用该 group 已绑定 owner；旧 run 已经 claimed 的 owner 原样保留。

main 只能把 `handoff.prompt` 原样交给 spawn 或 append：

```text
Role: <role>
Owner: <owner>
CWD: <cwd>
Claim message (verbatim):
<claim message 原文>
```

main 不摘要、不翻译、不解释 claim message，也不读取 subagent skill 后另写一份规则。owner 自己读取角色 skill 和 claim message 指定的本次交接文件。

### `finalize-delivery` 命令

agent 真正结束且报告写完后执行。controller：

- 校验 owner；
- 校验文件仍在固定路径；
- 封存 report 及适用的 formal bytes；
- 结束 owner 工作时间；
- 直接执行 phase validation 或 group validation。

正常路径没有第二个“检查 owner 交付”的公开命令。

main 使用 claim response 已返回的 `finalize_invocation`。若上下文丢失，重新执行 `step`；running/returned delivery 会在 `waiting_for` 中重新带出同一份完整 finalize invocation。只有 owner 已停止写入后才能执行。

annotation 的 report/diff 预检失败时返回 `report-repair-required`，delivery 继续 `running`；同一 owner 修正后重跑原命令。

group 首次 preflight 因报告或 annotation-gap Markdown 合同返回 `report-repair-required` 前，controller
先把 copied manual 与适用时的 lib 冻结为临时 `repair_formal_sha256`。同一 owner 随后只能修 JSON
report/Markdown；每次再次 finalize 都先重验该 seal，formal 漂移会终止为 `invalid-report`，不能以
漂移内容重新封存。成功 finalize 后清理 `repair_formal_sha256`，不把临时 repair seal 带入终态。

若报告合同合法且 `blocker.failure_class` 精确为 `annotation-gap`，controller 封存该 group 的 report、copied
manual 与适用时的 lib，以 `require_complete=False` 完成 structure、ownership、route、helper/import/
safety 检查且不运行 exact/full group Rocq，把它记为 blocked 终态；不发布
`append-group-worker` 要求它修改超出边界的 annotation。该终态不占用并发 slot，下一次 `step` 继续
从 `dispatch_order` 发布未领取 group。

同 owner 对未漂移文件重复 finalize 幂等。group validation 由一个 controller 命令完成；系统不发布
in-flight PID marker，也不支持对同一 action 并发调用。命令在长 Rocq 检查后重新读取 state、重验相同
attempt 与全部 seal，再增量提交结果。

## 五、Annotation 持续会话

run 内唯一 `annotation_session` 保存首次 annotation target。首个 action 为 spawn；以后只能 append。

后续 annotation attempt 的 `agent_input.md` 在创建时包含 controller 固定区段和五个 `MAIN_AGENT` 区段。main agent 只能填写：

1. `Main-agent blocker conclusion`
2. `Evidence and causal analysis`
3. `Reflection on the previous annotation attempt`
4. `Required annotation repair`
5. `Scope decision`

内容必须指出具体 witness 或检查、根因链、前次错误假设、要保留内容、必需修改位置和完成标准。
只有 action 的 `consider_broader_refactor: true` 才必须回应整体重构要求；该值来自至少两次机器分类为
annotation/spec/dependency 缺口的因果重试，不来自 `annotation_iteration` 目录序号。infrastructure、
tool/report、版本授权与上下文压缩等非 annotation 根因不得把该值变为 true。

`annotation-summary-ready` 检查：

- 模板 marker 已全部替换；
- 五段都具体；
- 全部原始 Markdown/JSON 来源仍在固定路径，且 bytes/digest 与 `feedback_sources` seal 一致；
- skill 路径、命令和 repeated-repair 说明未被删除；
- current version 和固定事实未改；
- input digest 已封存。

封存后修改 input 会阻止 append delivery。

## 六、重试来源

annotation `--previous-attempt` 可以指向：

- 上一次 annotation attempt；
- vc-checking attempt；
- 单个 `<vc-proving-round>:<group-id>` blocker；
- 一次含多个 annotation-gap blocked group 的 vc-proving round 汇总。

最后一种来源以 proving round 自身绑定同一轮全部 annotation 缺口；controller 只发布一次
`retry-round --phase annotation --reason group-worker-annotation-gaps --previous-attempt <vc-proving-round>`，
并把每个 group 对应 Markdown 和 JSON 的原路径按 plan/source 顺序放入同一 attempt 的
`feedback_sources`。旧文件只读，不复制覆盖。

创建 retry attempt 时，controller 用 `retry_previous_attempt` 绑定这一个完整 proving round source；
调用的 phase、reason 和 source 必须与 current action 逐项一致。相同调用在 attempt 已存在时只返回
`already-retried`，重验全部 feedback sources 后复用原 attempt，不能创建第二个 attempt；任一参数
不同或 source seal 漂移都拒绝幂等返回。

`report-repair-required`、可修 group proof 或可修 group report 不是新 round；继续相同 delivery。只有最终报告、明确取消、version mismatch、main-owned 检查失败或 `compact-error` 才进入相应重试规则。

## 七、State、event 与并发

`controller_state.json` 使用单调 `generation`。单个 controller 命令中的普通状态变更执行：

```text
读取 → 校验 → 修改 → generation CAS 写回
```

旧快照不能覆盖新 state。event 只在 state commit 成功后追加到 `run_logs.json`。event log 是 append-only JSONL，不复制整份 state。

group development、exact 和 validation 的长 Rocq 工作不整体写回检查前快照。validation：

1. 完成封存与预检；
2. 执行 Rocq；
3. 重新加载 fresh state；
4. 重验同一 attempt 与全部 seal；
5. 增量提交结果。

group owner 可以并行工作，但 main agent 按 controller action 串行执行命令；controller 不会用长检查前的
过期快照覆盖后续状态。

group 调度把 `accepted` 与合法 annotation-gap `blocked` 都视为本轮终态，但不把后者放入提前停止
集合。只要 manifest/accepted plan 仍有未终态 group 且 `max_parallel_group_workers` 下有可用 slot，
`step` 就继续 hydrate 下一个未领取 action；已出现 annotation blocker 不能把 ready group 隐藏在
`waiting_for` 后。只有全部计划 group 到终态后，controller 才检查整轮汇总：

- 汇总非空：发布唯一 annotation retry，保留 accepted 与结构合法 blocked group 的 sealed bytes，
  不产生 merge/parent verify action；
- 汇总为空且全部 accepted：发布 `vc-proving-verify`。

其他 blocker 的 report repair、proof repair、retry exhaustion 与终止规则不变，不能借 annotation
汇总路径把它们改写为 annotation gap。

controller 只支持一个 run 命令按 action 顺序执行，不创建 state、formal、workspace 或 dependency 的
同步文件，不保存 PID 占用记录，也不使用操作系统同步原语。state 使用 generation compare-and-swap
与原子替换；report/formal/build 使用 fixed path、digest seal 与原子替换。多个 run 同时修改同一 main
root 不在本合同范围内。

## 八、Timing summary

`timing_summary.json` 供人分析总体流程，不按每条 controller 命令做全局计数。零 manual VC 时没有 vc-checking 或 group-work 时间项；preparing、parent verify 与 finalization 仍正常记录。

- `run`：从创建到 done 的总墙钟。
- `annotation_attempts`：annotation work、symexec、存在时的 `formal_case_lib` selected-backend check、clean-output freshness、annotation-checking、controller validation、controller acceptance check、accepted annotation 后的 `dune-build` action。
- `rounds`：vc-checking 的 `witness-analysis`；vc-proving 的 group-work 并发区间、development/exact/group validation 和 parent verify。
- `finalization`：accepted proving 到 final-check 结束。

不记录单 witness 时间，不估算 agent 内部耗时。每项只保留 status、创建/完成时间、整体秒数和少量 stages。

## 九、性能观测

Selected dependency preparation 和每次 Coq check 都公开可核对的细分指标：

- `dune_preparation.base_artifact_count`、`current_source_count`、`rebuilt_count`、`returncode` 和四类 digest；
- `dune_preparation.elapsed_seconds`；
- Makefile receipt 还公开 `dependency_metrics`（breadth batch/process/node/source）、
  `current_cleanup` 与 `make_seconds`；
- `coq_check.current_compile_seconds`；
- `vc_checking.agent_output_metrics` 的 bytes、lines、公共模式数和 VC delta 数。

`dune-build` action 每个 accepted annotation 只执行一次。后续 Coq check 的 `dependency_mode` 按模式为
`dune-snapshot` 或 `makefile-snapshot`，且不能出现新的 Dune、Make 或 dependency-resolution 子进程；
性能判断优先看一次 selected preparation 墙钟、Make 模式有限的 batched `coqdep` process 数、实际重编数
和 current local compile 时间。state 字段名 `dune_preparation` 仅为兼容既有格式，不表示后端判断。
