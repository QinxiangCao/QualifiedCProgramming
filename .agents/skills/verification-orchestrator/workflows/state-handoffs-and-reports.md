# 状态、交接与报告

## 1. 权威数据

`verification_runs/<run>/controller_state.json` 是状态权威；`reports/<run>/controller_target_topology.json` 固定 case topology；owner report 只声明 terminal status/blocker，不声明 controller 检查结果。

主要目录：

```text
verification_runs/<run>/
  controller_state.json
  annotation_history/annotation-attemptN/{before,after}/...
  <case>-vc-proving-rN/
    base_manifest.json
    groups/group_NN__<id>/
      <case>_proof_manual.v
      <case>_lib.v                 # active lib 时

reports/<run>/
  annotation-attempts/annotation-attemptN/
    agent_input.md
    annotation_plan.json
    agent_output.md
    agent_report.json
  rounds/<round>/
    agent_input.md
    agent_output.md
    agent_report.json
    group_plan.json
    group_workers_manifest.json
    groups/group_NN__<id>/
      group_worker_input.md
      group_worker_output.md
      group_worker_report.json
      proof_reuse.md
```

所有 persisted path 都必须与 current run/round/attempt 的固定布局一致；seal 后的 source bytes 漂移会拒绝 retry、acceptance 或 merge。

## 2. Annotation state

用户 spec state：

```json
{
  "spec_freeze": {
    "functions": ["f"],
    "baseline": {}
  }
}
```

只有 `init-run --freeze-spec` 创建该 record；没有用户 spec 时 `spec_freeze` 为 `null`。用户确认修改后执行 `unfreeze`，保留 `functions` 并把 `baseline` 设为 `null`。当前 annotation attempt 接受后，controller 用已检查的当前 spec surface 更新 baseline。

每个 annotation attempt 都有 `failed_vcs`。首次 attempt 是空列表。每项 exact schema：

```json
{
  "source_attempt": "<round-or-round:group>",
  "name": "<top-level-or-split VC>",
  "parent": null,
  "annotation_location": "<C annotation point>",
  "manual": "/absolute/sealed/manual.v",
  "message": "<old gap>"
}
```

controller 验证 manual 位于 run root，VC 名称和 parent 存在。

## 3. Annotation plan version 2

Top-level exact fields：

```json
{
  "version": 2,
  "status": "planning",
  "function_specs": [],
  "loop_invariants": [],
  "new_predicates": [],
  "vc_comparisons": []
}
```

`function_specs` 对每个 C function spec 记录一句含义；`loop_invariants` 对每个 lexical loop 记录一句数学进度；`new_predicates` 只记录当前 case 实际新增的 predicate 及核心接口不足的原因。

首次 attempt 的 comparisons 必须为空。Retry 覆盖所有 `failed_vcs`，同一 `(source attempt, source name)` 只出现一次。每个 current VC 必须存在于当前 manual。Owner 直接比较 old/current proposition，记录 old gap、change 和 `resolved` / `unresolved`；`status: ready` 只接受全部 `resolved`。

Accepted annotation `main_check.vc_comparisons` 保存 comparison count、resolved count 和 source/current VC 名称。

## 4. Retry handoff

VC checking 或 VC proving 提供 annotation gap 后，annotation retry 直接从 `prepared` 开始。controller 一次生成完整 `agent_input.md`：

- assignment、target files 和 writable paths；
- 原始 sealed Markdown/JSON blocker paths；
- `failed_vcs`；
- 与当前 failed VCs 相关的 `Previous VC changes`；
- exact commands；
- completion contract。

history 来自旧 `vc_comparisons`，按时间排序，只保留同名 VC、同 parent 或 current VC 名称相关的记录。main 和 annotation agent 不维护另一份副本。

首次 annotation 使用 `spawn-annotation-agent`；retry 创建后直接使用 `append-annotation-agent`。同一 owner/target 持续复用。

## 5. Agent reports

成功：

```json
{"status": "completed"}
```

Blocked：

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "annotation-gap",
    "kind": "missing-annotation-premise",
    "vcs": [
      {
        "name": "proof_of_f_entail_wit_1_split_goal_2",
        "parent": "proof_of_f_entail_wit_1",
        "annotation_location": "outer loop exit"
      }
    ],
    "message": "<existing premises and missing conclusion>",
    "repair_boundary": "<annotation/spec boundary>"
  }
}
```

Blocker exact fields 是 `failure_class`、`kind`、`vcs`、`message`、`repair_boundary`。Group/VC-checking 的 annotation/spec/dependency blocker 必须有非空 `vcs`；controller 不从 message 猜 VC。Tool/report blocker 可以使用空 `vcs`。

合法 VC-checking classes：

- 回 annotation：`annotation-gap`、`specification-gap`、`dependency-gap`；
- 留在 VC checking：`plan-defect`、`report-defect`、`infrastructure`。

Agent 编写的 spec 在当前 attempt 中直接修改，不创建报告或新 attempt。用户 spec 需要修改时，annotation owner 不执行 `finalize-delivery`，只在 `agent_output.md` 写明方案并交回 main。用户确认并执行 `unfreeze` 后，同一 owner 在同一 attempt 中继续。

Annotation owner 自身发现的 annotation gap 也在当前 attempt 中继续修改，不新建 attempt。兼容已返回
的 annotation-gap 报告时，controller 发布 `append-annotation-agent`，仍使用原 round、attempt、owner
和 handoff 文件；owner 修复后重新写同一个 terminal report。

## 6. Group blocker 聚合

controller 只接受 sealed group manual 中存在且属于 assigned witness 的 blocker VCs。聚合 record 保留：

- round/group id；
- assigned witnesses；
- exact `vcs`；
- message/repair boundary；
- 原始 output/report paths。

首次 proving 等所有普通并发 group 到终态后聚合。Priority batch 出现 annotation gap 时不派发剩余 groups；已运行/返回的 priority work 完成后立即聚合当前 priority blockers。

`retry-round` 将每个 blocker VC 扩展成 `failed_vcs`，manual path 指向该 group 的 sealed copied manual。

## 7. Proving manifest 与上一轮材料

Compact group-worker manifest exact fields包含：

- base/group-plan/public-helper/dependency-snapshot digests；
- group ids；
- dispatch order；
- immediately previous proving round 或 `null`。

previous round id 直接取 controller state 中最近的 proving attempt；preparing 不再探测目录状态后静默清空它，也不在写完 manifest 后回读同一字段。

Proving attempt 还保存 `priority_group_ids`。所有 group 在 preparing 后都是 `prepared`；controller 不复制旧 proof、不生成报告或 `proof_reuse.md`，也不在 group state 保存 reuse 结果。

有上一 round 时，每个实际领取任务的 worker handoff 都包含上一轮目录和本组可选 `proof_reuse.md` 路径。worker 可跨旧 group搜索 current witness/helper并只读候选 proof block，自行决定复用；该 Markdown 缺失或为空都不阻断 finalize，证明是否成立仍仅由当前 group check 决定。第一轮以及未实际派发的 group 不生成该文件。

Accepted group seals report、manual 和 active group lib。Annotation-gap group还 seal `group_worker_output.md` 作为 retry source。

## 8. Owner 与 claim/finalize

Controller owner 是稳定身份：

- annotation：一个 run 一个 owner；
- vc-checking：每 attempt 独立；
- group：每 round/group 独立，repair 复用同 owner。

main 先执行 action 的 `claim_invocation`，再把返回的 `handoff.prompt` 原样发给对应 target。Owner 返回后 main 执行原 `finalize_invocation`。`report-repair-required` 使用同一 owner 和 invocation，不 spawn 新 agent。

## 9. Timing

Timing summary 分开记录 annotation attempts、owner generation、controller main refresh、clean replay、acceptance、VC checking、group work、parent verify、final apply/check。Annotation summary不记录 design revision 统计；进展由 VC comparisons 和实际 accepted proof 衡量。
