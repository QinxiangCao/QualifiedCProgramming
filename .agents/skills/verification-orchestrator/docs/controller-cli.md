# Controller 公共接口

公共入口共有 20 个 subcommands。以 parser 导出的 `public_command_schema()` 为准；main 使用 action 自带 invocation，不手写命令。

```text
<python> .agents/scripts/verification-orchestrator/controller.py --main-root <root> <subcommand> ...
```

## 命令表

| 命令 | 必需参数 | 作用 |
|---|---|---|
| `init-run` | `--case --target-c-file` | 创建固定 run/topology/state；其余 problem、policy、profile、group limits 和 hard spec 参数可选 |
| `step` | `--run` | 发布下一批 action 或 waiting/done/blocker |
| `pause-run` | `--run --reason` | cooperative pause |
| `cancel-action` | `--run --action --reason` | 取消精确 active action 并 pause |
| `resume-run` | `--run` | 用户明确要求后恢复 |
| `claim-attempt` | `--run --next-action --owner` | 原子认领 delivery，返回 handoff 与 finalize invocation |
| `finalize-delivery` | `--run --attempt --owner` | seal owner 交付并进入 controller validation |
| `retry-round` | `--run --phase --reason --previous-attempt` | 创建授权的 annotation/vc-checking retry |
| `unfreeze` | `--run --round` | 允许当前 attempt 修改用户提供的 spec |
| `annotation-check-round` | `--run --round` | annotation acceptance、clean replay 和 comparison 复验 |
| `vc-checking-check-round` | `--run --round` | seal group plan 并恢复 clean manual；`--group-plan` 仅绑定当前固定 path |
| `dune-build` | `--run` | 用 selected backend 准备 exact goal-check dependency snapshot |
| `vc-proving-preparing` | `--run --round` | 创建 groups、交接上一 proving round、计算 priority batch |
| `vc-proving-verify` | `--run --round` | merge accepted groups 并做 parent full check |
| `symexec` | `--run --round` | claimed annotation attempt 的 transactional generated refresh |
| `coq-check` | `--run --round --target-kind` | 检查 case lib、group development 或 exact group；group target 另带 `--group` |
| `coq-debug` | `--run --round` | VC manual/debug；group 模式另带 `--group` |
| `final-apply` | `--run` | 事务化写回 accepted merged candidate |
| `final-check` | `--run` | 最终 freshness、Rocq、结构、seal 和 cleanup 检查 |
| `validate-artifact` | `--kind --path` | 校验公开 JSON artifact，包括 annotation plan version 2 |

## Init

`--case` 是 authoritative Rocq/generated stem；`--target-c-file` 必须位于允许的 QCP tree。常用可选参数选择 case-lib policy、用户提供的 spec、symexec profile、group limits 和 problem/spec hints。现有 `--freeze-spec` 只要出现就表示 formal spec 由用户提供；每个名字必须精确匹配一个可抽取 spec 的 C 函数，否则 init 直接失败。省略则表示由 annotation owner 生成。Init 不接管已有同名 run/report directory。

## Claim 与 finalize

`claim-attempt` 只接受 current delivery action，返回 stable owner、role/CWD、原始 claim message、完整 `handoff.prompt` 和 `finalize_invocation`。main 保留 owner 到 agent target 的映射。Annotation retry 使用同一 target；group repair 使用同一 group target；vc-checking retry 创建独立 target。

`finalize-delivery` seal report/plan/formal copies并立即执行 phase/group validation。若返回 `report-repair-required`，沿用同一 owner/attempt 修复并重跑原 invocation。

Annotation owner 返回 annotation-gap 时不创建 retry attempt；controller 重新发布同一 attempt 的
`append-annotation-agent`，由同一 owner 在本 attempt 内继续修复。已有 `annotation-blocked` retry action
也兼容为这一同-attempt继续操作。

## Retry

`retry-round` 必须逐项匹配 current main-owned action。新的 annotation attempt 只接收 VC checking 或 VC proving 的 annotation gap：

- revalidate 所有 feedback seals；
- 从 blocker `vcs` 和 sealed manual 生成 exact `failed_vcs`；
- 继承尚未 `resolved` 的 failed VCs；
- 从旧 comparisons 渲染相关 history；
- 复制 function specs、loop invariants 和 new predicates，并清空 comparisons；
- 直接创建 `prepared` attempt 与 `append-annotation-agent` action。

重复相同 invocation 返回 `already-retried`，不创建第二个 attempt。

## Annotation 与 unfreeze

没有 `--freeze-spec` 时，function spec、内部 annotation 和 case lib 都由 annotation owner 在当前 attempt 中修改。`formal-case-lib-design` 只检查当前 C 与 case lib。

使用 `--freeze-spec` 时，annotation owner 不自行修改用户 spec；需要修改时先停止，在 `agent_output.md` 写明方案并由 main 询问用户。用户确认后，main 恢复 run 并执行 `unfreeze --run <run> --round <round>`。该命令保留 functions，把 baseline 设为 `null`，不改变 round、attempt 或 owner。

`annotation-check-round` 校验 plan version 2、用户 spec baseline、case-lib、transactional symexec、comparison 和 clean replay。baseline 为 `null` 时，全部检查通过后用当前 spec surface 更新 baseline。`unresolved`、遗漏 source 或不存在的 current VC 都交回同一 annotation owner 继续当前 attempt。

## VC checking 与 proving

`vc-checking-check-round` 要求 clean-equivalent manual 和完整 group plan。

`vc-proving-preparing` 的 compact manifest seal base manifest、group plan、public helper snapshot、dependency snapshot、group ids、dispatch order 和 previous round。它不判断或复制旧证明；所有 current groups 保持 `prepared`，再按 priority/remaining顺序派发。存在 previous round 时，实际 worker 按 current witness/helper搜索上一轮候选 proof block，无需逐份通读完整 manual；可选的 `proof_reuse.md` 缺失或为空不影响 finalize。

`vc-proving-verify` 只在当前需要的 groups 全部 accepted 时运行。

## Artifact validation

`--kind`：

```text
agent-report
group-worker-report
annotation-plan
manifest
group-plan
merge-result
controller-state
run-log
```

Blocker schema使用 `vcs`；annotation plan只接受 version 2 exact fields。

## 错误与幂等性

Command/action 不匹配、wrong owner、path topology/seal drift、current-file drift 或 artifact schema错误会明确拒绝或形成 controller blocker。按返回 action 在原边界修复，不修改 state/report seal，不重复 spawn 绕过错误。
