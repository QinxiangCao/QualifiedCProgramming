# 单个 C Case 的验证流程

main agent 只执行 controller action、维护 owner 到 agent target 的映射并传递 claim 的原始 `handoff.prompt`。Owner 修改各自允许的文件；controller 管理状态、seal、检查、调度、merge、写回和清理。

## 1. 总流程

```text
init-run
  → step
  → annotation
      → function spec + internal predicates + C annotations + case-lib lemmas + plan
      → symexec + failed-VC comparison
      → annotation-check-round
  → dune-build
  → vc-checking
      → structural scan + independent comparison review + group plan
      → vc-checking-check-round
  → vc-proving-preparing
      → group reviews previous manual/lib
      → priority groups
      → remaining groups
      → vc-proving-verify
  → final-apply
  → final-check
  → done
```

每次 controller 命令结束后读取最终 JSON：

- `next_actions` 非空：按 action 执行；
- `waiting_for` 非空：等待相应 owner/tool 完成；
- 当前 action 消耗后两者都空：运行一次 `step`；
- `phase: done`：结束；
- controller 给出 terminal blocker：停止并报告。

不要自行推断阶段、构造命令或改 state。

## 2. Init 与固定 topology

`init-run` 固定 run/report roots、C path、formal case stem、九个 `target_files`、case-lib policy、用户提供的 formal spec、symexec profile、group limits 和 public-helper pool。Spec 权限只看 `--freeze-spec` 是否出现：出现时 formal spec 由用户提供；省略时 formal spec 由 annotation owner 编写并在当前 attempt 中修改。后续所有路径都由该 topology 重算并校验。

`formal_case_lib_policy`：

- `present`：canonical lib 必须已存在；
- `create`：canonical path 必须不存在，controller 创建 seed；
- `absent`：path 必须保持 absent。

Windows 还要遵循 [Windows 说明](../docs/windows.md)。

## 3. Annotation

每个 run 只 spawn 一个 annotation agent；所有 retry 都 append 到同一 target。

Annotation owner 在当前 attempt 内发现新的 annotation gap 时继续修改当前 attempt，不能为该 gap 结束
当前 attempt 或创建下一轮。若 owner 已返回后才以 annotation-gap 报告该问题，controller 仍把同一
attempt 重新交给同一 owner 继续；round 与 attempt 均不改变。

首次 attempt 从 `prepared` 开始。controller 创建 `annotation_plan.json` version 2：

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

没有用户 spec 时，owner 从自然语言 spec 开始，在同一 attempt 编写和修改 Rocq spec、function specs、必要 predicates、最小 C body annotations、case-lib definitions/lemmas 和 plan，运行：

```text
formal-case-lib-design
symexec
formal-case-lib                 # active case lib 时
```

Annotation agent 不编辑 proof manual、不写 proof。

有用户 spec 时，owner 保持 `spec_freeze.baseline` 一致并完成内部 annotation 与 case-lib 工作。若用户 spec 本身需要修改，owner 立即停止，不修改 spec，也不执行 `finalize-delivery`；它在 `agent_output.md` 写清函数、原因、准备修改的 `With` / `Require` / `Ensure`、修改前后含义及对用户目标的影响。main 暂停 run 并询问用户。用户确认后 main 恢复 run，执行当前 round 的 `unfreeze`，再把确认方案交回同一 owner。round 与 attempt 均不改变。

### Retry

VC-checking 或 group blocker 必须用结构化 `vcs` 给出 exact `name`、`parent` 和 `annotation_location`。`retry-round` 从 sealed source manual 把每个目标写入新 attempt 的 `failed_vcs`。新 attempt 直接是 `prepared`，controller 生成完整 handoff 并立即发布 `append-annotation-agent`；main 不填写中间总结。

Retry plan 复制上一 plan 的 `function_specs`、`loop_invariants` 和 `new_predicates`，清空 `vc_comparisons`。Owner symexec 后直接比较 sealed old statement 与 current manual：

- `resolved`：本轮修改已经消除旧缺口；
- `unresolved`：继续修改当前 attempt。

只有所有 source VC 的 result 为 `resolved` 才能 `status: ready` 和 `completed`。Agent 编写的 spec、必要 predicates、内部 annotation 和 case lib 始终在当前 attempt 可改。新的 annotation attempt 只由 VC checking 或 VC proving 的 annotation gap 创建。

### Acceptance

`annotation-check-round`：

1. 重验 sealed report/plan 与 current files；
2. 校验 plan version 2、每个函数和循环的摘要、new predicate 记录、failed-VC 覆盖与 current VC 名称；
3. 有用户 spec 且 baseline 非空时校验用户 spec；
4. 执行 pre-symexec case-lib contract/dependency/coqc；
5. 复用 exact owner-generation receipt 或重跑 transactional symexec；
6. 重新校验 comparison；
7. 执行 post-symexec case-lib check；
8. clean replay 并再次校验 comparison 与最终 manual；
9. baseline 为 `null` 时用当前 spec surface 更新用户 baseline；保存 comparison count、resolved count 和 source/current VC 名称，接纳当前 C/lib/generated files。

## 4. Dependency Preparation

`dune-build` 是公共 action 名，实际 backend 由 controller 检测。它准备 exact goal-check target 并 seal dependency snapshot。VC checking、group checks、parent verify 和 final check 使用同一 selected snapshot；owner 不选择 target 或 raw build 参数。

## 5. VC Checking

每个 vc-checking attempt 使用独立 owner。Owner 读取当前 manual 和 annotation comparisons：

1. 廉价扫描全部 top-level VC，先看无 split goal 的 whole goal；
2. 有明确缺 premise/resource 或 countermodel 时，以结构化 `vcs` 返回 annotation/spec/dependency blocker；
3. 否则全量 split-first 判断可证性并选唯一 proof mode；
4. 直接复核 comparison 指向的 current VCs；annotation result 不是证明结果；
5. 依赖新重型数学 lemma 的 current VCs 标为高风险并单独成最先运行的 group；
6. 写 `group_plan.json` 和简洁 `agent_output.md`。

`vc-checking-check-round` seal plan，重新 symexec 去除临时 `Show.`，要求 clean manual 与 owner manual 在允许差异外一致，然后接纳 plan。

## 6. Proving 调度

`vc-proving-preparing` 创建 base manifest、固定 group copies、public-helper snapshot 和 compact worker manifest。

### Proof reuse

controller 只把紧邻上一 proving round 的目录和当前可选 `proof_reuse.md` 路径交给每个实际派发的 group worker，不匹配 statement/split hash、proof mode、group id，也不比较 case-lib、dependency 或 public-helper digest来决定复用。

worker 先用 current witness/helper/predicate 名跨上一轮 group manual/lib搜索，只读取候选 declaration/proof block，并在当前 copied manual/lib 中完成实际复制或改写；可按需在 `proof_reuse.md` 简短记录直接复用、修改后复用或不复用。不要逐份通读内容重复的完整 manual。该文件缺失或为空不影响 finalize；旧 group 是否 accepted、旧名是否相同都不替代当前判断，最终一律执行当前 group 的完整 Rocq check。第一 proving round 和未实际派发的 group 不生成该文件。

### Priority batch

首次 proving 没有 comparisons，按现有 concurrency 并行派发全部 groups。

Annotation retry 后，controller 把包含 comparison `current` 的 groups 作为第一批：

- 第一批全部 accepted：再派发剩余 groups；
- 第一批出现 annotation gap：不派发剩余 groups，等待已运行/待验证的第一批交付结束后，聚合现有 blocker 并立即创建 annotation retry。

剩余 groups 仍按 `dispatch_order` 和 `max_parallel_group_workers` 派发。

### Group terminal result

`completed` group 必须通过 statement/write-boundary/helper/import/safety/proof-mode 和 exact Rocq check。Annotation gap group 可保留未完成 proof，但其 `vcs` 必须全部存在于 sealed group manual 且属于本组 top-level witness；`group_worker_output.md` 说明已有 premises、缺失结论和 repair boundary。

全部需要的 group accepted 后，`vc-proving-verify` 机械合并 manual/lib，处理 helper namespace/public helper promotion，并运行 parent full verification。

## 7. Retry 路由

- `annotation-gap`、`specification-gap`、`dependency-gap` → annotation；
- `plan-defect`、`report-defect`、`infrastructure` → vc-checking；
- group proof/report repair → 同一 group owner；
- current-file drift → accepted annotation 边界；
- 用户提供的 spec 需要修改 → 当前 attempt 停止，用户确认后 `unfreeze` 并继续；
- agent 生成的 spec 需要修改 → 当前 attempt 直接修改。

controller 只读结构化字段，不从 `message` 解析 VC 名或 retry phase。

## 8. Final

`final-apply` 事务化写回 accepted merged candidate。随后 main 完整读取并使用 `final-check` skill，执行 action 中的 `final-check`。终检验证 generated freshness、manual/lib/goal-check、proof structure、annotation backup、merge/apply receipts、dependency/public helper seals并清理 run 临时产物。

只有 controller 返回 `done` 才完成。任何 final failure 都按 controller action 修复或回滚，不手工覆盖 main-root 文件。

## 9. Pause 与恢复

用户要求停止时，对精确 active action 执行 `cancel-action`；没有 active action 时执行 `pause-run`。等待 controller-owned process 清理后停止。只有用户明确要求恢复时才执行 `resume-run`，然后继续原 action。
