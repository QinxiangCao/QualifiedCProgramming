# Final-apply 与终检流程

本流程只由 main agent 执行，不启动 subagent。controller 只接受 `proving_merged_result.json` 为 `passed` 且 parent full check 已通过的 candidate。

## 一、写回前来源检查

首次触碰 main root formal target 前，controller 依次重验：

1. accepted annotation 的 target C；
2. annotation `after_snapshot`；
3. current target C 与 persisted `target_files` 中各 formal/generated role 的 present/missing 状态和 present bytes 是否仍为 accepted annotation 的交付结果；
4. parent merge result 的完整 digest；
5. 每个已存在 accepted group 的 report、copied manual 和适用时的 `group_worker_lib` digest；
6. candidate manual 与 `proving_merged_lib` 的 per-role digest；optional role absent 时为 `null`。

`group_worker_output.md` 等可选说明不在封存范围内。缺少 `after_snapshot`、路径无效、JSON 无法解析或任一 digest 漂移时，controller 写入明确 blocker，并在修改 formal target 前停止。

这一步防止把未接纳的 optional manual/lib 当成 rollback original，也防止只替换 present formal 文件来掩盖 goal、auto 或 check 漂移。

## 二、`final-apply`

来源必须位于：

```text
verification_runs/<run>/<round>/proving_merged/
```

controller 只写回实际 present 的 candidate：

- 合并后的 manual → main root 正式 manual；
- `proving_merged_lib` → main root `formal_case_lib`。

任一 optional role absent 时不创建 target 或 placeholder；两者都 absent 时，零 target transaction 合法，但 controller 仍完成来源重验和 phase 转移。target C 和其他 generated files 保留 accepted annotation 的 main root 版本，不从 group 或 merged directory 复制。apply/rollback 由 fixed exact paths、backup digests 与原子替换约束。

### 持久事务

apply 使用固定状态转移：

```text
prepared → backed-up → completed
```

1. `prepared`：把 source、target、candidate digest、original 是否存在及其 digest 写入 state。
2. `backed-up`：在 `reports/<run>/final-check/backup/<transaction-id>/` 建立不可覆盖的唯一 backup。
3. `completed`：逐个 target 原子替换并记录完成。

中断后只能核对并继续同一事务，或用同一 backup 回滚。不得建立新 backup 覆盖最初 original。

每次 recovery、reentry 或 rollback 前，controller 都重新推导本次 accepted proving 的 exact 0/1/2 个 candidate，并严格绑定 transaction：record 集合与顺序不能多、少或重复；source、target、relative path、candidate digest、original presence/digest、transaction id 和 backup path 必须与 current run、accepted seals 及固定 backup topology 完全一致。零 target transaction 只能有空 records。任一字段被注入、路径跨 run、原始 digest 不等于 accepted annotation seal 或 backup topology 异常时，controller 不执行 rollback；该状态以 `rollback-failed` 终止，避免让损坏记录成为删除或恢复任意 main-root 文件的授权。

已有 `backed-up` 或 `completed` 事务再次进入时，每个 formal target 只能是封存的 original 或 candidate。若此时 annotation、candidate、manifest 或 group seal 失败，controller 先用同一 backup 回滚可能的部分写回，再持久化 `blocked`。

apply 复制失败或 final-check 失败时也只使用事务内的 backup。即使 target leaf 被换成 symlink，rollback 也只替换或删除该目录项，不访问外部指向。

不得直接从 group directory、annotation history 或 stale report 采用文件。

## 三、新鲜度检查

controller 在以下目录重新运行 canonical symexec：

```text
reports/<run>/final-check/symexec-refresh/
```

该检查复用 annotation clean-output 的实现，但不覆盖已经证明的 manual。

比较内容：

- fresh goal、auto、goal-check 与 main root 完全一致；
- raw fresh manual present 时直接解析；
- raw fresh manual 与 proved manual 都 present 时 declaration 顺序一致；
- manual present 时 top-level VC 名称和 statement 一致；
- manual present 时 split-goal 名称和 statement 一致；
- current target C digest 等于 accepted annotation `source_version`；
- goal、auto、goal-check 等 final-apply 不会替换的文件仍等于 sealed annotation history。

proved manual present 时，其 proof body 本来就与 raw manual 不同，因此不比较 proof body digest，也不额外生成另一个 manual artifact。annotation 接纳时的 clean replay 只阻止不稳定 obligations 进入 proving，不能代替这里对最终 candidate 的检查。

final applied manual 与 `formal_case_lib` 若 present，预期不同于 annotation bundle，分别与 accepted proving candidate 比较；absent role 的 candidate/applied digest 都必须为 `null`，不能创建 placeholder，也不能错误地要求 optional role 等于 annotation 版本。

零 manual VC 时，manual 可以 absent；若 present，raw 与 proved manual 都只能有 generated import 与作用域命令，且 declaration 列表同为空。无论 manual 是否存在，freshness、goal、auto、goal-check、accepted annotation 来源和 parent/full Coq 检查都不减少；goal-check 若导入 missing manual，检查必须失败。

## 四、Main-root Rocq 检查

controller 通过固定 `coq-check` 检查 main root：

- 工作区：main root；
- build：`verification_runs/<run>/_coq_builds/final-check/src`；
- 目标：相对 root 的 goal check；
- target kind：`check`；
- version：current `source_goal_version`。

`coqc`、`coqtop` 来自显式环境变量或 PATH；accepted dependencies 来自 selected build output。main agent 不手写 flags，不直接调用内部模块、Dune、Make、`coqdep` 或 raw Coq。

main 只执行 `step` 返回的 `final-check` action 中的完整 `invocation.argv`，工作目录使用 `invocation.cwd`。不要根据本文示意手拼命令。

人类首次启动 controller 时使用根级 `uv run --frozen --python 3.12 python`。本阶段的 action 已绑定通过门禁的绝对 `sys.executable`，main 不替换它，也不在 action 外再次嵌套 uv。

### 已接纳的 selected dependency snapshot

accepted annotation 后的 `dune-build` action 已按 `_build` directory 判定选择 Dune 或 Makefile 后端，对 exact goal-check 完成依赖发现和过期重建，并把固定版本写入 run 根的 `dune_dependency_snapshot.json` 或 `makefile_dependency_snapshot.json`。final-check：

- 只 stage applied current 的 exact snapshot closure；
- dependency `.v/.vo` 不复制进 local build；
- dependency `.vo` 从 selected base 的绝对 load path 读取：Dune 为 `_build/default`，Makefile 为 main-root `Rocq/`；
- case 身份只取 persisted `target_files`，其中 `--case` 是 authoritative formal stem；
- current ownership 只包含本 run exact 五个 canonical artifact identities；其中实际可达的 generated artifacts 与 editable `formal_case_lib` 才会 stage；
- fixed broad selected-base mappings 保持不变，build-local current exact mapping 始终最后加入；
- current dependency 必须先有本 build local `.vo`。

shared/异名 lib 不因位于同目录或被当前 goal import 就成为 editable current lib；它们只有在 accepted snapshot 中才是可读 dependency。final 验证 snapshot、dependency source/artifact、selected configuration 与适用时的 run Makefile digests，直接复用相应 `.vo`；不运行 Dune、Make、`coqdep`，不重新解析 dependency graph，不在 final 内编译 dependency source。

dependency 缺失/漂移、snapshot 外 project import、current edge 改变或 current local artifact 不一致都必须返回精确失败。不得回退到 whole-workspace Dune target、仓库 Make aggregate target、整库 mirror、source-tree 旧 current artifact或 check 内编译 dependency source。

## 五、Manual 与三级 lib

必须同时满足：

- present manual 不含 `Admitted.`、额外 `Axiom`、helper 或禁用的顶层 declaration。
- present manual declaration 名称、顺序和 statement hash 与 `source_goal_version` 一致。
- `target_witnesses` 为空时，manual absent，或只含 generated import 与作用域命令的 present manual、空 proof route 和 `group_count: 0` 都合法；这不减少 parent full check 或本阶段的任何检查。
- 全部 top-level VC 已完成。
- `aggressive_pre_process` 的全部 split goals 已完成，top-level proof 使用该 `proof_mode`。
- 只有 accepted manifest 标为 `LLM_pre_process` 的原始 split-goal block 可保留 `Abort.`。
- present `formal_case_lib` 不含 `Admitted.`、额外 `Axiom` 或禁用 lemma。
- present `formal_case_lib` digest 等于 accepted `proving_merged_lib`；absent 时二者 digest 均为 `null`。
- present `formal_case_lib` 即使未被 goal-check 引用，也作为独立 root 审计 import；不得触达本 run `target_files` 中任一 exact generated identity，无论该 generated leaf present 或 missing。其他 project import 必须属于 accepted dependency snapshot；不得用 namespace regex 扩大禁止范围。该审计只解析 source 与 snapshot，不运行 Dune、Make、`coqdep`、`coqc` 或编译。
- lib present 时，merged helper 可追踪到 `group_worker_lib` 和 `proving_merged_result.json`；lib absent 时不得存在 helper 或 `group_worker_lib`。
- present manual 不使用禁用 lemma。

accepted group manifest 用 plan digest 绑定 assignment。accepted plan 顺序决定机械 merge；`dispatch_order` 只决定调度，不参与 candidate。

同名且 declaration/proof token 一致的 helper 只保留一份。同名 token 不一致时，frozen public/reuse block 优先；没有时取 plan 首项。其余合法 variant 只在 merged candidate 中换成唯一 current-group suffix 名称，并同步改写该 group 的新增 helper closure 和 assigned proof references。sealed group 文件保持不变，改写后的 candidate 必须已经通过 parent full check。

run root `public_helper_lemma_lib.v` 的 path、digest 和 count 必须与 controller state 一致。它不 import、不作为 active case lib 编译，也不写回 main root。

## 六、副产物清理

final-check 开始时，controller 只删除：

- persisted `target_files` 中所有 exact current module identities 的旧 `.vo/.vos/.vok/.glob/.aux`；即使 optional source absent，其同名旧副产物也在边界内；
- current run 非 `_coq_builds` 区域中的同类旧副产物。

只记录删除数量。accepted dependency `.vo` 必须保留：Dune 模式位于 `_build/default`，Makefile 模式为 main-root trusted-base `.vo`。broken symlink、目录、FIFO 或其他非普通 side-product leaf 不能伪装成 absent；无法安全移除时计为 cleanup error。

新鲜度、Rocq 和结构检查后，再扫描同一 target/run 边界。新产生或无法删除的 target 副产物使清理失败。state 与输出只保存：

- 删除数；
- 错误数；
- 残留数；
- 首个错误或残留路径。

不得删除正式交付文件、基础 `.vo`、controller state、run log、annotation attempt 文件、annotation history、round/group report 或 merge result。agent 不手工清理。

## 七、单 run 执行边界

main 每次只执行 `step` 当前给出的一个 controller action，并保持同一终端会话直到进程退出。controller 不创建 state、formal、workspace 或 selected build artifact 的同步文件。state 使用 generation compare-and-swap 与原子替换；final formal mutation 使用持久 backup transaction、digest seal 和原子替换。多个 run 同时修改同一 main root 不在本合同范围内。

## 八、失败与恢复

任一新鲜度、Rocq、结构、lib、禁用 lemma 或清理项失败，controller 都尝试 rollback。

rollback 成功：

1. phase 回到 `final-candidate-apply`；
2. main agent 执行 `step`；
3. 执行 controller 返回的 `final-apply`；
4. 只有重新 apply 成功后才能再次 final-check。

不得在已经回滚的 main root 上直接重跑 final-check。

新的 `final-apply` 会在建立 backup 或写 root 前重新验证 accepted annotation、parent result、manifest 和 group seals。若原失败来自这些来源文件，入口用既有 `blocked` 状态消费 action，并保持回滚后的 formal bytes；不会再次进入 final-check 或循环抛出同一错误。

rollback 失败时停止自动恢复，保留明确 blocker。

只有全部项目通过，controller 才把 run 置为 `done`。
