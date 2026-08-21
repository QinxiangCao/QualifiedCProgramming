# 单个验证 case 的总流程

本流程由 main agent 控制。对外唯一程序入口是：

```text
.agents/scripts/verification-orchestrator/controller.py
```

首次人工调用从仓库根使用：

```text
uv sync --frozen --python 3.12
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py ...
```

controller 在 parser 和文件写入前强制检查 Python 3.12。通过后，action 使用当前 uv 环境中已验证的绝对 `sys.executable`；main 原样执行，不替换解释器，也不再次嵌套 uv。

正式 C、generated files 和 Rocq formal files 始终以仓库根目录为当前状态。各阶段不创建 Git
隔离目录；run root 只保存历史、build、group copies 与 merge candidate。main agent 不直接调用
controller 内部模块，不自行实现状态转移，也不代替各 owner 修改其文件。

## 一、角色与固定边界

| 角色 | 主要职责 | 可写范围 |
|---|---|---|
| main agent | 执行 controller action、管理 agent target、总结 blocker、执行写回与终检 | controller 指定的 main 总结区段 |
| annotation-subagent | 设计和修正 annotation 与数学规范 | main root 目标 C、存在时的 `formal_case_lib`、本 attempt 报告；generated files 只由 `symexec` 刷新 |
| vc-checking-subagent | 分析当前 VC、选择 `proof_mode`、分组、条件式复用比较 | 当前 round 的 plan、分析、提示与 debug script |
| group-worker | 证明本组 witnesses | 固定 group 的 copied manual、`group_worker_lib`、报告与 debug script |
| controller | 状态、封存、版本、检查、调度、机械 merge、写回事务和终检 | `verification_runs/`、`reports/`、controller-owned build/output |

每个 run 只有一个持续复用的 annotation agent。后续修正只追加到同一 target。有 manual VC 时，vc-checking 与每组首次 group-worker 使用独立会话，不继承 parent transcript；没有 manual VC 时不创建这两类 agent。

main 只主动读取 orchestrator 的 `SKILL.md` 及其全部 workflow/docs、controller 明确给出的当前
材料，以及进入终检时的 final-check skill/workflow；Windows 上再读根 `AGENTS_WIN.md` 及其指向的
Windows 文档。annotation、
VC 分析和 group 证明 skill 由对应 owner 自己读取；main 不读取、总结或解释这些角色文档，也不把
parent transcript 补进交接。owner 只读自己的 skill 与 claim message 指定的本次交接文件。

三级 active lib 在 `formal_case_lib` 存在时才形成：

1. main root `formal_case_lib`；
2. group directory `group_worker_lib`；
3. `proving_merged_lib`。

`formal_case_lib` 与 `proof_manual_file` 都保留由 authoritative formal stem 生成的候选路径，但可处于 missing 状态；controller 不 seed lib、不制造 placeholder。共享或异名 lib 是 selected build backend 的 dependency，不自动成为当前 case 的 editable lib。`public_helper_lemma_lib.v` 是 controller 维护的跨轮候选目录，不 import、不直接编译，不是第四种 active lib。每个 proving round 只读开始时冻结的 `public_helper_snapshot.txt`。

## 二、主状态转移

```text
intake
  → annotation
  → annotation-check-round
  → dune-build
  → 有 manual VC：vc-checking → vc-checking-check-round
  → 无 manual VC：controller 接纳 groups: []
  → vc-proving-preparing
  → 有 group：持续派发全部 group-worker / finalize-delivery / group validation
  → accepted plan 中全部 group 达到本轮终态
      ├─ 存在 annotation 缺口：统一反馈 → 一次 annotation retry
      └─ 不存在 annotation 缺口且全部 accepted：vc-proving-verify
  → final-apply
  → final-check
  → done
```

任何阶段发现 current version 变化，都不能沿用下游结论。controller 把相关 attempt 置为 `stale`，保存机械差异，并引导回 annotation。

## 三、逐阶段说明

### 1. `init-run` 与 `step`

`init-run` 创建固定 run root、report root、`controller_state.json`、event log 和 timing summary。run root 与 report root 作为一对分配；任一侧已有同名目录时都不能复用另一侧或接管遗留内容，只能选择新的 run id 或明确失败。`--case` 同时是 run id stem 与唯一 authoritative Rocq/generated formal stem，必须是合法 Rocq identifier；C stem、目录名和 case 可以不同，同一目录可以有多个程序。目标 C 可位于 `QCP_examples/<collection>/**`，其 parent path 镜像到 `Rocq/examples/<collection>/**`。controller 只把 C path、formal directory、五个 exact artifact 候选路径、case 与 active theory 持久化为九字段 `target_files`，并以 O_EXCL 一次写入 `reports/<run>/controller_target_topology.json`；该 anchor 顶层严格只含 `run_id`、`case` 和 `target_files`，后续不重写。每次加载 state 都从 fixed C path 与 authoritative case 重算九字段，并要求 state、anchor 与重算结果逐项完全一致；后续 action 不得从 C stem 或目录重新命名 formal modules，也不能信任被替换的 persisted target path。每次 symexec 都从 sealed C path 重新计算显式 profile 与递归 include/strategy search 参数，不把它们复制为 state 字段。`--max-parallel-group-workers N` 把正整数并发上限写入 run state；未指定时为 5，后续 proving attempt 原样继承，不叠加隐藏上限。

`init-run` 的可选参数由 main 依据本次任务描述填写。任务若要求某个已有 specification、function contract 或 case lib 内容不得改动（例如“不要修改 `solver` 的 `Require`/`Ensure`”“只允许在 lib 末尾追加”），必须以 `--freeze-spec <function>` 传入相应函数名；这是该约束唯一的机械保障，仅写在任务文字里不产生任何强制力。省略时 annotation agent 可自由改写 spec。

`step` 只根据当前 state 产生下一 action，或在仍有执行中的工作时写入 `waiting_for`。不能留下既无 action、也无等待原因的状态。所有 main-owned action 都带完整 `invocation.argv` 和绝对 `invocation.cwd`；main 直接执行，不根据 action 名猜参数。

首个 annotation attempt：

- 建立唯一 annotation session；
- 创建 `annotation-attempts/annotation-attempt1/`；
- 在 agent 启动前，把目标 C、实际存在的 optional formal/generated files 及每个候选角色的 present/missing 状态封存到独立 `annotation_history/<attempt-id>/before/`；
- state 保存聚合 digest 与存在/缺失计数。

每个 annotation、vc-checking、vc-proving 和 group attempt 的 directory、report、input、output、manifest、candidate 与 reuse 路径都由 current run root、report root、round 和 attempt id 重新推导。persisted path 只是需要核对的记录，不是新的信任根；任何跨 run、错 round、absolute alias、symlink/reparse parent 或特殊目录项都在首次读取、写入、删除、复用或验证前失败，controller 不接触其指向的树。

### 2. Agent 领取与交付

每次 agent 工作都先执行 `claim-attempt`：

- spawn/append action 给出稳定 owner 和完整 `claim_invocation`；
- main 原样执行该 invocation；
- controller 原子领取 action；
- 绑定 owner；
- 记录开始时间；
- 返回从当前权威字段渲染的固定 `handoff.prompt` 与完整 `finalize_invocation`。

同 owner 重复领取幂等，其他 owner 会被拒绝。

若 annotation retry 来自 group 汇总，controller 在首次领取、同 owner 重复领取和重新渲染 handoff
前都重验全部 `feedback_sources` 的固定路径与 sealed digests；来源漂移时不交付旧 prompt。

main 只能使用以下四段 prompt spawn 或 append，不得改写 claim message：

```text
Role: <role>
Owner: <owner>
CWD: <cwd>
Claim message (verbatim):
<claim message 原文>
```

main 保存 owner 到 agent target 的映射；annotation append 和 group repair 必须使用该 owner 的既有 target。agent 确认已写完并停止修改后，main 执行 claim response 中的 `finalize_invocation`。若上下文丢失，可从下一次 `step.waiting_for` 取回。不得先 finalize，再让 agent 继续写 formal 或 report。

### 3. Annotation owner 工作

annotation owner：

1. 修改 main root 目标 C 和存在时的 `formal_case_lib`；
2. 原样运行 controller `symexec`；
3. 仅当 `formal_case_lib` 存在时原样运行 `formal-case-lib` 检查；
4. 在同一工作中执行 annotation-checking；
5. 写最终报告。

每次 owner `symexec` 前，controller 重验本 attempt 的 sealed `before`，并对 persisted `target_files` 指定的 generated roles 建立持久临时事务；事务同时保护文件 bytes 与 present/missing 状态。

manual 只有在下列情况可由 controller 移除并重新生成：

- 缺失；
- 零字节；
- 全部 top-level/split proof 仍是 generated `Admitted`/`Abort` seed；
- exact bytes 等于本 attempt sealed before manual。

最后一种情况只表示 controller 可以恢复被暂时移除的旧 bytes，不使 history 成为 proof reuse source。其他 completed/custom manual 返回 `protected-proof-manual`。

main-root symexec 失败时，事务恢复调用前各 generated role 的存在状态和 exact bytes；成功才提交。中断留下的 prepared 事务在下一次调用前恢复。

### 4. Annotation 交付和 main-owned 检查

annotation `finalize-delivery` 先机械比较：

- attempt `before`；
- main root 当前内容；
- 最终报告；
- 允许写入边界。

若返回 `report-repair-required`：

- delivery 保持 `running`；
- 不创建新 attempt；
- 不更换 owner；
- 同一 annotation agent 修正报告或允许文件；
- 重跑原 `finalize-delivery`。

预检通过后，controller 创建并封存 `after/`、report digest 和实际 changed files，随后直接完成 phase validation。

`annotation-check-round` 再由 main agent 执行：

1. main root 按 persisted `target_files` 重跑 canonical symexec；
2. 解析存在的 raw manual；manual missing 等价于零 witnesses；
3. 仅在 `formal_case_lib` present 时，先对其 exact `.vo` target 执行一次 selected backend preparation，使依赖解析与过期依赖重建完成，再执行 fixed `formal_case_lib` 本地 `coqc` 检查；
4. 在 attempt-owned clean root 重放 canonical symexec；
5. 比较 generated roles 的 present/missing 状态和 present 文件 digests；
6. manual present 时比较 declaration 顺序、top-level/split 名称与 statement；
7. 保存 `source_version` 和 `source_goal_version`。

只有这些都稳定，annotation 才被接纳。owner 检查不替代该门禁。

### 5. Selected dependency preparation（公共 action：`dune-build`）

annotation 接纳后、判断是否需要 vc-checking 前，controller 执行 main-owned `dune-build` action。该历史
action 名不代表强制使用 Dune；共享 `build_mode.py` 只检查 `<main-root>/_build`：它是目录时选择原有
Dune 后端，否则选择 lock-free Makefile 后端。一个 run 期间不得改变该目录的 present/absent。

两种模式都：

1. 使用 persisted `goal_check_file` 与 `proof_auto_file` 确定 exact current case family；
2. 只准备 exact goal-check 传递闭包，把 persisted case family 分类为 current，其余分类为 trusted-base dependency；
3. 封存 current edges、dependency source/artifact digests、build configuration、case identity 与 `source_goal_version`；
4. 快照通过后才进入 vc-checking/proving；annotation retry 接纳新版本时旧 receipt 失效并重新 preparation。

Dune 模式的既有流程保持不变：清理会与 Dune rule 冲突的 canonical `Rocq/` 普通 side products，只运行
`dune build --root <main-root> --display=short <goal-check.vo>`，从 theory dependency data 取 exact closure，
并写 `verification_runs/<run>/dune_dependency_snapshot.json`；dependency `.vo` 位于 `_build/default`。

Makefile 模式只在 annotation 临时 lib preparation 和本阶段运行 breadth-batched `coqdep`，生成唯一 goal
为 `trusted-base` 的 exact standalone Makefile。正式 action 原子写 run 根 `Makefile` 与
`makefile_dependency_snapshot.json`；它拒绝仓库 aggregate goal、清除递归 Make/flag 注入、以
`.NOTPARALLEL` 顺序更新 main-root trusted-base `.vo`，并且只清理 exact current family 的旧
side products。它不使用旧的全局 Make target、per-source resolver 或任何 lock。

进入 proving 后，development、exact、validation、parent、debug 和 final 都只校验并复用 selected
snapshot 与对应 `.vo`，不再调用 Dune、Make 或 `coqdep`，也不再解析 dependency graph。local
`_coq_builds` 只编译 current case。worker 或 debug script 若增加快照外 project import，经 annotation
retry 形成新 accepted source 与新快照；不得在 group 内动态扩展依赖版本。

同一 controller action 的同一无副作用区间只完整校验一次 selected receipt；后续直接复用返回的
snapshot、dependency 摘要、已读取 current source bytes 和 debug build 摘要，不重复读取、散列或解析
相同输入。经过会改写已校验输入的 build/Rocq 步骤、state reload 或独立后置接纳边界时仍重新校验。
该复用只存在于当前进程，不增加持久 cache、freshness database 或新 handoff 字段；state 字段
`dune_preparation` 只因兼容历史 wire format 保留名称。

### 6. VC 分析与接纳

`source_goal_version.target_witnesses` 为空表示 symbolic execution 已经完成全部 VC。manual missing，或 present manual 只含 generated import 与作用域命令，都是合法结果。controller 此时在 report root 写入标准 `{"groups": []}` 并直接接纳，不创建 vc-checking attempt、agent 交接、reuse hint 或 debug script，也不制造 manual。goal-check 与后续 parent/final full Coq 仍强制；若 goal-check 导入缺失 manual，检查必须失败。

至少有一个 top-level VC 时，controller 才创建独立 vc-checking attempt。subagent 只读 main root 当前 formal files，输出：

- `group_plan.json`；
- `agent_output.md`；
- owner report；
- 仅在绑定封存来源时的 reuse hints 与 debug scripts。

分析顺序固定为：先只判断全部 split goals；全部可证的父 VC 直接选择 `aggressive_pre_process`，否则再分析整个父 VC并选择 `LLM_pre_process`；随后只为 aggressive split goals 或 `LLM_pre_process` top-level VC 分析证明思路和复用；最后按这些思路分配 top-level VC，split goals 始终随父 VC 进入同一 group。

proof mode 全部确定后，vc-checking 还要做第二次负载、耦合与预计关键路径审查：可独立的
final-result 与 transition/safety 拆组，确实不可拆时记录 helper/context 耦合；
`max_witnesses_per_group` 只是硬上限，不替代这次审查。

只有 controller 明确绑定正好上一封存 proving source 时才能比较复用，固定顺序是全部 helper、全部
aggressive split goals、全部 `LLM_pre_process` top-level VC。proof 的 `direct` 只来自 previous
accepted group，且 current/previous generated-goal 语义指纹一致；其他完整来源最多标为 `partial`，
helper 必须为 `from scratch`。controller 对 helper reuse mode 执行机器门禁，拒绝 `direct` 或
`partial`；未绑定时不得扫描其他历史 round。

`finalize-delivery` 封存 owner 报告后，`vc-checking-check-round` 机械验证：

- current version；
- 顶层 VC 精确覆盖；
- 每个 `proof_mode`；
- aggressive `split_strategies` 顺序；
- 1 到 5 的 `estimated_difficulty`；
- owner-suffixed helper 与 `visibility`；
- group 硬上限；
- 条件式 reuse hints、source range、语义指纹和 debug 结果。

controller 只在 state 保存 plan path、digest 和 current version，不改写 owner plan。关键路径和分组理由留在 `agent_output.md`，不增加脆弱的自然语言解析。

`agent_output.md` 使用决策摘要：公共证明模式只定义一次，每个 VC 只写 pattern reference 和实际差异；proof-mode、分组、关键路径和 blocker 保留。不得重复 handoff、完整 schema、controller 命令或相同证明步骤。controller 记录 bytes、lines、pattern 数和 VC delta 数，但这些统计不参与接纳；严格机器合同仍是完整 `group_plan.json`。

### 7. `vc-proving-preparing` 阶段

controller 重验 accepted plan 和 durable public pool，然后只在 present manual 含 witnesses 时一次创建全部 group：

- `base_manifest.json`；
- 固定 group directories 和 copied files；
- round-local `public_helper_snapshot.txt`；
- 适用时的 `reuse_source_raw/` 与 reference debug build；
- compact `group_workers_manifest.json`；
- 每组 `group_worker_input.md` 和可选 `proof_reuse.md`。

manifest 只保存不能从固定目录、base 或 accepted plan 推导的摘要和 seal。路径、assignment、route、namespace 与命令在读取时统一派生。

上一 proving round 已 stale 但被绑定为复用来源时，controller 解析其 manifest 必须显式使用该 source
round 已封存的 `reuse_source_raw` seed；不得用 annotation 修改后的 main-root raw files 重新解释旧
manifest、witness 或语义指纹。

accepted plan 顺序决定稳定 group 编号与机械 merge。`dispatch_order` 只用于填并发 slot，按无可复用单元优先、difficulty 降序、结构负载降序和 plan index 计算，不表示依赖。

空 plan 仍建立 base、public snapshot、适用的 raw source、`proving_merged/` 和 compact manifest；manifest 的 `groups`、`dispatch_order` 都是空数组。base/merged 中 optional manual/lib 缺失时对应 digest 为 `null`。controller 随即发布 `vc-proving-verify`，不发布 group action。

### 8. Group 调度、交付与 validation

本节只适用于非空 plan。所有 group 在机器调度上独立，不含 `depends_on`。controller 按 `dispatch_order` 和 run 中的并发上限填可用 slot。

每次 group delivery 领取前，controller 从 current state、accepted plan、base 与 manifest 重新渲染交接。升级前已准备但尚未领取的 group 也能获得当前规则。

worker 可按需运行 development 或 exact check；它们只是提前反馈。worker 写最终报告后，main agent
执行 `finalize-delivery`。controller 总是先封存 report、copied manual 和适用时的
`group_worker_lib`，重验 current version、manifest/seed/public/reuse seals、写入边界、statement 与
declaration order。`completed` delivery 再检查 ownership、proof route、helper/import/safety/禁用规则，
运行 Rocq，前后重验封存并在成功后把 group 置为 accepted。`blocked` delivery 则验证 blocker 分类与
本 failure class 要求的结构；它不能因为未完成 proof 而被误标 accepted，也不能跳过可复用 bytes 的
写入边界和结构检查。

validation 在同一个 controller 命令中运行 Rocq，结束后重新加载 fresh state、重验同一 attempt 与 seal
再提交结果；不发布 PID/in-flight 标记，也不支持同一 action 的并发调用。

可修的 structure、route、proof-completeness 或 safety 问题产生 `append-group-worker`，由同一 owner 在原目录修正；其他 ready/running group 继续调度。仅报告字段错误时，只开放报告修正。封存 formal 漂移形成 `invalid-report`，不自动用漂移内容重封。

首次 group preflight 若因 report 或 Markdown 合同返回 `report-repair-required`，controller 在返回前用
`repair_formal_sha256` 冻结 copied manual 与适用时的 lib。owner 只修 report/Markdown，再次 finalize
必须保持 formal bytes 不变；成功 finalize 后 controller 清理该临时 seal。

group 以 `blocker.failure_class: annotation-gap` 报告 annotation/spec 缺口时不走原地 proof 修正，
controller 只按该 failure class 分类，不从 `kind` 或 message 猜测。数学规范、function contract、loop
invariant、assertion 和调用实例都超出 group-worker 写入边界。该 group 仍使用现有 blocker 合同：

- owner 在固定 report path 的 `group_worker_output.md` 中逐项说明本组发现与证据；controller 要求
  它是非空 UTF-8 普通文件，并把其 digest 写入 finalized `artifact_sha256`；
- controller 在 group validation、reuse、feedback 汇总、annotation summary、首次/重复 claim 与重复
  handoff 时持续重验该 Markdown 及其他 feedback source seals；
- owner 在自己的 JSON 中说明本组发现，`location` 必须命名 affected witness；controller
  使用 `require_complete=False` 检查 structure、ownership、route、helper、import 与 safety，不跑
  exact/full group Rocq，也不要求 unfinished proof。只有结构合法时才把该 group 保留为本轮的
  `blocked` 终态和 reuse source；
- controller 按 manifest order 把每个缺口保留为一条扁平 `current_blockers` 记录：owner blocker
  的 `failure_class`、`kind`、`location`、`message`、`repair_boundary`，以及 controller 绑定的
  `round`、`group_id`、`witnesses`、`markdown`、`json`。`witnesses` 是 accepted-plan group assignment，
  精确 affected witness 仍由 `location` 指明；
- 不向该 group 追加 annotation 修正工作，也不在其目录内反复尝试证明；
- 这不会停止 sibling：running group 继续完成，ready 且尚未领取的 group 仍按 `dispatch_order` 和
  并发上限继续发布，直到 accepted plan 中全部 group 达到本轮终态。不能只等待缺口出现时已经
  running 的 delivery 收尾。

全部 group 都是 `accepted` 或结构合法的 annotation-gap `blocked` 后，controller 按 manifest order
汇总本轮所有 annotation 缺口，只创建一次
`retry-round --phase annotation --reason group-worker-annotation-gaps --previous-attempt <vc-proving-round>`。
retry 把各记录展开成按 plan/source 顺序的 `feedback_sources`；新 annotation input 必须逐项链接每个
原始 `group_worker_output.md` 与 `group_worker_report.json`，使 main 的五段总结和 annotation agent 的
修正可以覆盖全部根因。只要汇总非空，本轮就不发布 `vc-proving-verify`，不做机械 merge，也不运行
parent check。

全部 group 的 report/manual/lib seal 进入现有 `reuse_group_artifacts.groups`，结构筛选保存在
`structurally_valid_groups`。下一轮只有 previous accepted group 且语义指纹相同的 proof 可以
`direct`；结构合法 annotation-gap blocked group 的 proof 最多 `partial`，helper 仍从头证明。两类 bytes
都保持封存，历史来源只提供条件式复用，不是当前 round 的接纳依据。

其他 failure class 不参与这次汇总，仍遵循原有的同 delivery 报告修正、原地 proof 修正、
`compact-error` 耗尽或终止规则。annotation 缺口只改变本轮继续调度和统一反馈的时机，不放宽任何
group report、结构或封存检查。

accepted group 的 planned public helper 通过 before/after digest 事务追加到 durable pool，只供未来 round。pool 合同校验、append 基线和 round snapshot copy 复用同一次读取的 exact bytes；原子替换前后的 digest 门禁不省略。当前 round 的 sibling 仍使用冻结 snapshot。

`formal_case_lib` absent 时，plan 不得声明 helper，preparing 不创建 `group_worker_lib`，worker 不得修改共享/异名 lib。同一 owner 对同一个 group development workspace 顺序执行 development、debug 与 exact/validation 命令。

### 9. `vc-proving-verify` 阶段

accepted plan 本来为空，或本轮没有 annotation 缺口且全部 group accepted 时，controller 才发布
`vc-proving-verify` 执行：

1. 重验 current version、base/manifest/group seals；
2. 按 accepted plan 顺序机械合并 assigned proof spans；
3. 在 `formal_case_lib` present 时合并 `group_worker_lib`；
4. 对同名 helper 进行 token 一致去重或 candidate 内确定性改名；
5. 重验最终结构和禁用规则；
6. 只运行一次 parent full check；
7. 写 `proving_merged_result.json`。

parent 不逐组重复完整 Rocq。调度和完成顺序不影响 candidate。

同名 token 不一致时，frozen public/reuse canonical 优先；没有时取 plan 首项。其余合法 variant 只在 merged candidate 中使用唯一 current-group suffix，并只改写该 group 新增 lib 和 assigned proof blocks 的 exact identifier token；sealed group files不变。改写后的 candidate 必须通过 parent full check。

有 manual VC 时，parent 失败保存首个明确错误、result path 和 digest，供下一次 vc-checking 作为原始 blocker；零 manual VC 时，该错误直接返回 annotation 修正。不得直接重跑同一失败 candidate。

### 10. `final-apply` 与 `final-check`

`final-apply` 在写 main root 前重验：

- accepted annotation target C 与 `after_snapshot`；
- 当前 generated files；
- parent result；
- 全部已存在 group 的 accepted seals；
- candidate digests。

通过后，以 `prepared → backed-up → completed` 持久事务备份并原子替换实际 present 的 formal manual 和/或 `formal_case_lib`。两个 optional candidate 都 absent 时，零 target transaction 合法，但仍完成来源重验与状态转移。每次 recovery、re-entry 或 rollback 前，records 必须与 accepted 的零/一/二 candidate 集合精确绑定：不得多、缺或重复 record；source、target、relative path、candidate digest、original presence/digest、transaction id 和 backup path 必须与当前 run、accepted seal 和固定 backup topology 一致。零 target transaction 的 records 只能为空。注入、跨 run 路径、original digest 与 accepted annotation seal 不一致，或 backup topology 非法时，事务以 `rollback-failed` 终止且不执行 rollback；成功回滚的事务状态为 `rolled-back`，只有 `prepared`、`backed-up`、`rolled-back` 可以重新 apply。

`final-check` 再执行：

- 独立 symbolic execution 新鲜度；
- main root 全量 Rocq 检查；
- present manual 的 `proof_mode` 结构；
- present 时的三级 lib 与 public pool 一致性；
- 禁用 lemma；
- 独立检查 present `formal_case_lib` 不 import 本 run exact generated artifacts，且其他 project import 都属于 accepted dependency snapshot；
- 检查前后按全部 exact current module identities 清理副产物；optional source absent 也不能留下同名旧 artifact，broken symlink/非普通 leaf 必须报告 cleanup error。

cleanup 成功只记录删除数；失败只记录 error 数、residual 数和第一个错误或残留路径，不保存全部
路径清单。agent 不手工删除副产物。

失败且 rollback 成功时，先回到 `final-candidate-apply`，重新执行 `final-apply` 后才能再次终检。若来源 seal 仍异常，apply 入口以 `blocked` 停止且不修改已回滚 formal files。rollback 失败则停止自动恢复。

## 四、重试与失效

### Annotation 修正

vc-checking 的合法 `blocked` 报告必须使用固定 `failure_class`。`annotation-gap`、
`specification-gap`、`dependency-gap` 与 `source-version` 才路由 annotation；`plan-defect`、
`report-defect` 与 `infrastructure` 路由同阶段 vc-checking retry，并保留已接纳 annotation、
`source_goal_version` 与 selected dependency snapshot。controller 不从 `kind`、`message` 或 `repair_boundary` 的自然语言
推测恢复阶段；未知分类先按 invalid report 让 vc-checking 修正机器报告。

同一 accepted source/source-goal version 下，若 `infrastructure` 的 `failure_class`、`kind` 和把 round id
替换为固定占位符后的 `location` 连续三次相同，controller 不再创建第四个无进展 retry，而是清空 retry
action 并发布 `repeated-vc-checking-infrastructure-blocker`。该终态保留已接纳 annotation 与 selected
dependency snapshot，等待框架修复后从 VC-checking phase 恢复；report bytes 或 seal 无效的历史 attempt 不计入连续链。

annotation retry 创建新的独立 attempt 目录，但继续使用同一 annotation agent target。main agent 必须先阅读原始 blocker 的 Markdown 和 JSON，再在新 `agent_input.md` 的五个固定区段写：

1. 阻塞结论；
2. 依据与因果分析；
3. 前次 annotation 反思；
4. 必需修正；
5. 修正范围决定。

来源为 group annotation 缺口汇总时，main 必须阅读 controller 列出的全部原始 Markdown/JSON，五段
总结覆盖所有 group，而不是选择其中一个。`annotation-summary-ready`、首次/重复 claim 和重复 handoff
必须重验这些固定来源及其 digests；验证并封存输入后，controller 才产生一次
`append-annotation-agent`。controller 另行维护 `annotation_causal_retry_count`：只有反馈报告的机器
`failure_class` 属于 annotation/spec/dependency 缺口时才增加；infrastructure、tool/report、版本授权或
其他非 annotation 根因终止该连续计数并归零，`compact-error` 只保留原值而不增加。该计数达到 2，
也就是同一因果链至少进行第二次 annotation
修正时，才要求重新审视数学规范、function contract、loop invariant、assertion 和调用实例的整体关系；
annotation attempt 的目录序号本身不触发整体重构。

group 汇总 retry 用 `retry_previous_attempt` 绑定整个 previous proving round，且 phase、reason、source
必须与 current action 一致。同一调用重复时只在重验 feedback sources 后返回 `already-retried` 并复用
原 attempt，不创建第二个 annotation attempt。

### `compact-error` 错误

- annotation：未耗尽次数时追加到同一 agent。
- vc-checking：按 state 中的上限创建同阶段 retry。
- group：达到上限时，先按失败 round 规则封存固定 group artifacts 和结构合法集合，再写 `compact-error-retry-exhausted` blocker；不自动创建 retry，也不误标 annotation/plan。

### Version 变化

vc-checking、preparing、group validation 或 parent 发现 current version 变化时，controller 保存机械差异并引导回 annotation。group 有其他 running delivery 时，先等它们结束，再统一产生 annotation feedback。version mismatch 不是 `failure_class: annotation-gap`；current source 已 stale 时不继续派发尚未领取 group。本轮“全部 planned group 都派完”的新合同只用于合法 annotation-gap blocker，其他 failure class 的既有边界不变。

controller 按单 run、单命令执行合同工作，不创建 state、formal target、workspace 或 selected build artifact 的
锁文件，也不使用操作系统 locking API。state 仍通过 generation compare-and-swap 与原子替换拒绝 stale
whole-state write；formal/report/build 文件仍遵守 fixed path、digest seal 和原子替换合同。本文不定义
多个 run 同时修改同一 main root 的行为。

正好上一封存 proving round 若满足条件，可由 controller 绑定为下一次 vc-checking 的比较来源。它可以是 parent failed、含结构合法 blocked group，或曾 verified 后因 annotation/freshness retry 而 stale 的 round。历史 proof 只提供复用机会，不是当前接纳依据。

## 五、完成标准

controller 只有在以下条件同时成立时才能把 run 置为 `done`：

- 独立 symbolic execution freshness 通过；
- 全部 top-level VC 和 aggressive split goals 已完成，只有 `LLM_pre_process` 的原始 split blocks
  可以保留合法 `Abort.`；
- fixed goal check 与 main-root full Rocq check 通过；
- present manual 的 declaration 与 `proof_mode` 结构合法；present manual 和
  `formal_case_lib` 中没有 `Admitted.`、额外 `Axiom` 或禁用 lemma；
- present `formal_case_lib` digest 等于 accepted `proving_merged_lib`，absent 时两者 digest 都为
  `null`，三级 lib 与 public helper pool 在适用时一致；
- annotation attempts 的 `before/after` history 完整，所有采用的 formal 内容都来自 controller
  accepted candidate；
- `formal_case_lib` 的独立 import 审计、终检前后副产物清理和 final-check 全部通过；
- `controller_state.json` 的 phase 为 `done`，对应成功 event 已提交到 append-only event log。
