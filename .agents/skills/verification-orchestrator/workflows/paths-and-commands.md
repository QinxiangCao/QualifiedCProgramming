# 路径与命令

controller 拥有 executable、cwd、include/search mapping、formal relative path、overlay、build directory 和固定 flags。main 执行 action JSON 自带的 invocation；subagent 执行自己交接 Markdown 中已经渲染的命令。两者都不能手拼。

人类只在首次进入公共入口时从仓库根执行：

```text
uv sync --frozen --python 3.12
uv run --frozen --python 3.12 python .agents/scripts/verification-orchestrator/controller.py ...
```

公共入口在 parser 和写操作前拒绝任何非 3.12 解释器。之后 controller 生成的 invocation 直接使用这个已验证环境的绝对 `sys.executable`；main/owner 不把内部 action 再包进 uv。

根级 `pyproject.toml`、`uv.lock` 与 `.python-version` 只管理 agent 系统。`mcp/qcp-mcp`
保持独立 uv 项目，不共享环境。Windows 首次启动与路径差异见仓库根
`AGENTS_WIN.md` 和 [Windows 适配说明](../docs/windows.md)；它们不改变本文件的公共命令合同。

## 一、通用执行规则

1. main 对 `main-owned-action` 原样提交 `invocation.argv`，工作目录使用 `invocation.cwd`。
2. main 对 spawn/append 先原样提交 `claim_invocation.argv`，工作目录使用 `claim_invocation.cwd`。
3. annotation 读取本次独立的 `annotation-attempts/annotation-attemptN/agent_input.md`。
4. vc-checking 读取当前 round 的 `agent_input.md`。
5. group-worker 读取 `group_worker_input.md`。
6. subagent 交接中的 controller 命令必须原样到达系统终端。
7. 不抄写、不补 flag、不改 path、不换 cwd、不替换解释器。

invocation 的权威结构固定为：

```json
{
  "argv": ["/absolute/python", "/absolute/controller.py", "--main-root", "/absolute/root", "step", "--run", "case-run"],
  "cwd": "/absolute/root"
}
```

`argv` 是字符串数组，不是 shell 字符串；已经包含完整参数，不会出现 `<run>`、`<owner>` 等占位符。人类可读的 action 名只用于理解，不用于重新拼接命令。完整公共接口见 [Controller CLI](../docs/controller-cli.md)。

优先直接调用系统终端。若当前运行时仅通过 `functions.exec` 暴露终端工具，允许透明桥接，但每个单元必须：

- 只 `await` 一次 `tools.exec_command` 来启动命令，或为续接同一 live session 只调用一次 `tools.write_stdin`；运行时为同一终端操作公布的规范化等价名称也适用；
- 启动时原样传入完整命令/argv、全部参数和 cwd，续接时保留同一 session 标识，并仅转发结果；
- 只在规范化等价工具的输入形态能原样接收这些值时使用它；不得把 argv 数组序列化为 shell 字符串、重新解析已渲染命令或增添引号；
- 不构造、修改、串联、并行或解释命令，不在同一 cell 中调用第二个工具。

除此之外，禁止：

- 其他 JavaScript/Python 编排；
- 自建 shell/PowerShell/Python 脚本；
- 另一层 `uv run`；
- `sh -c`；
- 管道；
- 命令替换；
- 后台进程；
- 其他再次调用终端工具的封装。

也不得用自写脚本仿造 controller 功能。

必须保存并继续等待任何外层 cell 和内层进程/会话标识，直到实际命令退出。透明桥接若返回仍在运行的 `functions.exec` cell，只能用 `functions.wait` 恢复同一 cell，直到其中唯一一次终端操作返回。空输出、首次让出和 `Script completed` 只说明外层调用暂时结束，不表示 controller、symexec 或 Rocq 已结束。

一项检查只有同时满足以下条件才算通过：

- 终端进程退出码为 0；
- controller JSON 的 `status` 为 `passed`。

命令失败时，只修改当前阶段允许的 formal 内容或声明的 debug script，再原样重跑。路径不一致应报告 controller/交接问题，不试探另一套 path 或 flag。

## 二、固定路径安全

以下路径及其既有 ancestor/leaf 必须是 main root 内的固定非 symlink 路径：

- `verification_runs/`
- `reports/`
- formal target 文件
- annotation 历史
- round/group/report 目录
- `proving_merged`
- public helper pool 与 snapshot
- 干净刷新
- `_coq_builds`
- run 根目录按模式选择的 `dune_dependency_snapshot.json` 或
  `makefile_dependency_snapshot.json`，以及 Makefile 模式的 run 根 `Makefile`
- final backup 与 apply destinations

controller 拒绝：

- POSIX symlink；
- Windows 联接点 / 重解析点；
- 其他非普通特殊文件；
- 任何会把 state、cleanup、candidate、build 或 final apply 导向 owner 外的路径。

读取、删除、staging 和 formal 写入前都做 lexical fixed-path 检查。临时文件使用同目录不可预测名称，写入后 `fsync`，再由 `os.replace` 原子提交；不复用可被预先建立的固定 `.tmp` leaf。

controller 不创建 state、formal target、workspace 或 dependency 的同步文件，也不使用 POSIX/Windows 文件同步 API。命令按单 run action 顺序执行；generation compare-and-swap、fixed-path 检查、digest seal 和原子替换继续保护 stale write 与路径边界。多个 run 同时修改同一 main root 不在本合同范围内。

## 三、Annotation 命令与路径

交接提供类似：

```text
<handoff-python> .../controller.py --main-root <root> symexec --run <run> --round <round>
<handoff-python> .../controller.py --main-root <root> coq-check --run <run> --round <round> --target-kind formal-case-lib  # 仅 lib present
```

`<handoff-python>` 由 controller 使用已通过 Python 3.12 门禁的当前 `sys.executable` 渲染，并按当前平台正确引用。agent 不得固定改成 `python3` 或另一解释器，也不得再次包一层 `uv run`。

### Symexec 驱动程序

controller 根据运行平台选择：

| 平台 | driver |
|---|---|
| Windows | `win-binary/symexec.exe` |
| Linux | `linux-binary/symexec` |
| Apple Silicon macOS | `mac-arm64-binary/symexec` |
| Intel macOS | `mac-x86-64-binary/symexec` |

未知平台或 macOS 架构必须明确失败，不能默认使用 Linux 文件。

`--case` 是 run id stem 与唯一 authoritative Rocq/generated formal stem，必须是合法 Rocq identifier。C stem、C 所在目录名与 case 可以不同；同一目录可有多个程序，任何一个都只拥有自己 persisted mapping 中的 exact artifacts。

target C 可位于 `QCP_examples/<collection>/**`。init 以其 parent path 镜像得到 `Rocq/examples/<collection>/**`，再以 `--case` 生成 exact lib/goal/auto/manual/goal-check 候选路径；`target_files` 只持久化这组路径、C path、case 和 active theory。所有后续 snapshot、merge、Coq 和 final 只消费 persisted mapping，不得从 C stem 重算。例如 `QCP_examples/QCP_demos_LLM/3DGraphField.c --case three_d_graph_field` 对应 `Rocq/examples/QCP_demos_LLM/three_d_graph_field_*.v`，不会创建非法的 `3DGraphField_*` module。

每次 canonical symexec/clean replay 都从 sealed C path 重新解析 quoted include 与 annotation strategy graph，并确定有序 include/SLP；这些运行时 search 参数不写进 `target_files`。默认 profile 为 `LLM_bench`/`QCP_demos_LLM → QCP_demos_LLM`、`Applications_human`/`QCP_demos_human → QCP_demos_human`、`QCP_demos_tutorial → QCP_demos_tutorial`；`Applications_human/convex_hull/**` 覆盖为 LLM，`Applications_human/fme_ge_gmp/**` 覆盖为无 profile。未配置 collection 只允许 repository-wide 唯一匹配，裸 include 有多份就明确失败。比如 `LLM_bench/Engineering/string/memory.c` 递归进入 `stdlib/string.h` 后遇到裸 `verification_list.h`；human/LLM 各有一份，必须由 target 的显式 LLM profile 保留来源身份，不能靠全局 `-I QCP_demos_LLM` 或任意 basename 首选。`LLM_bench/Algorithms/convex_hull_float/**` 还加入固定 `--float-finite-vc`。不得恢复全局固定 `QCP_demos_LLM` 参数。

### `before` 与 generated refresh 事务

每个 annotation attempt 在交付前，controller 把 target C 与 persisted formal/generated roles 的当前状态一次性封存到：

```text
verification_runs/<run>/annotation_history/<attempt-id>/before/
```

state 保存聚合 digest、每个角色的候选 relative path 与 present/missing 状态；只有 present 文件有 digest。`formal_case_lib` 与 `proof_manual_file` 可 missing，controller 不 seed lib、不创建 placeholder。`before/` 是 attempt 前态与恢复边界，agent 只读，不能用 edited main root 重建或覆盖。

owner 每次调用 symexec 时，controller 先把 persisted mapping 中的 generated roles 保存到 attempt report directory 下的持久临时事务；manifest 记录事务状态、presence 与 present 文件 digest。

manual 只有在以下情况允许移除：

- 缺失；
- 零字节；
- 每个 top-level/split proof 仍分别是 generated `Admitted`/`Abort` seed；
- exact bytes 等于已重验的本 attempt sealed before manual。

其他 `Qed`、`Defined`、自定义 proof 或不可解析 drift 返回 `protected-proof-manual`。

main-root symexec 失败时，事务恢复调用前各 role 的存在状态和 exact bytes；成功才提交并清除。进程中断留下的 prepared 事务在下次调用前恢复，committed 残留只清理。

owner 阶段不做 clean replay。接纳时 clean output 位于：

```text
reports/<run>/annotation-attempts/annotation-attemptN/clean-output-freshness/
```

final freshness 位于：

```text
reports/<run>/final-check/symexec-refresh/
```

后者不覆盖 proved manual，也不建立额外 manual 角色。

## 四、VC-checking debug 与复用路径

本节只适用于 present manual 至少有一个 VC 的 run。manual absent 或 present 但零 VC 时，不创建 vc-checking round、debug script、reuse hint 或 group path；controller 直接准备空 manifest，并继续强制 parent goal-check/full Coq 与 final freshness/full Coq。若 goal-check 导入 missing manual，检查必须失败。

每轮 vc-checking 交接给出：

- 当前 debug 脚本；
- 每个 top-level VC 和适用 split goal 的完整 Rocq target；
- `controller.py coq-debug --round <current-round>`。

当前脚本的唯一 canonical path 是
`_coq_builds/<current-round>/vc-checking/src/.coq_debug/vc-checking.v`。handoff renderer、owner
授权、runtime validation、`coqtop -l` 和接纳检查必须共同消费 controller 的同一 path helper；不得在任一
边界重新拼接一个省略 `vc-checking/` 的替代路径。

只有 controller 绑定正好上一轮封存 proving source 时，才额外给出：

- reference debug script 与命令；
- previous group copied manual、适用时的 lib 和 report 路径；
- 可比较的 previous targets；
- `reuse_source_raw/`；
- `_coq_builds/<sealed-source-round>/reuse-source/src`。

`reuse_source_raw/` 保存未规范化且实际 present 的 raw goal/manual/`formal_case_lib`，用于结构和 generated-goal 语义指纹；optional role absent 时不制造文件，其 digest 为 `null`。`reuse-source/src` 只服务 reference `Show.`，不是新的 formal/lib 角色。

source proving round 已 stale 时，manifest parser 仍以该 round sealed `reuse_source_raw/` 为显式 seed，
并在每次消费前重验其 presence/digests；不得回退到已经被 annotation retry 更新的 main-root raw files。

现有 debug build seal 机械绑定：

- 本地构建树摘要；
- 本地构建文件数；
- 解释该 build 的 selected dependency artifact 摘要；
- reuse-source build 另绑定 `reuse-source/preparation.json` 摘要。

current debug 用当前 run-level preparation；reuse-source build 用 vc-proving 封存时随该 build 一起持久化的
`preparation.json`，因此后续 annotation 改变 `source_goal_version` 不会使它失效。该 preparation 每次使用都要
重验：base artifacts 按仓库现状重新取摘要，trusted base 重建会指名改变的 artifact。receipt 不增加字段，
`file_count` 仍只表示 local build 文件数。reference debug 前后重验 local tree 和其 preparation snapshot；任一
imported current module 必须有本 build local `.vo`。

current final script 只覆盖 aggressive split goals 和 `LLM_pre_process` top-level VC。reference script 只覆盖 direct/partial 实际引用的 previous goals；全 `from scratch` 时省略 reference script 和 receipt。

vc-checking 只能写交接声明的 `.coq_debug` 文件。不得修改 preserved artifacts 或扫描其他历史 round。

## 五、Group 路径与 overlay

group 交接可提供：

- `coq-debug`
- `coq-check --target-kind group-development --group <id>`
- `coq-check --target-kind group-check --group <id>`

每次 delivery 领取前，controller 从 current state、accepted plan、base 和 compact manifest 重新渲染这些命令。

controller 派生：

- copied manual，以及 `formal_case_lib` present 时的 `group_worker_lib` overlay destination；
- exact build：`_coq_builds/<round>/<group>/src`；
- development 独立增量 build；
- group-check 包装文件；
- assigned witnesses；
- 精确的 debug 脚本路径；
- proof modes 和 aggressive split assignment；
- 可选只读 `proof_reuse.md`；
- 精确的可编辑证明区间；
- round-local `public_helper_snapshot.txt` 路径 / 摘要。

debug script 文件名由 preparing 与运行时使用同一 canonical 函数生成。controller 在 group check/debug 前验证 manifest 绝对路径和运行时目标完全一致。`coq-debug` 只把已验证的 build 内 fixed absolute script path 交给 `coqtop -l`；不得把 build-relative 名称交给 Coq loadpath 搜索。spawn 前后重验同一路径与 digest，不能复制脚本、换 cwd 或扩大 load path 来获得成功。

group 只在 present manual 含 witnesses 时创建。group directory 始终有 copied manual；仅当 `formal_case_lib` present 时才有 `group_worker_lib`。lib absent 时 plan/worker 不得产生 helper，也不得修改 shared/异名 lib。report 和 build 不能写进该目录。

annotation-gap 的 Markdown 固定为
`reports/<run>/rounds/<round>/groups/<group>/group_worker_output.md`。finalize 要求它是 fixed-path、非空、
UTF-8 普通文件，并把 digest 放进 finalized `artifact_sha256`；validation、reuse、feedback/summary 与
首次或重复 handoff 都重新核对该路径和 digest，不能接受 alias、symlink 或更新后的 bytes。

首次 group preflight 返回 `report-repair-required` 前，controller 用 `repair_formal_sha256` 冻结 copied
manual 与可选 `group_worker_lib`。该 delivery 此后只允许 report/Markdown 修复；formal 漂移形成
`invalid-report`，成功 finalize 才清除临时 repair seal。

每个 group 只能编辑 assigned top-level proof spans，以及 `aggressive_pre_process` witness 对应的全部
assigned split-goal proof spans。statement、declaration order、未分配 proof 和
`LLM_pre_process` split token 都受保护；注释、空白、CRLF/LF、尾随空白和 EOF newline 不构成
语义授权。aggressive witness 必须先完成全部 split goals，再在 top-level 中执行
`aggressive_pre_process`，只用 `Goal_apply` 把对应 split lemma 应用到各分支。该 proof 原则由 owner
遵守，controller 仍以 proof mode、split completeness、结构 seal 与 Rocq 结果接纳，不解析 tactic
文本。

新建或实质修改的 helper 必须使用本组 suffix；只有与 frozen public snapshot 或 accepted reuse
declaration/proof token 一致的 helper 才能保留历史 suffix。所有 group 独立，不能读取或 import
sibling output。accepted plan 顺序控制固定编号与 merge；`dispatch_order` 只填并发 slot，不形成依赖。

`failure_class: annotation-gap` 的 blocked group，其 copied manual 与适用时的 lib 在 finalize 时和原始
report 一起封存；controller 用 `require_complete=False` 检查结构/ownership/route/helper/import/safety，
不跑 exact/full group Rocq。其目录不再接受 annotation 修正。controller 仍为所有未领取 group 派发
同样的固定路径和命令。整轮汇总非空时不会建立机械 merge 结果或 parent overlay，但全部 group seal
仍写入 `reuse_group_artifacts.groups`，通过结构筛选的 group 记录在 `structurally_valid_groups`，供下一
round 的 controller-bound reuse source 读取。accepted group proof 满足语义指纹条件时可 direct；
blocked group proof 最多 partial，helper 从头证明。

development、exact 和 finalize validation 在创建 build 或运行 Rocq 前使用同一结构检查。group 工具只允许当前已 claim 且 `running` 的 delivery 调用。

## 六、统一的本地构建合同

所有 annotation、group、parent、final 和 debug 使用同一套 controller-owned 本地构建合同。

### 构建模式选择与配置来源

唯一模式判定实现在共享脚本 `.agents/scripts/vc-proving/build_mode.py`：若
`<main-root>/_build` 是目录，就选择原有 Dune 后端；否则选择 lock-free Makefile 后端。不得根据 branch
name、环境变量、`dune-project`/`Makefile` 是否存在或探测命令成败改选模式。一个 run 期间必须保持
`_build` 的 present/absent 不变。公共 action、phase 与 state 字段为兼容既有 controller 仍命名为
`dune-build`、`dune_preparation`，但 Makefile receipt 明确含 `build_mode: makefile`，并使用自己的快照名。

Dune 模式实现保持原样：controller 从环境或 PATH 发现 `coqc`、`coqtop` 和 `dune`，依赖只来自
`dune-project`、相关 `dune` 文件和 Dune 输出。Windows setup 可显式设置 `COQC_EXE`、
`COQTOP_EXE`、`DUNE_EXE` 和 `DUNE_REAL`。

Makefile 模式优先从 `COQC_EXE`、`COQTOP_EXE`、`COQDEP_EXE`、`MAKE_EXE` 发现工具；未显式设置
Rocq executable 时读取可选 `Rocq/CONFIGURE` 的 `COQBIN`/`SUF`/tool assignments，最后才回退到
PATH。它固定封存 `Rocq/Makefile` 与可选 `Rocq/CONFIGURE` 的存在状态/bytes，但不运行仓库聚合 target。所有模式
共用 controller-owned canonical flags 与 load-path mapping。controller 假定同一 main root 上只有一个
顺序 run；两种模式都不创建 lock file、PID owner record，也不调用 POSIX/Windows locking API。

### Current 所有权

case 身份只来自 persisted `target_files`：`--case` 给出 authoritative formal stem，目标目录给出 active theory。current ownership 只包括：

- 本 run exact present generated artifacts；
- present 且明确可编辑的 `formal_case_lib`。

不能从 C stem、同目录 `<case>_` 前缀、strategy/helper 文件名或 lib import 反推 case。同目录的其他程序以及 shared/异名 lib 默认属于 dependency。

### Selected dependency snapshot

annotation 阶段每次检查 present `formal_case_lib` 前，selected backend 先为 exact library target 做一次
临时 dependency preparation；它只服务本次本地 `coqc`，不写入 accepted dependency state。annotation
接纳后，main-owned `dune-build` action 对 exact goal-check 再做一次正式 preparation，并把模式对应
快照直接写在 run 根。后续 proof、debug、parent 与 final 只重验并消费该快照，不再次解析依赖。

#### Dune 模式

annotation owner 和 main acceptance 在每次 `formal_case_lib` 本地 `coqc` 之前，先运行一次 exact library `.vo` Dune target。该次结果只服务 annotation 检查，不写入 accepted dependency state。

annotation 接纳后，main-owned `dune-build` 只执行：

```text
dune build --root <main-root> --display=short <persisted-goal-check.vo>
```

Dune 负责依赖发现、缺失/过期判断和必要重建。controller 随后读取这次 build 生成的 theory dependency data，截取 exact goal-check 传递闭包，并原子写入：

```text
verification_runs/<run>/dune_dependency_snapshot.json
```

快照包含 persisted case identity、current family 与 current direct edges、dependency source/artifact digests、Dune configuration digests、exact target 和 `source_goal_version`。它是 Dune 结果的固定版本，不是另一个 resolver。annotation retry 接纳新版本时覆盖同一路径并更新 state receipt，不保存快照历史。

正式 `dune-build` 前，controller 会清理 canonical `Rocq/` 下会与 Dune rule 冲突的旧普通 Coq side products。链接、目录或特殊 leaf 不删除并明确失败；Dune 产物只写入 `_build/default`。

case/target 由 `target_files_for_c` 从 `QCP_examples/<collection>/**/<program>.c` 镜像到 `Rocq/examples/<collection>/**`，Dune exact target也直接使用该 persisted path。因此嵌套深度、同目录多程序与非固定 collection 位置都不能被替换成硬编码的 example 路径；目标目录必须仍被仓库 Dune theory 覆盖。

#### Makefile 模式

controller 只在上述两个 preparation 边界运行 batched `coqdep`。它按 breadth frontier 批量解析 exact
传递闭包，把 persisted current family 从 trusted base 中剥离；同一次 action 后续不再按 source 重复
解析，所有 `coq-check`/`coq-debug`/parent/final 更不得启动 `coqdep`。receipt 的
`dependency_metrics` 公开 batch、process 与 node 数量。

正式 preparation 原子写入：

```text
verification_runs/<run>/Makefile
verification_runs/<run>/makefile_dependency_snapshot.json
```

run-local `Makefile` 是 controller 生成的 standalone exact plan，唯一公开 goal 为 `trusted-base`，带
`.NOTPARALLEL`，只允许已解析 trusted-base `.vo`。argv guard 明确拒绝 `all`、`core`、`examples*`、
`depend` 和任何更宽 target；环境中的递归 Make flags、外部 Makefile、Coq flags/load path 覆盖都被
清除。annotation 临时 preparation 使用同样内容的临时 exact Makefile，完成后删除。

Make 开始前只清理 persisted current family 在 main root 的普通
`.vo/.vos/.vok/.glob/.aux`，绝不删除 trusted-base 增量产物；symlink、reparse point、目录、FIFO 或
其他特殊 leaf 明确失败。Make 只在 canonical `Rocq/` source 旁更新 trusted-base `.vo`，不编译
current family。完成后 controller 重验 source 与 run Makefile 未漂移，封存 exact edges、current
edges、dependency source/artifact digests、Makefile/CONFIGURE 状态、tool paths、case identity 与
`source_goal_version`。annotation retry 覆盖同一路径和 receipt，不保存历史快照。

### Load path 规划

controller 用固定的绝对 `-R/-Q` broad mappings 读取 accepted dependencies：Dune 模式的 physical
root 是 `_build/default`，Makefile 模式是 main-root `Rocq/`。两者都遵守：

1. 保留完整、固定的 broad base mappings，不按 current basename 或目录做 `exclude-dir`；
2. 最后加入唯一的 build-local current exact mapping；
3. snapshot guard 要求每个 imported current module 在本 build 已有 local `.vo`，不能由 broad Dune mapping 下的旧 current 副产物满足。

同目录另一前缀模块只有在 accepted snapshot 中才可从 selected base output 读取，不复制源码。每个 current dependency 在 consumer 编译或 debug 前必须已有本 build local `.vo`，防止旧 artifact 回退。

build 内基础 `.v` 和 `.vo` 数量都必须为 0，不建 run-local 基础 cache，也不在 check 内重编基础源码。

present `formal_case_lib` 在 annotation 阶段以 selected backend 的 exact target 独立检查；它不得 import 本 run generated artifacts。正式快照完成后，所有 current source、group overlay 与 debug script 的 project import 都必须能映射到 snapshot 中的 current/dependency source。动态 `Load`、load-path 命令、缺 source、快照外 project import 和 current edge 改变都分别明确失败。

group current source不得动态扩展 dependency closure。若 proof/helper 确实需要新的官方 import，worker 报告该事实，由 annotation retry 把 import 放入 accepted source，再执行新的 `dune-build` action。同一 proving version 内不再启动 Dune、Make 或 `coqdep`，不写 group-specific dependency artifact。

accepted dependency artifact aggregate 与 local build digest 一起绑定 reuse/debug seal。

### Current 编译缓存

development 和强制检查共用 run-local `_coq_builds/current/` 中按内容寻址的 current 前置 `.vo`。键包含 source、current 依赖、compiler、配置、flags、accepted dependency artifact digest 和规范化版本。强制检查最终 target 始终实际运行；development target 仍按自身增量规则。缓存缺失、删除或损坏只从 source 重编 current 模块。

不同 local build 只保存 current case 产物。preparing、development、exact、validation、parent 和 final 都从 selected base load path 读取同一套 snapshot-bound dependency `.vo`，不得在各自 build 中复制或另编 dependency source。

任何失败都不能回退到：

- Dune 聚合/全工作区目标或仓库 Make 聚合目标；
- 整库 mirror；
- check 内基础源码编译；
- main root 旧 current `.vo`；
- 扩大 target 集合。

## 七、Parent 与 final build

parent verify 只在本轮没有 annotation 缺口且所有非空 plan group accepted 时运行。它按 accepted plan
顺序机械 merge，与 `dispatch_order` 无关。controller 先重验每组 seal 与结构，不逐组重复完整
Rocq；然后只把实际 present 的 merged manual 和/或 `proving_merged_lib` 作为 overlay，在：

```text
_coq_builds/<round>/parent/src
```

运行一次 full check。

两个 optional roles 都 absent 时不创建虚假 overlay，但仍运行 parent goal-check/full Coq。base/merged manifest 对 absent role 使用 `null` digest。

final-check 在：

```text
_coq_builds/final-check/src
```

检查 main root applied files。开始前按 persisted exact current module identities 清理 `.vo/.vos/.vok/.glob/.aux`，即使对应 optional source 当前 absent 也清理它的同名旧副产物；同时清理 current run 非 build 区域的同类副产物，并保留 selected trusted-base artifacts（Dune 的 `_build/default` 或 Makefile 模式的 main-root base `.vo`）。broken symlink、目录或其他非普通 side-product leaf 不得当作“missing”，必须形成 cleanup error。结束后重扫同一边界。

parent 和 final 只读取 accepted mode-specific snapshot 指定的 dependency `.vo`，并分别在自己的 local build 重新编译 merged/applied current source。dependency source/artifact/configuration 任一漂移都返回精确 blocker；parent/final 内不得运行 Dune、Make、`coqdep`、扩大 target 或编译 dependency source。

## 八、长命令与超时

controller-owned 外部进程都有有限墙钟：

- 同一次 canonical symexec 的 driver 与恢复调用共享 600 秒；
- 同一次 `dune-build`、`coq-check` 或 `coq-debug` 的全部子进程共享 1800 秒。

路径解析、依赖图和 staging 已消耗的时间会从下一次子进程启动的剩余时间扣除。截止时间耗尽后不再启动进程。

controller 把外部工具放入独立 process group。超时时先终止整组，必要时强制结束；即使逃逸子进程仍占用输出 pipe，最终读取也有界。agent 不得自行重启 raw process 或构造无上限替代命令。
