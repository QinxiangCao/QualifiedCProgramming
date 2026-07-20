# Path Configuration

controller内部 repository tooling拥有所有 executable、cwd、include/search mapping、formal relative path、overlay、build directory与fixed flags。agent只执行 handoff Markdown 已渲染的命令。

## 通用规则

1. annotation读取本次独立的 `reports/<run>/annotation-attempts/annotation-attemptN/agent_input.md`；vc-checking读取round内 current `agent_input.md`；group读取`group_worker_input.md`。
2. 原样执行其中的 controller command，不抄写、补 flag或改 path。
3. 命令失败时只修改本 phase 允许的 formal content或 declared debug script，再原样重跑。
4. path mismatch直接报告 controller/handoff 问题；不得尝试另一套 cwd/flag。

## Annotation

handoff 提供：

```text
python3 .../controller.py --main-root <root> symexec --run <run> --round <round>
python3 .../controller.py --main-root <root> coq-check --run <run> --round <round> --target-kind formal-case-lib
```

controller内部根据运行环境选择 symexec driver：Windows 使用 `win-binary/symexec.exe`，Linux 使用 `linux-binary/symexec`，Apple Silicon macOS 使用 `mac-arm64-binary/symexec`，Intel macOS 使用 `mac-x86-64-binary/symexec`。随后从 target C 推导 generated paths，添加 canonical `-I`/`-slp`，在 main root运行，并把 Coq build限制到 current run `_coq_builds`。未知平台或未知 macOS 架构必须明确失败，不能默认为 Ubuntu binary。

首次 annotation handoff用于唯一 agent startup。后续 handoff写入新的 `annotation-attempts/annotation-attemptN`，先由 main agent按模板完成 blocker summary/reflection并通过 `annotation-summary-ready`，再通过 append action交给原 target；不覆盖旧 report。run root `annotation_history/<attempt-id>/` 只保存 formal before/after，history命令只作只读记录，不再执行。

annotation handoff还提供annotation-checking前后的两条`timing-stage`命令；owner必须把完整review、repair与recheck包在这一对start/finish之间。所有phase/group owner delivery/return使用`mark-attempt-started`/`mark-attempt-returned`，使timing summary可从真实边界生成。

final freshness复用 symexec helper，但 output root固定为 `reports/<run>/final-check/symexec-refresh/`，不覆盖 proved manual。raw refresh manual 由 controller 在该目录内执行与 annotation acceptance 相同的 diagnostics split，再比较 cleaned witness names/statements；agent 不处理 refresh files。

## Group

group handoff提供 `coq-debug` 与 `coq-check --target-kind group-check --group <id>`。controller从 current state和compact manifest派生：

- main root formal source mirror与前置全量make已有的基础`.vo`；
- copied manual与`group_worker_lib`到正式 relative paths的两个 overlays；
- group-unique `_coq_builds/<round>/<group>/src`；
- build-only group-check wrapper与assigned witnesses；
- exact debug script path。

group directory本身只有两个 copied formal files。group-worker不接触 overlay参数或internal helper。

## Parent/final

Coq tooling从`SeparationLogic/CONFIGURE`和Makefile的`COQBIN`/`SUF`约定解析可执行文件。基础`.vo`复用是跨run的系统级规则：任意run的annotation、group、parent、final和debug入口都从同一main root full-make产物读取Makefile全部`-R`/`-Q` load path，并stage到该check build；不按源码digest、Coq版本或fixed flags建立cache，也不在check中重编译。缺失的required基础`.vo`是明确失败。current target case的lib/goal/auto/manual/check五个module始终排除旧`.vo`，并从current source或overlay重编译。

parent verify把 proving_merged manual/`proving_merged_lib` overlay到 main root mirror，在 `_coq_builds/<round>/parent/src`运行 full check。final-check先由 controller 删除current target case及current run非`_coq_builds`区域中的旧Coq side products，保留基础`.vo`，再在 `_coq_builds/final-check/src`检查 main-root applied files，结束后重扫同一target/run边界；agent 不手工删除或移动这些文件。

## 禁止

禁止直接调用 `symexec_tooling.py` / `coq_tooling.py`、raw symexec、raw `coqc`/`coqtop`、Dune、Rocq MCP、`coqc -o`、`_CoqProject` derived command；禁止自行构造 driver、`-R`、include/SLP、cwd、overlay或build path。
