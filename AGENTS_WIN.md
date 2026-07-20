# Windows 执行入口

Windows 与其他平台使用同一份 [AGENTS.md](AGENTS.md) controller 状态机、Markdown handoff、轻量 JSON result、三级 lib 和 acceptance contract。本文件只补充 PowerShell/driver 差异；若与 `AGENTS.md` 冲突，以 `AGENTS.md` 为准。

Windows 也只把 `controller.py` 作为公共脚本入口；不得直接执行内部 `symexec_tooling.py`、`coq_tooling.py`、group copy/merge 或 final-check 模块。

# 环境准备

- 默认 shell 是 PowerShell。
- 在仓库根目录执行 `. .\scripts\setup-windows-env.ps1`，确保 `win-binary\symexec.exe`、StrategyCheck、LSP、`coqc.exe` 和 `coqtop.exe` 可被 repository tooling 找到。
- 需要 qcp-mcp 时再执行 `. .\scripts\setup-windows-mcp-env.ps1`。qcp-mcp 只用于 C annotation/symbolic execution 交互，不用于 Rocq manual proof。
- Python 命令可使用 `python` 或 `py -3`；JSON 操作使用 Python/controller helper/PowerShell builtin，不依赖 `jq`。
- 路径可使用 `/` 或 `\`。含空格路径用单引号，并用 PowerShell 调用运算符 `&`。

# 固定目录与三级 lib

Windows 不改变目录：

```text
verification_runs/<run>/
  _coq_builds/
  annotation_history/<attempt-id>/
    before/ / after/
  <case>-vc-proving-rN/
    base_manifest.json
    groups/group_NN__<group-id>/
    proving_merged/

reports/<run>/
  controller_state.json
  run_logs.json
  timing_summary.json
  annotation-attempts/
    annotation-attemptN/
      agent_input.md / agent_report.json / agent_output.md
  rounds/<round-id>/
    agent_input.md / agent_report.json / agent_output.md   # vc-checking
    groups/<group>/group_worker_input.md / group_worker_report.json / group_worker_output.md
```

lib 角色仍只有：

- `formal_case_lib`：根目录 `SeparationLogic` 的正式 lib，annotation 维护 spec；final apply 才能用 accepted merge 替换。
- `group_worker_lib`：group directory 中的 copy，当前 group 新增 suffixed proved helpers。
- `proving_merged_lib`：机械合并并通过 parent full check 的 lib，随后替换 `formal_case_lib`。

# Script-owned 路径

agent 只能执行 handoff 已渲染的完整命令：

- handoff 的 `controller.py symexec` 内部调用共享的跨平台 `symexec_tooling.py`；该 selector 在 Windows 自动选择 `win-binary\symexec.exe`（Linux、Apple Silicon macOS、Intel macOS 分别选择各自 binary 目录），再拼接 C/generated path、canonical `-I`、`-slp`、logic path 和 cwd。未知平台不得回退到 Ubuntu binary。
- handoff 的 `controller.py coq-check/coq-debug` 内部调用 `coq_tooling.py`，拼接固定 Coq flags、root source mirror、group/proving overlays 和 `_coq_builds` path。

Coq check以前置全量make产生的基础`.vo`为条件信任输入；该信任跨全部run和annotation/group/parent/final/debug全流程，从同一main root复用Makefile全部load path下的基础`.vo`并stage到各check build。controller使用`SeparationLogic\CONFIGURE`与Makefile的`COQBIN`/`SUF`配置选择`coqc.exe`，不按源码digest、Coq版本或flags另建cache或重编译基础库。current target case的lib/goal/auto/manual/check五个module不在信任范围内，每个适用check都删除其旧build产物并从本轮source/overlay重编译。final cleanup只处理current target与run非build副产物，不删除基础`.vo`。

`timing_summary.json`按annotation attempt及vc-checking/vc-proving round记录整体时间和少量重要stage；不得回退到按command全局累计，也不记录单witness时间。owner delivery/return必须调用`mark-attempt-started`/`mark-attempt-returned`，annotation-checking前后还必须执行handoff中的`timing-stage` start/finish。

不得在 PowerShell 中自行重建 driver path、include/search path、Coq flags、cwd、overlay 或 build directory；不得调用 raw symexec、raw `coqc.exe`/`coqtop.exe`、Dune、Rocq MCP、`coqc -o` 或 `_CoqProject` derived command。

# Controller 示例

```powershell
python .agents\skills\verification-orchestrator\scripts\controller.py `
  --main-root (Get-Location).Path `
  init-run --case demo --target-c-file QCP_examples\LLM_bench\Algorithms\demo\demo.c
```

后续命令继续使用 `--main-root` 和 controller 返回的 run id。每个 run 的首次 annotation action只启动一个 annotation-subagent，main agent必须保存其 target；后续 annotation retry先创建独立的 `annotation-attempts/annotation-attemptN/agent_input.md` 模板。main agent阅读原始 blocker Markdown/JSON，填写 blocker conclusion、causal analysis、previous-attempt reflection、required repair与scope decision五段，执行 `annotation-summary-ready` 后，controller才给出追加到既有 target 的 `append-annotation-agent` action，不得再次 spawn。每次 append都要求重读两个 annotation skills，并读取主总结及原始 blocker；第三次及以后还要考虑整体重构 spec/contract/invariant。vc-checking-subagent与group-worker仍按 controller/handoff 的 spawn instruction启动；scripts不启动 agent。
