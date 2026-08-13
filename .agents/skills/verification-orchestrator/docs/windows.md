# Windows 适配说明

本文只定义 Windows 与通用 verification workflow 的平台差异。阶段、owner、state、handoff、检查与
完成标准仍以本 skill 的三个 workflow 和 `controller-cli.md` 为准，不形成第二套流程。

## 一、环境准备

Windows 需要：

- uv 与由 uv 管理的 Python 3.12；
- Coq 8.20.1；若 `_build` 是目录，还需要 Dune 3.16.1 或更新版本；否则需要 GNU Make 与同套 Coq 的 `coqdep.exe`；
- 可从当前或注册表 PATH 找到，或由环境变量指定的 selected tools；
- 仓库已有的 `win-binary\symexec.exe`、StrategyCheck 和 LSP 二进制文件；
- 仓库已有的 `dune.cmd` 与 `tools\windows\fake-ocaml\` shim files。

每个新 PowerShell 进程从仓库根执行：

```powershell
. .\scripts\setup-windows-env.ps1
& $env:UV_EXE sync --frozen --python 3.12
```

setup script 只修改当前 PowerShell 进程。它先合并进程、机器和用户注册表中的 PATH，因此刚由安装器加入
注册表、但旧终端尚未继承的工具也可被发现；合并保留进程特有项并按大小写不敏感方式去重。它随后验证
repository 文件、native executable 和版本，并设置：

| 变量 | 含义 |
|---|---|
| `QCP_SYMEXEC_EXE` | 仓库内的 Windows 符号执行二进制文件 |
| `QCP_STRATEGYCHECK_EXE`、`QCP_LSP_EXE` | repository 内的辅助可执行文件 |
| `UV_EXE` | 实际 `uv.exe` 的绝对路径 |
| `UV_PYTHON_PREFERENCE=only-managed` | 禁止 uv 选择 LibreOffice 等系统 Python |
| `COQC_EXE`、`COQTOP_EXE` | 实际 Rocq executables |
| `DUNE_REAL`、`DUNE_EXE` | 仅 Dune 模式；实际 `dune.exe` |
| `OCAMLLIB`、`CAMLLIB` | 仅 Dune 模式；repository 内的伪 OCaml 库目录 |
| `COQDEP_EXE`、`MAKE_EXE` | 仅 Makefile 模式；实际 `coqdep.exe` 与 GNU `make.exe` |

setup 与 controller 使用同一粗粒度判定：`<repo>\_build` 是目录时选择 Dune，否则选择 Makefile，且不按
branch name 或工具探测结果 fallback。显式环境变量存在时，script 先验证并复用其绝对路径；否则使用
`Get-Command ... -CommandType Application` 从合并后的 PATH 发现 `.exe`。setup 要求两个 Coq
executable 都报告 8.20.1；Dune 模式另要求 Dune 至少为 3.16.1，Makefile 模式要求工具确为 GNU Make
并找到 `coqdep.exe`。不能把“文件存在”当成版本可用。

已有 `.venv` 时，setup 同时检查其 Python home 位于 `uv python dir` 返回的管理目录内，并实际执行 venv
Python 确认版本为 3.12。若旧 venv 由 LibreOffice 或其他系统 Python 创建，先移走或删除该 `.venv`，再
运行上面的 `uv sync`；setup 不会自动删除或覆盖环境。没有 `.venv` 时，`uv sync` 可按 `only-managed`
约束取得并创建 Python 3.12 环境，也可先显式执行：

```powershell
& $env:UV_EXE python install 3.12
```

setup 把已验证的 selected tool 目录加入当前进程 PATH 并去重。Dune 模式仍加入 fake OCaml、设置
`OCAMLLIB`/`CAMLLIB` 并直接启动 `DUNE_EXE`；`dune.cmd` 只供人工 PowerShell build，不能作为
`DUNE_REAL`。Makefile 模式不要求 Dune/fake OCaml，controller 直接启动 `MAKE_EXE` 与 `COQDEP_EXE`，
run-local exact Makefile 在 native Windows 显式使用 `cmd.exe` recipe shell。

只有确实需要 qcp-mcp 时才额外 dot-source `scripts\setup-windows-mcp-env.ps1`；基础 setup 不要求
`mcp.exe`，也不设置无消费者的 `QCP_MCP_EXE`。MCP script 使用自己的 `QCP_MCP_BIN`，不参与 Rocq
manual proof 或 selected dependency preparation。

setup 还读取 `LongPathsEnabled`。未启用时只发出环境警告；`init-run` 会结合本次 main root、case 和完整
任意深度 target 预估实际最深路径，只有达到 legacy 248 字符目录边界或 260 字符文件边界时才在创建
run 前拒绝，不会为浅路径无条件阻断。修改系统设置后需按 Windows 要求重启相关进程，才能依赖
long-path 行为。

## 二、首次入口与 controller 命令

首次人工 `init-run` 使用：

```powershell
$Controller = Join-Path (Get-Location).Path '.agents\scripts\verification-orchestrator\controller.py'
& $env:UV_EXE run --frozen --python 3.12 python $Controller `
  --main-root (Get-Location).Path `
  init-run --case demo --target-c-file 'QCP_examples\SomeCollection\nested\demo.c'
```

controller 在 parser 和写入前要求 Python 恰为 3.12。此后 action 的 `argv` 已含当前环境绝对
`sys.executable`、完整参数与 `cwd`；main 必须把它作为参数数组直接交给终端工具。owner 只执行 handoff
中的完整 controller 命令。不得再包 `uv run`、`powershell -Command`、`cmd /c`、pipeline、background
job、临时 script 或 raw executable。

终端返回 live session/process id 时，沿用同一 id 等待真正退出。空输出或首次 yield 不表示完成；exit
code 0 与 controller JSON `status: passed` 必须同时成立。controller 不另设 execution lease 或 in-flight
marker；因此原进程退出前不得再次调用同一 action、`step` 或 retry。generation compare-and-swap 只能
拒绝已经提交后的 stale write，不能把仍在运行的同一 action 变成可安全并发。

## 三、路径、目录深度与分隔符

controller 对路径分成两种表示：

- physical access 使用 `pathlib.Path` 和规范化绝对 Windows path；drive、空格与反斜杠由参数数组处理；
- state、manifest、snapshot digest input、formal relative path 与 mode-specific exact target 使用 repository-relative
  POSIX 表示，例如 `Rocq/examples/Collection/nested/demo_goal_check.vo`。

`coq-debug` 的 script 是 physical access 的特例：controller 仍在 state/handoff 中保存 build-relative
identity，但 spawn 时把刚验证的 fixed absolute Windows path 原样作为 `coqtop -l` 的单个 argv 元素，并
核对 load argument 与解析路径都等于该授权路径。不得让 Coq 从 cwd/loadpath 搜索
`.coq_debug\*.v`，也不得复制到 drive root 或其他目录；child 退出后必须重验同一 script digest。

不要把机器 JSON 中的 relative path 批量改为反斜杠，不要因 drive-letter 大小写、Windows
case-insensitivity 或显示出来的 separator 重新计算 digest。Dune exact target 有意使用正斜杠；Windows
Dune 接受该 repository-relative target，`--root` 则使用 controller 给出的绝对 physical path。

Dune dependency 输出若把绝对盘符写成 Make 风格的 `C\:/...`，parser 只还原 token 开头的盘符冒号为
`C:/...`，然后继续执行既有 fixed-root 与 snapshot 校验。不得全局删除反斜杠或放宽 repository
boundary；普通 relative token 和文件名中的字符保持原样。

`target_files_for_c` 保留 `QCP_examples/<collection>/**` 的全部目录组件并镜像到
`Rocq/examples/<collection>/**`。Windows 适配不得固定某个 collection、目录深度或示例 case；只要求
每个目录组件是合法 Rocq logical identifier；Dune 模式的目标还必须受仓库 Dune theory 覆盖。

为降低 Windows 路径长度而不丢失上述映射，只有非权威的运行时目录使用现有编号缩写：annotation 历史
写入 `annotation_history/annotation-attemptN/`，VC-checking exact/debug build 直接使用
`_coq_builds/<round>/src/`，group exact build 使用
`_coq_builds/<round>/group_NN/src/`，可选 development build 使用相邻的 `group_NN/dev/`。state、handoff、
正式 group directory 与 target relative path 仍保存完整 identity；不要截短 collection 或 formal path。
loader 只为已经落盘的旧 run 接受原 full-attempt annotation history，新的 run 一律写 compact path。

所有 run/report/formal/build path 及既有 ancestor/leaf 都必须是 main root 内普通固定路径。symlink、
junction、mount/cloud reparse point 与其他外跳 reparse point 会被拒绝。不要用短路径、subst drive 或
junction 改写 persisted topology。未启用 Windows long paths 时，`init-run` 的预检覆盖 formal、compact
annotation history、vc-checking、group development、parent、final 及最长 final backup；超过边界时缩短
main root 或 case，不能删减任意深度 target identity。

## 四、Selected backend 与固定依赖版本

annotation 的 present `formal_case_lib` 在本地 `coqc` 前先执行 selected exact preparation。annotation
接纳后，`dune-build` action 再准备 persisted goal-check：Dune 模式维持原有 exact build 并写
`dune_dependency_snapshot.json`；Makefile 模式使用 batched `coqdep`、只含 `trusted-base` 的
`.NOTPARALLEL` run Makefile，并写 `makefile_dependency_snapshot.json`。

进入 vc-checking/proving 后，controller 只验证 snapshot 与 selected base artifacts；group、debug、
parent 和 final 都不再次调用 Dune、Make、`coqdep` 或解析 dependency graph。snapshot 外 project import
必须返回 annotation 形成新 accepted version，不能在 Windows 上用额外 target、手写 flags 或另一次 build
调用绕过。同一无副作用区间直接复用一次完整校验返回的 snapshot/摘要；经过会改写已校验输入的 Rocq/build 步骤、
state reload 或独立后置接纳边界时再重验，不增加 Windows-only cache、metadata database 或 handoff 字段。

controller 不创建 state、formal、workspace 或 dependency 的同步文件，也不使用操作系统 locking API。
单 run action 按顺序执行；多个 run 同时修改同一 main root 不在合同范围内。generation
compare-and-swap、digest seal、fixed path 与原子替换仍必须保留。旧实现中 `msvcrt` 独占锁引起的并发
`PermissionError` 已不存在；这不构成允许同一 run 并发 `step` 的新合同，stale generation 应作为结构化
冲突处理，而不是重加平台锁。

## 五、原子文件与只读属性

Windows 会对只读打开的文件句柄执行 `fsync` 返回 `bad file descriptor`。共享 atomic copy 合同因此是：

1. temporary file 以可写 descriptor 创建；
2. copy 后在同一可写 descriptor 上 `flush` 和 `os.fsync`；
3. 关闭 descriptor 后才用 `copystat` 保留 metadata；
4. 不为重复 `fsync` 重新只读打开 temporary；
5. 最后 `os.replace`。

任何新 helper 都必须沿用该顺序。不能通过吞掉 `OSError`、去掉第一次 writable flush/fsync，或清除
source readonly metadata 来规避问题。

仓库文本由 `.gitattributes` 固定 LF，只有 `*.cmd` 固定 CRLF。不要用 `Get-Content | Set-Content`、
`Out-File` 等整体重写 formal/state/report；它们可能改变 BOM、换行、行尾空白或 EOF newline。命令行
显示的 CRLF/LF 差异不授权修改 sealed bytes。

## 六、常见失败定位

- `Cannot find dune.exe`：仅 Dune 模式；安装 Dune 或把实际绝对路径设为 `DUNE_REAL`，重新 dot-source setup。
- `Cannot find make.exe` / `coqdep.exe`：仅 Makefile 模式；安装 GNU Make 与 Coq 8.20.1 自带的 `coqdep`，或设置对应绝对 `MAKE_EXE` / `COQDEP_EXE`。
- Coq/build-tool version mismatch：安装仓库要求的 Coq 8.20.1；Dune 模式另需 Dune 3.16.1 以上，Makefile 模式需 GNU Make。不要绕过 setup 继续运行 controller。
- `.venv does not use a uv-managed Python`：移走旧 venv，以 `UV_PYTHON_PREFERENCE=only-managed` 重新
  `uv sync`，不要继续复用 LibreOffice Python。
- projected Windows path reaches the legacy limit：启用 long paths 并重启相关进程，或缩短 main root /
  case 自身；不得用 subst、junction 或删减任意深度 target identity 绕过。
- `Missing fake ocamlc.exe` / `Makefile.config`：仅 Dune 模式；恢复 repository `tools\windows\fake-ocaml` files；不要用
  系统目录中的随机 OCaml 文件替代。
- Dune target not found：检查 persisted arbitrary-depth `target_files` 和覆盖该 collection 的 `dune`
  theory；不要改成 whole-workspace target。
- snapshot drift：dependency source/artifact 或 selected build configuration 已变；回到 annotation 并执行 controller
  给出的新 `dune-build`，不要在 proving 内修补 snapshot。
- `bad file descriptor` 出现在 copy：检查是否在 readonly reopen 后调用了 `fsync`；共享 atomic helper
  只允许对 writable descriptor 执行该调用。
- path seal mismatch：保留 state 中 POSIX relative path 和 exact 大小写，使用 action 给出的 cwd/argv；
  不自行转换 separator 或 drive spelling。
- terminal 已 yield 但仍有 live process：继续等待同一 session；不要并发调用 `step` 或 retry。
