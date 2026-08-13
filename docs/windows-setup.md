# Windows 环境配置

本文面向原生 Windows PowerShell，不适用于 WSL。

## 一、Git 与系统长路径

克隆仓库前先安装 Git，并启用 Git 自身的长路径支持：

```powershell
winget install --id Git.Git -e --source winget
git config --global core.longpaths true
```

`git core.longpaths` 只影响 Git，不能解除 Python、PowerShell、Dune 或其他程序的传统路径限制。建议在
管理员 PowerShell 中同时启用 Windows 系统长路径：

```powershell
Set-ItemProperty `
  -Path 'HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem' `
  -Name LongPathsEnabled `
  -Type DWord `
  -Value 1
```

修改系统设置后应重启相关进程。若不能启用，verification controller 会在 `init-run` 创建任何 run 前，
根据 main root、case 和完整任意深度 target 检查传统的 248 字符目录边界与 260 字符文件边界。

打开新的 PowerShell 并确认 Git 可用：

```powershell
git --version
```

随后克隆仓库：

```powershell
git clone --recurse-submodules https://bitbucket.org/WxWyashen/qcp-binary-democases.git
cd qcp-binary-democases
```

更新已有 checkout 时执行：

```powershell
git submodule sync --recursive
git submodule update --init --recursive
```

## 二、证明后端

选择并安装一个证明后端。不确定时选择 Rocq/Coq。

### Rocq/Coq

本仓库要求 Coq 8.20.1。下载官方
[Coq Platform 2025.01.0 release](https://github.com/rocq-prover/platform/releases/tag/2025.01.0)
中的 Windows x86_64 installer，预期 asset 为：

```text
Coq-Platform-release-2025.01.0-version.8.20.2025.01-Windows-x86_64.exe
```

安装时选择较短、不含空格的原生路径，例如 `D:\Coq8.20`。安装后把 Coq Platform 的 `bin` 目录加入
用户 PATH：

```powershell
$coqBinForQcp = 'D:\Coq8.20\bin'
$userPathForQcp = [Environment]::GetEnvironmentVariable('PATH', [EnvironmentVariableTarget]::User)
[Environment]::SetEnvironmentVariable(
  'PATH',
  "$coqBinForQcp;$userPathForQcp",
  [EnvironmentVariableTarget]::User
)
```

新开 PowerShell 后验证：

```powershell
coqc --version
dune --version
```

`coqc --version` 必须报告 8.20.1，Dune 必须为 3.16.1 或更新版本。Coq Platform 自带 `dune.exe`，无需
另外安装。verification 初始化脚本也会检查两个 Coq executable 与 Dune 版本，不能用仅“命令存在”的
结果代替版本门禁。

#### 构建 Rocq 文件

PowerShell 中使用仓库 wrapper 构建：

```powershell
.\dune.cmd build -j4
```

人工构建应使用 `.\dune.cmd`，不要使用 plain `dune build`。`-j4` 表示最多四个并行 job；只在 CPU 与
内存充足时增加，出现内存不足后应减少或省略。

<details>
<summary>实现说明</summary>

Dune 即使只构建 Coq 文件也会检查 PATH 中的 `ocamlc`。`dune.cmd` 在自己的子进程环境中设置
`tools\windows\fake-ocaml` 下的最小 shim，以满足该检查，然后把原参数传给真实 `dune.exe`。
</details>

### Lean

在仓库根执行以下命令。setup script 安装 `elan`；pinned toolchain 提供 Lean 4.25.2 与 Lake。

```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
.\scripts\setup-windows-lean-env.ps1
lean --version
lake --version
.\scripts\build-lean.ps1 -Task build
```

`lean --version` 必须报告 4.25.2。若 toolchain 下载报告 `CRYPT_E_REVOCATION_OFFLINE`，执行：

```powershell
.\scripts\setup-windows-lean-env.ps1 -ManualFallback
```

位于 QCP 根目录时，不要把命令缩写为 `.\scripts\setup-windows.ps1`；该短路径只在 `cd Lean` 后存在。

## 三、verification agent 的 Python 环境

verification controller 要求 Python 恰为 3.12，并要求解释器由 uv 管理。先安装 uv：

```powershell
winget install --id astral-sh.uv -e --source winget
```

从仓库根为每个新 PowerShell 进程执行：

```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
. .\scripts\setup-windows-env.ps1
& $env:UV_EXE sync --frozen --python 3.12
```

setup 会把当前进程 PATH 与机器、用户注册表 PATH 合并，所以 winget 刚安装的工具即使尚未被旧终端继承，
也可被发现。它设置 `UV_PYTHON_PREFERENCE=only-managed`，避免 uv 选中 LibreOffice 等附带的同版本
Python；已有 `.venv` 时还会检查其 Python home 与实际版本。

若 setup 报告 `.venv does not use a uv-managed Python`，先移走或删除旧 `.venv`，再执行：

```powershell
& $env:UV_EXE python install 3.12
& $env:UV_EXE sync --frozen --python 3.12
```

setup 不会自行删除或覆盖 `.venv`。它还把已验证的 Coq/Dune 目录与 fake OCaml shim 加到当前进程
PATH，确保 controller direct check 和 Dune 子进程使用同一套 Coq 8.20.1。

首次人工 `init-run` 使用 `$env:UV_EXE`；controller 后续 action 已绑定 `.venv` 中经过门禁的绝对 Python，
必须按返回的 `argv` 与 `cwd` 直接执行，不再包一层 uv、PowerShell 或 `cmd /c`。完整合同见
[Windows 适配说明](../.agents/skills/verification-orchestrator/docs/windows.md)。

## 四、VS Code

- QIDE 配置见 [qide.md](qide.md)。
- VsRocq/VsCoq 配置见 [vsrocq-setup.md](vsrocq-setup.md)。

## 五、QCP 命令行工具

直接运行 Windows QCP binary：

```powershell
.\win-binary\symexec.exe --help
```

仓库 example runner 面向 Rocq，可从 PowerShell 启动：

```powershell
.\run-example-windows.cmd
```

只使用 Lean 时运行 `run-example-lean-windows.cmd`。命令行选项、预处理、CRules import 与
Rocq/Lean 生成示例见 [qcp-cli.md](qcp-cli.md)。

## 六、MCP

MCP 是可选组件，按 [mcp-setup.md](mcp-setup.md) 单独配置。基础 verification setup 不要求
`win-binary\mcp.exe`，也不设置 `QCP_MCP_EXE`；需要 MCP 时才额外 dot-source：

```powershell
. .\scripts\setup-windows-mcp-env.ps1
```

该脚本使用 `QCP_MCP_BIN`，与 Rocq manual proof 和 Dune dependency preparation 相互独立。

## 七、agent 入口

Windows 上的 agent 入口规则见 [../AGENTS.md](../AGENTS.md)。执行单个 C verification case 前，
必须先完成本页的 verification Python 环境步骤，再按 AGENTS.md 路由读取 orchestrator skill 与 Windows
适配说明。
