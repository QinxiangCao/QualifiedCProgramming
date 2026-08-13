# 构建环境安装说明

本文面向尚未安装 Lean 相关环境的用户。

在整个 QCP 仓库中，Lean 与 Rocq 是两种可选的证明后端。普通用户只需安装其中一种；
只有需要同时生成并检查 `.lean` 与 `.v` 文件时，才需要同时安装两者。

## 路径约定

本文中的“Lean 根目录”专指 QCP 仓库内的 `Lean/` 目录，不是外层 QCP
仓库根目录。若当前终端位于 QCP 仓库根目录，请先执行：

```sh
cd Lean
```

Windows 用户也可以留在 QCP 仓库根目录，改用外层包装脚本
`scripts/setup-windows-lean-env.ps1` 和 `scripts/build-lean.ps1`。

## 所需工具

本仓库需要以下命令行工具：

- `git`
- `curl`
- `elan`

在 macOS 或 Linux 中使用 `Lean/Makefile` 时还需要 `make`。在 Windows
PowerShell 中可以使用 `scripts/build.ps1`，不需要额外安装 `make`。

不需要单独安装 Lean 或 Lake。`elan` 是 Lean 的工具链管理器，安装后会提供
`lean` 和 `lake` 命令，并根据 `Lean/lean-toolchain` 文件自动下载和使用
Lean `v4.25.2`。

所有 Lake 包都通过本地同级目录互相依赖，构建过程不依赖 Mathlib。

## macOS

1. 打开“终端”。
2. 安装 Apple 命令行开发工具，其中包含 `git` 和 `make`：

```sh
xcode-select --install
```

在弹出的系统窗口中完成安装。macOS 默认已经提供 `curl`。

3. 安装 `elan`：

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

安装程序询问安装方式时，选择默认选项即可。

4. 让当前终端立即识别新安装的命令：

```sh
source "$HOME/.elan/env"
```

也可以关闭终端并重新打开。

## Ubuntu 或 Debian

1. 安装基础工具：

```sh
sudo apt update
sudo apt install -y git curl make
```

2. 安装 `elan`：

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

安装程序询问安装方式时，选择默认选项即可。

3. 让当前终端立即识别新安装的命令：

```sh
source "$HOME/.elan/env"
```

## 其他 Linux 发行版

先使用系统的软件包管理器安装 `git`、`curl` 和 `make`，然后安装 `elan`：

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

NixOS 用户应当按照 `elan` 官方说明使用 Nixpkgs 中经过适配的版本。

## Windows

Windows 可以直接在 PowerShell 中构建本仓库。我们强烈不推荐使用 WSL，尤其不推荐
初学者使用；WSL 会引入额外的文件系统、路径、权限和工具链边界，本仓库不提供基于
WSL 的安装步骤或入门排障支持。请使用下面的原生 PowerShell 配置。

### PowerShell 原生配置

1. 安装 `git`。如果当前 PowerShell 中已经能执行 `git --version`，可以跳过这一步。
   否则可以安装 Git for Windows，或使用 `winget`：

```powershell
winget install --id Git.Git -e --source winget
```

2. 在 Lean 根目录执行 Windows 配置脚本：

```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
.\scripts\setup-windows.ps1
```

该脚本会安装 `elan`，并使用仓库的 `lean-toolchain` 固定 Lean `v4.25.2`。
普通模式不会主动下载完整 Lean toolchain；第一次执行 `lake` 或 `lean` 时，`elan`
会按需下载。

如果下载 Lean toolchain 时出现
`CRYPT_E_REVOCATION_OFFLINE`、`schannel` 或 certificate revocation 相关错误，
说明当前网络无法完成 Windows 证书吊销检查。可以使用脚本的手动 fallback：

```powershell
.\scripts\setup-windows.ps1 -ManualFallback
```

fallback 会从 Lean 官方 GitHub Release 下载 Windows `.tar.zst` 包，使用
`curl.exe --ssl-no-revoke` 续传下载，并把解压后的 Lean 注册为当前仓库的本地
elan override。这个选项只跳过该下载命令的吊销检查，不会关闭系统全局证书验证。
该文件约 472 MiB。运行 fallback 前先确认当前 Windows 提供它需要的两个命令：

```powershell
Get-Command curl.exe
Get-Command tar
```

两条命令都必须返回可执行文件路径。

也可以手动安装 `elan`：

```powershell
Invoke-WebRequest -Uri https://elan.lean-lang.org/elan-init.ps1 -UseBasicParsing -OutFile $env:TEMP\elan-init.ps1
& $env:TEMP\elan-init.ps1 -NoPrompt 1 -DefaultToolchain leanprover/lean4:v4.25.2
```

安装完成后，关闭并重新打开 PowerShell。也可以在当前窗口临时加入 PATH：

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
```

3. 在 Lean 根目录验证工具链：

```powershell
elan --version
lean --version
lake --version
```

第一次运行 `lean` 或 `lake` 时，`elan` 会根据 `lean-toolchain` 下载
Lean `v4.25.2`。下载完成后，`lean --version` 应显示 `4.25.2`。

4. 构建整个仓库：

```powershell
.\scripts\build.ps1 -Task build
```

如果前面使用过 `.\scripts\setup-windows.ps1 -ManualFallback`，构建脚本会自动将
`ELAN_TOOLCHAIN` 指向该本地 toolchain，使子包目录中的 `lean-toolchain` 文件也不会
重新触发下载。脚本默认会对包级构建失败重试 2 次，以缓解 Windows 上偶发的 Lean
原生进程崩溃。

清理全部 Lake 编译产物：

```powershell
.\scripts\build.ps1 -Task clean
```

如果执行脚本时遇到 PowerShell 执行策略限制，可以只对当前进程放宽策略后再运行：

```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
.\scripts\build.ps1 -Task build
```

## 验证安装

进入 Lean 根目录后执行：

```sh
elan --version
lean --version
lake --version
```

在 macOS 或 Linux 中还可以执行：

```sh
make --version
```

第一次运行 `lean` 或 `lake` 时，`elan` 会根据 `lean-toolchain` 下载
Lean `v4.25.2`。下载完成后，`lean --version` 应显示 `4.25.2`。

macOS/Linux 如果出现 `elan`、`lean` 或 `lake: command not found`，请重新打开终端，
或者再次执行：

```sh
source "$HOME/.elan/env"
```

Windows PowerShell 用户应重新打开 PowerShell，或在当前窗口执行：

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
```

在 Ubuntu/Debian 上，不要按照命令行建议另行执行 `apt install elan`；
应当先确认 `$HOME/.elan/bin` 已经加入 `PATH`。

## 开始构建

环境验证通过后，在 Lean 根目录执行：

```sh
make build
```

PowerShell 用户执行：

```powershell
.\scripts\build.ps1 -Task build
```

完整的构建和清理说明见 [`README.md`](README.md)。

## 官方资料

- [Lean 手动安装说明](https://lean-lang.org/install/manual/)
- [elan 官方仓库与安装说明](https://github.com/leanprover/elan)
- [Apple 命令行开发工具安装说明](https://developer.apple.com/documentation/xcode/installing-the-command-line-tools/)
