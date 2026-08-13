# Annotated SimpleC Lean

本仓库是 Annotated SimpleC 及其所需 Coq 子模块的 Lean 迁移版本。

在整个 QCP 仓库中，Lean 与 Rocq 是两种可选的证明后端。普通用户只需安装其中一种；
只有需要同时生成并检查 `.lean` 与 `.v` 文件时，才需要同时安装 Lean 和 Rocq。

本文中的“Lean 根目录”专指 QCP 仓库内的 `Lean/` 目录。若终端当前位于 QCP
仓库根目录，请先执行 `cd Lean`；或者使用 QCP 根目录下的
`scripts/build-lean.*` 包装脚本。

## 环境要求

本仓库使用 Lean `v4.25.2`，需要 `git`、`curl`、`elan`，在 macOS/Linux
中还需要 `make`。PowerShell 用户可以直接使用仓库提供的 `scripts/build.ps1`，
不需要额外安装 `make`。
不需要单独安装 Lean、Lake 或 Mathlib。

Windows 用户应使用原生 PowerShell 流程。我们强烈不推荐 WSL，尤其不推荐初学者使用；
本仓库不提供基于 WSL 的安装步骤或入门排障支持。

尚未安装 Lean 相关环境的用户，请先阅读
[`INSTALL.md`](INSTALL.md) 中的 macOS、Linux 和 Windows 安装说明。
Windows PowerShell 用户在 `Lean/` 目录中运行：

```powershell
.\scripts\setup-windows.ps1
```

VS Code 用户可以参考 [`docs/vscode.md`](docs/vscode.md)，其中包含推荐扩展和
可直接运行的构建任务。

## 构建整个仓库

在 `Lean/` 目录中执行：

```sh
make
```

也可以显式执行：

```sh
make build
```

PowerShell 用户执行：

```powershell
.\scripts\build.ps1
```

或显式执行：

```powershell
.\scripts\build.ps1 -Task build
```

该脚本会自动使用 `setup-windows.ps1 -ManualFallback` 注册的本地 Lean toolchain，并对
Windows 上偶发的 Lean 原生进程崩溃进行包级重试。

该命令会按照依赖顺序构建全部正式库和已登记的测试目标：

1. `compcert_lib`
2. `unifysl`
3. `auxlibs`
4. `sets`
5. `listlib`
6. `fixedpoints`
7. `SeparationLogic`
8. `MonadLib`
9. `examples`

Lake 支持增量构建。再次执行 `make build` 时，只会重新编译受到源码变更影响的目标。

构建过程中可能出现已有的 linter 警告，这些警告不表示构建失败。成功时，每个包最终都会输出
`Build completed successfully`。

## 清理编译产物

清理全部包的 Lake 编译产物：

```sh
make clean
```

PowerShell 用户执行：

```powershell
.\scripts\build.ps1 -Task clean
```

执行一次完整的干净重建：

```sh
make clean
make build
```

PowerShell 用户执行：

```powershell
.\scripts\build.ps1 -Task clean
.\scripts\build.ps1 -Task build
```

`make clean` 只会删除生成的编译产物，不会删除源码、迁移文档或包配置。

## 单独构建一个包

每个组件本身也是一个独立的 Lake 包。例如：

```sh
cd SeparationLogic
lake build
```

`unifysl` 当前没有设置默认 Lake 构建目标，因此需要显式指定 `Unifysl`：

```sh
cd unifysl
lake build Unifysl
```

验证完整迁移结果时，应当在 `Lean/` 目录使用 `make build`。只在 `examples`
中执行 `lake build`，不会构建其依赖包各自拥有的全部测试目标。

## Coq 源码版本

本仓库对应的 Coq 主仓库提交以及全部 Coq 子模块版本记录在
[`COQ_BASELINE.md`](COQ_BASELINE.md)。

更详细的迁移基线和已知兼容性差异分别记录在：

- [`docs/coq_source_baseline.md`](docs/coq_source_baseline.md)
- [`docs/migration_inconsistencies.md`](docs/migration_inconsistencies.md)
