# Rocq 库

使用 VS Code 时，请打开仓库根目录，以使用根目录的 `_CoqProject` 配置；不要单独打开 `Rocq/`。

## 一、支持的 Coq 版本

本目录使用 **Coq 8.20.1** 测试，推荐 OCaml 4.14.1。Coq 8.20.1 已属于 Rocq project，但早于命令行
重命名，因此预期 executable 仍为 `coqc`、`coqtop` 和 `coqdep`。Rocq 9.x 目前不能直接替代本仓库要求
的版本。

在仓库层面，Rocq/Coq 与 Lean 是两个可选证明后端。安装两者前先阅读
[`../README.md`](../README.md#proof-backend)。

## 二、环境准备

安装与 PATH 配置见对应平台文档：
[`Windows`](../docs/windows-setup.md)、
[`Linux`](../docs/linux-setup.md) 与
[`macOS`](../docs/macos-setup.md)。

## 三、编译方式

目前推荐使用 **dune** 构建，在仓库根目录运行：

```bash
dune build -j4
```

以下内容仅介绍保留的 **legacy Make** 用法。Make 命令也从仓库根目录执行，使用 `-C Rocq`
进入构建目录。

### Legacy Make 要求与行为

需要 **GNU Make 4.0 或更新版本**。

- Windows 使用 GNU Make，不是 `nmake`；
- Windows 可用 `winget install --id ezwinports.make --exact --source winget`
安装 GNU Make 4.4.1，不要使用仍为 3.81 的 `GnuWin32.Make`;
- macOS 自带的旧 Make 需要替换，例如使用 `gmake`）。

Make 自动发现 `.v` 文件，并按当前 dune 的 theory 范围、递归设置和排除规则选择源文件。
目录与文件名使用 `/` 分隔，仓库内相对路径不能包含空白。Make 会把长文件列表写入参数文件，
避免 Windows `cmd.exe` 命令行长度限制。

平台分支依据 GNU Make 的 `MAKE_HOST`：官方 `Windows32` 或 MinGW 构建使用 `cmd.exe`；
Linux、macOS、Cygwin、MSYS 构建使用 POSIX shell。
`MAKE_HOST` 的具体字符串不是手册规定的固定枚举；特殊定制版本可显式传入
`USE_WINDOWS_COMMANDS=yes` 或 `USE_WINDOWS_COMMANDS=`。

依赖图自动生成；新增、删除文件或修改 import 后会自动刷新，不需要先单独构建 `unifysl`，
也不需要手动执行 `depend`。旧 `depend` / `depend-*` 命令保留为强制刷新完整依赖图的兼容入口。
失败的依赖扫描不会覆盖已有依赖图，并会中止构建。

Make 的增量编译依据文件时间戳，而不是内容摘要。在同一秒内快速改写源文件时，已有的 `.vo` 可能
被错误判断为最新；需要强制复核时，先删除对应 `.vo` 再构建。

```bash
make -C Rocq -j4 core       # 默认目标：全部核心库
make -C Rocq -j4 all        # 与 dune 对齐的全部 Coq 文件
make -C Rocq -j4 examples   # 全部示例及所需依赖
make -C Rocq list-sources   # 查看实际选中的源文件，不运行 Coq
```

`-j4` 表示最多四个 job；内存有限时减少并行数，不要使用无上界的 `make -j`。
Make 的产物写在源文件旁，而 dune 写入 `_build`；从 Make 切换到 dune 前运行 `make -C Rocq clean`，
避免 `.glob` 等文件与 dune 生成规则冲突。

也可直接构建单个 `.vo` 或以下分组，依赖会自动补齐：

```bash
make -C Rocq -j4 examples-applications
make -C Rocq -j4 examples-qcp-democases
make -C Rocq -j4 examples-qcp-demo-feature-cases
make -C Rocq -j4 examples-qcp-demo-tutorial
make -C Rocq -j4 examples-llm-friendly-cases
make -C Rocq -j4 examples-llm-bench
make -C Rocq -j4 coq-record-update
make -C Rocq -j4 tracelib
make -C Rocq -j4 algorithms
make -C Rocq -j4 convex-hull
```

### Legacy Make 可选配置

当 `coqc` 与 `coqdep` 已在 PATH 中时，无需创建配置文件。需要指定其他安装路径时，
可在 `Rocq/CONFIGURE` 中设置：

```make
COQBIN = /absolute/path/to/coq/bin/
```

Windows 路径使用 `/`，例如 `COQBIN = D:/path/to/Coq/bin/`，无需配置 `.exe` 后缀。
`COQBIN` 必须以 `/` 结尾。也可以直接在 Make 命令行传入 `COQBIN`。
本 Makefile 只读取 `Rocq/CONFIGURE`，无需配置 `Rocq/unifysl/CONFIGURE`；dune 不使用这些文件。

### 清理 Make 输出

清理 Rocq Makefile 管理的全部输出：

```bash
make -C Rocq clean
```

也可只清理指定输出组：

```bash
make -C Rocq clean-core
make -C Rocq clean-examples
make -C Rocq clean-examples-applications
make -C Rocq clean-examples-qcp-democases
make -C Rocq clean-examples-qcp-demo-feature-cases
make -C Rocq clean-examples-qcp-demo-tutorial
make -C Rocq clean-examples-llm-friendly-cases
make -C Rocq clean-examples-llm-bench
make -C Rocq clean-deps
make -C Rocq clean-tmp
```

## 四、证明中可用 tactic 简介

对于结论 `P |-- Q`，下文称 $P$ 为前置条件、$Q$ 为后置条件；“前提”指 Coq hypothesis。

`Intros`：把前置条件中的纯命题引入前提。

`Intros_any`：实例化前置条件中的存在变量并引入前提，名称由 Coq 自动生成。

`Intros x`：把前置条件中的一个存在变量实例化为 $x$ 并引入前提。

`Intros_r_any`：实例化后置条件中的全称变量并引入前提，名称由 Coq 自动生成。

`Intros_r x`：把后置条件中的一个全称变量实例化为 $x$ 并引入前提。

`Exists x`：用 $x$ 填充后置条件中的存在变量。

`Exists_l x`：用 $x$ 填充前置条件中的全称变量。

`entailer!`：自动尝试消去 separation logic。

`sep_apply H`：尝试用 $H$ 变换结论，典型形式为 `P * Q |-- R`；它把前置条件中的 `P * Q` 替换为
`R`。

`prop_apply H`：尝试用 $H$ 变换结论，典型形式为 `P * Q |-- “ R ”`；它把纯命题 `“ R ”` 加入
前置条件。

`Left`：把 `P |-- Q || R` 变为 `P |-- Q`。

`Right`：把 `P |-- Q || R` 变为 `P |-- R`。

`Split`：把 `P || Q |-- R` 拆成 `P |-- R` 与 `Q |-- R` 两个分支。

`csimpl`：化简 notation。
