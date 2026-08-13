# Rocq 库

## 一、支持的 Coq 版本

本目录使用 **Coq 8.20.1** 测试，推荐 OCaml 4.14.1。Coq 8.20.1 已属于 Rocq project，但早于命令行
重命名，因此预期 executable 仍为 `coqc`、`coqtop` 和 `coqdep`。Rocq 9.x 目前不能直接替代本仓库要求
的版本。

在仓库层面，Rocq/Coq 与 Lean 是两个可选证明后端。安装两者前先阅读
[`../README.md`](../README.md#proof-backend)。

## 二、安装

- Windows：从官方
  [Coq Platform 2025.01.0 release](https://github.com/rocq-prover/platform/releases/tag/2025.01.0)
  安装原生 **Windows 64 bit Coq 8.20**。
- Linux 与 macOS：在隔离的 opam switch 中安装精确版本：

```bash
opam init -y
opam update
opam switch create qcp-rocq ocaml-base-compiler.4.14.1
eval $(opam env --switch=qcp-rocq)
opam install coq.8.20.1
coqc --version
```

最后一条命令必须报告 8.20.1。Git、构建工具与 PATH 配置见平台说明：
[`../docs/windows-setup.md`](../docs/windows-setup.md)、
[`../docs/linux-setup.md`](../docs/linux-setup.md) 与
[`../docs/macos-setup.md`](../docs/macos-setup.md)。

## 三、配置入口

verification controller 与 Dune workflow 不读取 `Rocq/CONFIGURE` 或 `Rocq/unifysl/CONFIGURE`。
Windows agent 应 dot-source `scripts/setup-windows-env.ps1`；该脚本通过经过版本校验的绝对 executable 与
当前进程 PATH 让 controller、Dune 和 direct check 使用同一套 Coq 8.20.1。

只有人工使用本目录的 legacy Make workflow 时，Makefile 才会选择性读取大小写敏感、无扩展名的
`CONFIGURE`。当 `coqc` 已在 PATH 中时，Linux/macOS 通常不需要该文件；否则可在 `Rocq/` 与
`Rocq/unifysl/` 分别创建。

Linux/macOS 示例：

```ini
COQBIN = /absolute/path/to/coq/bin/
```

原生 Windows legacy Make 示例：

```ini
COQBIN = D:/path/to/Coq/bin/
SUF = .exe
```

`COQBIN` 必须以 `/` 结尾，并指向包含 `coqc` 与 `coqdep`（Windows 为对应 `.exe`）的目录。不要为了
Dune 或 agent workflow 创建第二套配置；它们以 `COQC_EXE`、`COQTOP_EXE`、`DUNE_REAL` 及对齐后的
PATH 为准。

## 四、编译方式

verification controller 使用精确 Dune target 与 dependency snapshot；下面的 Make 命令只供人工构建
legacy target。使用 Make 时先生成 dependency，再编译，并始终给并行参数指定上界。`-j4` 表示最多
四个 job；内存有限时减少或省略。禁止使用不带数字的 `make -j`，因为那会请求无界并行。

先构建 `Rocq/unifysl`：

```bash
make -C Rocq/unifysl depend
make -C Rocq/unifysl -j4
```

然后在 A 与 B 中只选择一个。

选项 A——只构建 core library，速度较快，不含 `Rocq/examples`：

```bash
make -C Rocq depend-core
make -C Rocq -j4 core
```

选项 B——构建 core library 与全部 generated examples：

```bash
make -C Rocq depend
make -C Rocq -j4 all
```

构建完成后即可按标准 Coq 8.20.1 development 使用这些库。

### 细分 Make target

只构建 core library：

```bash
make -C Rocq depend-core
make -C Rocq -j4 core
```

构建全部 generated examples：

```bash
make -C Rocq depend-examples
make -C Rocq -j4 examples
```

只构建一个 generated example subtree 时，dependency target 与 build target 必须成对使用：

```bash
make -C Rocq depend-examples-applications
make -C Rocq -j4 examples-applications

make -C Rocq depend-examples-qcp-democases
make -C Rocq -j4 examples-qcp-democases

make -C Rocq depend-examples-qcp-demo-feature-cases
make -C Rocq -j4 examples-qcp-demo-feature-cases

make -C Rocq depend-examples-qcp-demo-tutorial
make -C Rocq -j4 examples-qcp-demo-tutorial

make -C Rocq depend-examples-llm-friendly-cases
make -C Rocq -j4 examples-llm-friendly-cases

make -C Rocq depend-examples-llm-bench
make -C Rocq -j4 examples-llm-bench
```

还可以构建下列 focused libraries：

```bash
make -C Rocq coq-record-update
make -C Rocq tracelib
make -C Rocq algorithms
make -C Rocq convex-hull
```

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

## 五、证明中可用 tactic 简介

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
