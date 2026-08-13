# TraceLib

`tracelib` 是一个用于 **顺序程序（以状态关系/集合语义建模）** 的轻量级“执行轨迹（trace）”与“幽灵状态（ghost state）”验证库，面向 Coq 证明中对 **带标记事件的程序执行**、**递归/循环结构的轨迹化**、以及 **ghost code 与原程序等价性** 的刻画与推理。


## 主要内容

- **基础轨迹与标记事件**
  - `TraceBasic.v`：轨迹/事件的基础定义与操作。
  - `TraceLogic.v`：与轨迹相关的逻辑性质与证明辅助。
  - `TraceLib.v`：对外汇总导出入口。
- **递归/循环结构的轨迹化**
  - `TraceRecur.v`：递归结构的轨迹化工具与性质。
  - `TraceLoop.v`：循环/迭代结构的轨迹化（例如对集合元素的遍历 `forset'` 等）。
- **幽灵状态与等价性**
  - `GhostCode.v`：将程序提升到携带 ghost state 的程序、以及 `Gequiv`（带 ghost 的程序与原程序的等价）等规则与引理。
- **证明辅助**
  - `CommonTactics.v`：常用战术/引理集合。
  - `MapLib.v`：与映射/有限映射相关的辅助定义与引理（如有）。

## 依赖

`tracelib` 依赖本仓库内的一些基础库（以 `-R` 映射方式引入），主要包括：

- `sets/`（`SetsClass`）
- `fixedpoints/`（`FP`）
- `monadlib/`（`MonadLib`）
- `graph_lib/`（`GraphLib`）
- `coq-record-update/`（`RecordUpdate`）

具体编译参数请参考 `Makefile` 中的 `FLAG` 设置。

## 编译

在主仓库根目录初始化 submodule 后（含 `tracelib`）：

```bash
git submodule update --init --recursive
```

然后在 `tracelib` 目录下执行：

```bash
make
```

## 目录维护说明（给贡献者）

- 修改 `tracelib` 内容请在 `tracelib` 子仓库内提交；
- 主仓库只提交对 `tracelib` 的 submodule 指针更新，以及 `.gitmodules` 配置变更。


