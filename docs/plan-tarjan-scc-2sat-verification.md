# 使用 QCP 框架证明 Tarjan SCC 算法正确性并用于 2-SAT 的全过程计划

> **⚠️ 架构变更说明 (2026-06-11)**
>
> 本计划编写时假设 SCC 基础定义在 `GraphLib/examples/scc_basic.v`。当前仓库已重构：
> - Tarjan 算法形式化已移至 `SeparationLogic/algorithms/Tarjan/`（8911 行，11 个文件）
> - `scc_basic.v` 已删除，其 SCC 数学定义（`mutually_reachable`、`is_SCC`、`scc_partition`、`condensation`）尚未在新架构中重写
> - 新架构使用 `OriginalGraphType`（无向图），而原 `scc_basic.v` 使用自建的 `DirectedGraphType`
> - **若恢复 SCC 正确性证明工作**，应在 `algorithms/Tarjan/` 下基于 `OriginalGraphType` 重建 SCC 数学规格层
>
> 本文档保留作为整体路线参考，但具体文件路径和依赖关系需按新架构调整。

## 目录

1. [项目背景与 QCP 框架概述](#1-项目背景与-qcp-框架概述)
2. [现有基础设施分析](#2-现有基础设施分析)
3. [总体路线图](#3-总体路线图)
4. [阶段一：Rocq 中 Tarjan SCC 算法的数学形式化](#4-阶段一rocq-中-tarjan-scc-算法的数学形式化)
5. [阶段二：C 语言的 Tarjan SCC 实现与标注](#5-阶段二c-语言的-tarjan-scc-实现与标注)
6. [阶段三：符号执行与 VC 生成](#6-阶段三符号执行与-vc-生成)
7. [阶段四：验证条件的证明](#7-阶段四验证条件的证明)
8. [阶段五：2-SAT 问题形式化与归约](#8-阶段五2-sat-问题形式化与归约)
9. [阶段六：集成与最终验证](#9-阶段六集成与最终验证)
10. [文件结构与交付物](#10-文件结构与交付物)
11. [工作量估算与风险评估](#11-工作量估算与风险评估)
12. [执行建议](#12-执行建议)

---

## 1. 项目背景与 QCP 框架概述

### 1.1 QCP 是什么

QCP（Qualified C Programming）是一个基于分离逻辑的 C 程序验证工具。它的核心工作流程为：

1. **编写带标注的 C 程序**
   - 前置条件（`Require`）和后置条件（`Ensure`）
   - 循环不变量（`Inv Assert`）
   - 中间断言（`Assert`）
   - 函数的逻辑变量声明（`With`）
   - 所有标注均使用分离逻辑断言语言编写

2. **运行符号执行**（`symexec` 命令行工具）
   - 逐条语句执行符号计算
   - 在每个标注点生成蕴含条件（entailment）
   - 输出三个 Rocq（Coq 8.20.1）文件：
     - `*_goal.v`：全部需要证明的验证条件（VC）
     - `*_proof_auto.v`：工具自动证明的 VC
     - `*_proof_manual.v`：需要人工补全证明的 VC

3. **在 Rocq 中证明验证条件**
   - 使用分离逻辑专用策略：`Intros`、`Exists`、`entailer!`、`sep_apply`、`prop_apply` 等
   - 结合标准 Coq 策略：`intros`、`destruct`、`induction`、`lia` 等
   - 证明目标形式为 `P |-- Q`（分离逻辑蕴含）

4. **最终检查**
   - 编译 Rocq 文件确保无 `Admitted` 或额外 `Axiom`
   - 验证 `*_goal_check.v` 通过
   - 清理临时文件

### 1.2 Agent 验证工作流

QCP 仓库支持结构化的 agent 验证工作流（详见 `AGENTS.md`），状态机如下：

```
intake → annotation → goal-frozen → vc-checking → vc-proving → final-check → done
```

- **主 agent**：独占 phase 切换、符号执行、Rocq 编译、最终检查
- **`annotation-subagent`**：在隔离 scratch 上迭代标注和 spec 定义，每轮标注后必须通过 `annotation-checking` 质量门
- **`vc-checking-subagent`**：对 manual VC 进行语义分类，给出 proof group 分组建议
- **`vc-proving-subagent`**：执行脚本化并发 worker 流水线证明 manual VC
- **`final-check`**：结构审计、Rocq 编译、`Admitted`/额外 `Axiom` 审查

### 1.3 分离逻辑断言语言速览

| 说明 | Rocq 写法 | C 标注写法 |
|------|-----------|------------|
| 分离合取 | `P ** Q` | `P * Q` |
| 存在量词 | `EX` | `exists` |
| 纯命题 | `[| P |]` | `P` |
| 4字节整数存储 | `p # Int \|-> v` | `data_at(p, int, v)` |
| 指针存储 | `p # Ptr \|-> v` | `data_at(p, int *, v)` |
| 结构体字段访问 | `x # "A" ->ₛ "f"` | `x -> f` |

---

## 2. 现有基础设施分析

### 2.1 GraphLib 图论库

位于 `SeparationLogic/GraphLib/`，这是一个基于 **Type Classes** 的高度抽象 Coq 图论形式化库。

**核心 Type Classes**：

```coq
Class Graph (G V E: Type) := {
  vvalid : G -> V -> Prop;       (* 顶点有效性 *)
  evalid : G -> E -> Prop;       (* 边有效性 *)
  step_aux : G -> E -> V -> V -> Prop  (* 边 e 连接 u 到 v *)
}.

Class Path (G V E: Type) `{Graph G V E} (P: Type) := {
  path_valid: G -> P -> Prop;
  head: P -> V;
  tail: P -> V;
  vertex_in_path: P -> list V;
  edge_in_path: P -> list E;
}.

Class RootedTree (G V E: Type) `{Graph G V E} `{GValid G} := {
  root: G -> V;
  root_is_valid: forall g, gvalid g -> vvalid g (root g);
  root_is_root: forall g x, gvalid g -> vvalid g x -> reachable g (root g) x;
  root_no_father: forall g x, gvalid g -> ~ step g x (root g);
  father_eunique: forall g x1 x2 e1 e2 y, ... -> e1 = e2;
}.
```

**库的层次结构**：

```
Graph / Path（抽象接口层）
    ↓
vpath / epath（具体实现层）
    ↓
Dijkstra / Floyd / Prim / Kruskal / Tarjan（应用层）
```

**与 SCC 直接相关的文件**：

| 文件 | 内容 |
|------|------|
| `graph_basic.v` | Graph Type Class 定义、step、reachable、StepValid 等 |
| `directed/rootedtree.v` | RootedTree Type Class、offspring、有根树归纳原理 |
| `directed/dfstree.v` | dfn_valid 定义（`dfn x < dfn y` 当 x 是 y 的父节点）、dfn 相关引理 |
| `directed/dfstree_dfn.v` | dfn 和 offspring 之间的更多性质 |
| `subgraph/subgraph.v` | 子图关系、增边/删边操作 |
| `reachable/reachable_basic.v` | 可达性基础定义与策略 |
| `reachable/reachable_restricted.v` | 受限可达性（不经过特定边的路径） |
| `examples/tarjan.v` | **Tarjan 桥定理的完整证明** |

### 2.2 `tarjan.v` 已有的关键成果

`examples/tarjan.v` 已经完整证明了 Tarjan 算法相关的**核心数学定理**：

1. **dfn 与 offspring 的关系**：`dfn_valid_offspring`（后代有更大的 dfn）
2. **low 值的定义与性质**：
   - `is_low`：low 是 `low_tree` 上 dfn 的最小值
   - `low_tree`：子树 ∪ 通过子树可达的非树边目标
   - `low_valid_implies_is_low`：局部 low 条件蕴含全局 low 性质（通过有根树归纳）
3. **无横叉边性质**：`no_cross_edge` 假设下的路径分析
4. **Tarjan 主定理**：`dfn x < low y ↔ is_bridge g e`（当 e 是树边 x→y 时）
5. **副定理**：非树边一定不是桥

这些成果**直接为 SCC 算法验证提供了理论基础**——特别是 `is_low`、`low_tree`、`closed_offspring` 等概念。

### 2.3 现有示例参考

根据 `AGENTS.md`，只参考 `QCP_demos_LLM` 版本的示例（不参考 `QCP_demos_human`）。与本计划最相关的现有示例：

- `sll_insert_sort.c`：展示了多函数、复杂循环不变量、函数调用
- `fme/fme.c`：展示了嵌套循环、复杂数据结构、多文件组织
- `kmp_rel.c` / `int_array_merge_rel.c`：展示了 refinement proof 模式

---

## 3. 总体路线图

本计划分六个阶段推进，各阶段之间存在依赖关系：

```
阶段一：Rocq 数学形式化（SCC 定义 + Tarjan 算法）
    ↓
阶段二：C 语言的 Tarjan SCC 实现与标注
    ↓
阶段三：符号执行与 VC 生成
    ↓
阶段四：验证条件的证明
    ↓
阶段五：2-SAT 的形式化与实现
    ↓
阶段六：集成与最终验证
```

建议**从阶段一开始，先不碰 C 代码**。在纯 Coq 中完成 SCC 理论后，再进入标注-符号执行-证明的循环。

---

## 4. 阶段一：Rocq 中 Tarjan SCC 算法的数学形式化

### 4.1 新建文件：`GraphLib/examples/scc_basic.v`

定义强连通分量的基本概念和性质。

#### 4.1.1 相互可达性与 SCC

```coq
(* 相互可达性 *)
Definition mutually_reachable {G V E: Type} `{Graph G V E} (g: G) (u v: V): Prop :=
  reachable g u v /\ reachable g v u.

(* 证明这是一个等价关系 *)
Lemma mutually_reachable_refl: forall g u, vvalid g u -> mutually_reachable g u u.
Lemma mutually_reachable_sym: forall g u v, mutually_reachable g u v -> mutually_reachable g v u.
Lemma mutually_reachable_trans: forall g u v w,
  mutually_reachable g u v -> mutually_reachable g v w -> mutually_reachable g u w.

(* SCC 定义为相互可达的等价类 *)
Definition is_SCC {G V E: Type} `{Graph G V E} (g: G) (s: V -> Prop): Prop :=
  (exists v, s v) /\                                  (* 非空 *)
  (forall u v, s u -> s v -> mutually_reachable g u v) /\  (* 内部相互可达 *)
  (forall u v, s u -> mutually_reachable g u v -> s v).    (* 极大性 *)
```

#### 4.1.2 SCC 划分

```coq
(* SCC 构成顶点的划分 *)
Definition scc_partition {G V E: Type} `{Graph G V E} (g: G) (sccs: list (V -> Prop)): Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\       (* 覆盖 *)
  (forall s, In s sccs -> is_SCC g s) /\                        (* 每个都是 SCC *)
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2). (* 互不相交 *)
```

#### 4.1.3 缩点图

```coq
(* 缩点图：以 SCC 为顶点 *)
Definition condensation_graph {G V E: Type} `{Graph G V E} (g: G) (sccs: list (V -> Prop)):
  Graph (list (V -> Prop)) (V -> Prop) (V * V) := ...

(* 缩点图是一个 DAG *)
Lemma condensation_is_dag: forall g sccs,
  scc_partition g sccs -> acyclic (condensation_graph g sccs).
```

### 4.2 新建文件：`GraphLib/examples/scc_tarjan.v`

形式化 Tarjan 算法本身（栈式 DFS 的数学描述）。

#### 4.2.1 算法状态

```coq
Record TarjanState (V: Type) := {
  ts_index    : V -> option nat;   (* None = 未访问 *)
  ts_lowlink  : V -> option nat;
  ts_onStack  : V -> bool;
  ts_stack    : list V;
  ts_sccs     : list (list V);     (* 已发现的 SCC *)
  ts_nextIdx  : nat;
}.

(* 初始状态 *)
Definition tarjan_init (vertices: list V): TarjanState V :=
  {| ts_index   := fun _ => None;
     ts_lowlink := fun _ => None;
     ts_onStack := fun _ => false;
     ts_stack   := nil;
     ts_sccs    := nil;
     ts_nextIdx := 0 |}.
```

#### 4.2.2 算法步骤

```coq
(* 对顶点 v 执行 strongconnect *)
Inductive strongconnect_step {V E: Type} `{Graph G V E} (g: G)
  : TarjanState V -> V -> TarjanState V -> Prop :=
  | sc_enter:    (* v 未访问，分配 index *)
      ts_index s v = None -> ...
  | sc_explore:  (* 遍历邻居 w *)
      ...
  | sc_backtrack: (* 回溯时更新 lowlink *)
      ...
  | sc_pop_scc:  (* lowlink[v] == index[v] 时弹出 SCC *)
      ...

(* 完整算法：对所有顶点迭代 *)
Inductive tarjan_multi_step {V E: Type} `{Graph G V E} (g: G)
  : TarjanState V -> TarjanState V -> Prop := ...
```

#### 4.2.3 主正确性定理

```coq
Theorem tarjan_scc_correctness:
  forall (g: OriginalGraphType V E) (gvalid: OriginalGraph_gvalid g),
  exists s_final,
    tarjan_multi_step g (tarjan_init (original_listV g)) s_final /\
    is_terminal s_final /\
    (* 发现的 SCC 构成顶点的划分 *)
    scc_partition g (map list_to_set s_final.(ts_sccs)) /\
    (* 每个 SCC 列表对应于正确的顶点集 *)
    (forall scc, In scc s_final.(ts_sccs) -> is_SCC g (list_to_set scc)).
```

### 4.3 新建文件：`GraphLib/examples/scc_characterization.v`

建立 DFS dfn/low 理论与 SCC 之间的桥梁。这是将 `tarjan.v` 的成果连接到 SCC 理论的关键步骤，也是阶段四 VC 证明的数学基础。

#### 4.3.1 关键引理

```coq
(* SCC 可以通过 low 值来刻画 *)
Lemma scc_by_low_root:
  forall g dfstree dfn low v,
  dfn_valid dfstree dfn ->
  is_low g dfstree dfn low ->
  low v = dfn v ->
  (* 在 dfstree 中，v 子树中所有 low >= dfn v 的顶点构成一个 SCC *)
  let scc_v := fun w => offspring dfstree v w /\ low w >= dfn v in
  is_SCC g scc_v.

(* 栈弹出子序列构成一个 SCC *)
Lemma stack_pop_is_scc:
  forall g dfstree dfn low stack stack' v,
  (* 前提：low[v] = dfn[v]，且栈包含 v *)
  pop_until stack v = Some (popped, stack') ->
  (* 则 popped 中的顶点构成一个 SCC *)
  is_SCC g (fun w => In w popped).

(* Tarjan 算法发现的 SCC 与 mutual_reachability 等价类是一致的 *)
Lemma tarjan_partition_matches_mutual_reach:
  forall g sccs,
  tarjan_scc_result g = sccs ->
  scc_partition g sccs /\
  (forall u v, mutually_reachable g u v <-> exists s, In s sccs /\ s u /\ s v).
```

---

## 5. 阶段二：C 语言的 Tarjan SCC 实现与标注

### 5.1 目录结构

```
QCP_examples/Applications_human/tarjan_scc/
├── tarjan_scc.c           # Tarjan SCC 算法实现
├── tarjan_scc_def.h       # C 结构体定义
├── tarjan_scc_lib.v       # common_case_formal_lib
├── common.strategies      # 通用策略文件（如需要）
└── tarjan_scc.strategies  # SCC 专用策略（如需要）
```

### 5.2 C 数据结构定义

```c
/* tarjan_scc_def.h */

// 邻接表的边节点
struct EdgeNode {
    int to;                   // 目标顶点编号
    struct EdgeNode *next;    // 下一条边
};

// 有向图：邻接表表示
struct Graph {
    int numVertices;
    struct EdgeNode **adj;    // 链表头指针数组
};

// Tarjan 算法的运行时状态
struct TarjanContext {
    int *index;               // DFS 编号数组，-1 表示未访问
    int *lowlink;             // low 值数组
    int *stack;               // 顶点栈
    int stackTop;             // 栈顶指针
    bool *onStack;            // 顶点是否在栈中
    int *sccIds;              // 每个顶点所属的 SCC ID
    int nextIndex;            // 下一个 DFS 编号
    int sccCount;             // 已发现的 SCC 数量
};
```

### 5.3 对应 Rocq 表示谓词（写入 `tarjan_scc_lib.v`）

```coq
(* 边链表表示谓词 *)
Fixpoint EdgeList_rep (x: addr) (edges: list Z): Assertion :=
  match edges with
  | nil => [| x = NULL |] && emp
  | to :: edges' =>
      [| x <> NULL |] &&
      EX next: addr,
        &(x # "EdgeNode" ->ₛ "to") # Int |-> to **
        &(x # "EdgeNode" ->ₛ "next") # Ptr |-> next **
        EdgeList_rep next edges'
  end.

(* 邻接数组表示谓词：arr 指向 numVertices 个 EdgeNode* 的数组，
   每个元素指向一个边链表 *)
Fixpoint AdjArray_rep (arr: addr) (n: nat) (adj: list (list Z)): Assertion :=
  match n, adj with
  | O, nil => emp
  | S n', edges :: adj' =>
      EX head: addr,
        (arr # Ptr |-> head) **
        EdgeList_rep head edges **
        AdjArray_rep (arr +ₚ 4) n' adj'
  | _, _ => [| False |]
  end.

(* 图的完整表示 *)
Definition Graph_rep (g: addr) (adj: list (list Z)): Assertion :=
  EX numV: Z, EX adjPtr: addr,
    &(g # "Graph" ->ₛ "numVertices") # Int |-> numV **
    &(g # "Graph" ->ₛ "adj") # Ptr |-> adjPtr **
    AdjArray_rep adjPtr (Z.to_nat numV) adj.

(* Tarjan 上下文的表示 *)
Definition TarjanContext_rep (ctx: addr) (n: nat)
    (index lowlink: list Z) (stack: list Z) (stackTop: Z)
    (onStack: list bool) (sccIds: list Z)
    (nextIndex sccCount: Z): Assertion :=
  EX idxPtr llPtr stkPtr osPtr sccPtr: addr,
    &(ctx # "TarjanContext" ->ₛ "index") # Ptr |-> idxPtr **
    &(ctx # "TarjanContext" ->ₛ "lowlink") # Ptr |-> llPtr **
    &(ctx # "TarjanContext" ->ₛ "stack") # Ptr |-> stkPtr **
    &(ctx # "TarjanContext" ->ₛ "stackTop") # Int |-> stackTop **
    &(ctx # "TarjanContext" ->ₛ "onStack") # Ptr |-> osPtr **
    &(ctx # "TarjanContext" ->ₛ "sccIds") # Ptr |-> sccPtr **
    &(ctx # "TarjanContext" ->ₛ "nextIndex") # Int |-> nextIndex **
    &(ctx # "TarjanContext" ->ₛ "sccCount") # Int |-> sccCount **
    IntArray_rep idxPtr n index **
    IntArray_rep llPtr n lowlink **
    IntArray_rep stkPtr n stack **
    BoolArray_rep osPtr n onStack **
    IntArray_rep sccPtr n sccIds.
```

### 5.4 核心函数：`strongconnect` 的标注

```c
void strongconnect(struct Graph *graph, int v, struct TarjanContext *ctx)
  /*@ With (adj: list (list Z)) (n: Z)
             (index lowlink: list Z) (stack: list Z) (stackTop: Z)
             (onStack: list bool) (sccIds: list Z)
             (nextIndex sccCount: Z)
             (G: OriginalGraphType Z Z)
      Require n == Zlength adj /\
              n <= INT_MAX /\
              0 <= v /\
              v < n /\
              graph_well_formed G adj /\
              Znth v index = -1 /\
              tarjan_invariant_partial G adj v index lowlink
                                       stack stackTop onStack sccIds
                                       nextIndex sccCount /\
              Graph_rep(graph, adj) *
              TarjanContext_rep(ctx, n, index, lowlink, stack,
                                stackTop, onStack, sccIds,
                                nextIndex, sccCount)
      Ensure exists index' lowlink' stack' stackTop' onStack' sccIds'
                    nextIndex' sccCount',
             (* index[v] 已被赋值 *)
             Zlength index' == n /\
             Znth v index' != -1 /\
             (* lowlink[v] 正确刻画包含 v 的 SCC 的根 *)
             lowlink_correct_for_root G dfstree dfn index' lowlink' v /\
             (* 所有包含 v 的 SCC 中的顶点已经出栈并分配了 SCC ID *)
             scc_completed_at G adj v sccIds' sccCount' /\
             (* 对其他顶点的副作用受控 *)
             tarjan_side_effect index index' lowlink lowlink' stack stack' ... /\
             Graph_rep(graph, adj) *
             TarjanContext_rep(ctx, n, index', lowlink', stack',
                               stackTop', onStack', sccIds',
                               nextIndex', sccCount')
  */
{
    // DFS 进入：分配编号，入栈
    ctx->index[v] = ctx->nextIndex;
    ctx->lowlink[v] = ctx->nextIndex;
    ctx->nextIndex++;
    ctx->stack[ctx->stackTop] = v;
    ctx->stackTop++;
    ctx->onStack[v] = true;

    /*@ Assert
        exists index1 lowlink1 stack1 stackTop1,
        index1 == set_nth(index, v, nextIndex@pre) /\
        lowlink1 == set_nth(lowlink@pre, v, nextIndex@pre) /\
        stackTop1 == stackTop@pre + 1 /\
        data_at(&(ctx -> index[v]), nextIndex@pre) *
        data_at(&(ctx -> lowlink[v]), nextIndex@pre) *
        data_at(&(ctx -> nextIndex), nextIndex@pre + 1) *
        data_at(&(ctx -> stack[stackTop@pre]), v) *
        data_at(&(ctx -> stackTop), stackTop1) *
        data_at(&(ctx -> onStack[v]), true) *
        ...
    */

    // 遍历 v 的所有邻居
    struct EdgeNode *e = graph->adj[v];
    /*@ Inv
        exists e_ptr index2 lowlink2 stack2 stackTop2 onStack2
               sccIds2 nextIndex2 sccCount2 processed,
        (* 不变量：对已处理的邻居 w，lowlink[v] 已更新 *)
        forall w, In w processed ->
          update_lowlink_correct G dfstree dfn index2 lowlink2 v w /\
          if Znth w index2 == -1 then
            (* 未访问的邻居：已递归处理 *)
            scc_completed_for_subtree G adj w sccIds2 sccCount2
          else if Znth w onStack2 then
            (* 在栈中的邻居：已用 index[w] 更新 lowlink[v] *)
            lowlink2[v] <= index2[w]
        /\
        EdgeList_seg(graph->adj[v], e, e_ptr, processed, adj_nth adj v) *
        TarjanContext_rep(ctx, n, index2, lowlink2, stack2,
                          stackTop2, onStack2, sccIds2,
                          nextIndex2, sccCount2)
    */
    while (e != NULL) {
        int w = e->to;

        /*@ Assert
            exists w_val,
            data_at(&(e -> to), w_val) *
            data_at(&(e -> next), e_next) *
            ...
        */

        if (ctx->index[w] == -1) {
            /* w 未访问，递归调用 */
            strongconnect(graph, w, ctx);
            /*@ Assert
                exists index3 lowlink3 ...,
                (* strongconnect 的后置条件在此生效 *)
                Znth w index3 != -1 /\
                scc_completed_at G adj w sccIds3 sccCount3 /\
                ...
            */
            if (ctx->lowlink[w] < ctx->lowlink[v]) {
                ctx->lowlink[v] = ctx->lowlink[w];
            }
        } else if (ctx->onStack[w]) {
            /* w 在当前栈中（回边） */
            if (ctx->index[w] < ctx->lowlink[v]) {
                ctx->lowlink[v] = ctx->index[w];
            }
        }

        e = e->next;
    }

    /*@ Assert
        (* 所有邻居处理完毕 *)
        lowlink_fully_updated G dfstree dfn index lowlink v
    */

    /* 弹出 SCC */
    if (ctx->lowlink[v] == ctx->index[v]) {
        /*@ Assert
            exists sccMembers,
            stack_prefix(ctx->stack, ctx->stackTop@pre, ctx->stackTop, v, sccMembers) /\
            is_SCC G (list_to_set sccMembers)
        */
        int w;
        do {
            ctx->stackTop--;
            w = ctx->stack[ctx->stackTop];
            ctx->onStack[w] = false;
            ctx->sccIds[w] = ctx->sccCount;
        } while (w != v);
        ctx->sccCount++;
    }
}
```

### 5.5 主函数：`tarjan_scc` 的标注

```c
void tarjan_scc(struct Graph *graph, struct TarjanContext *ctx)
  /*@ With (adj: list (list Z)) (n: Z) (G: OriginalGraphType Z Z)
      Require n == Zlength adj /\
              n <= INT_MAX /\
              graph_well_formed G adj /\
              Graph_rep(graph, adj) *
              TarjanContext_init(ctx, n)   (* 所有数组已分配，初始化为 -1/false *)
      Ensure exists sccIds sccCount,
             (* 每个顶点被分配了 SCC ID *)
             Zlength sccIds == n /\
             (forall i, 0 <= i < n -> Znth i sccIds >= 0 /\ Znth i sccIds < sccCount) /\
             (* 两个顶点有相同的 SCC ID 当且仅当它们相互可达 *)
             (forall i j, 0 <= i < n -> 0 <= j < n ->
               Znth i sccIds == Znth j sccIds <->
               mutually_reachable G (Z.to_nat i) (Z.to_nat j)) /\
             (* SCC 数量正确 *)
             sccCount == scc_count G /\
             Graph_rep(graph, adj) *
             TarjanContext_rep_final(ctx, n, sccIds, sccCount)
  */
{
    int v;

    /*@ Inv
        exists index lowlink stack stackTop onStack sccIds nextIndex sccCount,
        (* 对前 v 个顶点，如果未访问，已通过 DFS 处理 *)
        (forall i, 0 <= i < v ->
           Znth i index != -1 ->   (* 已编号 *)
           scc_assigned G adj i sccIds sccCount) /\
        (* 未访问的顶点 index 为 -1 *)
        (forall i, v <= i < n -> Znth i index == -1) /\
        (* SCC 计数正确 *)
        partial_scc_invariant G adj v index lowlink stack
                               stackTop onStack sccIds nextIndex sccCount /\
        Graph_rep(graph, adj) *
        TarjanContext_rep(ctx, n, index, lowlink, stack,
                          stackTop, onStack, sccIds,
                          nextIndex, sccCount)
    */
    for (v = 0; v < graph->numVertices; v++) {
        if (ctx->index[v] == -1) {
            strongconnect(graph, v, ctx);
            /*@ Assert scc_completed_for_root G adj v ctx->sccIds ctx->sccCount */
        }
    }
}
```

### 5.6 关键标注挑战与应对

| 挑战 | 应对策略 |
|------|----------|
| `strongconnect` 是递归函数 | 使用 QCP 的函数规约机制。在调用点通过前置条件匹配来实例化逻辑变量，后置条件中的 existentials 在调用后引入 |
| 对数组的细粒度更新 | 使用 ArrayLib 谓词（`IntArray_rep`、`BoolArray_rep`）。标注中显式声明每次数组访问的权限 |
| 递归调用中的栈帧 | 递归函数的逻辑变量在每次调用时独立量化。将"调用前的状态"保存在 `@pre` 标记变量中 |
| DFS 树结构与 C 迭代过程的对应 | 在 `common_case_formal_lib` 中证明一个引理：C 实现的访问顺序恰好产生一个合法的 DFS 树（dfstree） |
| 收缩传值后的不变量维护 | 在循环体中显式声明每个变量修改后的新旧值关系 |
| 结构体字段访问的权限展开 | 使用 `Assert` + `which implies` 语法手动展开 `sll` / `EdgeList_rep` 以获得内部字段的 `data_at` 权限 |

---

## 6. 阶段三：符号执行与 VC 生成

### 6.1 运行符号执行

```bash
linux-binary/symexec \
  --input-file=QCP_examples/Applications_human/tarjan_scc/tarjan_scc.c \
  --goal-file=SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_goal.v \
  --proof-auto-file=SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_proof_manual.v \
  --coq-logic-path=SimpleC.EE.Applications_human.tarjan_scc \
  -slp QCP_examples/Applications_human/ SimpleC.EE.Applications_human \
  -IQCP_examples/QCP_demos_LLM/ \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --no-exec-info
```

### 6.2 迭代调试流程

标注调试是不可避免的迭代过程：

```
编写/修改 C 标注
    → 运行 symexec
    → 检查错误输出（缺失权限、无法实例化等）
    → 分析生成的 goal 文件中哪个 VC 失败
    → 回到标注修正
    → 重复直到 symexec 成功到达文件尾
```

使用 `qcp-mcp` 进行**交互式增量检查**可以大幅加速此过程。在 QIDE VS Code 扩展中，`Alt+⇒` 可以逐步执行符号执行，在每一步检查当前符号状态。

### 6.3 预期的 VC 分类

符号执行成功后，生成的 VC 可预分类为：

**A 类：直接内存布局 VC（预期 40%+ 自动解决）**
- 结构体字段访问权限（`e->to`、`e->next`）
- 数组读写权限（`index[v]`、`lowlink[v]`）
- 栈入栈出权限（`stack[stackTop]`）

**B 类：函数调用参数实例化 VC（预期 20% 策略解决）**
- `strongconnect(graph, w, ctx)` 调用处：匹配前置条件、分离内存帧
- 可能需要自定义 `tarjan_scc.strategies` 指导工具分离 Graph/TarjanContext

**C 类：循环不变量维护 VC（预期 25% 需要手动证明）**
- 外层循环：v 的增加保持不变量
- 邻居遍历循环：e 的移动保持不变量
- SCC 弹出循环：栈收缩保持不变量

**D 类：纯数学命题 VC（预期 15% 需要深入手动证明）**
- `lowlink` 更新保持 `is_low` 性质
- 栈弹出子序列构成 SCC
- 后置条件中的 `mutually_reachable` 等价性

### 6.4 策略文件

如需要自定义策略，创建 `QCP_examples/Applications_human/tarjan_scc/tarjan_scc.strategies`：

```
# 用于分离 Graph_rep 和 TarjanContext_rep 的策略
# 在函数调用时指导工具如何匹配前提

# 匹配 Graph_rep
pattern: Graph_rep(g, adj) * TarjanContext_rep(ctx, ...) |-- Graph_rep(g, adj)
action: cancel Graph_rep

# 匹配 IntArray_rep 读取
pattern: IntArray_rep(arr, n, l) |-- data_at(arr + offset, Int, v)
action: ...
```

运行策略检查：

```bash
linux-binary/StrategyCheck \
  --strategy-folder-path=SeparationLogic/examples/Applications_human/tarjan_scc/ \
  --coq-logic-path=SimpleC.EE.Applications_human.tarjan_scc \
  --input-file=QCP_examples/Applications_human/tarjan_scc/tarjan_scc.strategies \
  --no-exec-info
```

---

## 7. 阶段四：验证条件的证明

### 7.1 设置证明环境

在 `SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_lib.v` 中：

- 导入 GraphLib（`graph_basic`、`reachable_basic`、`rootedtree`、`dfstree`、`tarjan`、`scc_basic`、`scc_tarjan`、`scc_characterization`）
- 导入 ArrayLib（`ArrayLib`、`IntLib`）
- 导入分离逻辑策略库
- 定义阶段二中的所有表示谓词
- 陈述辅助引理：
  - `graph_rep_open`：展开 `Graph_rep` 以暴露单个 `data_at`
  - `edge_list_read`：读取边链表节点的 `to` 和 `next`
  - `int_array_read` / `int_array_write`：IntArray 的读写引理
  - `tarjan_context_frame`：TarjanContext 各字段是分离的
- 记录 `lib_frozen_prefix_end_line` 和 `lib_frozen_prefix_snapshot`

### 7.2 VC 检查阶段（`vc-checking`）

主 agent 启动 `vc-checking-subagent`，对 `*_proof_manual.v` 中的每个 VC 进行语义分类：

| Proof Group | 描述 | 估计数量 | 策略 |
|-------------|------|---------|------|
| Group 1 | 直接 entailer 可解 | ~30% | `entailer!` 一步完成 |
| Group 2 | 需要简单引理 | ~25% | 应用 `sep_apply graph_rep_open` 等再 `entailer!` |
| Group 3 | 需要 low/dfn 性质 | ~20% | 引用 `tarjan.v` 和 `scc_characterization.v` 的引理 |
| Group 4 | 深度数学（SCC 正确性） | ~15% | 结合分离逻辑与图论的复杂证明 |
| Group 5 | 可能语义不可证 | ~10% | 回到 annotation 阶段修正 |

输出：每个 VC 的 witness 分诊结论和自然语言 proof group 分组。

### 7.3 VC 证明阶段（`vc-proving`）

使用 `vc-proving` 技能的**脚本化并发 worker 流水线**：

1. **Split**（`split_manual_goals.py`）：将 `*_proof_manual.v` 按 proof group 拆分为 worker-local manual 文件
2. **Prepare**（`prepare_agent.py` / `prepare_group_workdir.py`）：为每个 worker 创建工作目录和 `worker_helper_scratch_lib`
3. **Run**（`run_agent_concurrent.py`）：并发启动 Codex worker，每个 worker 在隔离的 `rocq-mcp` 会话中证明分配到的 VC
4. **Validate**（`validate_and_merge.py` / `verify_manual_goals.py`）：检查所有 VC 已证明（无 `Admitted`）、合并 manual
5. **Migrate**（`migrate_helpers_to_lib.py`）：将审计通过的 helper lemmas 迁移到 `task_local_scratch_lib`→`common_case_formal_lib`

#### Group 3 证明示例

```coq
(* VC: state after processing neighbor w implies loop invariant *)
Lemma neighbor_processed_preserves_invariant:
  forall G dfstree dfn low index lowlink stack ...,
  (* 前提：处理 w 后的状态 *)
  ...
  |--
  (* 结论：不变量仍然成立 *)
  EX index' lowlink' ..., ... ** TarjanContext_rep ...
Proof.
  intros. Intros.
  (* 使用 GraphLib tarjan.v 中的引理 *)
  sep_apply lowlink_update_preserves_is_low.
  { (* 证明更新条件 *) ... }
  entailer!.
Qed.
```

#### Group 4 证明示例（核心困难 VC）

```coq
(* VC: lowlink[v] == index[v] 时弹出的顶点构成一个 SCC *)
Lemma pop_scc_when_low_equals_index:
  forall G dfstree dfn low stack stack' v popped,
  dfn_valid dfstree dfn ->
  is_low G dfstree dfn low ->
  low v = dfn v ->
  pop_until_stack stack v = Some (popped, stack') ->
  ...
  |--
  is_SCC G (fun w => In w popped).
Proof.
  intros.
  (* 这需要深入的图论证明，连接 GraphLib 已有的理论 *)
  apply scc_characterization.stack_pop_is_scc with (g := G) (dfstree := dfstree); auto.
  (* 从 C 状态重建 dfstree *)
  - (* 证明 C 的访问顺序产生合法的 DFS 树 *)
    apply build_dfstree_from_tarjan_trace; auto.
  - (* 证明 low 值满足 is_low *)
    apply lowlink_implies_is_low; auto.
Qed.
```

### 7.4 分离逻辑策略参考

根据 `SeparationLogic/README.md`，可用的主要策略：

| 策略 | 用途 |
|------|------|
| `Intros` | 将前提中的纯命题移入 Coq 上下文 |
| `Intros x` | 实例化前提中的存在量词为 `x` |
| `Exists x` | 用 `x` 填充结论中的存在量词 |
| `Exists_l x` | 用 `x` 填充前提中的全称量词 |
| `entailer!` | 自动尝试消除分离逻辑目标 |
| `sep_apply H` | 应用引理 `H` 转换前提（`P * Q \|-- R` 形式） |
| `prop_apply H` | 应用引理 `H` 添加纯命题 |
| `csimpl` | 简化记号 |

---

## 8. 阶段五：2-SAT 问题形式化与归约

### 8.1 新建文件：`GraphLib/examples/two_sat.v`

#### 8.1.1 2-SAT 的形式化

```coq
(* 文字：变量编号 + 极性 *)
Definition literal := (Z * bool).  (* (var, true) = 正文字，(var, false) = 负文字 *)
Definition negate (l: literal): literal := (fst l, negb (snd l)).

(* 子句：两个文字的析取 *)
Definition clause := (literal * literal).

(* 公式：子句的列表 *)
Definition formula := list clause.

(* 赋值 *)
Definition assignment := Z -> bool.

(* 文字求值 *)
Definition eval_literal (a: assignment) (l: literal): bool :=
  if snd l then a (fst l) else negb (a (fst l)).

(* 子句和公式的可满足性 *)
Definition satisfies_clause (a: assignment) (c: clause): Prop :=
  eval_literal a (fst c) = true \/ eval_literal a (snd c) = true.

Definition satisfies (a: assignment) (f: formula): Prop :=
  forall c, In c f -> satisfies_clause a c.

Definition satisfiable (f: formula): Prop :=
  exists a, satisfies a f.
```

#### 8.1.2 蕴含图构造

```coq
(* 对公式 f 构造蕴含图（implication graph）：
   顶点：2 * numVars 个顶点（每个变量对应两个文字）
   边：对每个子句 (a \/ b)，添加边 (~a -> b) 和 (~b -> a) *)
Definition implication_graph (f: formula) (numVars: Z): OriginalGraphType Z Z := ...

(* 蕴含图的关键性质 *)
Lemma implication_graph_meaning:
  forall f numVars G,
  G = implication_graph f numVars ->
  forall l1 l2,
  reachable G (encode_literal l1) (encode_literal l2) <->
  (forall a, satisfies a f -> eval_literal a l1 = true -> eval_literal a l2 = true).
```

#### 8.1.3 2-SAT 定理

```coq
(* 主定理：公式可满足 当且仅当 没有变量与其否定在同一个 SCC *)
Theorem two_sat_characterization:
  forall f numVars,
  (forall c, In c f -> valid_clause c numVars) ->
  (satisfiable f <->
   forall v, 1 <= v <= numVars ->
     ~ same_SCC (implication_graph f numVars) (v, true) (v, false)).

(* SCC 测试的正确性 *)
Lemma same_scc_implies_contradiction:
  forall f numVars v,
  same_SCC (implication_graph f numVars) (v, true) (v, false) ->
  ~ satisfiable f.

(* 从缩点图的拓扑序构造满足性赋值 *)
Lemma build_assignment_from_scc_order:
  forall f numVars,
  (forall v, 1 <= v <= numVars ->
    ~ same_SCC (implication_graph f numVars) (v, true) (v, false)) ->
  exists a, satisfies a f.
```

### 8.2 C 语言的 2-SAT 实现

创建 `QCP_examples/Applications_human/tarjan_scc/two_sat.c`：

```c
#include "tarjan_scc_def.h"

// 2-SAT 求解器
// 返回 true 表示可满足，并将赋值写入 assignment 数组
// 返回 false 表示不可满足
int two_sat(int numVars, int *clauseA, int *clauseB, int numClauses,
            int *assignment)
  /*@ With (f: formula) (nv nc: Z)
      Require nv == numVars /\
              nc == numClauses /\
              numVars > 0 /\
              numVars <= INT_MAX / 2 /\
              2 * numVars <= INT_MAX /\
              numClauses >= 0 /\
              numClauses <= INT_MAX /\
              formula_from_arrays clauseA clauseB numClauses f /\
              (* clauseA, clauseB 编码为整数：
                 正数 v 表示文字 v，
                 负数 -v 表示文字 ~v *)
              int_array_rep(clauseA, nc, ...) *
              int_array_rep(clauseB, nc, ...) *
              int_array_undef(assignment, nv)
      Ensure exists a,
             ((__return == 1 && satisfies a f &&
               assignment_holds(assignment, nv, a)) ||
              (__return == 0 && ~ satisfiable f)) /\
             int_array_rep(assignment, nv, ...)
  */
{
    // 步骤 1：构造蕴含图
    // 顶点数 = 2 * numVars（每个变量对应正负两个文字）
    int n = 2 * numVars;
    struct Graph *graph = build_implication_graph(clauseA, clauseB,
                                                   numClauses, numVars);

    // 步骤 2：分配 Tarjan 上下文
    struct TarjanContext ctx;
    allocate_tarjan_context(&ctx, n);

    // 步骤 3：运行 Tarjan SCC
    tarjan_scc(graph, &ctx);

    // 步骤 4：检查每个变量的正负文字是否在同一 SCC
    /*@ Inv
        forall i, 0 <= i < v -> ctx.sccIds[2*i] != ctx.sccIds[2*i + 1]
    */
    for (int v = 0; v < numVars; v++) {
        if (ctx.sccIds[2 * v] == ctx.sccIds[2 * v + 1]) {
            // 矛盾：v 和 ~v 在同一 SCC 中
            free_graph(graph);
            free_tarjan_context(&ctx);
            return 0;
        }
    }

    // 步骤 5：根据 SCC 拓扑序构造赋值
    // SCC ID 越小的 SCC 在缩点图的拓扑序中越靠前
    // 如果 SCC(~x) 的 ID 小于 SCC(x)，则设 x = true
    // 否则设 x = false
    /*@ Inv
        forall i, 0 <= i < v ->
          assignment[i] == (ctx.sccIds[2*i + 1] < ctx.sccIds[2*i] ? 1 : 0) /\
          consistent_with_scc_order G i assignment[i] ctx.sccIds
    */
    for (int v = 0; v < numVars; v++) {
        if (ctx.sccIds[2 * v + 1] < ctx.sccIds[2 * v]) {
            assignment[v] = 1;   // ~v 的 SCC 拓扑序更前，设 x = true
        } else {
            assignment[v] = 0;   // x 的 SCC 拓扑序更前，设 x = false
        }
    }

    free_graph(graph);
    free_tarjan_context(&ctx);
    return 1;
}
```

### 8.3 2-SAT 的 VC 证明策略

2-SAT 验证的关键在于**归约**——C 实现步骤与 `two_sat.v` 中形式化定理之间的对应：

| C 实现 | 对应的 Coq 定理 |
|--------|----------------|
| `build_implication_graph` | `implication_graph` 构造 |
| `tarjan_scc` 调用 | `tarjan_scc_correctness`（阶段四的产出） |
| `sccIds[2*v] == sccIds[2*v+1]` 检查 | `same_scc_implies_contradiction` |
| 按 SCC 序赋值 | `build_assignment_from_scc_order` |

因为 `two_sat.c` 调用的是**已验证的 `tarjan_scc`**，其前置条件只需要匹配 `tarjan_scc` 的前置条件。2-SAT 的额外 VC 主要是：

1. 蕴含图构造保持了语义对应关系
2. SCC ID 相等性检查正确检测了"同 SCC"条件
3. 赋值构造产生一个满足性赋值

---

## 9. 阶段六：集成与最终验证

### 9.1 文件编译依赖

确保 Rocq 文件之间的依赖正确：

```
GraphLib/graph_basic.v
    ↓
GraphLib/reachable/*.v、directed/*.v、subgraph/*.v
    ↓
GraphLib/examples/tarjan.v（已有）
GraphLib/examples/scc_basic.v（新增）
GraphLib/examples/scc_tarjan.v（新增）
GraphLib/examples/scc_characterization.v（新增）
GraphLib/examples/two_sat.v（新增）
    ↓
SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_lib.v
    ↓
SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_goal.v
SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_proof_auto.v
SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_proof_manual.v
SeparationLogic/examples/Applications_human/tarjan_scc/two_sat_goal.v
SeparationLogic/examples/Applications_human/tarjan_scc/two_sat_proof_auto.v
SeparationLogic/examples/Applications_human/tarjan_scc/two_sat_proof_manual.v
```

### 9.2 多规约层次

使用 QCP 的多规约机制：

```c
// tarjan_scc 的实现规约（用于验证函数体）
void tarjan_scc(struct Graph *graph, struct TarjanContext *ctx)
  /*@ impl_spec
      Require ...
      Ensure sccIds 和 sccCount 对应 tarjan_algorithm_trace...
  */

// tarjan_scc 的抽象规约（供 two_sat 等调用者使用）
void tarjan_scc(struct Graph *graph, struct TarjanContext *ctx)
  /*@ abstract_spec <= impl_spec
      Require ...
      Ensure *(ctx->sccIds) 是 SCC 划分的正确编码
  */
```

在 `two_sat.c` 中指定使用哪个规约：

```c
tarjan_scc(graph, &ctx) /*@ where (abstract_spec) */;
```

### 9.3 Final-Check 检查清单

根据 `AGENTS.md` 的完成标准：

1. **符号执行**：已到达文件尾，生成文件是最新的
2. **手动 VC**：所有 manual VC 都已完成证明（无 `Admitted`）
3. **Goal check**：`*_goal_check.v` 编译通过
4. **Proof manual 审计**：
   - `*_proof_manual.v` 只含 witness proofs，无 helper lemmas
   - 无新增顶层 `Definition`/`Fixpoint`/`Inductive`/`Axiom`
5. **Common lib 审计**：
   - `common_case_formal_lib` 无可疑 spec 定义（不是 C 算法镜像）
   - 冻结前缀未被改写
   - 冻结前缀后的 helper imports 均为审计通过的 `Require Import` 行
   - helper lemmas 均已证明
6. **Rocq 编译**：`coqc` 全量编译通过
7. **清理**：`.tmp` 文件、`.aux` 文件、临时 scratch 删除完毕

### 9.4 最终编译命令

```bash
cd SeparationLogic

# 编译核心库
make depend-core && make core

# 编译 GraphLib（包括新增的 scc 文件）
cd GraphLib && make && cd ..

# 编译 tarjan_scc 案例
make depend-examples-applications && make examples-applications
```

---

## 10. 文件结构与交付物

### 10.1 新增文件清单

```
QCP_examples/Applications_human/tarjan_scc/
├── tarjan_scc_def.h              # C 结构体定义
├── tarjan_scc.c                  # Tarjan SCC 实现（带标注）
├── two_sat.c                     # 2-SAT 求解器（带标注）
├── common.strategies             # 通用策略（如需要）
├── tarjan_scc.strategies         # SCC 专用策略（如需要）
└── two_sat.strategies            # 2-SAT 专用策略（如需要）

SeparationLogic/examples/Applications_human/tarjan_scc/
├── tarjan_scc_goal.v             # 生成的：SCC 验证条件
├── tarjan_scc_proof_auto.v       # 生成的：自动证明
├── tarjan_scc_proof_manual.v     # 人工证明（最终所有 VC 被证明）
├── tarjan_scc_goal_check.v       # 生成的：一致性检查
├── two_sat_goal.v                # 生成的：2-SAT 验证条件
├── two_sat_proof_auto.v          # 生成的：自动证明
├── two_sat_proof_manual.v        # 人工证明（最终所有 VC 被证明）
├── two_sat_goal_check.v          # 生成的：一致性检查
└── tarjan_scc_lib.v              # common_case_formal_lib（两个 C 文件共用）

SeparationLogic/GraphLib/examples/
├── scc_basic.v                   # 新增：SCC 定义、等价关系、划分、缩点图
├── scc_tarjan.v                  # 新增：Tarjan 算法的数学描述与正确性定理
├── scc_characterization.v        # 新增：SCC 与 dfn/low 之间的桥梁引理
└── two_sat.v                     # 新增：2-SAT 归约的形式化与正确性定理
```

### 10.2 不修改的已有文件

- `SeparationLogic/GraphLib/examples/tarjan.v`（直接引用）
- `SeparationLogic/GraphLib/*.v`（核心库，只读引用）
- `SeparationLogic/SeparationLogic/*.v`（分离逻辑库，只读引用）
- `SeparationLogic/ArrayLib/*.v`（数组库，只读引用）

---

## 11. 工作量估算与风险评估

### 11.1 工作量估算

| 阶段 | 子任务 | 预估人周 | 关键交付物 |
|------|--------|---------|-----------|
| **一** | 阶段一共 3 个 `.v` 文件 | **3–4 周** | `scc_basic.v`, `scc_tarjan.v`, `scc_characterization.v` |
| | 1.1 SCC 基础定义与性质 | 1 周 | `scc_basic.v` |
| | 1.2 Tarjan 算法的数学描述 | 1–1.5 周 | `scc_tarjan.v` |
| | 1.3 dfn/low 与 SCC 的桥梁 | 1–1.5 周 | `scc_characterization.v` |
| **二** | C 实现与标注 | **4–5 周** | `tarjan_scc.c`, `two_sat.c`, `tarjan_scc_lib.v` |
| | 2.1 表示谓词定义 | 0.5 周 | `tarjan_scc_lib.v` |
| | 2.2 `strongconnect` 标注 | 2–3 周 | 核心递归函数标注 |
| | 2.3 `tarjan_scc` 主函数标注 | 1 周 | 外层循环标注 |
| | 2.4 `two_sat` 标注 | 0.5 周 | 调用已验证的 tarjan_scc |
| **三** | 符号执行迭代 | **1–2 周** | `*_goal.v`, `*_proof_*.v` |
| | 3.1 tarjan_scc 的 symexec | 1 周 | 生成正确的 VC |
| | 3.2 two_sat 的 symexec | 0.5 周 | 较简单（主要靠函数调用） |
| | 3.3 策略文件编写 | 0.5 周 | `.strategies` 文件 |
| **四** | VC 证明 | **3–5 周** | 全部 VC 被证明 |
| | 4.1 Group 1–2 VC（简单） | 0.5 周 | entailer! 一步解决 |
| | 4.2 Group 3 VC（中等） | 1–1.5 周 | low/dfn 性质 |
| | 4.3 Group 4 VC（困难） | 1.5–2 周 | SCC 正确性的深度证明 |
| | 4.4 迭代修正 | 0.5–1 周 | 标注与证明之间的往返 |
| **五** | 阶段五 2-SAT 形式化 | **1–2 周** | `two_sat.v` + 证明 |
| **六** | 集成与 final-check | **1 周** | 编译通过，checklist 完成 |
| **总计** | | **13–19 周** | |

- **单人总预估**：约 4–5 个月
- **两人团队**：约 2.5–3 个月（阶段二和阶段四可并行推进）
- **有经验团队（3 人）**：约 2–2.5 个月（纯 Coq / 标注 / 证明可部分并行）

### 11.2 风险矩阵

| 风险 | 可能性 | 影响 | 缓解措施 |
|------|--------|------|----------|
| `strongconnect` 的递归函数规约在 QCP 中不被充分支持 | 中 | 高：可能需要重新设计 | 尽早用最小递归示例（如阶乘）测试递归支持；准备迭代版本作为备选 |
| 标注调试循环耗时过长 | 高 | 中：推迟进度 | 使用 `qcp-mcp` 交互式验证做增量检查；从最简单的标注（只有前后置条件）开始，逐步细化不变量 |
| SCC 正确性的数学证明比预期更深 | 中 | 高：核心定理无法按时完成 | 先证一个简化版本（固定图、无递归），再泛化；充分利用已有的 `tarjan.v` 引理 |
| GraphLib 的 Type Class 机制与自动生成的 VC 不兼容 | 低 | 中：需要额外的胶水代码 | 在 `tarjan_scc_lib.v` 中预先实例化 GraphLib 的 instance；减少 VC 中的类型类推导 |
| 数组/栈操作的细粒度权限在符号执行中产生意外 | 中 | 中：VC 爆炸 | 在标注中使用更高层的聚合谓词（如 `IntArray_rep`），通过引理展开而非在标注中展开 |
| 2-SAT 蕴含图构造与 Tarjan SCC 之间的接口不匹配 | 低 | 中：需要适配 | 确保 Tarjan 适用于任意 `OriginalGraphType`；2-SAT 图必须在相同的 `V = E = Z` 类型参数下构造 |

---

## 12. 执行建议

### 12.1 推荐执行顺序

1. **首先在纯 Coq 中完成 SCC 形式化（阶段一）**
   - 不涉及 C 代码、标注或符号执行
   - 如果数学定义和定理不能在纯 Coq 中证出，那么 C 验证将无从谈起
   - 这是整个项目**最关键的降低风险步骤**

2. **充分利用 `tarjan.v` 已有的成果**
   - `is_low` / `low_valid` / `low_valid_implies_is_low` 等定义直接适用
   - `closed_offspring` 和 `tarjan`（桥定理）两个引理是 SCC 证明的核心
   - 不要重新定义 low 或 dfn，在已有基础上扩展

3. **在两个方向上逐步推进**
   - 先用**最简标注**（只有函数规约，没有循环不变量）运行 `symexec`
   - 如果符号执行成功到达文件尾，说明函数调用和基本内存操作无误
   - 然后再逐步细化循环不变量和内部断言
   - 每次迭代都使用 `qcp-mcp` 做交互式检查

4. **将 2-SAT 作为独立的后续案例**
   - 一旦 Tarjan SCC 模块通过 `final-check`，2-SAT 案例就是"调用已验证的 Tarjan + 额外的归约证明"
   - 2-SAT 的 C 实现本身相对简单（构建图、调用 Tarjan、检查 SCC、构造赋值）
   - 难度集中在"构建图保持语义"的引理上

5. **遵循 Agent 工作流纪律**
   - 不要在主线程做子 agent 的工作
   - annotation 阶段使用 annotation scratch + `annotation_scratch_lib`，通过 `annotation-checking` 质量门后才能回填正式文件
   - vc-proving 阶段先让 `vc-checking-subagent` 完成分类，再进行并发证明
   - 最终 `final-check` 必须由主 agent 串行执行

6. **参考 `QCP_demos_LLM` 的示例**
   - `sll_insert_sort.c` 的多函数、复杂不变量模式
   - `fme/fme.c` 的嵌套循环、多文件组织模式
   - 不参考 `QCP_demos_human`（按照 `AGENTS.md` 的规定）

---

*计划文档版本：1.0*
*最后更新：2026-06-05*
*本计划基于 QCP v2.0.2、Rocq 8.20.1、GraphLib 现有版本编写*
