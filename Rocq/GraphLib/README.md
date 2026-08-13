# Coq 图论库 (Graph Theory Library)

[![Coq](https://img.shields.io/badge/Coq-8.17+-blue.svg)](https://coq.inria.fr/)

一个基于 Type Classes 的高度抽象 Coq 图论形式化验证库，提供了图的基本定义、路径抽象和经典图算法的形式化验证。

## 目录

- [核心 Type Classes](#核心-type-classes)
- [架构概览](#架构概览)
- [核心概念](#核心概念)
- [使用示例](#使用示例)
- [项目结构](#项目结构)
- [编译与安装](#编译与安装)

---

## 核心 Type Classes

### 1. Graph - 图的基本定义

`Graph` 是整个库的基础，定义了图的三个核心要素：

```coq
Class Graph (G V E: Type) := {
  vvalid : G -> V -> Prop;          (* 顶点有效性谓词 *)
  evalid : G -> E -> Prop;          (* 边有效性谓词 *)
  step_aux : G -> E -> V -> V -> Prop  (* 边 e 连接顶点 u 到 v *)
}.
```

**类型参数**：
- `G`: 图的类型（可以是任意表示，如邻接表、邻接矩阵等）
- `V`: 顶点类型
- `E`: 边类型

**核心字段**：
- `vvalid g v`: 判断顶点 `v` 在图 `g` 中是否有效
- `evalid g e`: 判断边 `e` 在图 `g` 中是否有效
- `step_aux g e u v`: 表示边 `e` 从顶点 `u` 指向顶点 `v`

---

### 2. Path - 路径的抽象定义

`Path` Type Class 将路径的**抽象概念**与**具体表示**分离，是本库的核心创新：

```coq
Class Path (G V E: Type) `{Graph G V E} (P: Type) := {
  path_valid: G -> P -> Prop;       (* 路径在图中是否有效 *)
  head: P -> V;                      (* 路径的起点 *)
  tail: P -> V;                      (* 路径的终点 *)
  vertex_in_path: P -> list V;      (* 路径经过的顶点序列 *)
  edge_in_path: P -> list E;        (* 路径包含的边序列 *)
  (* ... 以及顶点序列和边序列的一致性约束 ... *)
}.
```

**设计思想**：
- 用户通过抽象接口操作路径，不关心底层是顶点列表还是边列表
- 支持两种主要实现：
  - **顶点路径 (vpath)**：`P = list V`，路径由访问的顶点序列表示
  - **边路径 (epath)**：`P = list E`，路径由经过的边序列表示

---

### 3. 路径操作 Type Classes

#### EmptyPath - 空路径（单点路径）

```coq
Class EmptyPath := {
  empty_path: V -> P;
  empty_path_valid: forall g v, vvalid g v -> path_valid g (empty_path v);
  empty_path_head: forall v, head (empty_path v) = v;
  empty_path_tail: forall v, tail (empty_path v) = v
}.
```

表示只包含一个顶点的路径（长度为 0）。

#### SinglePath - 单边路径

```coq
Class SinglePath := {
  single_path: V -> V -> E -> P;
  single_path_valid: forall g u v e, 
    step_aux g e u v -> path_valid g (single_path u v e);
  single_path_head: forall u v e, head (single_path u v e) = u;
  single_path_tail: forall u v e, tail (single_path u v e) = v
}.
```

表示恰好包含一条边的路径。

#### ConcatPath - 路径连接

```coq
Class ConcatPath := {
  concat_path: P -> P -> P;
  concat_path_valid: forall g p1 p2, 
    path_valid g p1 -> path_valid g p2 -> 
    tail p1 = head p2 -> 
    path_valid g (concat_path p1 p2);
  concat_path_head: forall p1 p2, head (concat_path p1 p2) = head p1;
  concat_path_tail: forall p1 p2, tail (concat_path p1 p2) = tail p2
}.
```

将两个路径连接成一个更长的路径（要求第一个路径的终点是第二个路径的起点）。

---

## 架构概览

### Type Class 层次结构

库采用三层架构设计：

```
┌─────────────────────────────────────────────────────────┐
│        抽象接口层 (Abstract Interface)                   │
│  ┌───────────────────────────────────────────────────┐  │
│  │ Graph G V E                                       │  │
│  │   - vvalid: 顶点有效性                            │  │
│  │   - evalid: 边有效性                              │  │
│  │   - step_aux: 边的连接关系                        │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ Path G V E P                                      │  │
│  │   - path_valid: 路径有效性                        │  │
│  │   - head / tail: 起点/终点                        │  │
│  │   - vertex_in_path: 顶点序列                      │  │
│  │   - edge_in_path: 边序列                          │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ EmptyPath / SinglePath / ConcatPath               │  │
│  │   - 路径的基本操作                                │  │
│  └───────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────┐
│           具体实现层 (Concrete Realizations)            │
│  ┌──────────────────┐       ┌──────────────────┐       │
│  │  Vertex Path     │       │   Edge Path      │       │
│  │  (vpath)         │       │   (epath)        │       │
│  │                  │       │                  │       │
│  │  P = list V      │       │  P = list E      │       │
│  │                  │       │                  │       │
│  │  路径由访问的    │       │  路径由经过的    │       │
│  │  顶点序列表示    │       │  边序列表示      │       │
│  └──────────────────┘       └──────────────────┘       │
└─────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────┐
│              应用层 (Applications)                      │
│  - Dijkstra 最短路径算法                                │
│  - Floyd-Warshall 全源最短路径                          │
│  - Prim 最小生成树                                      │
│  - Kruskal 最小生成树                                   │
│  - Tarjan 强连通分量                                    │
└─────────────────────────────────────────────────────────┘
```

**设计优势**：
1. **证明复用**：在抽象层证明的定理自动适用于所有具体实现
2. **灵活性**：算法可以根据需要选择最适合的路径表示
3. **可扩展性**：可以轻松添加新的路径表示或图表示

---

## 核心概念

### 可达性 (Reachability)

```coq
Class Destruct1nPath := {
  destruct_1n_path: P -> PathConsView;
  destruct_1n_spec: forall g p, path_valid g p ->
    match destruct_1n_path p with
    | DestructBase1n v => 
        p = empty_path v                    (* 空路径 *)
    | DestructStep1n p' u v e =>
        path_valid g p' /\
        head p' = v /\
        step_aux g e u v /\
        p = concat_path (single_path u v e) p'   (* p = (u→v) ++ p' *)
    end
}.
```

**分解模式**：`p = Empty(v)` 或 `p = Single(u→v) ++ Rest`

**典型应用场景**：
- 前向可达性证明（从起点 `u` 出发证明可以到达 `v`）
- 构造从起点开始的路径
- Dijkstra 算法等单源最短路径算法

#### PathInd1n - 头部归纳

```coq
Class PathInd1n := {
  path_ind1n: forall g (X: P -> Type)
    (H_empty: forall v, X (empty_path v))
    (H_step: forall u v e rest, 
      step_aux g e u v -> 
      path_valid g rest ->
      head rest = v ->
      X rest -> 
      X (concat_path (single_path u v e) rest)),
    forall p, path_valid g p -> X p
}.
```

**核心定理**：路径与可达性等价
```coq
Class Destructn1Path := {
  destruct_n1_path: P -> PathSnocView;
  destruct_n1_spec: forall g p, path_valid g p ->
    match destruct_n1_path p with
    | DestructBasen1 p' v =>
        p = empty_path v                    (* 空路径 *)
    | DestructStepn1 p' u v e =>
        path_valid g p' /\
        tail p' = u /\
        step_aux g e u v /\
        p = concat_path p' (single_path u v e)   (* p = p' ++ (u→v) *)
    end
}.
```

**分解模式**：`p = Empty(v)` 或 `p = Rest ++ Single(u→v)`

**典型应用场景**：
- 后向可达性证明（证明从某点可以到达终点 `v`）
- 从终点倒推构造路径
- 路径末尾追加操作

#### PathIndn1 - 尾部归纳

```coq
Class PathIndn1 := {
  path_indn1: forall g (X: P -> Type)
    (H_empty: forall v, X (empty_path v))
    (H_step: forall u v e rest, 
      step_aux g e u v -> 
      path_valid g rest ->
      tail rest = u ->
      X rest -> 
      X (concat_path rest (single_path u v e))),
    forall p, path_valid g p -> X p
}.
```

---

### 路径表示

#### 顶点路径 (vpath)

```coq
(* valid_vpath g u l v: 列表 l 是从 u 到 v 的有效顶点序列 *)
Inductive valid_vpath (g: G): V -> list V -> V -> Prop :=
  | vpath_nil: forall v, vvalid g v -> valid_vpath g v nil v
  | vpath_cons: forall u v w l e,
      step_aux g e u v ->
      valid_vpath g v l w ->
      valid_vpath g u (v :: l) w.
```

**示例**：`valid_vpath g u [v; w] x` 表示路径 u → v → w → x

#### 边路径 (epath)

```coq
(* valid_epath g u l v: 列表 l 是从 u 到 v 的有效边序列 *)
Inductive valid_epath (g: G): V -> list E -> V -> Prop :=
  | epath_nil: forall v, vvalid g v -> valid_epath g v nil v
  | epath_cons: forall u v w l e,
      step_aux g e u v ->
      valid_epath g v l w ->
      valid_epath g u (e :: l) w.
```

**示例**：`valid_epath g u [e1; e2] v` 表示通过边 e1, e2 从 u 到 v

---

### 权重支持

库提供了带权图的支持：

```coq
(* 整数权重 *)
Class EdgeWeight (G E: Type) := {
  edge_weight: G -> E -> option Z
}.

(* 路径权重 = 所有边权重之和 *)
Definition path_weight {P: Type} `{Path G V E P} (g: G) (p: P): option Z :=
  fold_left_option Zweight_plus (edge_in_path p).
```

---

## 使用示例

### 示例 1：定义一个简单的图

```coq
Require Import GraphLib.

(* 使用自然数作为顶点，有序对 (nat * nat) 作为边 *)
Definition SimpleGraph := nat -> nat -> bool.  (* 邻接矩阵 *)

Instance simple_graph_instance: Graph SimpleGraph nat (nat * nat) := {
  vvalid g v := v < graph_size;
  evalid g e := let '(u, v) := e in g u v = true;
  step_aux g e u v := e = (u, v) /\ g u v = true
}.
```

---

### 示例 2：证明路径的传递性

```coq
Context {G V E: Type}
        {pg: Graph G V E}
        {P: Type}
        {path: Path G V E P}
        {cp: ConcatPath G V E P path}.

Theorem path_transitivity: forall g p1 p2,
  path_valid g p1 ->
  path_valid g p2 ->
  tail p1 = head p2 ->
  path_valid g (concat_path p1 p2).
Proof.
  intros.
  apply concat_path_valid; auto.
Qed.
```

---

### 示例 3：Dijkstra 算法框架

```coq
Require Import GraphLib.Zweight.

Context {G V E: Type}
        {pg: Graph G V E}
        {P: Type}
        {path: Path G V E P}
        {ew: EdgeWeight G E}.

(* 最短路径定义 *)
Definition shortest_path (g: G) (src dst: V) (p: P) : Prop :=
  path_valid g p /\
  head p = src /\
  tail p = dst /\
  forall p', 
    path_valid g p' -> head p' = src -> tail p' = dst ->
    path_weight g p <= path_weight g p'.

(* Dijkstra 正确性陈述（详细证明见 examples/dijkstra.v） *)
Theorem dijkstra_correctness: forall g src dst dist_map,
  dijkstra g src = dist_map ->
  forall p,
    shortest_path g src dst p ->
    dist_map dst = path_weight g p.
```

---

## 项目结构

```
graph_lib/
├── graph_basic.v              # 图的基本定义 (Graph Type Class)
├── Syntax.v                   # 语法糖和记号定义
├── GraphLib.v                 # 库的统一入口
│
├── reachable/                 # 路径与可达性
│   ├── reachable_basic.v      # 可达性定义 (step, reachable)
│   ├── path.v                 # 路径抽象接口 (Path Type Class)
│   ├── path_basic.v           # 路径基本性质
│   ├── vpath.v                # 顶点路径实现
│   ├── epath.v                # 边路径实现
│   ├── Zweight.v              # 整数权重支持
│   └── eweight.v              # 扩展权重支持
│
├── directed/                  # 有向图专用
│   ├── rootedtree.v           # 有根树
│   └── dfstree.v              # DFS 树
│
├── undirected/                # 无向图专用
│   ├── undirected_basic.v     # 无向图基础
│   ├── tree.v                 # 无向树
│   └── bigraph.v              # 二分图
│
├── subgraph/                  # 子图
│   └── subgraph.v             # 子图定义与性质
│
└── examples/                  # 经典算法示例
    ├── dijkstra.v             # Dijkstra 最短路径
    ├── floyd.v                # Floyd-Warshall 全源最短路径
    ├── prim.v                 # Prim 最小生成树
    ├── kruskal.v              # Kruskal 最小生成树
    └── tarjan.v               # Tarjan 强连通分量
```

---

## 编译与安装

### 前置依赖

- **Coq**: 8.17 或更高版本
- **SetsClass**: 集合类型类库
- **RecordUpdate**: 记录更新库
- **MonadLib**: 单子库（用于状态证明）
- **ListLib**: 扩展列表库

### 编译

```bash
cd graph_lib
make
```

### 在项目中使用

```coq
(* 导入完整库 *)
Require Import GraphLib.

(* 或选择性导入 *)
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable_basic.
Require Import GraphLib.path.
```

---

## 贡献与许可

欢迎提交 Issue 和 Pull Request！

本项目使用的具体许可证请参见仓库。

---

## 相关资源

- [Coq 官方网站](https://coq.inria.fr/)
- [Type Classes in Coq](https://coq.inria.fr/refman/language/core/typeclasses.html)

---
