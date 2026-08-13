# MaxMinLib - 最值库

本库提供全序关系上的最大值和最小值定义及相关定理，是证明算法正确性（特别是最优化算法）的核心工具。

## 编译

1) Configure paths: set the path to to COQBIN and the sets repo in `CONFIGURE` (used by `Makefile`):

    ```make
    COQBIN = # your own path to coqc, e.g. COQBIN=../coq-8.20/bin/
    SETS_DIR = # your own path to sets, e.g. SETS_DIR=../Sets
    ```

   If Coq is already installed into `PATH` (check `coqc --version`), you do not need to configure COQBIN.

2) Generate dependencies: run `make depend`.  
3) Build: run `make` (or `make -j` to parallelize).  

## 文件结构

```
MaxMinLib/
└── MaxMin.v    # 全序关系、最大最小值定义与定理
```

## 核心概念

### 全序关系（TotalOrder）

定义在类型`T`上的二元关系`le: T -> T -> Prop`满足以下性质：

```coq
Class TotalOrder {T : Type} (le: T -> T -> Prop) := {
  le_refl : forall x, le x x;                      (* 自反性 *)
  le_trans : forall x y z, le x y -> le y z -> le x z;  (* 传递性 *)
  le_antisym : forall x y, le x y -> le y x -> x = y;   (* 反对称性 *)
  le_total : forall x y, {le x y} + {le y x};      (* 完全性 *)
}.
```

**已实例化的全序关系：**
- `Z.le` (整数)：`Zle_TotalOrder`
- `Nat.le` (自然数)：`NatLe_TotalOrder`  
- `option_le` (可选自然数)：`option_le_TotalOrder`
  - `Some x ≤ Some y` ⟺ `x ≤ y`
  - `None ≤ _` 为真
  - `_ ≤ None` 为假（除非左侧也是None）

### 最大值定义

给定集合`X: A -> Prop`和映射函数`f: A -> T`：

**最大元素（max_object）：**
```coq
max_object_of_subset X f a :=
  a ∈ X /\ forall b, b ∈ X -> f b ≤ f a
```
表示`a`是集合`X`中使`f`达到最大的元素。

**最大值（max_value）：**
```coq
max_value_of_subset X f n :=
  exists a, max_object_of_subset X f a /\ f a = n
```
表示`n`是集合`X`上`f`的最大值。

**带默认值的最大值：**
```coq
max_value_of_subset_with_default X f default n :=
  (max_value_of_subset X f n /\ default ≤ n) \/
  ((forall a, a ∈ X -> f a ≤ default) /\ default = n)
```
当`X`为空集时，返回默认值。

### 最小值定义

类似地定义最小值（将`≤`改为`≥`）：

- `min_object_of_subset X f a`: 最小元素
- `min_value_of_subset X f n`: 最小值
- `min_value_of_subset_with_default X f default n`: 带默认值的最小值

## 主要记法

### 最大值记法

```coq
(* 基本形式 *)
n is-the-max-of f(x) in-which x satisfies P(x)

(* 模式匹配形式 *)
n is-the-max-of e in-which '(x, y) satisfies P(x, y)

(* 带默认值形式 *)
n is-the-max-of f(x) in-which x satisfies P(x) with-default d
```

### 最小值记法

```coq
(* 基本形式 *)
n is-the-min-of f(x) in-which x satisfies P(x)

(* 模式匹配形式 *)
n is-the-min-of e in-which '(x, y) satisfies P(x, y)

(* 带默认值形式 *)
n is-the-min-of f(x) in-which x satisfies P(x) with-default d

(* 最小值存在性（不指定具体值） *)
the-min-of f(x) in-which x satisfies P(x)
```

## 核心定理

### 唯一性定理

**最大值唯一：**
- `max_unique`: 若`n`和`m`都是最大值，则`n = m`
- `max_default_unique`: 带默认值的最大值唯一

**最小值唯一：**
- `min_unique`: 若`n`和`m`都是最小值，则`n = m`
- `min_default_unique`: 带默认值的最小值唯一

### 大小关系定理

**最大值比较：**
- `max_le`: 若每个`P1`中的元素都能找到`P2`中不小于它的元素，则`max(P1) ≤ max(P2)`
- `max_default_le`: 带默认值版本
- `max_eq`: 若`P1`和`P2`互相支配，则最大值相等
- `max_default_eq`: 带默认值版本

**最小值比较：**
- `min_le`: 若每个`P1`中的元素都能找到`P2`中不大于它的元素，则`min(P2) ≤ min(P1)`
- `min_default_le`: 带默认值版本
- `min_eq`: 若`P1`和`P2`互相支配，则最小值相等
- `min_default_eq`: 带默认值版本

### 等价变换定理

**正向等价：**
- `max_eq_forward`: 在保持最大值的条件下改变集合和函数
- `max_default_eq_forward`: 带默认值版本
- `min_eq_forward`: 最小值版本
- `min_default_eq_forward`: 带默认值版本

### 单调性定理

**单调递增变换：**
- `max_mono_incr_bind`: 若`h`单调递增，则`max(h∘f) = h(max f)`
- `min_mono_incr_bind`: 若`h`单调递增，则`min(h∘f) = h(min f)`

**单调递减变换：**
- `max_mono_decr_bind`: 若`h`单调递减，则`min(h∘f) = h(max f)`
- `min_mono_decr_bind`: 若`h`单调递减，则`max(h∘f) = h(min f)`

### 并集定理

**最大值的并集：**
- `max_union'`: `max(P ∪ Q) = max{max(P), max(Q)}`
- `max_union`: 带集合等价的版本
- `max_default_union'`: 带默认值版本
- `max_default_union`: 带集合等价和默认值版本

**最小值的并集：**
- `min_union'`: `min(P ∪ Q) = min{min(P), min(Q)}`
- `min_union`: 带集合等价的版本
- `min_default_union'`: 带默认值版本
- `min_default_union`: 带集合等价和默认值版本

### 单点集定理

**单点集的最值：**
- `max_1`: 单点集的最大值就是该点的函数值
- `max_default_1`: 带默认值的单点集最大值
- `min_1`: 单点集的最小值就是该点的函数值
- `min_default_1`: 带默认值的单点集最小值

**添加单点：**
- `max_union_1_right`: 向集合添加一个元素后的最大值
- `max_default_union_1_right`: 带默认值版本
- `min_union_1_right`: 向集合添加一个元素后的最小值
- `min_default_union_1_right`: 带默认值版本

### 空集定理

**默认值定理：**
- `max_default_default`: 空集的最大值是默认值
- `max_default_default_inv`: 若结果为默认值且满足条件，则为空集
- `min_default_default`: 空集的最小值是默认值
- `min_default_default_inv`: 若结果为默认值且满足条件，则为空集

### 辅助定理

**最大/最小元素性质：**
- `max_object_sound`: 最大元素确实最大
- `max_object_legal`: 最大元素属于集合
- `min_object_sound`: 最小元素确实最小
- `min_object_legal`: 最小元素属于集合

**默认值界：**
- `max_default_ge_default`: 带默认值的最大值不小于默认值
- `min_default_le_default`: 带默认值的最小值不大于默认值

## 辅助操作

### max/min函数

在全序关系下定义：

```coq
Definition le_max (x y: T): T := if le_total x y then y else x
Definition le_min (x y: T): T := if le_total x y then x else y
```

**性质定理：**
- `max_r`/`max_l`: 根据大小关系确定max结果
- `max_comm`: 交换律
- `max_assoc`: 结合律
- `min_r`/`min_l`: 根据大小关系确定min结果

### 对偶关系（ge）

定义大于等于关系：`ge x y := le y x`

**性质：**
- `ge_total_order`: `ge`也是全序关系
- 所有`le`的定理都有对应的`ge`版本

## 使用示例

### 示例1：证明最短路径的唯一性

```coq
Theorem shortest_path_unique:
  forall g u v d1 d2,
    d1 is-the-min-of weight(p) in-which p satisfies (path g u v p) ->
    d2 is-the-min-of weight(p) in-which p satisfies (path g u v p) ->
    d1 = d2.
Proof.
  intros. apply (min_unique _ _ _ _ H H0).
Qed.
```

### 示例2：最大值的单调性

```coq
Theorem max_distance_monotone:
  forall g1 g2 u v d1 d2,
    subgraph g1 g2 ->
    d1 is-the-max-of weight(p) in-which p satisfies (path g1 u v p) ->
    d2 is-the-max-of weight(p) in-which p satisfies (path g2 u v p) ->
    d1 <= d2.
Proof.
  intros.
  apply (max_le _ _ _ _ _ _ H0 H1).
  intros. exists a1. split; auto.
  (* 证明g1中的路径也是g2中的路径 *)
Qed.
```

### 示例3：并集的最小值

```coq
Theorem min_union_example:
  forall X Y f n m,
    n is-the-min-of f(x) in-which x satisfies X(x) ->
    m is-the-min-of f(x) in-which x satisfies Y(x) ->
    (le_min n m) is-the-min-of f(x) in-which x satisfies (X(x) \/ Y(x)).
Proof.
  intros. apply (min_union _ _ _ X Y); auto.
  intros; tauto.
Qed.
```

### 示例4：带默认值的空集

```coq
Theorem empty_max_is_default:
  forall f d,
    d is-the-max-of f(x) in-which x satisfies False with-default d.
Proof.
  intros. apply max_default_default.
  intros a [].
Qed.
```

## 证明策略建议

### 证明最值相等

1. 使用`max_eq`/`min_eq`或其变体
2. 分别证明两个方向的支配关系
3. 或使用`max_eq_forward`/`min_eq_forward`直接转换

### 证明最值不等式

1. 使用`max_le`/`min_le`或其变体
2. 对任意元素构造对应的支配元素

### 处理并集

1. 使用`max_union`/`min_union`分解并集
2. 分别证明各部分的最值
3. 使用`le_max`/`le_min`合并结果

### 处理单点集

1. 使用`max_1`/`min_1`直接得到结果
2. 使用`max_union_1_right`/`min_union_1_right`增量添加元素

### 处理空集

1. 使用`max_default_default`/`min_default_default`
2. 证明集合为空（`forall a, ~ P a`）

## 依赖关系

- **标准库**: `SetsClass.SetsClass`, `Coq.Classes.Morphisms`, `Coq.ZArith.ZArith`, `Lia`
- **项目依赖**: `sets` 库

## 常用定理速查

| 目标 | 最大值定理 | 最小值定理 |
|-----|-----------|-----------|
| 唯一性 | `max_unique` | `min_unique` |
| 比较 | `max_le` | `min_le` |
| 相等 | `max_eq` | `min_eq` |
| 等价变换 | `max_eq_forward` | `min_eq_forward` |
| 单调递增 | `max_mono_incr_bind` | `min_mono_incr_bind` |
| 单调递减 | `max_mono_decr_bind` | `min_mono_decr_bind` |
| 并集 | `max_union` | `min_union` |
| 单点集 | `max_1` | `min_1` |
| 添加元素 | `max_union_1_right` | `min_union_1_right` |
| 空集 | `max_default_default` | `min_default_default` |

## 技巧与注意事项

1. **选择合适的变体**：根据是否需要默认值、是否有集合等价关系选择带`'`、`default`、不带后缀的版本

2. **使用记法**：`is-the-max-of`等记法比直接使用定义更清晰

3. **max/min的区别**：注意单调递减变换会交换max和min

4. **默认值的处理**：当集合可能为空时，务必使用`with_default`版本

5. **集合操作**：熟练使用`Sets_unfold`和`sets_unfold`展开集合记法



