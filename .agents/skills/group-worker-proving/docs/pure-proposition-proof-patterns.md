# 纯命题证明模式

本指南用于 group-worker 证明工作。annotation 使用 `increasing`、`decreasing`、边界、`sum`，或封装 `MaxMinLib` / `SumLib` 的 case 谓词时，应让 annotation 保持语义化，并在 group 证明中桥接到便于证明的形式。

不要把面向证明的形式反推回 C annotation。缺少桥接 lemma 时，先查看 handoff 中的 public-helper 目录；若其中存在适用的 exact sealed candidate 就复制它，否则在 `group_worker_lib` 中添加并证明带当前 group 后缀的 helper。

## 顺序谓词

常见的 annotation-facing 形式：

```coq
increasing l
decreasing l
strict_decreasing l
```

适用时，桥接到 `MonotonicList` 谓词：

```coq
pose proof (proj2 (mono_nondec_iff_increasing l) Hinc) as Hmono.
unfold mono_nondec in Hmono.
specialize (Hmono i j Hi Hij Hj).
```

常见对应关系：

- `increasing l` <-> `mono_nondec l`
- `decreasing l` <-> `mono_noninc l`
- `strict_decreasing l` <-> `mono_dec l`
- 严格递增证明通常使用 `mono_inc l` / `mono_inc_ind l`

常用桥接或结构 lemma 包括 `mono_nondec_iff_increasing`、`mono_noninc_iff_decreasing`、`mono_dec_iff_strict_decreasing`、`increasing_iff_chain`、`decreasing_iff_chain`、`strict_decreasing_iff_chain`、`mono_*_nil`、`mono_*_single`、`mono_*_cons`、`mono_*_iff_adjacent` 和 `mono_*_iff_ind`。

## 边界谓词

常见的 annotation-facing 形式：

```coq
upperbound x l
strict_upperbound x l
lowerbound x l
strict_lowerbound x l
```

优先使用 `ListLib` 已有的引入/消去 lemma：

- `upperbound_Znth`
- `lowerbound_Znth`
- `upperbound_intro_Znth`
- `lowerbound_intro_Znth`
- `strict_upperbound_app`
- `strict_lowerbound_cons`
- `lowerbound_app_cons`
- `lowerbound_trans`
- `lowerbound_perm`
- `upperbound_sublist_elim` / `upperbound_sublist_intro`
- `lowerbound_sublist_elim` / `lowerbound_sublist_intro`

若某个 VC 需要把边界事实转成 `Znth` 不等式，应在证明中消去边界谓词；不要要求 annotation 把主 spec 改写成庞大的 `forall i` 公式。

## 求和谓词

常见的 annotation-facing 形式：

```coq
sum l
sum (sublist lo hi l)
```

先尝试 `sum_app`、`sum_bound` 和 `sum_bound_lt` 等轻量 `ListLib` lemma。

证明需要区间和或有限集合求和时，使用 `list_sum_as_Z_range_sum`、`list_sum_sublist_as_Z_range_sum`、`list_sum_map_as_Z_range_sum`、`sum_Z_range_empty`、`sum_Z_range_cons`、`sum_Z_range_split`、`sum_Z_range_le` 和 `sum_Z_range_bounds` 等 lemma 桥接到 `SumLib`。

`ListLib.sum` 是对 `list Z` 的计算，`SumLib.sum` 是有限谓词集合求和。需要时在证明中桥接；不要只为方便证明而要求 annotation 把简单的 `sum(sublist(...))` 展开为 `SumLib.sum`。

## 最大值与最小值谓词

annotation 通常应调用 case-level 谓词，例如：

```coq
MinimizedMaxSegmentSum l m ans
CanSplit l m cap
CannotSplit l m cap
```

在证明中展开这些定义，并使用 `max_unique`、`max_le`、`max_eq`、`max_union`、`max_default_*`、`min_unique`、`min_le`、`min_eq`、`min_union` 和 `min_default_*` 等 `MaxMinLib` lemma。

对于二分答案 VC，常见 helper 形式为：

- 可行性给出最优值的上界，例如 `CanSplit l m mid -> MinimizedMaxSegmentSum l m ans -> ans <= mid`；
- 不可行性给出最优值的下界，例如 `CannotSplit l m mid -> MinimizedMaxSegmentSum l m ans -> mid < ans`。

新增或改写的形式应作为带当前 helper 后缀的 group-local helper 来证明。exact sealed public/reuse helper 可以保留其来源后缀。不要把 helper 留在正式 `*_proof_manual.v` 中，也绝不能直接 import 非 active public 目录。

## 交接规则

如果 annotation 使用了正确的语义谓词，只是缺少桥接 lemma，应把问题归类为 group-worker helper 任务，不要退回 annotation。

只有当 annotation 暴露了错误语义、谓词参数不足、循环不变量缺少必要数学事实，或当前 VC 前提无法推出 helper 前提时，才退回 annotation。
