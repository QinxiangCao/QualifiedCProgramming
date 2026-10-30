# 纯命题证明模式

本指南用于 group-worker 证明工作。annotation 使用 `increasing`、`decreasing`、边界、`sum`、封装 `MaxMinLib` / `SumLib` 的 case 谓词，或 CDCLLib 名称时，应让 annotation 保持语义化，并在 group 证明中桥接到便于证明的形式。

不要把面向证明的形式反推回 C annotation。缺少桥接 lemma 时，先检查 proof_reuse.md，并按 lemma/predicate 名读取指定历史 candidate；适用时复制必要 helper closure 并使用当前 suffix，否则在 `group_worker_lib` 中添加并证明带当前 group 后缀的 helper。

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

新增或改写的形式应作为带当前 helper 后缀的 group-local helper 来证明。复用历史 helper 也使用当前后缀。不要把 helper 留在正式 `*_proof_manual.v` 中，不直接 import 历史候选库。

## CNF 与 SAT 谓词

对 CDCLLib 名称（`models`、`cnf_sat`、`cnf_unsat`、`entails_clause`、`cnf_with_units`、计数器、`cdcl_view`），使用 `Rocq/cdcllib/sat_shared_lib.v` 与 `cdcl_shared_lib.v` 中的 lemma。不重述共享定义，也不以 case 名或 group 后缀复制 lemma。对强化的 case invariant，先用 `proj1` 或 `formal_case_lib` 中的 `_elim` 取出共享谓词。CDCLLib 名称经由 seed `formal_case_lib` 的 `From CDCLLib Require Export` 可见；`group_worker_lib` 只能新增 `Coq` / `Coq.*` import，不能自行添加 `From CDCLLib Require`，seed 未导出所需 CDCLLib 文件时按 annotation/spec 缺口写 blocker。

- 单点更新：`sat_function_update_eq` / `_neq`，不 `unfold` 后对 `Z.eq_dec` 分情况；
- 取反：`eval_literal_neg`、`eval_partial_literal_neg`、`literal_neg_involutive`；
- 计数器：`clause_counts_assign` / `clause_counts_clear`、`clause_false_counts` / `clause_counts_zero_false`、`clause_unit_other_false`；
- 蕴含：`entails_clause_in`、`entails_clause_mono`、`entails_clause_perm`、`entails_unit_step`、`entails_clause_units_weaken`；
- UNSAT：由被蕴含的空 clause 用 `entails_empty_cnf_unsat`，assumption 增加用 `cnf_unsat_units_mono`，用 `models_cnf_with_units` 拆出 assumption；
- SAT：`partial_clause_has_true` 配合 `eval_partial_literal_total_agree`；由 model 得到 `cnf_sat` 用 `rho_restrict_bounded` 与 `models_rho_restrict`；
- 拼接：没有 `models_app`；`unfold models` 后用 `Forall_app` / `Forall_cons`，`clause_satisfied` 用 `in_app_iff`。

```coq
rewrite sat_function_update_neq by lia.
eapply entails_empty_cnf_unsat; eauto.   (* cnf_wf n F -> entails_clause F nil -> cnf_unsat n F *)
```

CDCLLib 缺少的通用事实（例如 `entails_clause` 的传递性）写成一条只用 CDCLLib 名称表述的当前 suffix helper，并在 `group_worker_output.md` 中记为库缺口。

## 交接规则

如果 annotation 使用了正确的语义谓词，只是缺少桥接 lemma，应把问题归类为 group-worker helper 任务，不要退回 annotation。

只有当 annotation 暴露了错误语义、谓词参数不足、循环不变量缺少必要数学事实，或当前 VC 前提无法推出 helper 前提时，才退回 annotation。
