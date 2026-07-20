# Forbidden Lemma 列表

manual、`group_worker_lib`、`proving_merged_lib` 和最终 `formal_case_lib` 均不得使用下列 lemma。它们绕过 separation logic proof 的核心结构。

## 规则

- group-worker scripted check 前扫描 copied manual/`group_worker_lib`。
- parent verify 合并前后扫描 group candidates 与 proving_merged files。
- final-check 扫描正式 manual/`formal_case_lib`。
- 命中时记录 path、line、lemma 和所属 witness/helper；不能通过改名或注释规避，必须重写 proof。

## 列表

| # | Lemma | 说明 |
|---|---|---|
| 1 | `logic_equiv_refl` | 逻辑等价自反 |
| 2 | `elim_wand_emp_emp` | wand-emp-emp 消除 |
| 3 | `logic_equiv_symm` | 逻辑等价对称 |
| 4 | `sepcon_emp_logic_equiv'` | sepcon emp 等价变体 |
| 5 | `logic_equiv_andp_comm` | andp 交换 |
| 6 | `logic_equiv_sepcon_comm` | sepcon 交换 |
| 7 | `logic_equiv_sepcon_emp` | sepcon emp 等价 |
| 8 | `logic_equiv_andp_truep` | andp truep 等价 |
| 9 | `logic_equiv_truep_andp` | truep andp 等价 |
| 10 | `truep_andp_right_equiv` | truep andp 右侧等价 |
| 11 | `logic_equiv_orp_comm` | orp 交换 |
| 12 | `logic_equiv_trans` | 逻辑等价传递 |
| 13 | `logic_equiv_orp_assoc` | orp 结合 |
| 14 | `logic_equiv_sepcon_assoc` | sepcon 结合 |
| 15 | `logic_equiv_andp_assoc` | andp 结合 |
| 16 | `logic_equiv_sepcon_orp` | sepcon-orp 分配 |
| 17 | `logic_equiv_sepcon_orp_distr` | sepcon-orp 分配变体 |
| 18 | `logic_equiv_orp_sepcon` | orp-sepcon 分配 |
| 19 | `derivable1_trans` | derivable 传递 |
| 20 | `derivable1_refl` | derivable 自反 |
| 21 | `derivable1_sepcon_comm` | derivable sepcon 交换 |
| 22 | `coq_prop_andp_right` | Coq prop andp 右侧引理 |
| 23 | `derivable1_sepcon_mono` | derivable sepcon 单调 |
