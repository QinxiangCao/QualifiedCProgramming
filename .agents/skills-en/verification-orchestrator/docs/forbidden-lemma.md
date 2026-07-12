# Forbidden Lemma 列表

manual proof 和 `case_lib` 中不得使用本文件列出的 lemma。它们会绕过 separation logic 证明的核心结构；命中时应回到 `vc-proving` 重写对应 proof。

## 规则

- 扫描范围：最终 `*_proof_manual.v` 和 `case_lib`，以及 group-worker 产出的候选 proof。
- 命中任意 forbidden lemma 时，`vc-proving` 不得合并；若在 `final-check` 命中，final-check 失败并回到 `vc-proving`。
- 记录所有命中位置：文件、行号、lemma 名称和所属 witness / helper。

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

## 检查

`vc-proving` 应在 parent verify 合并前扫描 group-worker candidate。`final-check` 应在 `Admitted.` / extra `Axiom` review 后扫描正式文件。

推荐用 `rg -n` 搜索 lemma 名称。扫描只是结构检查；若命中，不能通过改名或注释规避，必须改写 proof。
