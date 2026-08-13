# Forbidden Lemmas

The manual, `group_worker_lib`, `proving_merged_lib`, and final `formal_case_lib` must not use any lemma below. These lemmas bypass the core structure of separation-logic proofs.

## Rules

- Scan the copied manual and `group_worker_lib` before a group worker's scripted check.
- Scan group candidates and proving-merged files before and after parent merge.
- Scan the formal manual and `formal_case_lib` during final-check.
- On a match, record the path, line, lemma, and owning witness/helper. Renaming or commenting does not evade the rule; rewrite the proof.

## List

| # | Lemma | Description |
|---|---|---|
| 1 | `logic_equiv_refl` | Reflexivity of logical equivalence |
| 2 | `elim_wand_emp_emp` | Elimination of wand-emp-emp |
| 3 | `logic_equiv_symm` | Symmetry of logical equivalence |
| 4 | `sepcon_emp_logic_equiv'` | Variant of sepcon-emp equivalence |
| 5 | `logic_equiv_andp_comm` | Commutativity of andp |
| 6 | `logic_equiv_sepcon_comm` | Commutativity of sepcon |
| 7 | `logic_equiv_sepcon_emp` | Sepcon-emp equivalence |
| 8 | `logic_equiv_andp_truep` | Andp-truep equivalence |
| 9 | `logic_equiv_truep_andp` | Truep-andp equivalence |
| 10 | `truep_andp_right_equiv` | Right-side truep-andp equivalence |
| 11 | `logic_equiv_orp_comm` | Commutativity of orp |
| 12 | `logic_equiv_trans` | Transitivity of logical equivalence |
| 13 | `logic_equiv_orp_assoc` | Associativity of orp |
| 14 | `logic_equiv_sepcon_assoc` | Associativity of sepcon |
| 15 | `logic_equiv_andp_assoc` | Associativity of andp |
| 16 | `logic_equiv_sepcon_orp` | Sepcon-orp distribution |
| 17 | `logic_equiv_sepcon_orp_distr` | Variant of sepcon-orp distribution |
| 18 | `logic_equiv_orp_sepcon` | Orp-sepcon distribution |
| 19 | `derivable1_trans` | Transitivity of derivability |
| 20 | `derivable1_refl` | Reflexivity of derivability |
| 21 | `derivable1_sepcon_comm` | Sepcon commutativity for derivability |
| 22 | `coq_prop_andp_right` | Right-side Coq-proposition andp lemma |
| 23 | `derivable1_sepcon_mono` | Sepcon monotonicity for derivability |
| 24 | `logic_equiv_coq_prop_andp_sepcon` | Logical-equivalence rearrangement of Coq prop and sepcon |
| 25 | `derivable1_sepcon_assoc1` | Sepcon associativity for derivability (right to left) |
| 26 | `derivable1_sepcon_assoc2` | Sepcon associativity for derivability (left to right) |
| 27 | `derivable1_orp_assoc1` | Orp associativity for derivability |
| 28 | `derivable1_andp_assoc` | Andp associativity for derivability |
| 29 | `provable_sepcon_assoc` | Sepcon associativity for provability |
| 30 | `provable_sepcon_assoc1` | Sepcon associativity variant for provability |
| 31 | `provable_sepcon_assoc2` | Sepcon associativity variant for provability |
| 32 | `provable_orp_assoc` | Orp associativity for provability |
| 33 | `provable_andp_assoc` | Andp associativity for provability |

## Forbidden tactics

| # | Tactic | Reason |
|---|---|---|
| 1 | `entailer!` | Hides which step actually closes the goal |
| 2 | `pre_process` | Alias for `LLM_pre_process ltac:(lia \|\| nia \|\| int_auto)` that hides the closer |

Same scan and same `forbidden-lemma` failure class as the lemmas above. For rewrites see the Whole-proof Skeleton section of [Separation-logic proof tactics](separation-logic-whole-proof-tactics.md). Internal calls from `LLM_pre_process` and `Goal_apply` are unaffected.
