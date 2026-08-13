Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma char_array_strategy1_correctness : char_array_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (CharArray.full_split_to_missing_i p i n l 0).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 1) with (p + i * sizeof (CHAR))
      by (rewrite sizeof_char; lia).
    cancel (CharArray.missing_i p i 0 n l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma char_array_strategy4_correctness : char_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma char_array_strategy5_correctness : char_array_strategy5.
  pre_process_default.
Qed.

Lemma char_array_strategy6_correctness : char_array_strategy6.
Proof.
  pre_process_default.
  prop_apply (CharArray.full_Zlength p n l1).
  Intros.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    rewrite <- H.
    apply Zlength_nonneg.
Qed.

Lemma char_array_strategy2_correctness : char_array_strategy2.
Proof.
  pre_process_default.
  replace (p + i * 1) with (p + i * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  sep_apply_l_atomic (CharArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma char_array_strategy3_correctness : char_array_strategy3.
Proof.
  pre_process_default.
  replace (p + i * 1) with (p + i * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  sep_apply_l_atomic (CharArray.missing_i_merge_to_full p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma char_array_strategy7_correctness : char_array_strategy7.
Proof.
  pre_process_default.
  subst n.
  Intros_p H.
  subst l.
  rewrite CharArray.full_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma char_array_strategy8_correctness : char_array_strategy8.
Proof.
  pre_process_default.
  subst l.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg p r).
  cancel.
Qed.

Lemma char_array_strategy9_correctness : char_array_strategy9.
Proof.
  pre_process_default.
  sep_apply_l_atomic (CharArray.undef_seg_split_to_undef_missing_i p l i n).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 1) with (p + i * sizeof (CHAR))
      by (rewrite sizeof_char; lia).
    cancel (CharArray.undef_missing_i p i l n).
    apply_sepcon_adjoint.
    cancel (poly_undef_store FET_char (p + i * sizeof (CHAR))).
    cancel.
Qed.

Lemma char_array_strategy10_correctness : char_array_strategy10.
Proof.
  pre_process_default.
  subst i.
  replace (p + n * 1) with (p + n * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  sep_apply_l_atomic (CharArray.seg_single p n v).
  sep_apply_l_atomic (CharArray.seg_to_full p n (n + 1) (v :: nil)).
  prop_apply (CharArray.full_Zlength p n l).
  Intros.
  sep_apply_l_atomic (CharArray.full_merge_to_full p n (n + 1) l (v :: nil)).
  - dump_pre_spatial.
    split.
    + rewrite <- H.
      apply Zlength_nonneg.
    + lia.
  - cancel.
Qed.

Lemma char_array_strategy11_correctness : char_array_strategy11.
Proof.
  pre_process_default.
  subst l.
  sep_apply_l_atomic (CharArray.undef_missing_i_to_undef_seg_head p r n).
  - dump_pre_spatial.
    lia.
  - replace (p + r * 1) with (p + r * sizeof (CHAR))
      by (rewrite sizeof_char; lia).
    cancel.
Qed.
