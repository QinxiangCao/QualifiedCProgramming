Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import char_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma char_array_strategy1_correctness : char_array_strategy1.
  pre_process_default.
  prop_apply (CharArray.full_length). Intros.
  sep_apply (CharArray.full_split_to_missing_i p i); [ | tauto].
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma char_array_strategy4_correctness : char_array_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma char_array_strategy5_correctness : char_array_strategy5.
  pre_process_default.
Qed.

Lemma char_array_strategy6_correctness : char_array_strategy6.
  pre_process_default.
  prop_apply (CharArray.full_length).
  rewrite <- Zlength_correct.
  entailer!.
  pose proof Zlength_nonneg l1; subst; auto.
Qed.

Lemma char_array_strategy2_correctness : char_array_strategy2.
  pre_process_default.
  simpl.
  replace (p + i * 1) with (p + i * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  sep_apply (CharArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma char_array_strategy3_correctness : char_array_strategy3.
  pre_process_default.
  simpl.
  replace (p + i * 1) with (p + i * sizeof (CHAR))
    by (rewrite sizeof_char; lia).
  sep_apply (CharArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
Qed.

Lemma char_array_strategy7_correctness : char_array_strategy7.
  pre_process_default. 
  Intros. 
  subst.
  cbn. 
  entailer!.
Qed.

Lemma char_array_strategy8_correctness : char_array_strategy8.
  pre_process_default.
  sep_apply (CharArray.undef_full_to_undef_seg p r).
  subst.
  entailer!. 
Qed.

Lemma char_array_strategy9_correctness : char_array_strategy9.
  pre_process_default.
  simpl.
  sep_apply (CharArray.undef_seg_split_to_undef_missing_i p l i n); [ | tauto].
  entailer!. 
  rewrite <- derivable1_wand_sepcon_adjoint. 
  entailer!.
Qed.

Lemma char_array_strategy10_correctness : char_array_strategy10.
  pre_process_default.
  subst.
  prop_apply (CharArray.full_length). Intros.
  sep_apply (CharArray.full_to_seg).
  sep_apply (CharArray.seg_single).
  sep_apply (CharArray.seg_merge_to_full p 0 n (n + 1)) ; try lia.
  replace (p + 0 * sizeof (CHAR)) with p by lia.
  replace (n + 1 - 0) with (n + 1) by lia.
  entailer!.
Qed.

Lemma char_array_strategy11_correctness : char_array_strategy11.
  pre_process_default.
  simpl. subst.
  sep_apply (CharArray.undef_missing_i_to_undef_seg_head ); try lia.
  entailer!.
Qed.
