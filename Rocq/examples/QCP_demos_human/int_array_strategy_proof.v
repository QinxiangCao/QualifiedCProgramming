Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import int_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Require Import Coq.micromega.Lia.

Lemma int_array_strategy1_correctness : int_array_strategy1.
  pre_process_default.
  prop_apply (IntArray.full_length). Intros.
  sep_apply (IntArray.full_split_to_missing_i p i); [ | tauto].
  entailer!.
  Intros_r v.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma int_array_strategy4_correctness : int_array_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma int_array_strategy5_correctness : int_array_strategy5.
Proof.  
  pre_process_default.
Qed.

Lemma int_array_strategy6_correctness : int_array_strategy6.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma int_array_strategy7_correctness : int_array_strategy7.
  pre_process_default.
  sep_apply (IntArray.seg_split_to_missing_i p x i y); [ | tauto].
  entailer!.
  Intros_r_any.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros; subst; entailer!.
Qed.

Lemma int_array_strategy8_correctness : int_array_strategy8.
  pre_process_default.
  Intros; subst.
  prop_apply (IntArray.seg_length p x y).
  prop_apply (IntArray.seg_length p y z).
  Intros.
  sep_apply (IntArray.seg_merge_to_seg p x y z l1 l2) ; try lia.
  entailer!.
Qed.

Lemma int_array_strategy9_correctness : int_array_strategy9.
  pre_process_default.
  Intros. subst.
  prop_apply (IntArray.seg_length p x z).
  Intros.
  sep_apply (IntArray.seg_split_to_seg p x y z (l1 ++ l2)) ; try lia.
  rewrite <- H2.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite Zlength_correct in *.
  rewrite length_app in H1.
  replace (z - x - Z.of_nat (Datatypes.length l1)) with (Zlength l2).
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_correct. lia.
Qed.

Lemma int_array_strategy10_correctness : int_array_strategy10.
  pre_process_default.
  Intros;subst.
  cbn.
  entailer!.
Qed.

Lemma int_array_strategy2_correctness : int_array_strategy2.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma int_array_strategy11_correctness : int_array_strategy11.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply (IntArray.missing_i_merge_to_seg); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma int_array_strategy3_correctness : int_array_strategy3.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
Qed.

Lemma int_array_strategy12_correctness : int_array_strategy12.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply (IntArray.missing_i_merge_to_seg); [ | tauto].
  entailer!.
Qed.
