Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma uint_array_strategy1_correctness : uint_array_strategy1.
  pre_process_default.
  prop_apply (UIntArray.full_length). Intros.
  sep_apply (UIntArray.full_split_to_missing_i p i); [ | tauto].
  entailer!.
  Intros_r v.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma uint_array_strategy4_correctness : uint_array_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma uint_array_strategy5_correctness : uint_array_strategy5.
  pre_process_default.
Qed.

Lemma uint_array_strategy6_correctness : uint_array_strategy6.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma uint_array_strategy7_correctness : uint_array_strategy7.
  pre_process_default.
  sep_apply (UIntArray.seg_split_to_missing_i p x i y); [ | tauto].
  entailer!.
  Intros_r_any.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros; subst; entailer!.
Qed.

Lemma uint_array_strategy8_correctness : uint_array_strategy8.
  pre_process_default.
  Intros; subst.
  prop_apply (UIntArray.seg_length p x y).
  prop_apply (UIntArray.seg_length p y z).
  Intros.
  sep_apply (UIntArray.seg_merge_to_seg p x y z l1 l2); try lia.
  entailer!.
Qed.

Lemma uint_array_strategy9_correctness : uint_array_strategy9.
  pre_process_default.
  Intros. subst.
  prop_apply (UIntArray.seg_length p x z).
  Intros.
  sep_apply (UIntArray.seg_split_to_seg p x y z (l1 ++ l2)) ; try lia.
  rewrite <- H2.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  replace (z - x - Zlength l1) with (Zlength l2).
  rewrite sublist_self ; try lia.
  entailer!.
  repeat rewrite Zlength_correct in *. 
  rewrite length_app in H1.
  lia.
Qed.

Lemma uint_array_strategy10_correctness : uint_array_strategy10.
  pre_process_default.
  Intros;subst.
  cbn.
  entailer!.
Qed.

Lemma uint_array_strategy2_correctness : uint_array_strategy2.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply (UIntArray.missing_i_merge_to_full); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma uint_array_strategy11_correctness : uint_array_strategy11.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply (UIntArray.missing_i_merge_to_seg); [ | tauto].
  rewrite replace_Znth_Znth by tauto.
  entailer!.
Qed.

Lemma uint_array_strategy3_correctness : uint_array_strategy3.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply (UIntArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
Qed.

Lemma uint_array_strategy12_correctness : uint_array_strategy12.
  pre_process_default.
  simpl.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply (UIntArray.missing_i_merge_to_seg); [ | tauto].
  entailer!.
Qed.

Lemma uint_array_strategy13_correctness : uint_array_strategy13.
  pre_process_default.
  Intros.
  subst. cbn. 
  entailer!.
Qed.

Lemma uint_array_strategy14_correctness : uint_array_strategy14.
  pre_process_default.
  Intros.
  subst.
  prop_apply (UIntArray.full_length p). Intros.
  replace (p + n * 4) with (p + n * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply UIntArray.seg_single.
  sep_apply (UIntArray.seg_to_full p n (n + 1) (a :: nil)).
  sep_apply (UIntArray.full_merge_to_full p) ; try lia.
  entailer!.
Qed.
