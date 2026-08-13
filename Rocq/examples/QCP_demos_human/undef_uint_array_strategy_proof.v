Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import undef_uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma undef_uint_array_strategy1_correctness : undef_uint_array_strategy1.
  pre_process_default.
  sep_apply (UIntArray.undef_full_split_to_undef_missing_i p i); [ | tauto].
  entailer!.
  pre_process_default.
Qed.

Lemma undef_uint_array_strategy7_correctness : undef_uint_array_strategy7.
  pre_process_default.
  sep_apply UIntArray.undef_full_to_undef_seg.
  entailer!.
Qed.

Lemma undef_uint_array_strategy8_correctness : undef_uint_array_strategy8.
  pre_process_default.
  subst.
  cbn.
  entailer!.
Qed.

Lemma undef_uint_array_strategy9_correctness : undef_uint_array_strategy9.
  pre_process_default.
  subst.
  apply UIntArray.undef_seg_empty.
Qed.

Lemma undef_uint_array_strategy10_correctness : undef_uint_array_strategy10.
  pre_process_default.
  subst. entailer!.
Qed.

Lemma undef_uint_array_strategy11_correctness : undef_uint_array_strategy11.
  pre_process_default.
  sep_apply (IntArray.undef_full_split_to_undef_missing_i p i n) ; try lia.
  entailer!.
  pre_process_default.
Qed.

Lemma undef_uint_array_strategy13_correctness : undef_uint_array_strategy13.
  pre_process_default.
  sep_apply (IntArray.undef_seg_split_to_undef_seg p x (x + 1) y) ; try lia.
  entailer!.
  pre_process_default.
  unfold IntArray.undef_seg. 
  replace (Z.to_nat (x + 1 - x)) with 1%nat by lia.
  simpl. entailer!.
Qed.

Lemma undef_uint_array_strategy2_correctness : undef_uint_array_strategy2.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply UIntArray.undef_missing_i_merge_to_undef_full; [ | tauto].
  entailer!.
Qed.

Lemma undef_uint_array_strategy3_correctness : undef_uint_array_strategy3.
  pre_process_default.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg p x (x + 1) y) ; try lia.
  entailer!.
  pre_process_default.
  rewrite (UIntArray.undef_seg_unfold p x (x + 1)) ; try lia.
  rewrite (UIntArray.undef_seg_empty).
  entailer!. 
Qed. 

Lemma undef_uint_array_strategy12_correctness : undef_uint_array_strategy12.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply (IntArray.undef_missing_i_merge_to_undef_full p i n) ; try lia.
  entailer!.
Qed.

Lemma undef_uint_array_strategy14_correctness : undef_uint_array_strategy14.
  pre_process_default.
  sep_apply IntArray.undef_seg_merge_to_undef_seg ; try lia.
  entailer!.
Qed.

Lemma undef_uint_array_strategy4_correctness : undef_uint_array_strategy4.
  pre_process_default.
  sep_apply UIntArray.undef_seg_merge_to_undef_seg ; try lia.
  entailer!.
Qed.


Lemma undef_uint_array_strategy17_correctness : undef_uint_array_strategy17.
  pre_process_default.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
Qed.

Lemma undef_uint_array_strategy18_correctness : undef_uint_array_strategy18.
  pre_process_default.
  subst.
  cbn.
  entailer!.
Qed.

Lemma undef_uint_array_strategy19_correctness : undef_uint_array_strategy19.
  pre_process_default.
  subst.
  apply IntArray.undef_seg_empty.
Qed.

Lemma undef_uint_array_strategy20_correctness : undef_uint_array_strategy20.
  pre_process_default.
  subst. entailer!.
Qed.

Lemma undef_uint_array_strategy5_correctness : undef_uint_array_strategy5.
  pre_process_default.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg p x y z) ; try lia.
  entailer!.
Qed.

Lemma undef_uint_array_strategy15_correctness : undef_uint_array_strategy15.
  pre_process_default.
  sep_apply (IntArray.undef_seg_split_to_undef_seg p x y z) ; try lia.
  entailer!.
Qed.

Lemma undef_uint_array_strategy6_correctness : undef_uint_array_strategy6.
  pre_process_default.
  unfold UIntArray.undef_seg.
  replace (Z.to_nat (x - x)) with 0%nat by lia.
  simpl.
  entailer!.
Qed.

Lemma undef_uint_array_strategy16_correctness : undef_uint_array_strategy16.
  pre_process_default.
  unfold IntArray.undef_seg.
  replace (Z.to_nat (x - x)) with 0%nat by lia.
  simpl.
  entailer!.
Qed.

Lemma undef_uint_array_strategy21_correctness : undef_uint_array_strategy21.
  pre_process_default.
  sep_apply (UIntArray.undef_full_split_to_undef_seg p 1) ; try lia.
  entailer!.
  replace (1) with (0 + 1) by lia.
  rewrite UIntArray.undef_seg_unfold; try lia.
  rewrite Z.mul_0_l.
  rewrite (UIntArray.undef_seg_empty p (0 + 1)).
  pre_process_default.
Qed.

Lemma undef_uint_array_strategy22_correctness : undef_uint_array_strategy22.
  pre_process_default.
  sep_apply (IntArray.undef_full_split_to_undef_seg p 1) ; try lia.
  entailer!.
  replace (1) with (0 + 1) by lia.
  rewrite IntArray.undef_seg_unfold; try lia.
  rewrite Z.mul_0_l.
  rewrite (IntArray.undef_seg_empty p (0 + 1)).
  pre_process_default.
Qed.
