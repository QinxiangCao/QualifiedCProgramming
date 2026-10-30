From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification.BuiltIn Require Import undef_uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.

Lemma undef_uint_array_strategy13_correctness : undef_uint_array_strategy13.
Proof.
  pre_process_default.
  subst i.
  sep_apply (UIntArray.undef_missing_i_to_undef_seg_head p x y).
  2: lia.
  cancel.
Qed.

Lemma undef_uint_array_strategy14_correctness : undef_uint_array_strategy14.
Proof.
  pre_process_default.
  assert (i = y - 1) by lia.
  subst i.
  sep_apply (UIntArray.undef_missing_i_to_undef_seg_tail p x y).
  2: lia.
  cancel.
Qed.

Lemma undef_uint_array_strategy16_correctness : undef_uint_array_strategy16.
Proof.
  pre_process_default.
Qed.

Lemma undef_uint_array_strategy17_correctness : undef_uint_array_strategy17.
Proof.
  pre_process_default.
Qed.

Lemma undef_uint_array_strategy3_correctness : undef_uint_array_strategy3.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  rewrite (UIntArray.undef_seg_unfold p x y) by lia.
  entailer!.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma undef_uint_array_strategy4_correctness : undef_uint_array_strategy4.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.undef_seg_split_to_undef_missing_i p x i y).
  2: lia.
  cancel (UIntArray.undef_missing_i p i x y).
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma undef_uint_array_strategy6_correctness : undef_uint_array_strategy6.
Proof.
  pre_process_default.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg p x y z).
  2: lia.
  cancel.
Qed.

Lemma undef_uint_array_strategy7_correctness : undef_uint_array_strategy7.
Proof.
  pre_process_default.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg p x y z).
  2: lia.
  cancel.
Qed.

Lemma undef_uint_array_strategy8_correctness : undef_uint_array_strategy8.
Proof.
  pre_process_default.
  rewrite UIntArray.undef_seg_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy9_correctness : undef_uint_array_strategy9.
Proof.
  pre_process_default.
  sep_apply UIntArray.undef_full_to_undef_seg.
  cancel.
Qed.

Lemma undef_uint_array_strategy10_correctness : undef_uint_array_strategy10.
Proof.
  pre_process_default.
  subst n.
  rewrite UIntArray.undef_full_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy11_correctness : undef_uint_array_strategy11.
Proof.
  pre_process_default.
  subst y.
  rewrite UIntArray.undef_seg_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy12_correctness : undef_uint_array_strategy12.
Proof.
  pre_process_default.
  subst x1 y1.
  cancel.
Qed.

Lemma undef_uint_array_strategy15_correctness : undef_uint_array_strategy15.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply UIntArray.undef_full_to_undef_seg.
  rewrite (UIntArray.undef_seg_unfold p 0 n) by lia.
  replace (0 + 1) with 1 by lia.
  cancel (UIntArray.undef_seg p 1 n).
  apply_sepcon_adjoint.
  Intros.
  cbn [poly_store poly_undef_store].
  cancel.
Qed.

Lemma undef_uint_array_strategy2_correctness : undef_uint_array_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.undef_missing_i_merge_to_undef_full p i n).
  2: lia.
  cancel.
Qed.

Lemma undef_uint_array_strategy5_correctness : undef_uint_array_strategy5.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.undef_missing_i_merge_to_undef_seg p x i y).
  2: lia.
  cancel.
Qed.

Lemma undef_uint_array_strategy1_correctness : undef_uint_array_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.undef_full_split_to_undef_missing_i p i n).
  2: lia.
  cancel (UIntArray.undef_missing_i p i 0 n).
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.
