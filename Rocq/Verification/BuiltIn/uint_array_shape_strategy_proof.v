From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification.BuiltIn Require Import uint_array_shape_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.

Lemma uint_array_shape_strategy1_correctness : uint_array_shape_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.full_shape_split_to_missing_i_shape p i n).
  2: lia.
  Intros v0.
  Exists v0.
  entailer!.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma uint_array_shape_strategy3_correctness : uint_array_shape_strategy3.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  rewrite (UIntArray.seg_shape_unfold p x y) by lia.
  Intros v0.
  Exists v0.
  entailer!.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma uint_array_shape_strategy6_correctness : uint_array_shape_strategy6.
Proof.
  pre_process_default.
  subst y.
  rewrite UIntArray.seg_shape_empty.
  cancel.
Qed.

Lemma uint_array_shape_strategy7_correctness : uint_array_shape_strategy7.
Proof.
  pre_process_default.
  subst y.
  rewrite UIntArray.seg_shape_empty.
  cancel.
Qed.

Lemma uint_array_shape_strategy8_correctness : uint_array_shape_strategy8.
Proof.
  pre_process_default.
  subst n.
  rewrite UIntArray.full_shape_empty.
  cancel.
Qed.

Lemma uint_array_shape_strategy9_correctness : uint_array_shape_strategy9.
Proof.
  pre_process_default.
  subst i.
  sep_apply (UIntArray.seg_shape_to_full_shape p 0 n).
  replace (p + 0 * sizeof(UINT)) with p by lia.
  replace (n - 0) with n by lia.
  cancel.
Qed.

Lemma uint_array_shape_strategy10_correctness : uint_array_shape_strategy10.
Proof.
  pre_process_default.
  subst x1 y1.
  cancel.
Qed.

Lemma uint_array_shape_strategy2_correctness : uint_array_shape_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.missing_i_shape_merge_to_full_shape p i n v).
  2: lia.
  cancel.
Qed.

Lemma uint_array_shape_strategy4_correctness : uint_array_shape_strategy4.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst x.
  sep_apply (UIntArray.seg_shape_single p i v).
  prop_apply (UIntArray.seg_shape_valid p (i + 1) y).
  Intros.
  sep_apply (UIntArray.seg_shape_merge_to_seg_shape p i (i + 1) y).
  2: lia.
  cancel.
Qed.

Lemma uint_array_shape_strategy5_correctness : uint_array_shape_strategy5.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UIntArray.seg_shape_single p z v).
  prop_apply (UIntArray.seg_shape_valid p y z).
  Intros.
  sep_apply (UIntArray.seg_shape_merge_to_seg_shape p y z (z + 1)).
  2: lia.
  cancel.
Qed.
