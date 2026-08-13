Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma array_shape_strategy1_correctness : array_shape_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.full_shape_split_to_missing_i_shape p i n).
  - dump_pre_spatial.
    lia.
  - Intros x.
    Exists x.
    normalize.
    replace (p + i * 4) with (p + i * sizeof (UINT))
      by (rewrite sizeof_uint; lia).
    cancel (UIntArray.missing_i_shape p i 0 n).
    cancel ((p + i * sizeof ( UINT )) # UInt |-> x).
    Intros_r v.
    apply_sepcon_adjoint.
    cancel ((p + i * sizeof ( UINT )) # UInt |-> v).
    cancel.
Qed.

Lemma array_shape_strategy3_correctness : array_shape_strategy3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.seg_shape_split_to_missing_i_shape p x x y).
  - dump_pre_spatial.
    lia.
  - Intros v0.
    Exists v0.
    sep_apply_l_atomic (UIntArray.missing_i_shape_to_seg_shape_head p x y).
    + dump_pre_spatial.
      lia.
    + normalize.
      replace (p + x * 4) with (p + x * sizeof (UINT))
        by (rewrite sizeof_uint; lia).
      cancel (UIntArray.seg_shape p (x + 1) y).
      cancel ((p + x * sizeof ( UINT )) # UInt |-> v0).
      Intros_r v.
      apply_sepcon_adjoint.
      cancel ((p + x * sizeof ( UINT )) # UInt |-> v).
      cancel.
Qed.

Lemma array_shape_strategy6_correctness : array_shape_strategy6.
Proof.
  pre_process_default.
  subst y.
  rewrite UIntArray.seg_shape_empty.
  cancel.
Qed.

Lemma array_shape_strategy7_correctness : array_shape_strategy7.
Proof.
  pre_process_default.
  subst y.
  rewrite UIntArray.seg_shape_empty.
  cancel.
Qed.

Lemma array_shape_strategy8_correctness : array_shape_strategy8.
Proof.
  pre_process_default.
  subst n.
  rewrite UIntArray.full_shape_empty.
  cancel.
Qed.

Lemma array_shape_strategy9_correctness : array_shape_strategy9.
Proof.
  pre_process_default.
  subst i.
  sep_apply_l_atomic (UIntArray.seg_shape_to_full_shape p 0 n).
  replace (p + 0 * sizeof ( UINT )) with p by lia.
  replace (n - 0) with n by lia.
  cancel.
Qed.

Lemma array_shape_strategy10_correctness : array_shape_strategy10.
Proof.
  pre_process_default.
  subst y1.
  cancel.
Qed.

Lemma array_shape_strategy11_correctness : array_shape_strategy11.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.full_shape_split_to_missing_i_shape p i n).
  - dump_pre_spatial.
    lia.
  - Intros x.
    Exists x.
    normalize.
    replace (p + i * 4) with (p + i * sizeof (INT))
      by (rewrite sizeof_int; lia).
    cancel (IntArray.missing_i_shape p i 0 n).
    cancel ((p + i * sizeof ( INT )) # Int |-> x).
    Intros_r v.
    apply_sepcon_adjoint.
    cancel ((p + i * sizeof ( INT )) # Int |-> v).
    cancel.
Qed.

Lemma array_shape_strategy13_correctness : array_shape_strategy13.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.seg_shape_split_to_missing_i_shape p x x y).
  - dump_pre_spatial.
    lia.
  - Intros v0.
    Exists v0.
    sep_apply_l_atomic (IntArray.missing_i_shape_to_seg_shape_head p x y).
    + dump_pre_spatial.
      lia.
    + normalize.
      replace (p + x * 4) with (p + x * sizeof (INT))
        by (rewrite sizeof_int; lia).
      cancel ((p + x * sizeof ( INT )) # Int |-> v0).
      cancel (IntArray.seg_shape p (x + 1) y).
      Intros_r v.
      apply_sepcon_adjoint.
      cancel ((p + x * sizeof ( INT )) # Int |-> v).
      cancel.
Qed.

Lemma array_shape_strategy16_correctness : array_shape_strategy16.
Proof.
  pre_process_default.
  subst y.
  rewrite IntArray.seg_shape_empty.
  cancel.
Qed.

Lemma array_shape_strategy17_correctness : array_shape_strategy17.
Proof.
  pre_process_default.
  subst y.
  rewrite IntArray.seg_shape_empty.
  cancel.
Qed.

Lemma array_shape_strategy18_correctness : array_shape_strategy18.
Proof.
  pre_process_default.
  subst n.
  rewrite IntArray.full_shape_empty.
  cancel.
Qed.

Lemma array_shape_strategy19_correctness : array_shape_strategy19.
Proof.
  pre_process_default.
  subst i.
  sep_apply_l_atomic (IntArray.seg_shape_to_full_shape p 0 n).
  replace (p + 0 * sizeof ( INT )) with p by lia.
  replace (n - 0) with n by lia.
  cancel.
Qed.

Lemma array_shape_strategy20_correctness : array_shape_strategy20.
Proof.
  pre_process_default.
  subst y1.
  cancel.
Qed.

Lemma array_shape_strategy2_correctness : array_shape_strategy2.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.missing_i_shape_merge_to_full_shape p i n v).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma array_shape_strategy4_correctness : array_shape_strategy4.
Proof.
  pre_process_default.
  subst x.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.seg_shape_single p i v).
  prop_apply (UIntArray.seg_shape_valid p (i + 1) y).
  Intros.
  sep_apply_l_atomic (UIntArray.seg_shape_merge_to_seg_shape p i (i + 1) y).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma array_shape_strategy5_correctness : array_shape_strategy5.
Proof.
  pre_process_default.
  replace (p + z * 4) with (p + z * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.seg_shape_single p z v).
  prop_apply (UIntArray.seg_shape_valid p y z).
  Intros.
  sep_apply_l_atomic (UIntArray.seg_shape_merge_to_seg_shape p y z (z + 1)).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma array_shape_strategy12_correctness : array_shape_strategy12.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic (IntArray.missing_i_shape_merge_to_full_shape p i n v).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma array_shape_strategy14_correctness : array_shape_strategy14.
Proof.
  pre_process_default.
  subst x.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic (IntArray.seg_shape_single p i v).
  prop_apply (IntArray.seg_shape_valid p (i + 1) y).
  Intros.
  sep_apply_l_atomic (IntArray.seg_shape_merge_to_seg_shape p i (i + 1) y).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma array_shape_strategy15_correctness : array_shape_strategy15.
Proof.
  pre_process_default.
  replace (p + z * 4) with (p + z * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic (IntArray.seg_shape_single p z v).
  prop_apply (IntArray.seg_shape_valid p y z).
  Intros.
  sep_apply_l_atomic (IntArray.seg_shape_merge_to_seg_shape p y z (z + 1)).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.
