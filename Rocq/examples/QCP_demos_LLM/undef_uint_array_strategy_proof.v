Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma undef_uint_array_strategy1_correctness : undef_uint_array_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_missing_i p i n).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 4) with (p + i * sizeof (UINT))
      by (rewrite sizeof_uint; lia).
    cancel (UIntArray.undef_missing_i p i 0 n).
    apply_sepcon_adjoint.
    normalize.
    cancel.
Qed.

Lemma undef_uint_array_strategy7_correctness : undef_uint_array_strategy7.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg p n).
  cancel.
Qed.

Lemma undef_uint_array_strategy8_correctness : undef_uint_array_strategy8.
Proof.
  pre_process_default.
  subst n.
  rewrite UIntArray.undef_full_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy9_correctness : undef_uint_array_strategy9.
  pre_process_default.
  subst.
  apply UIntArray.undef_seg_empty.
Qed.

Lemma undef_uint_array_strategy10_correctness : undef_uint_array_strategy10.
Proof.
  pre_process_default.
  subst x1 y1.
  cancel.
Qed.

Lemma undef_uint_array_strategy11_correctness : undef_uint_array_strategy11.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_missing_i p i n).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 4) with (p + i * sizeof (INT))
      by (rewrite sizeof_int; lia).
    cancel (IntArray.undef_missing_i p i 0 n).
    apply_sepcon_adjoint.
    normalize.
    cancel.
Qed.

Lemma undef_uint_array_strategy13_correctness : undef_uint_array_strategy13.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (IntArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + replace (p + x * 4) with (p + x * sizeof (INT))
        by (rewrite sizeof_int; lia).
      cancel (IntArray.undef_seg p (x + 1) y).
      apply_sepcon_adjoint.
      normalize.
      cancel.
Qed.

Lemma undef_uint_array_strategy2_correctness : undef_uint_array_strategy2.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.undef_missing_i_merge_to_undef_full p i n).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma undef_uint_array_strategy3_correctness : undef_uint_array_strategy3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (UIntArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + replace (p + x * 4) with (p + x * sizeof (UINT))
        by (rewrite sizeof_uint; lia).
      cancel (UIntArray.undef_seg p (x + 1) y).
      apply_sepcon_adjoint.
      normalize.
      cancel.
Qed.

Lemma undef_uint_array_strategy12_correctness : undef_uint_array_strategy12.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply_l_atomic (IntArray.undef_missing_i_merge_to_undef_full p i n).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma undef_uint_array_strategy14_correctness : undef_uint_array_strategy14.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_seg p x y z).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma undef_uint_array_strategy4_correctness : undef_uint_array_strategy4.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg p x y z).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.


Lemma undef_uint_array_strategy17_correctness : undef_uint_array_strategy17.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg p n).
  cancel.
Qed.

Lemma undef_uint_array_strategy18_correctness : undef_uint_array_strategy18.
Proof.
  pre_process_default.
  subst n.
  rewrite IntArray.undef_full_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy19_correctness : undef_uint_array_strategy19.
  pre_process_default.
  subst.
  apply IntArray.undef_seg_empty.
Qed.

Lemma undef_uint_array_strategy20_correctness : undef_uint_array_strategy20.
Proof.
  pre_process_default.
  subst x1 y1.
  cancel.
Qed.

Lemma undef_uint_array_strategy5_correctness : undef_uint_array_strategy5.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg p x y z).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma undef_uint_array_strategy15_correctness : undef_uint_array_strategy15.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.undef_seg_split_to_undef_seg p x y z).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma undef_uint_array_strategy6_correctness : undef_uint_array_strategy6.
Proof.
  pre_process_default.
  rewrite UIntArray.undef_seg_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy16_correctness : undef_uint_array_strategy16.
Proof.
  pre_process_default.
  rewrite IntArray.undef_seg_empty.
  cancel.
Qed.

Lemma undef_uint_array_strategy21_correctness : undef_uint_array_strategy21.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (UIntArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + cancel (UIntArray.undef_seg p 1 n).
      apply_sepcon_adjoint.
      normalize.
      replace (p + 0 * sizeof ( UINT )) with (p + 0) by lia.
      cancel.
Qed.

Lemma undef_uint_array_strategy22_correctness : undef_uint_array_strategy22.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (IntArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + cancel (IntArray.undef_seg p 1 n).
      apply_sepcon_adjoint.
      normalize.
      replace (p + 0 * sizeof ( INT )) with (p + 0) by lia.
      cancel.
Qed.
