Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma uint_array_strategy1_correctness : uint_array_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.full_split_to_missing_i p i n l 0).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 4) with (p + i * sizeof (UINT))
      by (rewrite sizeof_uint; lia).
    cancel (UIntArray.missing_i p i 0 n l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma uint_array_strategy4_correctness : uint_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma uint_array_strategy5_correctness : uint_array_strategy5.
  pre_process_default.
Qed.

Lemma uint_array_strategy6_correctness : uint_array_strategy6.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma uint_array_strategy7_correctness : uint_array_strategy7.
Proof.
  pre_process_default.
  sep_apply_l_atomic (UIntArray.seg_split_to_missing_i p x i y l 0).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 4) with (p + i * sizeof (UINT))
      by (rewrite sizeof_uint; lia).
    cancel (UIntArray.missing_i p i x y l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma uint_array_strategy8_correctness : uint_array_strategy8.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l3.
  sep_apply_l_atomic (UIntArray.seg_merge_to_seg p x y z l1 l2).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma uint_array_strategy9_correctness : uint_array_strategy9.
Proof.
  pre_process_default.
  Intros_p Heq.
  Intros_p Hlen.
  subst l3.
  prop_apply (UIntArray.seg_Zlength p x z (l1 ++ l2)).
  Intros.
  assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
  sep_apply_l_atomic (UIntArray.seg_split_to_seg p x y z (l1 ++ l2)).
  - dump_pre_spatial.
    lia.
  - rewrite <- Hlen.
    rewrite sublist_app_exact1.
    rewrite (sublist_split_app_r (Zlength l1) (z - x) (Zlength l1) l1 l2) by lia.
    replace (Zlength l1 - Zlength l1) with 0 by lia.
    replace (z - x - Zlength l1) with (z - y) by lia.
    rewrite sublist_self by exact (eq_sym Hz2).
    cancel.
Qed.

Lemma uint_array_strategy10_correctness : uint_array_strategy10.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  rewrite UIntArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma uint_array_strategy2_correctness : uint_array_strategy2.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma uint_array_strategy11_correctness : uint_array_strategy11.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.missing_i_merge_to_seg p x i y (Znth (i - x) l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma uint_array_strategy3_correctness : uint_array_strategy3.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.missing_i_merge_to_full p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma uint_array_strategy12_correctness : uint_array_strategy12.
Proof.
  pre_process_default.
  replace (p + i * 4) with (p + i * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.missing_i_merge_to_seg p x i y v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma uint_array_strategy13_correctness : uint_array_strategy13.
Proof.
  pre_process_default.
  subst n.
  Intros_p H.
  subst l.
  rewrite UIntArray.full_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma uint_array_strategy14_correctness : uint_array_strategy14.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  replace (p + n * 4) with (p + n * sizeof (UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic (UIntArray.seg_single p n a).
  sep_apply_l_atomic (UIntArray.seg_to_full p n (n + 1) (a :: nil)).
  prop_apply (UIntArray.full_Zlength p n l1).
  Intros.
  sep_apply_l_atomic (UIntArray.full_merge_to_full p n (n + 1) l1 (a :: nil)).
  - dump_pre_spatial.
    split.
    + rewrite <- H.
      apply Zlength_nonneg.
    + lia.
  - cancel.
Qed.
