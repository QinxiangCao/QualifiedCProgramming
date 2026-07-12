Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Require Import Coq.micromega.Lia.

Lemma int_array_strategy1_correctness : int_array_strategy1.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.full_split_to_missing_i p i n l 0).
  - dump_pre_spatial.
    lia.
  - cancel (IntArray.missing_i p i 0 n l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma int_array_strategy4_correctness : int_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma int_array_strategy5_correctness : int_array_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma int_array_strategy6_correctness : int_array_strategy6.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma int_array_strategy7_correctness : int_array_strategy7.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.seg_split_to_missing_i p x i y l 0).
  - dump_pre_spatial.
    lia.
  - cancel (IntArray.missing_i p i x y l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma int_array_strategy8_correctness : int_array_strategy8.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l3.
  sep_apply_l_atomic (IntArray.seg_merge_to_seg p x y z l1 l2).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma int_array_strategy9_correctness : int_array_strategy9.
Proof.
  pre_process_default.
  Intros_p Heq.
  Intros_p Hlen.
  subst l3.
  prop_apply (IntArray.seg_Zlength p x z (l1 ++ l2)).
  Intros.
  assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
  sep_apply_l_atomic (IntArray.seg_split_to_seg p x y z (l1 ++ l2)).
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

Lemma int_array_strategy10_correctness : int_array_strategy10.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma int_array_strategy13_correctness : int_array_strategy13.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l2.
  subst n.
  sep_apply_l_atomic (IntArray.seg_to_full p 0 i l1).
  replace (p + 0 * sizeof ( INT )) with p by lia.
  replace (i - 0) with i by lia.
  cancel.
Qed.

Lemma int_array_strategy14_correctness : int_array_strategy14.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l.
  subst n.
  rewrite IntArray.full_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma int_array_strategy15_correctness : int_array_strategy15.
Proof.
  pre_process_default.
  subst y.
  prop_apply (IntArray.seg_Zlength p x x l).
  Intros.
  assert (l = nil).
  { destruct l; auto.
    rewrite Zlength_cons in H.
    pose proof (Zlength_nonneg l).
    lia. }
  subst l.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma int_array_strategy16_correctness : int_array_strategy16.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.seg_single p z v).
  prop_apply (IntArray.seg_valid p y z l).
  Intros.
  sep_apply_l_atomic (IntArray.seg_merge_to_seg p y z (z + 1) l (v :: nil)).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma int_array_strategy17_correctness : int_array_strategy17.
Proof.
  pre_process_default.
  subst x.
  rewrite (IntArray.seg_unfold p i y l v).
  cancel.
Qed.

Lemma int_array_strategy2_correctness : int_array_strategy2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma int_array_strategy11_correctness : int_array_strategy11.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_seg p x i y (Znth (i - x) l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma int_array_strategy3_correctness : int_array_strategy3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma int_array_strategy12_correctness : int_array_strategy12.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_seg p x i y v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.
