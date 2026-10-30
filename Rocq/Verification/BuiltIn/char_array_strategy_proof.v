Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.Verification.BuiltIn Require Import char_array_strategy_goal.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma char_array_strategy1_correctness : char_array_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.full_split_to_missing_i p i n l 0).
  - dump_pre_spatial.
    lia.
  - cancel (CharArray.missing_i p i 0 n l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma char_array_strategy4_correctness : char_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma char_array_strategy5_correctness : char_array_strategy5.
  pre_process_default.
Qed.

Lemma char_array_strategy6_correctness : char_array_strategy6.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma char_array_strategy17_correctness : char_array_strategy17.
Proof.
  pre_process_default.
  subst n.
  Intros_p Hl.
  subst l2.
  sep_apply_l_atomic (CharArray.seg_to_full p 0 i l1).
  replace (p + 0 * sizeof(CHAR)) with p by lia.
  replace (i - 0) with i by lia.
  cancel.
Qed.

Lemma char_array_strategy2_correctness : char_array_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma char_array_strategy31_correctness : char_array_strategy31.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  1: dump_pre_spatial; lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma char_array_strategy3_correctness : char_array_strategy3.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.missing_i_merge_to_full p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma char_array_strategy7_correctness : char_array_strategy7.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.seg_split_to_missing_i p x i y l 0).
  - dump_pre_spatial.
    lia.
  - cancel (CharArray.missing_i p i x y l).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma char_array_strategy8_correctness : char_array_strategy8.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l3.
  sep_apply_l_atomic (CharArray.seg_merge_to_seg p x y z l1 l2).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma char_array_strategy9_correctness : char_array_strategy9.
Proof.
  pre_process_default.
  Intros_p Heq.
  Intros_p Hlen.
  subst l3.
  prop_apply (CharArray.seg_Zlength p x z (l1 ++ l2)).
  Intros.
  assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
  sep_apply_l_atomic (CharArray.seg_split_to_seg p x y z (l1 ++ l2)).
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

Lemma char_array_strategy10_correctness : char_array_strategy10.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  rewrite CharArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma char_array_strategy11_correctness : char_array_strategy11.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.missing_i_merge_to_seg p x i y (Znth (i - x) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma char_array_strategy12_correctness : char_array_strategy12.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.missing_i_merge_to_seg p x i y v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma char_array_strategy13_correctness : char_array_strategy13.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l.
  subst n.
  rewrite CharArray.full_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma char_array_strategy101_correctness : char_array_strategy101.
Proof.
  pre_process_default.
  prop_apply (CharArray.full_Zlength p n l).
  Intros. entailer!.
Qed.

Lemma char_array_strategy102_correctness : char_array_strategy102.
Proof.
  pre_process_default.
  prop_apply (CharArray.seg_Zlength p x y l).
  Intros. entailer!.
Qed.

Lemma char_array_strategy103_correctness : char_array_strategy103.
Proof.
  pre_process_default.
  prop_apply (CharArray.missing_i_Zlength p i x y l).
  Intros. entailer!.
Qed.

Lemma char_array_strategy14_correctness : char_array_strategy14.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst i.
  sep_apply_l_atomic (CharArray.seg_single p n v).
  sep_apply_l_atomic (CharArray.seg_to_full p n (n + 1) (v :: nil)).
  prop_apply (CharArray.full_Zlength p n l).
  Intros.
  sep_apply_l_atomic (CharArray.full_merge_to_full p n (n + 1) l (v :: nil)).
  - dump_pre_spatial.
    split.
    + rewrite <- H.
      apply Zlength_nonneg.
    + lia.
  - cancel.
Qed.

Lemma char_array_strategy15_correctness : char_array_strategy15.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst i.
  sep_apply_l_atomic (CharArray.seg_single p y v).
  prop_apply (CharArray.seg_valid p x y l).
  Intros.
  sep_apply_l_atomic (CharArray.seg_merge_to_seg p x y (y + 1) l (v :: nil)).
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma char_array_strategy16_correctness : char_array_strategy16.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (CharArray.seg_single p (i - 1) v).
  sep_apply_l_atomic (CharArray.full_to_seg (p + i * sizeof(CHAR)) n l).
  rewrite <- CharArray.seg_shift.
  replace (i + 0) with i by lia.
  replace (i - 1 + 1) with i by lia.
  prop_apply (CharArray.seg_valid p i (i + n) l).
  Intros.
  sep_apply (CharArray.seg_merge_to_full p (i - 1) i (i + n) (v :: nil) l).
  2: lia.
  replace (i + n - (i - 1)) with (n + 1) by lia.
  cbn [app]. cancel.
Qed.
