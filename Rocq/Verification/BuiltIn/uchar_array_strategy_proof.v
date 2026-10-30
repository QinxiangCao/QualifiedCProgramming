From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification.BuiltIn Require Import uchar_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.

Lemma uchar_array_strategy101_correctness : uchar_array_strategy101.
Proof.
  pre_process_default.
  prop_apply (UCharArray.full_Zlength p n l).
  Intros. entailer!.
Qed.

Lemma uchar_array_strategy102_correctness : uchar_array_strategy102.
Proof.
  pre_process_default.
  prop_apply (UCharArray.seg_Zlength p x y l).
  Intros. entailer!.
Qed.

Lemma uchar_array_strategy103_correctness : uchar_array_strategy103.
Proof.
  pre_process_default.
  prop_apply (UCharArray.missing_i_Zlength p i x y l).
  Intros. entailer!.
Qed.

Lemma uchar_array_strategy1_correctness : uchar_array_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (UCharArray.full_split_to_missing_i p i n l 0).
  2: lia.
  cancel (UCharArray.missing_i p i 0 n l).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  cancel.
Qed.

Lemma uchar_array_strategy4_correctness : uchar_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma uchar_array_strategy5_correctness : uchar_array_strategy5.
  pre_process_default.
Qed.

Lemma uchar_array_strategy6_correctness : uchar_array_strategy6.
Proof.
  pre_process_default.
  Intros_p H.
  subst l2.
  cancel.
Qed.

Lemma uchar_array_strategy17_correctness : uchar_array_strategy17.
Proof.
  pre_process_default.
  subst n.
  Intros_p Hl.
  subst l2.
  sep_apply_l_atomic (UCharArray.seg_to_full p 0 i l1).
  replace (p + 0 * sizeof(UCHAR)) with p by lia.
  replace (i - 0) with i by lia.
  cancel.
Qed.

Lemma uchar_array_strategy7_correctness : uchar_array_strategy7.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.seg_split_to_missing_i p x i y l 0).
  1: dump_pre_spatial; lia.
  cancel (UCharArray.missing_i p i x y l).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p H1.
  subst v.
  cancel.
Qed.

Lemma uchar_array_strategy8_correctness : uchar_array_strategy8.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l3.
  sep_apply_l_atomic (UCharArray.seg_merge_to_seg p x y z l1 l2).
  1: dump_pre_spatial; lia.
  cancel.
Qed.

Lemma uchar_array_strategy9_correctness : uchar_array_strategy9.
Proof.
  pre_process_default.
  Intros_p Heq.
  Intros_p Hlen.
  subst l3.
  prop_apply (UCharArray.seg_Zlength p x z (l1 ++ l2)).
  Intros.
  assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
  sep_apply_l_atomic (UCharArray.seg_split_to_seg p x y z (l1 ++ l2)).
  1: dump_pre_spatial; lia.
  rewrite <- Hlen.
  rewrite sublist_app_exact1.
  rewrite (sublist_split_app_r (Zlength l1) (z - x) (Zlength l1) l1 l2) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  replace (z - x - Zlength l1) with (z - y) by lia.
  rewrite sublist_self by lia.
  cancel.
Qed.

Lemma uchar_array_strategy10_correctness : uchar_array_strategy10.
Proof.
  pre_process_default.
  Intros_p H.
  subst l.
  rewrite UCharArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma uchar_array_strategy13_correctness : uchar_array_strategy13.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l.
  subst n.
  rewrite UCharArray.full_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma uchar_array_strategy2_correctness : uchar_array_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  1: dump_pre_spatial; lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma uchar_array_strategy11_correctness : uchar_array_strategy11.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.missing_i_merge_to_seg p x i y (Znth (i - x) l 0) l).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma uchar_array_strategy31_correctness : uchar_array_strategy31.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.missing_i_merge_to_full p i n (Znth i l 0) l).
  1: dump_pre_spatial; lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma uchar_array_strategy3_correctness : uchar_array_strategy3.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.missing_i_merge_to_full p i n v l).
  1: dump_pre_spatial; lia.
  cancel.
Qed.

Lemma uchar_array_strategy12_correctness : uchar_array_strategy12.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.missing_i_merge_to_seg p x i y v l).
  1: dump_pre_spatial; lia.
  - cancel.
Qed.

Lemma uchar_array_strategy14_correctness : uchar_array_strategy14.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst i.
  sep_apply_l_atomic (UCharArray.seg_single p n v).
  sep_apply_l_atomic (UCharArray.seg_to_full p n (n + 1) (v :: nil)).
  prop_apply (UCharArray.full_Zlength p n l).
  Intros.
  sep_apply_l_atomic (UCharArray.full_merge_to_full p n (n + 1) l (v :: nil)).
  1: {
    dump_pre_spatial.
    pose proof (Zlength_nonneg l) as Hl.
    lia.
  }
  cancel.
Qed.

Lemma uchar_array_strategy15_correctness : uchar_array_strategy15.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst i.
  sep_apply_l_atomic (UCharArray.seg_single p y v).
  prop_apply (UCharArray.seg_valid p x y l).
  Intros.
  sep_apply_l_atomic (UCharArray.seg_merge_to_seg p x y (y + 1) l (v :: nil)).
  1: dump_pre_spatial; lia.
  cancel.
Qed.

Lemma uchar_array_strategy16_correctness : uchar_array_strategy16.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply_l_atomic (UCharArray.seg_single p (i - 1) v).
  sep_apply_l_atomic (UCharArray.full_to_seg (p + i * sizeof(UCHAR)) n l).
  rewrite <- UCharArray.seg_shift.
  replace (i + 0) with i by lia.
  replace (i - 1 + 1) with i by lia.
  prop_apply (UCharArray.seg_valid p i (i + n) l).
  Intros.
  sep_apply (UCharArray.seg_merge_to_full p (i - 1) i (i + n) (v :: nil) l).
  2: lia.
  replace (i + n - (i - 1)) with (n + 1) by lia.
  cbn [app]. cancel.
Qed.
