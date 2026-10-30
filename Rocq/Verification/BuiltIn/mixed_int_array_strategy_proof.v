From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification.BuiltIn Require Import mixed_int_array_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.

Lemma mixed_int_array_strategy101_correctness : mixed_int_array_strategy101.
Proof.
  pre_process_default.
  prop_apply (IntArray.mixed_full_Zlength p n l).
    Intros. entailer!.
Qed.

Lemma mixed_int_array_strategy102_correctness : mixed_int_array_strategy102.
Proof.
  pre_process_default.
  prop_apply (IntArray.mixed_seg_Zlength p x y l).
    Intros. entailer!.
Qed.

Lemma mixed_int_array_strategy103_correctness : mixed_int_array_strategy103.
Proof.
  pre_process_default.
  prop_apply (IntArray.mixed_missing_i_Zlength p i x y l).
    Intros. entailer!.
Qed.

Lemma mixed_int_array_strategy1_correctness : mixed_int_array_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  prop_apply (IntArray.mixed_full_Zlength p n l).
  Intros.
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i p i n l None).
  2: lia.
  cancel (IntArray.mixed_missing_i p i 0 n l).
  Intros_r v v1 d.
  apply_sepcon_adjoint.
  Intros_p Heq.
  Intros_p Hv.
  subst v.
  rewrite (Znth_indep l i None d) by lia.
  rewrite Heq.
  cbn [IntArray.mixedstoreA].
  cancel.
Qed.

Lemma mixed_int_array_strategy4_correctness : mixed_int_array_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
    subst l2.
    cancel.
Qed.

Lemma mixed_int_array_strategy5_correctness : mixed_int_array_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma mixed_int_array_strategy6_correctness : mixed_int_array_strategy6.
Proof.
  pre_process_default.
  Intros_p H.
    subst l2.
    cancel.
Qed.

Lemma mixed_int_array_strategy7_correctness : mixed_int_array_strategy7.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  prop_apply (IntArray.mixed_seg_Zlength p x y l).
  Intros.
  sep_apply (IntArray.mixed_seg_split_to_mixed_missing_i p x i y l None).
  2: lia.
  cancel (IntArray.mixed_missing_i p i x y l).
  Intros_r v v1 d.
  apply_sepcon_adjoint.
  Intros_p Heq.
  Intros_p Hv.
  subst v.
  rewrite (Znth_indep l (i - x) None d) by lia.
  rewrite <- Heq.
  cbn [IntArray.mixedstoreA].
  cancel.
Qed.

Lemma mixed_int_array_strategy8_correctness : mixed_int_array_strategy8.
Proof.
  pre_process_default.
  Intros_p H1.
    subst l3.
    sep_apply_l_atomic (IntArray.mixed_seg_merge_to_mixed_seg p x y z l1 l2).
    1: dump_pre_spatial; lia.
    cancel.
Qed.

Lemma mixed_int_array_strategy9_correctness : mixed_int_array_strategy9.
Proof.
  pre_process_default.
  Intros_p Heq.
    Intros_p Hlen.
    subst l3.
    prop_apply (IntArray.mixed_seg_Zlength p x z (l1 ++ l2)).
    Intros.
    assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
    sep_apply_l_atomic (IntArray.mixed_seg_split_to_mixed_seg p x y z (l1 ++ l2)).
    1: dump_pre_spatial; lia.
    rewrite <- Hlen.
    rewrite sublist_app_exact1.
    rewrite (sublist_split_app_r (Zlength l1) (z - x) (Zlength l1) l1 l2) by lia.
    replace (Zlength l1 - Zlength l1) with 0 by lia.
    replace (z - x - Zlength l1) with (z - y) by lia.
    rewrite sublist_self by lia.
    cancel.
Qed.

Lemma mixed_int_array_strategy10_correctness : mixed_int_array_strategy10.
Proof.
  pre_process_default.
  Intros_p H.
    subst l.
    rewrite IntArray.mixed_seg_empty.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial.
      reflexivity.
Qed.

Lemma mixed_int_array_strategy13_correctness : mixed_int_array_strategy13.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (IntArray.mixed_full_split_to_mixed_missing_i p i n l None).
  2: lia.
  sep_apply IntArray.mixedstoreA_to_undefstoreA.
  cancel (IntArray.mixed_missing_i p i 0 n l).
  apply_sepcon_adjoint.
  Intros.
  cancel.
Qed.

Lemma mixed_int_array_strategy2_correctness : mixed_int_array_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  prop_apply (IntArray.mixed_missing_i_Zlength p i 0 n l).
  Intros.
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_full p i n (Some v) l) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.
  rewrite H1.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma mixed_int_array_strategy11_correctness : mixed_int_array_strategy11.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  prop_apply (IntArray.mixed_missing_i_Zlength p i x y l).
  Intros.
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_seg p x i y (Some v) l) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.
  rewrite H1.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma mixed_int_array_strategy3_correctness : mixed_int_array_strategy3.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_full p i n (Some v) l) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.
  cancel.
Qed.

Lemma mixed_int_array_strategy14_correctness : mixed_int_array_strategy14.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_full p i n (None) l) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.
  cancel.
Qed.

Lemma mixed_int_array_strategy12_correctness : mixed_int_array_strategy12.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_seg p x i y (Some v) l) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.
  cancel.
Qed.

Lemma mixed_int_array_strategy15_correctness : mixed_int_array_strategy15.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (IntArray.undef_missing_i_to_mixed_missing_i p i 0 n).
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_full p i n (Some v) (repeat None (Z.to_nat (n - 0)))) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.
  replace (n - 0) with n by lia.
  fold (repeat_Z (@None Z) n).
  cancel.
Qed.

Lemma mixed_int_array_strategy16_correctness : mixed_int_array_strategy16.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  sep_apply (IntArray.undef_missing_i_to_mixed_missing_i p i x y).
  pose proof (IntArray.mixed_missing_i_merge_to_mixed_seg p x i y (Some v) (repeat None (Z.to_nat (y - x)))) as Hmerge.
  cbn [IntArray.mixedstoreA] in Hmerge.
  sep_apply_l_atomic Hmerge.
  1: dump_pre_spatial; lia.

  fold (repeat_Z (@None Z) (y - x)).
  cancel.
Qed.
