Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_mul_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_mul_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_mul_entail_wit_1 : mpn_mul_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Intros.
  prop_apply
    (uint_array_undef_full_implies_int_length rp_pre (un_pre + vn_pre)).
  Intros.
  assert (Hvp0_bound: 0 <= Znth 0 l_vp 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_vp 0).
    - split; [lia | rewrite PreH5; lia].
    - exact PreH7. }
  split_pure_spatial.
  - sep_apply (UIntArray.undef_full_split_to_undef_seg rp_pre un_pre (un_pre + vn_pre)).
    sep_apply (UIntArray.undef_seg_to_undef_full rp_pre 0 un_pre).
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (un_pre - 0) with un_pre by lia.
    cancel.
    lia.
  - Intros.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_mul_entail_wit_2 : mpn_mul_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (l' ++ retval :: nil).
  Intros.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l' PreH2) as Hout_bound.
  rewrite PreH1 in Hout_bound.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_src PreH11) as Hsrc_bound.
  rewrite PreH9 in Hsrc_bound.
  assert (Hvp0_bound: 0 <= Znth 0 l_vp 0 < UINT_MOD) by (unfold UINT_MOD in *; lia).
  assert (Hpow_pos: 0 < UINT_MOD ^ un_pre).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD in *; lia. }
  assert (Hpow_succ: UINT_MOD ^ (un_pre + 1) = UINT_MOD * UINT_MOD ^ un_pre).
  { rewrite Z.pow_add_r by (unfold UINT_MOD in *; lia). ring. }
  assert (Hprod_bound: 0 <= list_to_Z UINT_MOD l_src * Znth 0 l_vp 0 < UINT_MOD ^ (un_pre + 1)).
  { rewrite Hpow_succ. unfold UINT_MOD in *; nia. }
  assert (Hretval_bound: 0 <= retval < UINT_MOD).
  { rewrite <- PreH3 in PreH4.
    rewrite Hpow_succ in Hprod_bound.
    unfold UINT_MOD in *.
    nia. }
  assert (Hdone_len: Zlength (l' ++ retval :: nil) = un_pre + 1).
  { rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. lia. }
  assert (Hdone_bound: list_within_bound UINT_MOD (l' ++ retval :: nil)).
  { apply list_within_bound_concat.
    - exact PreH2.
    - simpl. split; [exact Hretval_bound | tauto]. }
  assert (Hsub01: sublist 0 1 l_vp = Znth 0 l_vp 0 :: nil).
  { replace 1 with (0 + 1) by lia.
    apply sublist_single.
    rewrite PreH10. lia. }
  assert (Heq_done:
    list_to_Z UINT_MOD (l' ++ retval :: nil) =
    list_to_Z UINT_MOD l_src * list_to_Z UINT_MOD (sublist 0 1 l_vp)).
  { rewrite (list_to_Z_concat_r UINT_MOD UINT_MOD_pos l' retval Hretval_bound).
    rewrite Hsub01.
    rewrite list_to_Z_single.
    rewrite PreH1.
    rewrite PreH3.
    lia. }
  split_pure_spatial.
  - sep_apply UIntArray.full_to_seg.
    sep_apply (store_uint_undef_store_uint &("vl") (Znth 0 l_vp 0)).
    cancel.
  - Intros.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + unfold UINT_MOD in Hretval_bound.
      lia.
Qed.

Lemma proof_of_mpn_mul_entail_wit_3 : mpn_mul_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2.
  Exists (sublist i (i + un_pre) l_done_2).
  Exists (sublist 0 i l_done_2).
  Intros.
  assert (Hmid_hi: i + un_pre = un_pre + i) by lia.
  assert (Hdone_split: l_done_2 = sublist 0 i l_done_2 ++ sublist i (i + un_pre) l_done_2).
  { rewrite Hmid_hi.
    rewrite <- (sublist_self l_done_2 (Zlength l_done_2)) at 1 by lia.
    rewrite PreH11.
    rewrite (sublist_split 0 (un_pre + i) i l_done_2) by lia.
    reflexivity. }
  assert (Hlow_len: Zlength (sublist 0 i l_done_2) = i).
  { rewrite Zlength_sublist; lia. }
  assert (Hmid_len: Zlength (sublist i (i + un_pre) l_done_2) = un_pre).
  { rewrite Zlength_sublist; lia. }
  assert (Hlow_bound: list_within_bound UINT_MOD (sublist 0 i l_done_2)).
  { apply list_within_bound_sublist; try lia; exact PreH14. }
  assert (Hmid_bound: list_within_bound UINT_MOD (sublist i (i + un_pre) l_done_2)).
  { apply list_within_bound_sublist; try lia; exact PreH14. }
  split_pure_spatial.
  - rewrite <- Hmid_hi.
    sep_apply (UIntArray.seg_split_to_seg rp_pre 0 i (i + un_pre) l_done_2).
    replace (i - 0) with i by lia.
    replace (i + un_pre - 0) with (i + un_pre) by lia.
    cancel.
    lia.
  - Intros.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_mul_entail_wit_4 : mpn_mul_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_done_2.
  Exists l_mid_2.
  Exists l_low_2.
  Intros.
  assert (Hvl_bound: 0 <= Znth i l_vp 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_vp i).
    - split; [lia | rewrite PreH15; lia].
    - exact PreH20. }
  split_pure_spatial.
  - sep_apply (UIntArray.seg_to_full rp_pre i (i + un_pre) l_mid_2).
    replace (i + un_pre - i) with un_pre by lia.
    cancel.
  - Intros.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_mul_entail_wit_5 : mpn_mul_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ((l_low ++ l_out) ++ retval :: nil).
  Intros.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH2) as Hout_bound.
  rewrite PreH1 in Hout_bound.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_mid PreH24) as Hmid_bound.
  rewrite PreH17 in Hmid_bound.
  pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_src PreH25) as Hsrc_bound.
  rewrite PreH20 in Hsrc_bound.
  assert (Hvl_bound: 0 <= vl < UINT_MOD) by (unfold UINT_MOD in *; lia).
  assert (Hpow_pos: 0 < UINT_MOD ^ un_pre).
  { apply Z.pow_pos_nonneg; unfold UINT_MOD in *; lia. }
  assert (Hpow_succ: UINT_MOD ^ (un_pre + 1) = UINT_MOD * UINT_MOD ^ un_pre).
  { rewrite Z.pow_add_r by (unfold UINT_MOD in *; lia). ring. }
  assert (Hrhs_bound: 0 <= list_to_Z UINT_MOD l_mid + list_to_Z UINT_MOD l_src * vl < UINT_MOD ^ (un_pre + 1)).
  { rewrite Hpow_succ. unfold UINT_MOD in *; nia. }
  assert (Hretval_bound: 0 <= retval < UINT_MOD).
  { rewrite <- PreH3 in PreH4.
    rewrite Hpow_succ in Hrhs_bound.
    unfold UINT_MOD in *.
    nia. }
  assert (Hnew_len: Zlength ((l_low ++ l_out) ++ retval :: nil) = un_pre + (i + 1)).
  { rewrite Zlength_app. rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. lia. }
  assert (Hnew_bound: list_within_bound UINT_MOD ((l_low ++ l_out) ++ retval :: nil)).
  { apply list_within_bound_concat.
    - apply list_within_bound_concat; [exact PreH23 | exact PreH2].
    - simpl. split; [exact Hretval_bound | tauto]. }
  assert (Hdone2_to_Z:
    list_to_Z UINT_MOD l_low + list_to_Z UINT_MOD l_mid * UINT_MOD ^ i =
    list_to_Z UINT_MOD l_src * list_to_Z UINT_MOD (sublist 0 i l_vp)).
  { rewrite <- PreH27.
    rewrite PreH18.
    rewrite (list_to_Z_app UINT_MOD UINT_MOD_pos l_low l_mid).
    rewrite PreH16.
    reflexivity. }
  assert (Hnew_to_Z:
    list_to_Z UINT_MOD ((l_low ++ l_out) ++ retval :: nil) =
    list_to_Z UINT_MOD l_low + (val_out + retval * UINT_MOD ^ un_pre) * UINT_MOD ^ i).
  { rewrite (list_to_Z_concat_r UINT_MOD UINT_MOD_pos (l_low ++ l_out) retval Hretval_bound).
    rewrite (list_to_Z_app UINT_MOD UINT_MOD_pos l_low l_out).
    rewrite PreH3.
    rewrite Zlength_app. rewrite PreH16. rewrite PreH1.
    assert (Hpow_add: UINT_MOD ^ (i + un_pre) = UINT_MOD ^ un_pre * UINT_MOD ^ i).
    { replace (i + un_pre) with (un_pre + i) by lia.
      rewrite Z.pow_add_r by (unfold UINT_MOD in *; lia). ring. }
    rewrite Hpow_add.
    ring. }
  assert (Hnew_eq:
    list_to_Z UINT_MOD ((l_low ++ l_out) ++ retval :: nil) =
    list_to_Z UINT_MOD l_src * list_to_Z UINT_MOD (sublist 0 (i + 1) l_vp)).
  { rewrite Hnew_to_Z.
    rewrite PreH4.
    replace (list_to_Z UINT_MOD l_low +
      (list_to_Z UINT_MOD l_mid + list_to_Z UINT_MOD l_src * vl) * UINT_MOD ^ i)
      with ((list_to_Z UINT_MOD l_low + list_to_Z UINT_MOD l_mid * UINT_MOD ^ i) +
            list_to_Z UINT_MOD l_src * vl * UINT_MOD ^ i) by ring.
    rewrite Hdone2_to_Z.
    rewrite (list_to_Z_list_append UINT_MOD UINT_MOD_pos l_vp i).
    2: { split; [lia | rewrite PreH21; lia]. }
    2: { exact PreH26. }
    rewrite <- PreH29.
    ring. }
  split_pure_spatial.
  - rewrite PreH28.
    sep_apply (UIntArray.seg_to_full rp_pre 0 i l_low).
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (i - 0) with i by lia.
    replace (UIntArray.full (rp_pre + i * sizeof(UINT)) un_pre l_out)
      with (UIntArray.full (rp_pre + i * sizeof(UINT)) (i + un_pre - i) l_out) by (f_equal; lia).
    sep_apply (UIntArray.full_merge_to_full rp_pre i (i + un_pre) l_low l_out).
    sep_apply (UIntArray_full_snoc' (l_low ++ l_out) retval rp_pre (i + un_pre)).
    replace (i + un_pre + 1) with (un_pre + (i + 1)) by lia.
    sep_apply UIntArray.full_to_seg.
    sep_apply (store_uint_undef_store_uint &("vl") vl).
    sep_apply (store_ptr_undef_store_ptr &("rp_i") (rp_pre + i * sizeof(UINT))).
    cancel.
    rewrite Zlength_app.
    rewrite PreH16.
    rewrite PreH1.
    lia.
    lia.
  - Intros.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + unfold UINT_MOD in Hretval_bound.
      lia.
Qed.

Lemma proof_of_mpn_mul_return_wit_1 : mpn_mul_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (list_to_Z UINT_MOD l_done).
  Exists l_done.
  Intros.
  assert (Hi: i = vn_pre) by lia.
  subst i.
  split_pure_spatial.
  - rewrite (UIntArray.undef_seg_empty rp_pre (un_pre + vn_pre)).
    sep_apply (UIntArray.seg_to_full rp_pre 0 (un_pre + vn_pre) l_done).
    replace (rp_pre + 0 * sizeof(UINT)) with rp_pre by lia.
    replace (un_pre + vn_pre - 0) with (un_pre + vn_pre) by lia.
    cancel.
  - Intros.
    rewrite (sublist_self l_vp vn_pre) in PreH17 by lia.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; lia.
Qed.
