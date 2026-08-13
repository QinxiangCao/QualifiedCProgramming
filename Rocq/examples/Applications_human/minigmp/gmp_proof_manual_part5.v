Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_mpz_abs_sub_entail_wit_1 : mpz_abs_sub_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z at 1.
  Intros rptr rsize rcap.
  Exists rptr; Exists ptr_2; Exists ptr; Exists rcap; Exists rsize.
  Exists cap; Exists size; Exists cap_2; Exists size_2.
  subst retval retval_2.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_2 : mpz_abs_sub_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l) (Zabs rsize_2) an
    (Z.max (Z.max an 1) rcap_2)); try lia.
  Intros_p Hcompact.
  Exists b_pre__mp_d_2; Exists a_pre__mp_d_2; Exists retval; Exists z_callee__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists a_pre__mp_alloc_2; Exists a_pre__mp_size_2.
  Exists b_pre__mp_alloc_2; Exists b_pre__mp_size_2.
  split_pure_spatial.
  - cancel (UIntArray.undef_full retval an).
    cancel (UIntArray.undef_seg retval an (Z.max (Z.max an 1) rcap_2)).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_3 : mpz_abs_sub_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z at 1.
  Intros rptr rsize rcap.
  Exists rptr; Exists ptr_2; Exists ptr; Exists rcap; Exists rsize.
  Exists cap; Exists size; Exists cap_2; Exists size_2.
  subst retval retval_2.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_4 : mpz_abs_sub_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l) (Zabs rsize_2) bn
    (Z.max (Z.max bn 1) rcap_2)); try lia.
  Intros_p Hcompact.
  Exists b_pre__mp_d_2; Exists a_pre__mp_d_2; Exists retval; Exists z_callee__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists a_pre__mp_alloc_2; Exists a_pre__mp_size_2.
  Exists b_pre__mp_alloc_2; Exists b_pre__mp_size_2.
  split_pure_spatial.
  - cancel (UIntArray.undef_full retval bn).
    cancel (UIntArray.undef_seg retval bn (Z.max (Z.max bn 1) rcap_2)).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_1 : mpz_abs_sub_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_Z_to_store_Z_remain_size_zero.
  replace (Zabs n - Zabs m) with 0 by lia.
  unfold store_Z at 1.
  Exists ptr; Exists size; Exists cap.
  unfold store_Z at 1.
  Exists ptr_2; Exists size_2; Exists cap_2.
  replace (Zabs n) with (Zabs m) by lia.
  rewrite PreH8, PreH5.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_2 : mpz_abs_sub_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (is_compact_Z_mono_size (Zabs m) (Zabs n) bn an ltac:(lia) PreH4 PreH5)
    as Hbn_ge_an.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n) an PreH5)
    as [Han_nonneg _].
  pose proof (mpn_sub_ret_0 b_pre__mp_d a_pre__mp_d rp
    (Zabs m) (Zabs n) val_r_out bn an retval retval_2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsub_ret.
  prop_apply Hsub_ret.
  Intros.
  subst retval_2.
  prop_apply (mpd_store_Z_to_is_compact_Z rp val_r_out retval).
  Intros.
  assert (Hretval_pos : retval > 0).
  { apply (is_compact_Z_positive_size val_r_out); try assumption; lia. }
  unfold store_Z at 1.
  Exists a_pre__mp_d; Exists a_pre__mp_size; Exists a_pre__mp_alloc.
  unfold store_Z at 1.
  Exists b_pre__mp_d; Exists b_pre__mp_size; Exists b_pre__mp_alloc.
  unfold store_Z_remain_size.
  Exists rp; Exists rsize; Exists r__mp_alloc.
  replace (Zabs a_pre__mp_size) with an by lia.
  replace (Zabs b_pre__mp_size) with bn by lia.
  replace (Zabs (- retval)) with retval by lia.
  assert (Habs_mn: Zabs (Zabs n - Zabs m) = Zabs m - Zabs n) by lia.
  rewrite Habs_mn.
  replace val_r_out with (Zabs m - Zabs n) by lia.
  rewrite PreH19, PreH20.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact b_pre__mp_d (Zabs m) bn PreH4).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact a_pre__mp_d (Zabs n) an PreH5).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold same_sign; right; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_3 : mpz_abs_sub_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (is_compact_Z_mono_size (Zabs n) (Zabs m) an bn ltac:(lia) PreH5 PreH4)
    as Han_ge_bn.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs m) bn PreH4)
    as [Hbn_nonneg _].
  pose proof (mpn_sub_ret_0 a_pre__mp_d b_pre__mp_d rp
    (Zabs n) (Zabs m) val_r_out an bn retval retval_2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsub_ret.
  prop_apply Hsub_ret.
  Intros.
  subst retval_2.
  prop_apply (mpd_store_Z_to_is_compact_Z rp val_r_out retval).
  Intros.
  assert (Hretval_pos : retval > 0).
  { apply (is_compact_Z_positive_size val_r_out); try assumption; lia. }
  unfold store_Z at 1.
  Exists a_pre__mp_d; Exists a_pre__mp_size; Exists a_pre__mp_alloc.
  unfold store_Z at 1.
  Exists b_pre__mp_d; Exists b_pre__mp_size; Exists b_pre__mp_alloc.
  unfold store_Z_remain_size.
  Exists rp; Exists rsize; Exists r__mp_alloc.
  replace (Zabs a_pre__mp_size) with an by lia.
  replace (Zabs b_pre__mp_size) with bn by lia.
  assert (Habs_diff_nm: Zabs (Zabs n - Zabs m) = Zabs n - Zabs m) by lia.
  rewrite Habs_diff_nm.
  replace val_r_out with (Zabs n - Zabs m) by lia.
  rewrite PreH18, PreH19.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact a_pre__mp_d (Zabs n) an PreH5).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact b_pre__mp_d (Zabs m) bn PreH4).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
  replace (Zabs retval) with retval by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold same_sign; left; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_2_pure : mpz_abs_sub_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | |- context[mpd_store_Z_compact UINT_MOD ?ptr ?v (Zabs ?size)] =>
      prop_apply (mpd_store_Z_compact_range UINT_MOD ptr v (Zabs size))
  end.
  Intros.
  match goal with
  | H : 0 <= Zabs ?size <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      pose proof (Z.abs_le size 1073741824)
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_4_pure : mpz_abs_sub_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | |- context[mpd_store_Z_compact UINT_MOD ?ptr ?v (Zabs ?size)] =>
      prop_apply (mpd_store_Z_compact_range UINT_MOD ptr v (Zabs size))
  end.
  Intros.
  match goal with
  | H : 0 <= Zabs ?size <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      pose proof (Z.abs_le size 1073741824)
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_pure : mpz_abs_sub_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_6_pure : mpz_abs_sub_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z a_pre__mp_d (Zabs n) an).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs n) an |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs n) an Hc ltac:(lia))
  end.
  prop_apply (mpd_store_Z_compact_range UINT_MOD a_pre__mp_d (Zabs n) an).
  Intros.
  match goal with
  | H : 0 <= an <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  prop_apply (store_int_range (&( r_pre # "__mpz_struct" ->ₛ "_mp_alloc"))).
  Intros.
  match goal with
  | H : Int.min_signed <= rcap <= Int.max_signed |- _ =>
      change Int.max_signed with 2147483647 in H
  end.
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_pure : mpz_abs_sub_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    a_pre__mp_d b_pre__mp_d (Zabs n) (Zabs m) an bn ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z a_pre__mp_d (Zabs n) an).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs n) an |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs n) an Hc ltac:(lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_pure : mpz_abs_sub_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9_pure : mpz_abs_sub_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z b_pre__mp_d (Zabs m) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs m) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs m) bn Hc ltac:(lia))
  end.
  prop_apply (mpd_store_Z_compact_range UINT_MOD b_pre__mp_d (Zabs m) bn).
  Intros.
  match goal with
  | H : 0 <= bn <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H
  end.
  prop_apply (store_int_range (&( r_pre # "__mpz_struct" ->ₛ "_mp_alloc"))).
  Intros.
  match goal with
  | H : Int.min_signed <= rcap <= Int.max_signed |- _ =>
      change Int.max_signed with 2147483647 in H
  end.
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_10_pure : mpz_abs_sub_partial_solve_wit_10_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    b_pre__mp_d a_pre__mp_d (Zabs m) (Zabs n) bn an ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z b_pre__mp_d (Zabs m) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs m) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs m) bn Hc ltac:(lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_pure : mpz_abs_sub_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_add_safety_wit_3 : mpz_add_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_Z_remain_size_int_range r_pre (Zabs n + Zabs m) retval).
  Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_add_safety_wit_5 : mpz_add_safety_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_Z_remain_size_int_range r_pre (Zabs n - Zabs m) retval).
  Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_add_return_wit_4 : mpz_add_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n < 0 /\ m >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia));
      lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs (Zabs n - Zabs m)) (Zabs retval)).
  Intros.
  assert (same_sign (n + m) (- retval)) as Hsg.
  { replace (n + m) with (-(Zabs n - Zabs m)) by lia.
    apply same_sign_opp_compact_abs; [exact PreH1 | assumption]. }
  assert (Habs_add_1: Zabs (Zabs n - Zabs m) = Zabs (n + m)) by lia.
  rewrite Habs_add_1.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists (- retval); Exists cap_4.
  replace (Zabs (- retval)) with (Zabs retval) by lia.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_add_return_wit_3 : mpz_add_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n >= 0 /\ m < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia));
      lia. }
  assert (same_sign (n + m) retval) as Hsg.
  { replace (n + m) with (Zabs n - Zabs m) by lia.
    exact PreH1. }
  assert (Habs_add_2: Zabs (Zabs n - Zabs m) = Zabs (n + m)) by lia.
  rewrite Habs_add_2.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists retval; Exists cap_4.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_add_return_wit_2 : mpz_add_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n < 0 /\ m < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia));
      lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs (Zabs n + Zabs m)) (Zabs retval)).
  Intros.
  assert (same_sign (n + m) (- retval)) as Hsg.
  { replace (n + m) with (-(Zabs n + Zabs m)) by lia.
    apply same_sign_opp_compact_abs; [exact PreH1 | assumption]. }
  assert (Habs_add_3: Zabs (Zabs n + Zabs m) = Zabs (n + m)) by lia.
  rewrite Habs_add_3.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists (- retval); Exists cap_4.
  replace (Zabs (- retval)) with (Zabs retval) by lia.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_add_return_wit_1 : mpz_add_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n >= 0 /\ m >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  assert (same_sign (n + m) retval) as Hsg.
  { replace (n + m) with (Zabs n + Zabs m) by lia.
    exact PreH1. }
  assert (Habs_add_4: Zabs (Zabs n + Zabs m) = Zabs (n + m)) by lia.
  rewrite Habs_add_4.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists retval; Exists cap_4.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_sub_safety_wit_3 : mpz_sub_safety_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_Z_remain_size_int_range r_pre (Zabs n - Zabs m) retval).
  Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_sub_safety_wit_5 : mpz_sub_safety_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_Z_remain_size_int_range r_pre (Zabs n + Zabs m) retval).
  Intros.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_4 : mpz_sub_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n < 0 /\ m >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia));
      lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs (Zabs n + Zabs m)) (Zabs retval)).
  Intros.
  assert (same_sign (n - m) (- retval)) as Hsg.
  { replace (n - m) with (-(Zabs n + Zabs m)) by lia.
    apply same_sign_opp_compact_abs; [exact PreH1 | assumption]. }
  assert (Habs_sub_1: Zabs (Zabs n + Zabs m) = Zabs (n - m)) by lia.
  rewrite Habs_sub_1.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists (- retval); Exists cap_4.
  replace (Zabs (- retval)) with (Zabs retval) by lia.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_3 : mpz_sub_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n >= 0 /\ m < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia));
      lia. }
  assert (same_sign (n - m) retval) as Hsg.
  { replace (n - m) with (Zabs n + Zabs m) by lia.
    exact PreH1. }
  assert (Habs_sub_2: Zabs (Zabs n + Zabs m) = Zabs (n - m)) by lia.
  rewrite Habs_sub_2.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists retval; Exists cap_4.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_2 : mpz_sub_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n < 0 /\ m < 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs (Zabs n - Zabs m)) (Zabs retval)).
  Intros.
  assert (same_sign (n - m) (- retval)) as Hsg.
  { replace (n - m) with (-(Zabs n - Zabs m)) by lia.
    apply same_sign_opp_compact_abs; [exact PreH1 | assumption]. }
  assert (Habs_sub_3: Zabs (Zabs n - Zabs m) = Zabs (n - m)) by lia.
  rewrite Habs_sub_3.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists (- retval); Exists cap_4.
  replace (Zabs (- retval)) with (Zabs retval) by lia.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_sub_return_wit_1 : mpz_sub_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (n >= 0 /\ m >= 0) as Hnm.
  { unfold same_sign in PreH4, PreH7, PreH9.
    destruct (lxor_nonneg_implies_same_sign size size_2 ltac:(lia)); lia. }
  assert (same_sign (n - m) retval) as Hsg.
  { replace (n - m) with (Zabs n - Zabs m) by lia; exact PreH1. }
  assert (Habs_sub_4: Zabs (Zabs n - Zabs m) = Zabs (n - m)) by lia.
  rewrite Habs_sub_4.
  unfold store_Z at 1.
  Intros bptr bsize bcap.
  unfold store_Z at 1.
  Exists ptr; Exists size_3; Exists cap_3.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  unfold store_Z at 1.
  Exists ptr_2; Exists retval; Exists cap_4.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.
