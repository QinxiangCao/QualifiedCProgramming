From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_abs_sub_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_abs_sub_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_1 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_2 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_3 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_4 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_5 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_5.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_6 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_6.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_7 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_7.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_8 : mpz_abs_sub_entail_wit_1_r_eq_a_split_goal_8.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_1_r_eq_a : mpz_abs_sub_entail_wit_1_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z.
  Intros rptr rsize rcap bptr bsize bcap.
  Exists bptr rptr bcap rcap bsize rsize.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_size")) rsize).
  Intros.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) rcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  match goal with
  | H : Int.min_signed <= rsize <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= rcap <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= bsize <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  match goal with
  | H : Int.min_signed <= bcap <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_2_r_eq_a_split_goal_spatial : mpz_abs_sub_entail_wit_2_r_eq_a_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  replace retval with (Zabs rsize) by lia.
  normalize.
  repeat cancel.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_2_r_eq_a : mpz_abs_sub_entail_wit_2_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_2_r_eq_a_split_goal_spatial zb_r_eq_a za_r_eq_a r_pre a_pre rptr rsize rcap bptr bsize bcap retval retval_2 retval_3).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_3_r_eq_a_split_goal_1 : mpz_abs_sub_entail_wit_3_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_3_r_eq_a : mpz_abs_sub_entail_wit_3_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&( "cmp")) cmp).
  Intros.
  prop_apply (store_int_range (&( "an")) an).
  Intros.
  prop_apply (store_int_range (&( "bn")) bn).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr (Zabs za_r_eq_a) (Zabs rsize)).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs za_r_eq_a) (Zabs rsize) |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs za_r_eq_a) (Zabs rsize) Hc
        ltac:(pose proof (Z.abs_nonneg zb_r_eq_a); lia))
  end.
  prop_apply (mpd_store_Z_compact_range UINT_MOD rptr (Zabs za_r_eq_a) (Zabs rsize)).
  Intros.
  prop_apply (mpd_store_Z_compact_range UINT_MOD bptr (Zabs zb_r_eq_a) bn).
  Intros.
  change (Int.max_unsigned / 4 + 1) with 1073741824 in *.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_4_r_eq_a_split_goal_1 : mpz_abs_sub_entail_wit_4_r_eq_a_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_4_r_eq_a : mpz_abs_sub_entail_wit_4_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_4_r_eq_a_split_goal_1 zb_r_eq_a za_r_eq_a r_pre a_pre rsize rcap bsize bcap cmp an bn).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_6_non_alias_split_goal_1 : mpz_abs_sub_entail_wit_6_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try dump_pre_spatial; pose proof (Z.abs_nonneg size_3); lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_6_non_alias : mpz_abs_sub_entail_wit_6_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_6_non_alias_split_goal_1 l_non_alias m_non_alias n_non_alias size cap retval size_2 cap_2 retval_2 retval_3 size_3 cap_3).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_7_non_alias : mpz_abs_sub_entail_wit_7_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z a__mp_d_2 (Zabs n_non_alias) an).
  Intros_p Hsource.
  assert (Hsize_pos : an > 0).
  { apply (is_compact_Z_positive_size (Zabs n_non_alias)); try assumption; lia. }
  replace (Z.max an 1) with an by lia.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l_non_alias) (Zabs rsize_2) an
    (Z.max an rcap_2)); try lia.
  Intros_p Hcompact.
  Exists b__mp_d_2; Exists a__mp_d_2; Exists retval; Exists z__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists a__mp_alloc_2; Exists a__mp_size_2.
  Exists b__mp_alloc_2; Exists b__mp_size_2.
  split_pure_spatial.
  - cancel (UIntArray.undef_full retval an).
    cancel (UIntArray.undef_seg retval an (Z.max an rcap_2)).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_8_r_eq_a : mpz_abs_sub_entail_wit_8_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst a_pre.
  Exists z__mp_alloc.
  replace an with (Zabs rsize) by lia.
  replace z__mp_alloc with (Z.max (Zabs rsize) rcap) by lia.
  split_pure_spatial.
  - normalize. repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_9_r_eq_a_split_goal_spatial : mpz_abs_sub_entail_wit_9_r_eq_a_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst r_pre.
  replace retval with (Zabs rsize) by lia.
  normalize.
  repeat cancel.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_9_r_eq_a : mpz_abs_sub_entail_wit_9_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_9_r_eq_a_split_goal_spatial zb_r_eq_a za_r_eq_a r_pre a_pre rptr rsize rcap bptr bsize bcap retval retval_2 retval_3).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_10_r_eq_a_split_goal_1 : mpz_abs_sub_entail_wit_10_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_abs_sub_entail_wit_10_r_eq_a : mpz_abs_sub_entail_wit_10_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_alloc")) bcap).
  Intros.
  prop_apply (store_int_range (&(b_pre # "__mpz_struct" ->ₛ "_mp_size")) bsize).
  Intros.
  prop_apply (store_int_range (&( "cmp")) cmp).
  Intros.
  prop_apply (store_int_range (&( "an")) an).
  Intros.
  prop_apply (store_int_range (&( "bn")) bn).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z bptr (Zabs zb_r_eq_a) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs zb_r_eq_a) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs zb_r_eq_a) bn Hc
        ltac:(pose proof (Z.abs_nonneg za_r_eq_a); lia))
  end.
  prop_apply (mpd_store_Z_compact_range UINT_MOD rptr (Zabs za_r_eq_a) (Zabs rsize)).
  Intros.
  prop_apply (mpd_store_Z_compact_range UINT_MOD bptr (Zabs zb_r_eq_a) bn).
  Intros.
  change (Int.max_unsigned / 4 + 1) with 1073741824 in *.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial.
    all: try assumption; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_11_r_eq_a_split_goal_1 : mpz_abs_sub_entail_wit_11_r_eq_a_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_11_r_eq_a : mpz_abs_sub_entail_wit_11_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_11_r_eq_a_split_goal_1 zb_r_eq_a za_r_eq_a r_pre a_pre rsize rcap bsize bcap cmp an bn).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_13_non_alias_split_goal_1 : mpz_abs_sub_entail_wit_13_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try dump_pre_spatial; pose proof (Z.abs_nonneg size_3); lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_13_non_alias : mpz_abs_sub_entail_wit_13_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_sub_entail_wit_13_non_alias_split_goal_1 l_non_alias m_non_alias n_non_alias size cap retval size_2 cap_2 retval_2 retval_3 size_3 cap_3).
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_14_non_alias : mpz_abs_sub_entail_wit_14_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z b__mp_d_2 (Zabs m_non_alias) bn).
  Intros_p Hsource.
  assert (Hsize_pos : bn > 0).
  { apply (is_compact_Z_positive_size (Zabs m_non_alias)); try assumption; lia. }
  replace (Z.max bn 1) with bn by lia.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l_non_alias) (Zabs rsize_2) bn
    (Z.max bn rcap_2)); try lia.
  Intros_p Hcompact.
  Exists b__mp_d_2; Exists a__mp_d_2; Exists retval; Exists z__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists a__mp_alloc_2; Exists a__mp_size_2.
  Exists b__mp_alloc_2; Exists b__mp_size_2.
  split_pure_spatial.
  - cancel (UIntArray.undef_full retval bn).
    cancel (UIntArray.undef_seg retval bn (Z.max bn rcap_2)).
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_sub_entail_wit_15_r_eq_a : mpz_abs_sub_entail_wit_15_r_eq_a.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst a_pre.
  Exists z__mp_alloc.
  replace an with (Zabs rsize) by lia.
  replace z__mp_alloc with (Z.max bn rcap) by lia.
  prop_apply (mpd_store_Z_compact_mono_size
    bptr retval (Zabs zb_r_eq_a) (Zabs za_r_eq_a) bn (Zabs rsize) ltac:(lia)).
  Intros.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg retval (Zabs rsize) bn (Z.max bn rcap)); try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_1_non_alias_split_goal_spatial : mpz_abs_sub_return_wit_1_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply store_Z_to_store_Z_remain_size_zero.
  replace (Zabs n_non_alias - Zabs m_non_alias) with 0 by lia.
  replace (Zabs n_non_alias) with (Zabs m_non_alias) by lia.
  rewrite PreH8, PreH5.
  cancel.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_1_non_alias : mpz_abs_sub_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_1_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_2_r_eq_a_split_goal_spatial : mpz_abs_sub_return_wit_2_r_eq_a_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split rptr (Zabs za_r_eq_a) (Zabs rsize) 0 rcap); try lia.
  Intros.
  unfold store_Z_with_old_size.
  Exists rptr rsize rcap.
  replace (Zabs za_r_eq_a - Zabs zb_r_eq_a) with 0 by lia.
  replace (Zabs 0) with 0 by lia.
  rewrite UIntArray.undef_full_empty.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  Exists (@nil Z) data.
  rewrite UIntArray.full_empty.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try apply same_sign_refl; try (unfold same_sign; lia); try lia.
  all: try (rewrite list_to_Z_nil; simpl; lia).
  all: rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_2_r_eq_a : mpz_abs_sub_return_wit_2_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_2_r_eq_a_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_3_non_alias_split_goal_spatial : mpz_abs_sub_return_wit_3_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (is_compact_Z_mono_size (Zabs m_non_alias) (Zabs n_non_alias) bn an ltac:(lia) PreH8 PreH9)
    as Hbn_ge_an.
  prop_apply (mpn_sub_ret_0_compact rp (Zabs m_non_alias) (Zabs n_non_alias) val_r_out bn an retval retval_2).
  Intros.
  all: try assumption; try lia.
  subst retval_2.
  prop_apply (mpd_store_Z_to_is_compact_Z rp val_r_out retval).
  Intros.
  assert (Hretval_pos : retval > 0).
  { apply (is_compact_Z_positive_size val_r_out); try assumption; lia. }
  unfold store_Z_remain_size.
  Exists rp; Exists rsize; Exists r__mp_alloc.
  replace (Zabs a__mp_size) with an by lia.
  replace (Zabs b__mp_size) with bn by lia.
  replace (Zabs (- retval)) with retval by lia.
  assert (Habs_mn: Zabs (Zabs n_non_alias - Zabs m_non_alias) = Zabs m_non_alias - Zabs n_non_alias) by lia.
  rewrite Habs_mn.
  replace val_r_out with (Zabs m_non_alias - Zabs n_non_alias) by lia.
  rewrite PreH23, PreH24.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact b__mp_d (Zabs m_non_alias) bn PreH8).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact a__mp_d (Zabs n_non_alias) an PreH9).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold same_sign; right; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_3_non_alias : mpz_abs_sub_return_wit_3_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_3_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_4_r_eq_a_split_goal_spatial : mpz_abs_sub_return_wit_4_r_eq_a_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst a.
  subst r_pre.
  pose proof (is_compact_Z_mono_size (Zabs zb_r_eq_a) (Zabs za_r_eq_a) bn an ltac:(lia) PreH7 PreH8).
  prop_apply (mpn_sub_ret_0_compact rptr_new (Zabs zb_r_eq_a) (Zabs za_r_eq_a) val_r_out bn an retval retval_2).
  Intros.
  all: try assumption; try lia.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr_new val_r_out retval).
  Intros.
  sep_apply_l_atomic (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn PreH7).
  match goal with
  | Hc : is_compact_Z UINT_MOD val_r_out retval |- _ =>
      pose proof (is_compact_Z_positive_size val_r_out retval Hc ltac:(lia))
  end.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg rptr_new retval bn rcap_new); try lia.
  unfold store_Z_with_old_size.
  Exists rptr_new rsize rcap_new.
  replace val_r_out with (Zabs zb_r_eq_a - Zabs za_r_eq_a) by lia.
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs zb_r_eq_a - Zabs za_r_eq_a) by lia.
  replace (Zabs (- retval)) with retval by lia.
  replace (Zabs bsize) with bn by lia.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try (unfold same_sign; right; lia); lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_4_r_eq_a : mpz_abs_sub_return_wit_4_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_4_r_eq_a_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_5_non_alias_split_goal_spatial : mpz_abs_sub_return_wit_5_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (is_compact_Z_mono_size (Zabs n_non_alias) (Zabs m_non_alias) an bn ltac:(lia) PreH9 PreH8)
    as Han_ge_bn.
  prop_apply (mpn_sub_ret_0_compact rp (Zabs n_non_alias) (Zabs m_non_alias) val_r_out an bn retval retval_2).
  Intros.
  all: try assumption; try lia.
  subst retval_2.
  prop_apply (mpd_store_Z_to_is_compact_Z rp val_r_out retval).
  Intros.
  assert (Hretval_pos : retval > 0).
  { apply (is_compact_Z_positive_size val_r_out); try assumption; lia. }
  unfold store_Z_remain_size.
  Exists rp; Exists rsize; Exists r__mp_alloc.
  replace (Zabs a__mp_size) with an by lia.
  replace (Zabs b__mp_size) with bn by lia.
  assert (Habs_diff_nm: Zabs (Zabs n_non_alias - Zabs m_non_alias) = Zabs n_non_alias - Zabs m_non_alias) by lia.
  rewrite Habs_diff_nm.
  replace val_r_out with (Zabs n_non_alias - Zabs m_non_alias) by lia.
  rewrite PreH22, PreH23.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact a__mp_d (Zabs n_non_alias) an PreH9).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact b__mp_d (Zabs m_non_alias) bn PreH8).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.
  replace (Zabs retval) with retval by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold same_sign; left; lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_5_non_alias : mpz_abs_sub_return_wit_5_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_5_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_6_r_eq_a_split_goal_spatial : mpz_abs_sub_return_wit_6_r_eq_a_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst a.
  subst r_pre.
  pose proof (is_compact_Z_mono_size (Zabs za_r_eq_a) (Zabs zb_r_eq_a) an bn ltac:(lia) PreH8 PreH7).
  prop_apply (mpn_sub_ret_0_compact rptr_new (Zabs za_r_eq_a) (Zabs zb_r_eq_a) val_r_out an bn retval retval_2).
  Intros.
  all: try assumption; try lia.
  prop_apply (mpd_store_Z_to_is_compact_Z rptr_new val_r_out retval).
  Intros.
  sep_apply_l_atomic (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn PreH7).
  match goal with
  | Hc : is_compact_Z UINT_MOD val_r_out retval |- _ =>
      pose proof (is_compact_Z_positive_size val_r_out retval Hc ltac:(lia))
  end.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg rptr_new retval an rcap_new); try lia.
  unfold store_Z_with_old_size.
  Exists rptr_new rsize rcap_new.
  replace val_r_out with (Zabs za_r_eq_a - Zabs zb_r_eq_a) by lia.
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs za_r_eq_a - Zabs zb_r_eq_a) by lia.
  replace (Zabs retval) with retval by lia.
  replace (Zabs bsize) with bn by lia.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_sub_return_wit_6_r_eq_a : mpz_abs_sub_return_wit_6_r_eq_a.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_return_wit_6_r_eq_a_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_2_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_2_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_2_non_alias_pure : mpz_abs_sub_partial_solve_wit_2_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_2_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_5_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_5_non_alias_pure : mpz_abs_sub_partial_solve_wit_5_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_5_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias_pure : mpz_abs_sub_partial_solve_wit_7_non_alias_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_7_non_alias_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_9_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_9_non_alias_pure : mpz_abs_sub_partial_solve_wit_9_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_9_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    a__mp_d b__mp_d (Zabs n_non_alias) (Zabs m_non_alias) an bn ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z a__mp_d (Zabs n_non_alias) an).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs n_non_alias) an |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs n_non_alias) an Hc ltac:(lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    a__mp_d b__mp_d (Zabs n_non_alias) (Zabs m_non_alias) an bn ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z a__mp_d (Zabs n_non_alias) an).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs n_non_alias) an |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs n_non_alias) an Hc ltac:(lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_3 : mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure : mpz_abs_sub_partial_solve_wit_11_non_alias_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_1 l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_2 l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_11_non_alias_pure_split_goal_3 l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    rptr_new bptr (Zabs za_r_eq_a) (Zabs zb_r_eq_a) an bn ltac:(lia)).
  Intros. dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z rptr_new (Zabs za_r_eq_a) an).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs za_r_eq_a) an |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs za_r_eq_a) an Hc ltac:(pose proof (Z.abs_nonneg zb_r_eq_a); lia))
  end.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_3 : mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_1 zb_r_eq_a za_r_eq_a r_pre a_pre b_pre rsize bptr bsize bcap rptr_new rcap_new cmp an bn a).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_2 zb_r_eq_a za_r_eq_a r_pre a_pre b_pre rsize bptr bsize bcap rptr_new rcap_new cmp an bn a).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_12_r_eq_a_pure_split_goal_3 zb_r_eq_a za_r_eq_a r_pre a_pre b_pre rsize bptr bsize bcap rptr_new rcap_new cmp an bn a).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_13_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_13_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (Z.abs_nonneg a__mp_size); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_13_non_alias_pure : mpz_abs_sub_partial_solve_wit_13_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_13_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (Z.abs_nonneg rsize); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_14_r_eq_a_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_15_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_15_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_15_non_alias_pure : mpz_abs_sub_partial_solve_wit_15_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_15_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    b__mp_d a__mp_d (Zabs m_non_alias) (Zabs n_non_alias) bn an ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z b__mp_d (Zabs m_non_alias) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs m_non_alias) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs m_non_alias) bn Hc ltac:(lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    b__mp_d a__mp_d (Zabs m_non_alias) (Zabs n_non_alias) bn an ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z b__mp_d (Zabs m_non_alias) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs m_non_alias) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs m_non_alias) bn Hc ltac:(lia))
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_3 : mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure : mpz_abs_sub_partial_solve_wit_17_non_alias_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_1 l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_2 l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_17_non_alias_pure_split_goal_3 l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre rsize rcap cmp bn b__mp_size b__mp_alloc an a__mp_size a__mp_alloc r__mp_alloc r__mp_d rp a__mp_d b__mp_d).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_mono_size
    bptr rptr_new (Zabs zb_r_eq_a) (Zabs za_r_eq_a) bn an ltac:(lia)).
  Intros. dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_2 : mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_to_is_compact_Z bptr (Zabs zb_r_eq_a) bn).
  Intros.
  match goal with
  | Hc : is_compact_Z UINT_MOD (Zabs zb_r_eq_a) bn |- _ =>
      pose proof (is_compact_Z_positive_size (Zabs zb_r_eq_a) bn Hc ltac:(pose proof (Z.abs_nonneg za_r_eq_a); lia))
  end.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_3 : mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_1 zb_r_eq_a za_r_eq_a r_pre a_pre b_pre rsize bptr bsize bcap rptr_new rcap_new cmp an bn a).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_2 zb_r_eq_a za_r_eq_a r_pre a_pre b_pre rsize bptr bsize bcap rptr_new rcap_new cmp an bn a).
  - Goal_apply (proof_of_mpz_abs_sub_partial_solve_wit_18_r_eq_a_pure_split_goal_3 zb_r_eq_a za_r_eq_a r_pre a_pre b_pre rsize bptr bsize bcap rptr_new rcap_new cmp an bn a).
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_19_non_alias_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_19_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (Z.abs_nonneg b__mp_size); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_19_non_alias_pure : mpz_abs_sub_partial_solve_wit_19_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_19_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure_split_goal_1 : mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (Z.abs_nonneg bsize); lia.
Qed.

Lemma proof_of_mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure : mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_sub_partial_solve_wit_20_r_eq_a_pure_split_goal_1.
Qed.

