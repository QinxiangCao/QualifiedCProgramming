From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_abs_add_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_abs_add_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_abs_add_safety_wit_1_non_alias_split_goal_1 : mpz_abs_add_safety_wit_1_non_alias_split_goal_1.
Proof.

  LLM_pre_process ltac:(int_auto).

  prop_apply_p (mpd_store_Z_compact_range UINT_MOD aptr (Zabs n_new) an).

  Intros_p Hrange.

  change Int.max_unsigned with 4294967295 in Hrange.

  change (4294967295 / 4 + 1) with 1073741824 in Hrange.

  dump_pre_spatial. lia.

Qed.

Lemma proof_of_mpz_abs_add_safety_wit_1_non_alias_split_goal_2 : mpz_abs_add_safety_wit_1_non_alias_split_goal_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: (dump_pre_spatial; pose proof (Z.abs_nonneg asize); lia).

Qed.

Lemma proof_of_mpz_abs_add_safety_wit_1_non_alias : mpz_abs_add_safety_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_1_non_alias_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_1_non_alias_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_safety_wit_3_r_eq_a_split_goal_1 : mpz_abs_add_safety_wit_3_r_eq_a_split_goal_1.
Proof.

  LLM_pre_process ltac:(int_auto).

  prop_apply (mpd_store_Z_compact_range UINT_MOD bptr (Zabs zb_r_eq_a) (Zabs bsize)).

  Intros.

  pose proof H as Hb_range.

  change Int.max_unsigned with 4294967295 in Hb_range.

  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.

  rewrite Hcalc in Hb_range.

  dump_pre_spatial; lia.

Qed.

Lemma proof_of_mpz_abs_add_safety_wit_3_r_eq_a_split_goal_2 : mpz_abs_add_safety_wit_3_r_eq_a_split_goal_2.
Proof.

  LLM_pre_process ltac:(int_auto).

Qed.

Lemma proof_of_mpz_abs_add_safety_wit_3_r_eq_a : mpz_abs_add_safety_wit_3_r_eq_a.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_3_r_eq_a_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_3_r_eq_a_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_safety_wit_5_r_eq_a_split_goal_1 : mpz_abs_add_safety_wit_5_r_eq_a_split_goal_1.
Proof.

  LLM_pre_process ltac:(int_auto).

  prop_apply (mpd_store_Z_compact_range UINT_MOD rptr (Zabs za_r_eq_a) (Zabs rsize)).

  Intros.

  pose proof H as Hr_range.

  change Int.max_unsigned with 4294967295 in Hr_range.

  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.

  rewrite Hcalc in Hr_range.

  dump_pre_spatial; lia.

Qed.

Lemma proof_of_mpz_abs_add_safety_wit_5_r_eq_a_split_goal_2 : mpz_abs_add_safety_wit_5_r_eq_a_split_goal_2.
Proof.

  LLM_pre_process ltac:(int_auto).

Qed.

Lemma proof_of_mpz_abs_add_safety_wit_5_r_eq_a : mpz_abs_add_safety_wit_5_r_eq_a.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_5_r_eq_a_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_safety_wit_5_r_eq_a_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_1 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_2 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_3 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_4 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_5 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_5.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_6 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_6.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_7 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_7.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a_split_goal_8 : mpz_abs_add_entail_wit_1_r_eq_a_split_goal_8.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_1_r_eq_a : mpz_abs_add_entail_wit_1_r_eq_a.
Proof.

  LLM_pre_process ltac:(int_auto).

  unfold store_Z.

  Intros rptr rsize rcap.

  Intros bptr bsize bcap.

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

Lemma proof_of_mpz_abs_add_entail_wit_2_1_non_alias_split_goal_1 : mpz_abs_add_entail_wit_2_1_non_alias_split_goal_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: (pose proof (Z.abs_nonneg size_3); lia).

Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2_1_non_alias_split_goal_2 : mpz_abs_add_entail_wit_2_1_non_alias_split_goal_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: apply perm_swap.

Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2_1_non_alias : mpz_abs_add_entail_wit_2_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_2_1_non_alias_split_goal_1 l_non_alias m_non_alias n_non_alias size cap retval size_2 cap_2 retval_2 size_3 cap_3).
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_2_1_non_alias_split_goal_2 l_non_alias m_non_alias n_non_alias a_pre b_pre size cap retval size_2 cap_2 retval_2 size_3 cap_3).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2_2_non_alias_split_goal_1 : mpz_abs_add_entail_wit_2_2_non_alias_split_goal_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: (pose proof (Z.abs_nonneg size_3); lia).

Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2_2_non_alias_split_goal_2 : mpz_abs_add_entail_wit_2_2_non_alias_split_goal_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: apply Permutation_refl.

Qed.

Lemma proof_of_mpz_abs_add_entail_wit_2_2_non_alias : mpz_abs_add_entail_wit_2_2_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_2_2_non_alias_split_goal_1 l_non_alias m_non_alias n_non_alias size cap retval size_2 cap_2 retval_2 size_3 cap_3).
  - Goal_apply (proof_of_mpz_abs_add_entail_wit_2_2_non_alias_split_goal_2 l_non_alias m_non_alias n_non_alias a_pre b_pre size cap retval size_2 cap_2 retval_2 size_3 cap_3).
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_3_non_alias : mpz_abs_add_entail_wit_3_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Z.max (an + 1) 1) with (an + 1) by lia.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split
    retval (Zabs l_non_alias) (Zabs rsize_2) an
    (Z.max (an + 1) rcap_2)); try lia.
  Intros_p Hcompact.
  Exists bptr_2; Exists aptr_2; Exists retval; Exists z__mp_alloc.
  Exists rcap_2; Exists rsize_2; Exists bcap_2; Exists acap_2.
  Exists bsize_2; Exists asize_2; Exists n_new_2; Exists m_new_2.
  split_pure_spatial.
  - cancel (UIntArray.undef_full retval an).
    cancel (UIntArray.undef_seg retval an
      (Z.max (an + 1) rcap_2)).
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_1 : mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_1.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_2 : mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_2.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_3 : mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_3.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_4 : mpz_abs_add_entail_wit_4_rp_eq_ap_split_goal_4.
Proof. Abort.

Lemma proof_of_mpz_abs_add_entail_wit_4_rp_eq_ap : mpz_abs_add_entail_wit_4_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) z__mp_alloc).
  Intros.
  match goal with
  | H : Int.min_signed <= z__mp_alloc <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  subst a_pre.
  Exists z__mp_alloc.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  replace z__mp_alloc with (Z.max (Zabs rsize + 1) rcap) by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_5_rp_eq_bp : mpz_abs_add_entail_wit_5_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (store_int_range (&(r_pre # "__mpz_struct" ->ₛ "_mp_alloc")) z__mp_alloc).
  Intros.
  match goal with
  | H : Int.min_signed <= z__mp_alloc <= Int.max_signed |- _ =>
      change Int.min_signed with (-2147483648) in H;
      change Int.max_signed with 2147483647 in H
  end.
  subst a_pre.
  Exists z__mp_alloc.
  replace retval with (Zabs rsize) by lia.
  replace retval_2 with (Zabs bsize) by lia.
  replace z__mp_alloc with (Z.max (Zabs bsize + 1) rcap) by lia.
  sep_apply (UIntArray.undef_seg_split_to_undef_seg
    retval_3 (Zabs rsize) (Zabs bsize) (Z.max (Zabs bsize + 1) rcap)); try lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_9_rp_eq_ap : mpz_abs_add_entail_wit_9_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpn_add_ret_0_or_1_compact
    rptr_new (Zabs za_r_eq_a) (Zabs zb_r_eq_a) val_r_out_2 an bn retval
    PreH14 PreH19 PreH16 PreH15).
  Intros.
  prop_apply (mpd_store_Z_bound rptr_new val_r_out_2 an).
  Intros.
  match goal with
  | Hb : 0 <= val_r_out_2 < UINT_MOD ^ an |- _ =>
      pose proof Hb as Hval_bound
  end.
  match goal with
  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval
  end.
  - assert (Hcompact: is_compact_Z UINT_MOD val_r_out_2 an).
    {
      replace val_r_out_2 with (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
      replace an with (Z.max an bn) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_0; eauto.
      rewrite Z.max_l by lia.
      lia.
    }
    Left.
    Exists val_r_out_2.
    Exists rcap_new_2.
    subst a.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      all: try lia; try assumption.
    + exact PreH15.
  - assert (Hcompact: is_compact_Z UINT_MOD (val_r_out_2 + UINT_MOD ^ an) (an + 1)).
    {
      replace (val_r_out_2 + UINT_MOD ^ an) with
        (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
      replace (an + 1) with (Z.max an bn + 1) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_1; eauto.
      - rewrite Z.max_l by lia.
        lia.
      - rewrite Z.max_l by lia.
        lia.
    }
    Right.
    Exists val_r_out_2.
    Exists rcap_new_2.
    subst a.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) bn).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      all: try lia; try assumption.
    + exact PreH15.
Qed.

Lemma proof_of_mpz_abs_add_entail_wit_10_rp_eq_bp : mpz_abs_add_entail_wit_10_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpn_add_ret_0_or_1_compact
    rptr_new (Zabs zb_r_eq_a) (Zabs za_r_eq_a) val_r_out_2 an bn retval
    PreH14 ltac:(lia) PreH16 PreH15).
  Intros.
  prop_apply (mpd_store_Z_bound rptr_new val_r_out_2 an).
  Intros.
  match goal with
  | Hb : 0 <= val_r_out_2 < UINT_MOD ^ an |- _ =>
      pose proof Hb as Hval_bound
  end.
  match goal with
  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval
  end.
  - assert (Hcompact: is_compact_Z UINT_MOD val_r_out_2 an).
    {
      replace val_r_out_2 with (Zabs zb_r_eq_a + Zabs za_r_eq_a) by lia.
      replace an with (Z.max an bn) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_0; eauto.
      rewrite Z.max_l by lia.
      lia.
    }
    Left.
    Exists val_r_out_2.
    Exists rcap_new_2.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) an).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      all: try lia; try assumption.
    + exact PreH16.
  - assert (Hcompact: is_compact_Z UINT_MOD (val_r_out_2 + UINT_MOD ^ an) (an + 1)).
    {
      replace (val_r_out_2 + UINT_MOD ^ an) with
        (Zabs zb_r_eq_a + Zabs za_r_eq_a) by lia.
      replace (an + 1) with (Z.max an bn + 1) by (rewrite Z.max_l; lia).
      eapply is_compact_Z_add_1; eauto.
      - rewrite Z.max_l by lia.
        lia.
      - rewrite Z.max_l by lia.
        lia.
    }
    Right.
    Exists val_r_out_2.
    Exists rcap_new_2.
    sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs zb_r_eq_a) an).
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial.
      all: try lia; try assumption.
    + exact PreH16.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_1_non_alias_split_goal_spatial : mpz_abs_add_return_wit_1_non_alias_split_goal_spatial.

Proof.

  LLM_pre_process ltac:(int_auto).

  pose proof (mpn_add_ret_0_or_1 aptr bptr rp (Zabs n_new) (Zabs m_new) val_r_out an bn retval

    ltac:(lia) ltac:(lia)) as Hadd_ret.

  prop_apply Hadd_ret.

  Intros.

  prop_apply (store_int_range (&( r_pre # "__mpz_struct" ->ₛ "_mp_alloc"))).

  Intros.

  match goal with

  | Halloc : Int.min_signed <= r__mp_alloc <= Int.max_signed,

    Hz : r__mp_alloc = Z.max (Z.max (an + 1) 1) rcap |- _ =>

      assert (Han_int : an <= Int.max_signed) by (rewrite Hz in Halloc; lia)

  end.

  match goal with

  | Hret : retval = 0 \/ retval = 1 |- _ => destruct Hret as [Hret | Hret]; subst retval

  end.

  - assert (Hsize_ret : signed_last_nbits (unsigned_last_nbits an 32 + 0) 32 = an).

    {

      match goal with

      | Hc : is_compact_Z UINT_MOD (Zabs n_new) an |- _ =>

          pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an Hc)

            as [Han_nonneg _]

      end.

      assert (Han_u32 : 0 <= an < 2 ^ 32)

        by (change (2 ^ 32) with 4294967296; change Int.max_signed with 2147483647 in Han_int; lia).

      assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))

        by (change (2 ^ (32 - 1)) with 2147483648; change Int.max_signed with 2147483647 in Han_int; lia).

      rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.

      replace (an + 0) with an by lia.

      rewrite signed_last_nbits_eq.

      2:{ lia. }

      2:{ exact Han_s32. }

      lia.

    }

    prop_apply (mpd_store_Z_bound rp val_r_out an).

    Intros.

    assert (Hcompact_r : is_compact_Z UINT_MOD val_r_out an).

    {

      replace val_r_out with (Zabs n_new + Zabs m_new) by lia.

      replace an with (Z.max an bn) by lia.

      eapply is_compact_Z_add_0.

      - eassumption.

      - eassumption.

      - rewrite Z.max_l by lia; lia.

    }

    match goal with

    | Hperm : Permutation (Prod2 a n_new :: Prod2 b m_new :: nil)

                          (Prod2 a_pre n_non_alias :: Prod2 b_pre m_non_alias :: nil) |- _ =>

        pose proof (Permutation_length_2 Hperm) as HP

    end.

    destruct HP as [[Hpair1 Hpair2] | [Hpair1 Hpair2]].

    + unfold Prod2 in Hpair1, Hpair2.

      inversion Hpair1; inversion Hpair2; subst a_pre n_non_alias b_pre m_non_alias; clear Hpair1 Hpair2.

      unfold store_Z at 1.

      Exists aptr; Exists asize; Exists acap.

      unfold store_Z at 1.

      Exists bptr; Exists bsize; Exists bcap.

      unfold store_Z_remain_size.

      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).

      rewrite Hsize_ret.

      replace (Zabs an) with an by lia.

      replace (Zabs (Zabs n_new + Zabs m_new)) with (Zabs n_new + Zabs m_new) by lia.

      replace (Zabs n_new + Zabs m_new) with val_r_out by lia.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);

        try assumption.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);

        try assumption.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp val_r_out an);

        try assumption.

      sep_apply (store_uint_undef_store_uint (rp + an * sizeof ( UINT )) 0);

        try lia.

      sep_apply (UIntArray.undef_seg_single rp an); try lia.

      sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.

      rewrite PreH34, PreH35.

      replace (Zabs asize) with an by lia.

      replace (Zabs bsize) with bn by lia.

      split_pure_spatial.

      * repeat cancel.

      * split_pures; dump_pre_spatial.

        all: try assumption; try (unfold same_sign; left; lia); lia.

    + unfold Prod2 in Hpair1, Hpair2.

      inversion Hpair1; inversion Hpair2; subst a_pre n_non_alias b_pre m_non_alias; clear Hpair1 Hpair2.

      unfold store_Z at 1.

      Exists bptr; Exists bsize; Exists bcap.

      unfold store_Z at 1.

      Exists aptr; Exists asize; Exists acap.

      unfold store_Z_remain_size.

      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).

      rewrite Hsize_ret.

      replace (Zabs an) with an by lia.

      replace (Zabs (Zabs m_new + Zabs n_new)) with (Zabs m_new + Zabs n_new) by lia.

      replace (Zabs m_new + Zabs n_new) with val_r_out by lia.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);

        try assumption.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);

        try assumption.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact rp val_r_out an);

        try assumption.

      sep_apply (store_uint_undef_store_uint (rp + an * sizeof ( UINT )) 0);

        try lia.

      sep_apply (UIntArray.undef_seg_single rp an); try lia.

      sep_apply UIntArray.undef_seg_merge_to_undef_seg; try lia.

      rewrite PreH34, PreH35.

      replace (Zabs asize) with an by lia.

      replace (Zabs bsize) with bn by lia.

      split_pure_spatial.

      * repeat cancel.

      * split_pures; dump_pre_spatial.

        all: try assumption; try (unfold same_sign; left; lia); lia.

  - assert (Han1 : an + 1 <= Int.max_signed).

    {

      match goal with

      | Halloc : Int.min_signed <= r__mp_alloc <= Int.max_signed,

        Hz : r__mp_alloc = Z.max (Z.max (an + 1) 1) rcap |- _ =>

          rewrite Hz in Halloc; lia

      end.

    }

    assert (Hsize_ret : signed_last_nbits (unsigned_last_nbits an 32 + 1) 32 = an + 1).

    {

      match goal with

      | Hc : is_compact_Z UINT_MOD (Zabs n_new) an |- _ =>

          pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an Hc)

            as [Han_nonneg _]

      end.

      assert (Han_u32 : 0 <= an < 2 ^ 32)

        by (change (2 ^ 32) with 4294967296; change Int.max_signed with 2147483647 in Han_int; lia).

      assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))

        by (change (2 ^ (32 - 1)) with 2147483648; change Int.max_signed with 2147483647 in Han1; lia).

      rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.

      rewrite signed_last_nbits_eq.

      2:{ lia. }

      2:{ exact Han1_s32. }

      lia.

    }

    match goal with

    | Hperm : Permutation (Prod2 a n_new :: Prod2 b m_new :: nil)

                          (Prod2 a_pre n_non_alias :: Prod2 b_pre m_non_alias :: nil) |- _ =>

        pose proof (Permutation_length_2 Hperm) as HP

    end.

    destruct HP as [[Hpair1 Hpair2] | [Hpair1 Hpair2]].

    + unfold Prod2 in Hpair1, Hpair2.

      inversion Hpair1; inversion Hpair2; subst a_pre n_non_alias b_pre m_non_alias; clear Hpair1 Hpair2.

      unfold store_Z at 1.

      Exists aptr; Exists asize; Exists acap.

      unfold store_Z at 1.

      Exists bptr; Exists bsize; Exists bcap.

      unfold store_Z_remain_size.

      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).

      rewrite Hsize_ret.

      replace (Zabs (an + 1)) with (an + 1) by lia.

      replace (Zabs (Zabs n_new + Zabs m_new)) with (Zabs n_new + Zabs m_new) by lia.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);

        try assumption.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);

        try assumption.

      sep_apply (mpd_store_Z_append_one_compact rp val_r_out an).

      replace (val_r_out + UINT_MOD ^ an) with (Zabs n_new + Zabs m_new) by lia.

      rewrite PreH34, PreH35.

      replace (Zabs asize) with an by lia.

      replace (Zabs bsize) with bn by lia.

      split_pure_spatial.

      * cancel.

      * split_pures; dump_pre_spatial.

        all: try assumption; try lia.

        unfold same_sign; left.

        pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an PreH22)

          as [Han_nonneg _].

        pose proof (Z.pow_pos_nonneg UINT_MOD an UINT_MOD_pos (Z.ge_le _ _ Han_nonneg)).

        lia.

    + unfold Prod2 in Hpair1, Hpair2.

      inversion Hpair1; inversion Hpair2; subst a_pre n_non_alias b_pre m_non_alias; clear Hpair1 Hpair2.

      unfold store_Z at 1.

      Exists bptr; Exists bsize; Exists bcap.

      unfold store_Z at 1.

      Exists aptr; Exists asize; Exists acap.

      unfold store_Z_remain_size.

      Exists rp; Exists rsize; Exists (Z.max (Z.max (an + 1) 1) rcap).

      rewrite Hsize_ret.

      replace (Zabs (an + 1)) with (an + 1) by lia.

      replace (Zabs (Zabs m_new + Zabs n_new)) with (Zabs m_new + Zabs n_new) by lia.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact bptr (Zabs m_new) bn);

        try assumption.

      sep_apply (mpd_store_Z_to_mpd_store_Z_compact aptr (Zabs n_new) an);

        try assumption.

      sep_apply (mpd_store_Z_append_one_compact rp val_r_out an).

      replace (val_r_out + UINT_MOD ^ an) with (Zabs m_new + Zabs n_new) by lia.

      rewrite PreH34, PreH35.

      replace (Zabs asize) with an by lia.

      replace (Zabs bsize) with bn by lia.

      split_pure_spatial.

      * cancel.

      * split_pures; dump_pre_spatial.

        all: try assumption; try lia.

        unfold same_sign; left.

        pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs n_new) an PreH22)

          as [Han_nonneg _].

        pose proof (Z.pow_pos_nonneg UINT_MOD an UINT_MOD_pos (Z.ge_le _ _ Han_nonneg)).

        lia.

Qed.

Lemma proof_of_mpz_abs_add_return_wit_1_non_alias : mpz_abs_add_return_wit_1_non_alias.

Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_abs_add_return_wit_1_non_alias_split_goal_spatial l_non_alias m_non_alias n_non_alias r_pre a_pre b_pre n_new m_new aptr bptr asize bsize acap bcap rsize rcap b a an bn r__mp_alloc r__mp_d rp val_r_out retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37).
Qed.

Lemma proof_of_mpz_abs_add_return_wit_2_rp_eq_bp_split_goal_spatial : mpz_abs_add_return_wit_2_rp_eq_bp_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an).
  {
    subst cy.
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos val_r_out an PreH23)
      as [Han_nonneg _].
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    replace (an + 0) with an by lia.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han_s32. }
    lia.
  }
  subst cy.
  subst b.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  rewrite Hsize_ret.
  replace (Zabs an) with an by lia.
  replace (Zabs bsize) with an by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with val_r_out by lia.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact rptr_new val_r_out an).
  sep_apply (store_uint_undef_store_uint (rptr_new + an * sizeof(UINT)) 0).
  sep_apply (UIntArray.undef_seg_single rptr_new an).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption; try (unfold same_sign; left; lia); lia.
  - lia.
  - exact PreH23.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_2_rp_eq_bp : mpz_abs_add_return_wit_2_rp_eq_bp.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_return_wit_2_rp_eq_bp_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_3_rp_eq_bp_split_goal_spatial : mpz_abs_add_return_wit_3_rp_eq_bp_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an + 1).
  {
    subst cy.
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han1_s32. }
    lia.
  }
  subst cy.
  subst b.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  rewrite Hsize_ret.
  replace (Zabs (an + 1)) with (an + 1) by lia.
  replace (Zabs bsize) with an by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  sep_apply (mpd_store_Z_append_one_compact rptr_new val_r_out an).
  replace (val_r_out + UINT_MOD ^ an) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_3_rp_eq_bp : mpz_abs_add_return_wit_3_rp_eq_bp.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_return_wit_3_rp_eq_bp_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_4_rp_eq_ap_split_goal_spatial : mpz_abs_add_return_wit_4_rp_eq_ap_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an).
  {
    subst cy.
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han_s32 : - 2 ^ (32 - 1) <= an < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    replace (an + 0) with an by lia.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han_s32. }
    lia.
  }
  subst cy.
  subst a.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  rewrite Hsize_ret.
  replace (Zabs an) with an by lia.
  replace (Zabs bsize) with bn by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with val_r_out by lia.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact rptr_new val_r_out an).
  sep_apply (store_uint_undef_store_uint (rptr_new + an * sizeof(UINT)) 0).
  sep_apply (UIntArray.undef_seg_single rptr_new an).
  sep_apply UIntArray.undef_seg_merge_to_undef_seg.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption; try (unfold same_sign; left; lia); lia.
  - lia.
  - exact PreH22.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_4_rp_eq_ap : mpz_abs_add_return_wit_4_rp_eq_ap.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_return_wit_4_rp_eq_ap_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_5_rp_eq_ap_split_goal_spatial : mpz_abs_add_return_wit_5_rp_eq_ap_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsize_ret:
    signed_last_nbits (unsigned_last_nbits an 32 + cy) 32 = an + 1).
  {
    subst cy.
    assert (Han_u32 : 0 <= an < 2 ^ 32)
      by (change (2 ^ 32) with 4294967296; lia).
    assert (Han1_s32 : - 2 ^ (32 - 1) <= an + 1 < 2 ^ (32 - 1))
      by (change (2 ^ (32 - 1)) with 2147483648; lia).
    rewrite (unsigned_last_nbits_eq an 32) by exact Han_u32.
    rewrite signed_last_nbits_eq.
    2:{ lia. }
    2:{ exact Han1_s32. }
    lia.
  }
  subst cy.
  subst a.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Exists rptr_new rsize rcap_new.
  rewrite Hsize_ret.
  replace (Zabs (an + 1)) with (an + 1) by lia.
  replace (Zabs bsize) with bn by lia.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  sep_apply (mpd_store_Z_append_one_compact rptr_new val_r_out an).
  replace (val_r_out + UINT_MOD ^ an) with
    (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    all: try assumption; try (unfold same_sign; left; lia); lia.
Qed.

Lemma proof_of_mpz_abs_add_return_wit_5_rp_eq_ap : mpz_abs_add_return_wit_5_rp_eq_ap.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_return_wit_5_rp_eq_ap_split_goal_spatial.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_2_non_alias_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_2_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_2_non_alias_pure : mpz_abs_add_partial_solve_wit_2_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_2_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_5_non_alias_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_5_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_5_non_alias_pure : mpz_abs_add_partial_solve_wit_5_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_5_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_11_non_alias_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_11_non_alias_pure_split_goal_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: (dump_pre_spatial; pose proof (Z.abs_nonneg asize); lia).

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_11_non_alias_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_11_non_alias_pure_split_goal_2.
Proof.

  LLM_pre_process ltac:(int_auto).

  prop_apply_p (mpd_store_Z_compact_range UINT_MOD aptr (Zabs n_new) an).

  Intros_p Hrange.

  change Int.max_unsigned with 4294967295 in Hrange.

  change (4294967295 / 4 + 1) with 1073741824 in Hrange.

  dump_pre_spatial. lia.

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_11_non_alias_pure : mpz_abs_add_partial_solve_wit_11_non_alias_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_11_non_alias_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_11_non_alias_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_12_r_eq_a_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_12_r_eq_a_pure_split_goal_1.
Proof.

  LLM_pre_process ltac:(int_auto).

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_12_r_eq_a_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_12_r_eq_a_pure_split_goal_2.
Proof.

  LLM_pre_process ltac:(int_auto).

  prop_apply (mpd_store_Z_compact_range UINT_MOD bptr (Zabs zb_r_eq_a) (Zabs bsize)).

  Intros.

  pose proof H as Hb_range.

  change Int.max_unsigned with 4294967295 in Hb_range.

  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.

  rewrite Hcalc in Hb_range.

  dump_pre_spatial; lia.

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_12_r_eq_a_pure : mpz_abs_add_partial_solve_wit_12_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_12_r_eq_a_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_12_r_eq_a_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_13_r_eq_a_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_13_r_eq_a_pure_split_goal_1.
Proof.

  LLM_pre_process ltac:(int_auto).

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_13_r_eq_a_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_13_r_eq_a_pure_split_goal_2.
Proof.

  LLM_pre_process ltac:(int_auto).

  prop_apply (mpd_store_Z_compact_range UINT_MOD rptr (Zabs za_r_eq_a) (Zabs rsize)).

  Intros.

  pose proof H as Hr_range.

  change Int.max_unsigned with 4294967295 in Hr_range.

  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.

  rewrite Hcalc in Hr_range.

  dump_pre_spatial; lia.

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_13_r_eq_a_pure : mpz_abs_add_partial_solve_wit_13_r_eq_a_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_13_r_eq_a_pure_split_goal_1.
  - Goal_apply proof_of_mpz_abs_add_partial_solve_wit_13_r_eq_a_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_14_non_alias_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_14_non_alias_pure_split_goal_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: try dump_pre_spatial; pose proof (Z.abs_nonneg asize); lia.

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_14_non_alias_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_14_non_alias_pure_split_goal_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).

  all: try dump_pre_spatial; pose proof (Z.abs_nonneg bsize); lia.

Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_14_non_alias_pure : mpz_abs_add_partial_solve_wit_14_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_14_non_alias_pure_split_goal_1.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_14_non_alias_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure : mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure_split_goal_1.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_15_rp_eq_bp_pure_split_goal_2.
Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure_split_goal_1 : mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure_split_goal_2 : mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure : mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure_split_goal_1.
  Goal_apply proof_of_mpz_abs_add_partial_solve_wit_17_rp_eq_ap_pure_split_goal_2.
Qed.

