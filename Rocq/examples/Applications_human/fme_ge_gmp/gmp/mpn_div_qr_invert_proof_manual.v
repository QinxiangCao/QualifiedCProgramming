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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_invert_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_invert_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_invert_entail_wit_1 : mpn_div_qr_invert_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold mpd_store_Z_compact.
  Intros l_dp.
  unfold div_inverse_slot.
  Exists l_dp.
  unfold mpd_store_list.
  rewrite H0.
  destruct H as [Hdp_value [Hdp_last Hdp_bound]].
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_2_split_goal_spatial :
  mpn_div_qr_invert_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold div_inverse_slot.
  repeat cancel.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_2 : mpn_div_qr_invert_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_invert_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_3_split_goal_spatial :
  mpn_div_qr_invert_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hd0: d = Znth 0 l_dp 0).
  {
    subst dn_pre.
    destruct l_dp as [|x [|y tl]].
    - rewrite Zlength_nil in PreH4; lia.
    - rewrite list_to_Z_single in PreH5.
      simpl.
      change (Znth 0 (x :: nil) 0) with x.
      lia.
    - rewrite !Zlength_cons in PreH4.
      pose proof (Zlength_nonneg tl); lia.
  }
  subst dn_pre.
  rewrite Hd0.
  unfold mpd_store_Z_compact.
  Exists l_dp.
  unfold mpd_store_list.
  split_pure_spatial.
  - rewrite PreH4.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try rewrite PreH4; try reflexivity; try lia.
    split; [rewrite PreH5; exact Hd0 | split; assumption].
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_3 :
  mpn_div_qr_invert_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_invert_entail_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_4_split_goal_spatial :
  mpn_div_qr_invert_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold div_inverse_slot.
  repeat cancel.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_4 :
  mpn_div_qr_invert_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_invert_entail_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_5_split_goal_spatial :
  mpn_div_qr_invert_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hd2: d = Znth 1 l_dp 0 * UINT_MOD + Znth 0 l_dp 0).
  {
    subst dn_pre.
    destruct l_dp as [|x [|y [|z tl]]].
    - rewrite Zlength_nil in PreH4; lia.
    - rewrite !Zlength_cons, Zlength_nil in PreH4; lia.
    - rewrite !list_to_Z_cons, list_to_Z_nil in PreH5.
      simpl.
      change (Znth 1 (x :: y :: nil) 0) with y.
      change (Znth 0 (x :: y :: nil) 0) with x.
      lia.
    - rewrite !Zlength_cons in PreH4.
      pose proof (Zlength_nonneg tl); lia.
  }
  subst dn_pre.
  rewrite Hd2.
  unfold mpd_store_Z_compact.
  Exists l_dp.
  unfold mpd_store_list.
  split_pure_spatial.
  - rewrite PreH4.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try rewrite PreH4; try reflexivity; try lia.
    split; [rewrite PreH5; exact Hd2 | split; assumption].
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_5 :
  mpn_div_qr_invert_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_invert_entail_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_6_1_split_goal_spatial :
  mpn_div_qr_invert_entail_wit_6_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdn_gt2: dn_pre > 2) by lia.
  assert (Hcompact: is_compact_Z UINT_MOD d dn_pre).
  {
    apply (is_compact_Z_from_full_last l_dp dn_pre d);
      try assumption; lia.
  }
  assert (Hdpos: 0 < d).
  {
    eapply is_compact_Z_size_pos_value_pos; eauto; lia.
  }
  assert (Htop_no_over:
    Znth (dn_pre - 1) l_dp 0 * 2 ^ retval < UINT_MOD).
  {
    change UINT_MOD with (2 ^ 32).
    exact PreH16.
  }
  pose proof (mpn_lshift_high2_quot_uint
    l_dp dn_pre retval PreH21 Hdn_gt2 PreH24 ltac:(lia) Htop_no_over)
    as Hhigh2.
  assert (Hd1range:
    0 <=
      Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval))
    <= 4294967295).
  {
    assert (Hmid:
      0 <= Znth (dn_pre - 2) l_dp 0 <= 4294967295).
    {
      pose proof (list_within_bound_Znth_bound
        UINT_MOD l_dp (dn_pre - 2) ltac:(rewrite PreH21; lia) PreH24).
      unfold UINT_MOD in *; lia.
    }
    pose proof (mpn_lshift_join_limb_bound
      (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
      (Znth (dn_pre - 2) l_dp 0)
      (Znth (dn_pre - 1) l_dp 0)
      retval Hmid ltac:(lia)) as Hjoin.
    specialize (Hjoin ltac:(rewrite Z.shiftl_mul_pow2 by lia; reflexivity)).
    unfold UINT_MOD in *; lia.
  }
  assert (Hd0range:
    0 <=
      Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 2) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 3) l_dp 0) (32 - retval))
    <= 4294967295).
  {
    assert (Hlow:
      0 <= Znth (dn_pre - 3) l_dp 0 <= 4294967295).
    {
      pose proof (list_within_bound_Znth_bound
        UINT_MOD l_dp (dn_pre - 3) ltac:(rewrite PreH21; lia) PreH24).
      unfold UINT_MOD in *; lia.
    }
    pose proof (mpn_lshift_join_limb_bound
      (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 2) l_dp 0) retval) 32)
      (Znth (dn_pre - 3) l_dp 0)
      (Znth (dn_pre - 2) l_dp 0)
      retval Hlow ltac:(lia)) as Hjoin.
    specialize (Hjoin ltac:(rewrite Z.shiftl_mul_pow2 by lia; reflexivity)).
    unfold UINT_MOD in *; lia.
  }
  assert (Hvalid:
    gmp_div_inverse_valid dn_pre d retval
      (Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval)))
      (Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 2) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 3) l_dp 0) (32 - retval)))
      retval_2).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try (unfold UINT_MOD in *; lia).
    - pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp PreH24) as Hbound.
      rewrite PreH21, PreH22 in Hbound.
      assert (Hpowpos: 0 < UINT_MOD ^ (dn_pre - 1)).
      { apply Z.pow_pos_nonneg; unfold UINT_MOD; lia. }
      assert (Htop:
        d / UINT_MOD ^ (dn_pre - 1) = Znth (dn_pre - 1) l_dp 0).
      {
        pose proof (list_to_Z_high_limb_quot_uint_for_div
          l_dp dn_pre PreH21 ltac:(lia) PreH24) as Hq.
        rewrite PreH22 in Hq.
        exact Hq.
      }
      pose proof (Z.div_mod d (UINT_MOD ^ (dn_pre - 1)) ltac:(lia)) as Hdivmod.
      pose proof (Z.mod_pos_bound d (UINT_MOD ^ (dn_pre - 1)) ltac:(lia))
        as Hmod_bound.
      rewrite Htop in Hdivmod.
      assert (Hpow_split:
        UINT_MOD ^ dn_pre = UINT_MOD * UINT_MOD ^ (dn_pre - 1)).
      {
        replace dn_pre with (1 + (dn_pre - 1)) at 1 by lia.
        rewrite Z.pow_add_r by (unfold UINT_MOD; lia).
        rewrite Z.pow_1_r.
        ring.
      }
      rewrite Hdivmod.
      rewrite Hpow_split.
      change UINT_MOD with (2 ^ 32) in *.
      assert (Hspos: 0 < 2 ^ retval) by (apply Z.pow_pos_nonneg; lia).
      assert (Hdivs:
        (Znth (dn_pre - 1) l_dp 0 * 2 ^ retval) mod (2 ^ retval) = 0).
      { apply Z.mod_mul; lia. }
      assert (Htop_gap:
        Znth (dn_pre - 1) l_dp 0 * 2 ^ retval <= 2 ^ 32 - 2 ^ retval).
      {
        apply Z.le_sub_le_add_l.
        replace (2 ^ 32 - 2 ^ retval + 2 ^ retval) with (2 ^ 32) by ring.
        assert (Hmul_mod:
          (Znth (dn_pre - 1) l_dp 0 * 2 ^ retval) mod (2 ^ retval) = 0)
          by (apply Z.mod_mul; lia).
        assert (Hceil:
          Znth (dn_pre - 1) l_dp 0 * 2 ^ retval <=
          ((2 ^ 32 - 1) / 2 ^ retval) * 2 ^ retval).
        {
          replace (Znth (dn_pre - 1) l_dp 0 * 2 ^ retval)
            with (((Znth (dn_pre - 1) l_dp 0 * 2 ^ retval) /
                    2 ^ retval) * 2 ^ retval) at 1.
          2: { rewrite Z.div_mul by lia. reflexivity. }
          apply Z.mul_le_mono_nonneg_r.
          - lia.
          - apply (Z.div_le_mono
              (Znth (dn_pre - 1) l_dp 0 * 2 ^ retval)
              (2 ^ 32 - 1) (2 ^ retval));
              lia.
        }
        assert (((2 ^ 32 - 1) / 2 ^ retval) * 2 ^ retval <=
                2 ^ 32 - 2 ^ retval).
        {
          assert (Hpow32:
            2 ^ 32 = 2 ^ (32 - retval) * 2 ^ retval).
          {
            rewrite <- Z.pow_add_r by lia.
            f_equal; lia.
          }
          replace ((2 ^ 32 - 1) / 2 ^ retval)
            with (2 ^ (32 - retval) - 1).
          2: {
            rewrite Hpow32.
            replace (2 ^ (32 - retval) * 2 ^ retval - 1)
              with ((2 ^ retval - 1) +
                    (2 ^ (32 - retval) - 1) * 2 ^ retval) by ring.
            rewrite Z.div_add by lia.
            rewrite Z.div_small by lia.
            ring.
          }
          rewrite Hpow32.
          ring_simplify.
          lia.
        }
        lia.
      }
      assert (Hcarry:
        d mod UINT_MOD ^ (dn_pre - 1) * 2 ^ retval <
        UINT_MOD ^ (dn_pre - 1) * 2 ^ retval).
      {
        apply Z.mul_lt_mono_pos_r.
        - lia.
        - exact (proj2 Hmod_bound).
      }
      replace (((2 ^ 32) ^ (dn_pre - 1) * Znth (dn_pre - 1) l_dp 0 +
                d mod (2 ^ 32) ^ (dn_pre - 1)) * 2 ^ retval)
        with ((Znth (dn_pre - 1) l_dp 0 * 2 ^ retval) *
              (2 ^ 32) ^ (dn_pre - 1) +
              d mod (2 ^ 32) ^ (dn_pre - 1) * 2 ^ retval) by ring.
      apply Z.lt_le_trans with
        ((2 ^ 32 - 2 ^ retval) * (2 ^ 32) ^ (dn_pre - 1) +
         (2 ^ 32) ^ (dn_pre - 1) * 2 ^ retval).
      + apply Z.add_le_lt_mono.
        * apply Z.mul_le_mono_nonneg_r; lia.
        * change UINT_MOD with (2 ^ 32) in Hcarry.
          exact Hcarry.
      + replace ((2 ^ 32 - 2 ^ retval) * (2 ^ 32) ^ (dn_pre - 1) +
                 (2 ^ 32) ^ (dn_pre - 1) * 2 ^ retval)
          with (2 ^ 32 * (2 ^ 32) ^ (dn_pre - 1)) by ring.
        lia.
    - right.
      split; [lia|].
      rewrite PreH22 in Hhigh2.
      rewrite Hhigh2.
      ring.
    - pose proof (list_within_bound_Znth_bound
        UINT_MOD l_dp (dn_pre - 2) ltac:(rewrite PreH21; lia) PreH24)
        as Hmid_bound.
      assert (Hmid_bound_uint: 0 <= Znth (dn_pre - 2) l_dp 0 < UINT_MOD)
        by (unfold UINT_MOD in *; lia).
      pose proof (mpn_lshift_lor_add
        (Znth (dn_pre - 1) l_dp 0) (Znth (dn_pre - 2) l_dp 0)
        retval Hmid_bound_uint ltac:(lia)) as Hlor.
      replace (unsigned_last_nbits
        (Znth (dn_pre - 1) l_dp 0 * 2 ^ retval) 32)
        with (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32) in Hlor.
      2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
      rewrite Hlor.
      assert (Hcarry_nonneg:
        0 <= Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval)).
      {
        rewrite Z.shiftr_div_pow2 by lia.
        apply Z.div_pos; lia.
      }
      assert (Htop_bits:
        unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32 =
        Znth (dn_pre - 1) l_dp 0 * 2 ^ retval).
      {
        rewrite Z.shiftl_mul_pow2 by lia.
        apply unsigned_last_nbits_eq.
        lia.
      }
      rewrite Htop_bits.
      change (UINT_MOD / 2) with (2 ^ 31).
      lia.
    - unfold div_inverse_den.
      destruct (Z.eq_dec dn_pre 1); [lia|].
      exact PreH10.
    - unfold div_inverse_den.
      destruct (Z.eq_dec dn_pre 1); [lia|].
      exact PreH11.
  }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact dp_pre dn_pre l_dp d);
    try assumption.
  unfold store_div_inverse.
  Exists retval
    (Z.lor
      (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
      (Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval)))
    (Z.lor
      (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 2) l_dp 0) retval) 32)
      (Z.shiftr (Znth (dn_pre - 3) l_dp 0) (32 - retval)))
    retval_2.
  unfold div_inverse_store.
  destruct (Z.eq_dec dn_pre 1); [lia|].
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_6_1 :
  mpn_div_qr_invert_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_invert_entail_wit_6_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_6_2_split_goal_spatial :
  mpn_div_qr_invert_entail_wit_6_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdn_gt2: dn_pre > 2) by lia.
  assert (Hshift0: retval = 0) by lia.
  subst retval.
  assert (Hcompact: is_compact_Z UINT_MOD d dn_pre).
  {
    apply (is_compact_Z_from_full_last l_dp dn_pre d);
      try assumption; lia.
  }
  assert (Hdpos: 0 < d).
  {
    eapply is_compact_Z_size_pos_value_pos; eauto; lia.
  }
  pose proof (list_to_Z_high2_quot_uint_for_div
    l_dp dn_pre PreH21 ltac:(lia) PreH24) as Hhigh2.
  assert (Hd1range: 0 <= Znth (dn_pre - 1) l_dp 0 <= 4294967295).
  {
    pose proof (list_within_bound_Znth_bound
      UINT_MOD l_dp (dn_pre - 1) ltac:(rewrite PreH21; lia) PreH24).
    unfold UINT_MOD in *; lia.
  }
  assert (Hd0range: 0 <= Znth (dn_pre - 2) l_dp 0 <= 4294967295).
  {
    pose proof (list_within_bound_Znth_bound
      UINT_MOD l_dp (dn_pre - 2) ltac:(rewrite PreH21; lia) PreH24).
    unfold UINT_MOD in *; lia.
  }
  assert (Hvalid:
    gmp_div_inverse_valid dn_pre d 0
      (Znth (dn_pre - 1) l_dp 0)
      (Znth (dn_pre - 2) l_dp 0)
      retval_2).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    repeat split; try (unfold UINT_MOD in *; lia).
    - pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp PreH24) as Hbound.
      rewrite PreH21, PreH22 in Hbound.
      change (2 ^ 0) with 1.
      replace (d * 1) with d by ring.
      exact (proj2 Hbound).
    - right.
      split; [lia|].
      change (2 ^ 0) with 1.
      replace (d * 1) with d by ring.
      rewrite PreH22 in Hhigh2.
      rewrite Hhigh2.
      ring.
    - change (UINT_MOD / 2) with (2 ^ 31).
      change (2 ^ 0) with 1 in PreH15.
      replace (Znth (dn_pre - 1) l_dp 0 * 1)
        with (Znth (dn_pre - 1) l_dp 0) in PreH15 by ring.
      exact PreH15.
    - unfold div_inverse_den.
      destruct (Z.eq_dec dn_pre 1); [lia|].
      exact PreH10.
    - unfold div_inverse_den.
      destruct (Z.eq_dec dn_pre 1); [lia|].
      exact PreH11.
  }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact dp_pre dn_pre l_dp d);
    try assumption.
  unfold store_div_inverse.
  Exists 0 (Znth (dn_pre - 1) l_dp 0) (Znth (dn_pre - 2) l_dp 0) retval_2.
  unfold div_inverse_store.
  destruct (Z.eq_dec dn_pre 1); [lia|].
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_entail_wit_6_2 :
  mpn_div_qr_invert_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_invert_entail_wit_6_2_split_goal_spatial.
Qed.

Lemma proof_of_mpn_div_qr_invert_partial_solve_wit_2_pure : mpn_div_qr_invert_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlast0: last l_dp 1 = Znth 0 l_dp 0).
  {
    rewrite (list_last_eq_Znth_last l_dp dn_pre PreH4 ltac:(lia)).
    replace (dn_pre - 1) with 0 by lia.
    reflexivity.
  }
  assert (Hlimb0: 0 <= Znth 0 l_dp 0 < UINT_MOD).
  {
    apply list_within_bound_Znth_bound; [rewrite PreH4; lia|assumption].
  }
  assert (Hpos0: 0 < Znth 0 l_dp 0) by (rewrite <- Hlast0; lia).
  assert (Hle0: Znth 0 l_dp 0 <= 4294967295)
    by (unfold UINT_MOD in Hlimb0; lia).
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_partial_solve_wit_5_pure : mpn_div_qr_invert_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlast1: last l_dp 1 = Znth 1 l_dp 0).
  {
    rewrite (list_last_eq_Znth_last l_dp dn_pre PreH4 ltac:(lia)).
    replace (dn_pre - 1) with 1 by lia.
    reflexivity.
  }
  assert (Hlimb0: 0 <= Znth 0 l_dp 0 < UINT_MOD).
  {
    apply list_within_bound_Znth_bound; [rewrite PreH4; lia|assumption].
  }
  assert (Hlimb1: 0 <= Znth 1 l_dp 0 < UINT_MOD).
  {
    apply list_within_bound_Znth_bound; [rewrite PreH4; lia|assumption].
  }
  assert (Hpos1: 0 < Znth 1 l_dp 0) by (rewrite <- Hlast1; lia).
  assert (Hle1: Znth 1 l_dp 0 <= 4294967295)
    by (unfold UINT_MOD in Hlimb1; lia).
  assert (Hnonneg0: 0 <= Znth 0 l_dp 0) by lia.
  assert (Hle0: Znth 0 l_dp 0 <= 4294967295)
    by (unfold UINT_MOD in Hlimb0; lia).
  repeat split_pures; dump_pre_spatial;
    try assumption; try reflexivity; lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_partial_solve_wit_8_pure : mpn_div_qr_invert_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlast: last l_dp 1 = Znth (dn_pre - 1) l_dp 0).
  {
    apply list_last_eq_Znth_last; lia.
  }
  assert (Hlimb: 0 <= Znth (dn_pre - 1) l_dp 0 < UINT_MOD).
  {
    apply list_within_bound_Znth_bound; [rewrite PreH5; lia|assumption].
  }
  assert (Hpos: 0 < Znth (dn_pre - 1) l_dp 0)
    by (rewrite <- Hlast; lia).
  assert (Hle: Znth (dn_pre - 1) l_dp 0 <= 4294967295)
    by (unfold UINT_MOD in Hlimb; lia).
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_partial_solve_wit_10_pure : mpn_div_qr_invert_partial_solve_wit_10_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hd1range:
    0 <=
      Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval))
    <= 4294967295).
  {
    assert (Hmid:
      0 <= Znth (dn_pre - 2) l_dp 0 <= 4294967295).
    {
      pose proof (list_within_bound_Znth_bound
        UINT_MOD l_dp (dn_pre - 2) ltac:(rewrite PreH10; lia) PreH13).
      unfold UINT_MOD in *; lia.
    }
    pose proof (mpn_lshift_join_limb_bound
      (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
      (Znth (dn_pre - 2) l_dp 0)
      (Znth (dn_pre - 1) l_dp 0)
      retval Hmid ltac:(lia)) as Hjoin.
    specialize (Hjoin ltac:(rewrite Z.shiftl_mul_pow2 by lia; reflexivity)).
    unfold UINT_MOD in *; lia.
  }
  assert (Hd0range:
    0 <=
      Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 2) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 3) l_dp 0) (32 - retval))
    <= 4294967295).
  {
    assert (Hlow:
      0 <= Znth (dn_pre - 3) l_dp 0 <= 4294967295).
    {
      pose proof (list_within_bound_Znth_bound
        UINT_MOD l_dp (dn_pre - 3) ltac:(rewrite PreH10; lia) PreH13).
      unfold UINT_MOD in *; lia.
    }
    pose proof (mpn_lshift_join_limb_bound
      (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 2) l_dp 0) retval) 32)
      (Znth (dn_pre - 3) l_dp 0)
      (Znth (dn_pre - 2) l_dp 0)
      retval Hlow ltac:(lia)) as Hjoin.
    specialize (Hjoin ltac:(rewrite Z.shiftl_mul_pow2 by lia; reflexivity)).
    unfold UINT_MOD in *; lia.
  }
  assert (Hd1lower:
    UINT_MOD / 2 <=
      Z.lor
        (unsigned_last_nbits
          (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32)
        (Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval))).
  {
    assert (Hmid_bound: 0 <= Znth (dn_pre - 2) l_dp 0 < UINT_MOD).
    {
      apply list_within_bound_Znth_bound; [rewrite PreH10; lia|assumption].
    }
    pose proof (mpn_lshift_lor_add
      (Znth (dn_pre - 1) l_dp 0) (Znth (dn_pre - 2) l_dp 0)
      retval Hmid_bound ltac:(lia)) as Hlor.
    replace (unsigned_last_nbits
      (Znth (dn_pre - 1) l_dp 0 * 2 ^ retval) 32)
      with (unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32) in Hlor.
    2: { rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    rewrite Hlor.
    assert (Hcarry_nonneg:
      0 <= Z.shiftr (Znth (dn_pre - 2) l_dp 0) (32 - retval)).
    {
      rewrite Z.shiftr_div_pow2 by lia.
      apply Z.div_pos; lia.
    }
    assert (Htop_bits:
      unsigned_last_nbits
        (Z.shiftl (Znth (dn_pre - 1) l_dp 0) retval) 32 =
      Znth (dn_pre - 1) l_dp 0 * 2 ^ retval).
    {
      rewrite Z.shiftl_mul_pow2 by lia.
      apply unsigned_last_nbits_eq.
      lia.
    }
    rewrite Htop_bits.
    change (UINT_MOD / 2) with (2 ^ 31).
    lia.
  }
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_mpn_div_qr_invert_partial_solve_wit_11_pure : mpn_div_qr_invert_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hshift0: retval = 0) by lia.
  subst retval.
  assert (Hd1range: 0 <= Znth (dn_pre - 1) l_dp 0 <= 4294967295).
  {
    pose proof (list_within_bound_Znth_bound
      UINT_MOD l_dp (dn_pre - 1) ltac:(rewrite PreH10; lia) PreH13).
    unfold UINT_MOD in *; lia.
  }
  assert (Hd0range: 0 <= Znth (dn_pre - 2) l_dp 0 <= 4294967295).
  {
    pose proof (list_within_bound_Znth_bound
      UINT_MOD l_dp (dn_pre - 2) ltac:(rewrite PreH10; lia) PreH13).
    unfold UINT_MOD in *; lia.
  }
  assert (Hd1lower: UINT_MOD / 2 <= Znth (dn_pre - 1) l_dp 0).
  {
    change (UINT_MOD / 2) with (2 ^ 31).
    change (2 ^ 0) with 1 in PreH4.
    replace (Znth (dn_pre - 1) l_dp 0 * 1)
      with (Znth (dn_pre - 1) l_dp 0) in PreH4 by ring.
    exact PreH4.
  }
  repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.
