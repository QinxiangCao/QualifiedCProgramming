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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_preinv_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_div_qr_preinv_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_1 : mpn_div_qr_preinv_entail_wit_1.
Proof.
  aggressive_pre_process; entailer!.
  subst.
  replace (Zlength l_np - 1 + 1) with (Zlength l_np) by lia.
  sep_apply (store_preinv_divisor_dn1_project dp_pre inv_pre d_orig).
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_2 : mpn_div_qr_preinv_entail_wit_2.
Proof.
  unfold mpn_div_qr_preinv_entail_wit_2.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 qv_2 l_q_2 retval
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12.
  prop_apply (mpd_store_Z_compact_bound dp0 d_orig 1).
  Exists (sublist 1 nn0 (replace_Znth 0 retval l_np)) (retval :: nil) l_q_2.
  repeat split_pure_spatial.
  - Intros_p Hbound.
    subst dn0.
    replace (nn0 - 1 + 1) with nn0 by lia.
    sep_apply (store_preinv_divisor_dn1_intro dp0 inv0 d_orig).
    sep_apply_l_atomic (UIntArray.full_split_to_seg np0 1 nn0 (replace_Znth 0 retval l_np)).
    + entailer!.
    + replace (sublist 0 1 (replace_Znth 0 retval l_np)) with (retval :: nil).
      * entailer!.
      * replace 1 with (0 + 1) by lia.
        pose proof (sublist_single 0 0 (replace_Znth 0 retval l_np)) as Hsub.
        assert (Hrange: 0 <= 0 < Zlength (replace_Znth 0 retval l_np)).
        { rewrite Zlength_replace_Znth. rewrite PreH11. lia. }
        specialize (Hsub Hrange).
        rewrite Hsub.
        rewrite Znth_replace_Znth_Same.
        -- reflexivity.
        -- rewrite PreH11. lia.
  - Intros_p Hbound.
    split_pures.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. rewrite PreH1, PreH7. ring.
    + dump_pre_spatial. rewrite PreH7, Zlength_cons, Zlength_nil. ring.
    + dump_pre_spatial.
      rewrite Zlength_sublist.
      * rewrite PreH7. ring.
      * split.
        -- split.
           ++ apply Z.le_0_1.
           ++ rewrite <- PreH7. exact PreH9.
        -- rewrite Zlength_replace_Znth, PreH11. apply Z.le_refl.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial.
      simpl. change (list_within_bound UINT_MOD nil) with True.
      change (UINT_MOD ^ 1) with UINT_MOD in Hbound.
      split.
      * split.
        -- exact PreH5.
        -- apply Z.lt_trans with (m := d_orig); [exact PreH6 | apply Hbound].
      * exact I.
    + dump_pre_spatial.
      apply list_within_bound_sublist.
      * split.
        -- apply Z.le_0_1.
        -- rewrite <- PreH7. exact PreH9.
      * rewrite Zlength_replace_Znth, PreH11. apply Z.le_refl.
      * apply list_within_bound_replace_Znth.
        -- rewrite PreH11.
           split.
           ++ apply Z.le_refl.
           ++ apply Z.lt_le_trans with (m := dn0).
              ** rewrite PreH7. apply Z.lt_0_1.
              ** exact PreH9.
        -- split.
           ++ exact PreH5.
           ++ change (UINT_MOD ^ 1) with UINT_MOD in Hbound.
              apply Z.lt_trans with (m := d_orig); [exact PreH6 | apply Hbound].
        -- exact PreH12.
    + dump_pre_spatial. rewrite list_to_Z_single, PreH3. exact PreH4.
    + dump_pre_spatial. rewrite list_to_Z_single. exact PreH5.
    + dump_pre_spatial. rewrite list_to_Z_single. exact PreH6.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_3 : mpn_div_qr_preinv_entail_wit_3.
Proof.
  aggressive_pre_process; entailer!.
  subst.
  replace (Zlength l_np - 2 + 1) with (Zlength l_np - 1) by lia.
  sep_apply (store_preinv_divisor_dn2_project dp_pre inv_pre d_orig).
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_4 : mpn_div_qr_preinv_entail_wit_4.
Proof.
  unfold mpn_div_qr_preinv_entail_wit_4.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 rv_2 qv_2 l_tail_2 l_rem_2 l_q_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  Exists l_tail_2 l_rem_2 l_q_2.
  repeat split_pure_spatial.
  - sep_apply (store_preinv_divisor_dn2_intro dp0 inv0 d_orig).
    rewrite PreH12.
    replace (nn0 - 2 + 1) with (nn0 - 1) by ring.
    entailer!.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity;
      try rewrite PreH12; try rewrite PreH7; try rewrite PreH8; try ring.
    + rewrite PreH1. ring.
    + exact PreH2.
    + exact PreH3.
    + exact PreH9.
    + exact PreH10.
    + exact PreH11.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_5 : mpn_div_qr_preinv_entail_wit_5.
Proof.
  unfold mpn_div_qr_preinv_entail_wit_5.
  right.
  intros inv_pre dn_pre dp_pre nn_pre np_pre qp_pre d_orig l_np dn0 nn0 inv0 dp0 np0 qp0
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13.
  assert (Hdn_gt2: dn_pre > 2) by lia.
  sep_apply (store_preinv_divisor_gt2_project dp_pre inv_pre dn_pre d_orig Hdn_gt2).
  Intros di_orig l_dp shift_orig.
  Exists di_orig l_dp shift_orig.
  repeat split_pure_spatial.
  - subst.
    unfold div_inverse_fields.
    entailer!.
  - subst.
    repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_6 : mpn_div_qr_preinv_entail_wit_6.
Proof.
  unfold mpn_div_qr_preinv_entail_wit_6.
  right.
  intros d_orig l_np dn0 nn0 np0 qp0 l_dp_2 shift_orig d1_orig_2 d0_orig_2
    di_orig_2 l_out retval rv_2 qv_2 l_tail_2 l_rem_2 l_q_2 PreH1 PreH2
    PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
    PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34 PreH35 PreH36 PreH37.
  Exists l_rem_2 l_q_2 l_out.
  repeat split_pure_spatial.
  - sep_apply (UIntArray.seg_to_full np0 0 dn0 l_rem_2).
    replace (np0 + 0 * sizeof(UINT)) with np0 by ring.
    replace (dn0 - 0) with dn0 by ring.
    entailer!.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_7 : mpn_div_qr_preinv_entail_wit_7.
Proof.
  unfold mpn_div_qr_preinv_entail_wit_7.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 l_dp l_norm l_q l_tail
    qv rv nh_orig d1_orig d0_orig di_orig shift l_rem l_out retval
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
    PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
    PreH47 PreH48 PreH49 PreH50 PreH51.
  assert (Hdiv:
    list_to_Z UINT_MOD l_np * 2 ^ shift =
      qv * list_to_Z UINT_MOD l_dp + rv).
  {
    rewrite <- PreH46.
    replace (list_to_Z UINT_MOD l_norm + nh_orig * UINT_MOD ^ nn0)
      with (nh_orig * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_norm) by ring.
    exact PreH49.
  }
  assert (Hrem_mult:
    list_to_Z UINT_MOD l_rem =
      (list_to_Z UINT_MOD l_np - qv * d_orig) * 2 ^ shift).
  {
    rewrite PreH48.
    rewrite PreH45 in Hdiv.
    replace ((list_to_Z UINT_MOD l_np - qv * d_orig) * 2 ^ shift)
      with (list_to_Z UINT_MOD l_np * 2 ^ shift - qv * (d_orig * 2 ^ shift))
      by ring.
    lia.
  }
  assert (retval = 0).
  {
    eapply mpn_rshift_return_zero_if_multiple with
      (l := l_rem) (l_out := l_out) (cnt := shift)
      (k := list_to_Z UINT_MOD l_np - qv * d_orig).
    - lia.
    - rewrite PreH37. lia.
    - exact PreH43.
    - exact PreH15.
    - exact PreH16.
    - exact Hrem_mult.
  }
  subst retval.
  rewrite H.
  entailer!.
Qed.

Lemma proof_of_mpn_div_qr_preinv_return_wit_1 : mpn_div_qr_preinv_return_wit_1.
Proof.
  unfold mpn_div_qr_preinv_return_wit_1.
  left.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 l_q_2 l_rem_2 l_tail_2 qv_2 rv_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12.
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  repeat split_pure_spatial.
  - entailer!.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_return_wit_2 : mpn_div_qr_preinv_return_wit_2.
Proof.
  unfold mpn_div_qr_preinv_return_wit_2.
  left.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 l_q_2 l_rem_2 l_tail_2 qv_2 rv_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12.
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  repeat split_pure_spatial.
  - entailer!.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_return_wit_3 : mpn_div_qr_preinv_return_wit_3.
Proof.
  unfold mpn_div_qr_preinv_return_wit_3.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 l_dp l_norm l_q_2 l_tail_2
    qv_2 rv_2 nh_orig d1_orig d0_orig di_orig shift l_rem_2 l_out retval
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
    PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46
    PreH47 PreH48 PreH49.
  Exists l_out l_q_2.
  assert (Hdiv:
    list_to_Z UINT_MOD l_np * 2 ^ shift =
      qv_2 * list_to_Z UINT_MOD l_dp + rv_2).
  {
    rewrite <- PreH44.
    replace (list_to_Z UINT_MOD l_norm + nh_orig * UINT_MOD ^ nn0)
      with (nh_orig * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_norm) by ring.
    exact PreH47.
  }
  assert (Hrem_mult:
    list_to_Z UINT_MOD l_rem_2 =
      (list_to_Z UINT_MOD l_np - qv_2 * d_orig) * 2 ^ shift).
  {
    rewrite PreH46.
    rewrite PreH43 in Hdiv.
    replace ((list_to_Z UINT_MOD l_np - qv_2 * d_orig) * 2 ^ shift)
      with (list_to_Z UINT_MOD l_np * 2 ^ shift - qv_2 * (d_orig * 2 ^ shift))
      by ring.
    lia.
  }
  assert (Hretval0: retval = 0).
  {
    eapply mpn_rshift_return_zero_if_multiple with
      (l := l_rem_2) (l_out := l_out) (cnt := shift)
      (k := list_to_Z UINT_MOD l_np - qv_2 * d_orig).
    - lia.
    - rewrite PreH35. lia.
    - exact PreH41.
    - exact PreH13.
    - exact PreH14.
    - exact Hrem_mult.
  }
  assert (Hrem_decomp_zero:
    list_to_Z UINT_MOD l_rem_2 = list_to_Z UINT_MOD l_out * 2 ^ shift).
  {
    rewrite PreH14, Hretval0.
    replace (0 ÷ 2 ^ (32 - shift)) with 0
      by (symmetry; apply Z.quot_0_l; apply Z.pow_nonzero; lia).
    ring.
  }
  assert (Hout_eq:
    list_to_Z UINT_MOD l_out = list_to_Z UINT_MOD l_np - qv_2 * d_orig).
  {
    rewrite Hrem_mult in Hrem_decomp_zero.
    assert (Hpow_pos: 0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
    nia.
  }
  assert (Hout_nonneg: 0 <= list_to_Z UINT_MOD l_out).
  {
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH12) as Hbound.
    exact (proj1 Hbound).
  }
  assert (Hout_lt: list_to_Z UINT_MOD l_out < d_orig).
  {
    rewrite PreH46 in Hrem_decomp_zero.
    rewrite PreH43 in PreH49.
    assert (Hpow_pos: 0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
    nia.
  }
  assert (Hvalid: gmp_div_inverse_valid dn0 d_orig shift d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    split; [lia |].
    split; [exact PreH18 |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    - pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp PreH39) as Hbound.
      rewrite PreH33 in Hbound.
      rewrite PreH43 in Hbound.
      exact (proj2 Hbound).
    - split.
      + right.
      split; [lia |].
      pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn0 PreH33 ltac:(lia) PreH39) as Hhigh.
      rewrite PreH43 in Hhigh.
      rewrite PreH21, PreH22.
      rewrite Hhigh.
      ring.
      + split; [exact PreH23 |].
        split.
        * destruct (Z.eq_dec dn0 1); [lia | exact PreH29].
        * destruct (Z.eq_dec dn0 1); [lia | exact PreH30].
  }
  repeat split_pure_spatial.
  - unfold store_preinv_divisor, div_inverse_store.
    Exists l_dp shift d1_orig d0_orig di_orig.
    unfold preinv_dp_value.
    destruct (Z.gtb_spec dn0 2); [|lia].
    destruct (Z.eq_dec dn0 1) as [Heq | Hneq]; [lia |].
    sep_apply UIntArray.full_to_seg.
    entailer!.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_return_wit_4 : mpn_div_qr_preinv_return_wit_4.
Proof.
  unfold mpn_div_qr_preinv_return_wit_4.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 qp0 l_dp shift_orig d1_orig d0_orig
    di_orig rv_2 qv_2 l_tail_2 l_rem_2 l_q_2 PreH1 PreH2 PreH3 PreH4
    PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
    PreH35 PreH36 PreH37 PreH38 PreH39.
  Exists l_q_2.
  assert (Hshift0: shift_orig = 0) by lia.
  repeat split_pure_spatial.
  - assert (Hvalid: gmp_div_inverse_valid dn0 d_orig shift_orig d1_orig d0_orig di_orig).
    {
      unfold gmp_div_inverse_valid, div_inverse_den.
      repeat split; try (unfold UINT_MOD in *; lia).
      + pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp PreH28) as Hbound.
        rewrite PreH26 in Hbound.
        rewrite PreH29 in Hbound.
        exact (proj2 Hbound).
      + right.
        split; [lia |].
        pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn0 PreH26 ltac:(lia) PreH28) as Hhigh.
        rewrite PreH29 in Hhigh.
        rewrite PreH30, PreH31.
        rewrite Hhigh.
        ring.
      + exact PreH32.
      + destruct (Z.eq_dec dn0 1); [lia |].
        exact PreH38.
      + destruct (Z.eq_dec dn0 1); [lia |].
        exact PreH39.
    }
    unfold store_preinv_divisor, div_inverse_store.
    Exists l_dp shift_orig d1_orig d0_orig di_orig.
    unfold preinv_dp_value.
    destruct (Z.gtb_spec dn0 2); [|lia].
    destruct (Z.eq_dec dn0 1) as [Heq | Hneq]; [lia |].
    entailer!.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite PreH13, PreH14.
      rewrite PreH29 in PreH15.
      rewrite Hshift0 in PreH15.
      simpl in PreH15.
      replace (d_orig * 1) with d_orig in PreH15 by ring.
      replace (0 * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_np)
        with (list_to_Z UINT_MOD l_np) in PreH15 by ring.
      exact PreH15.
    + rewrite PreH14.
      rewrite PreH29 in PreH17.
      rewrite Hshift0 in PreH17.
      simpl in PreH17.
      replace (d_orig * 1) with d_orig in PreH17 by ring.
      exact PreH17.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure : mpn_div_qr_preinv_partial_solve_wit_5_pure.
Proof.
  unfold mpn_div_qr_preinv_partial_solve_wit_5_pure.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 l_dp shift_orig d1_orig
    d0_orig di_orig l_out retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  assert (Hdp_pos: 0 < list_to_Z UINT_MOD l_dp).
  {
    rewrite PreH25.
    apply Z.mul_pos_pos.
    - exact PreH18.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Htop_half: UINT_MOD / 2 <= Znth (dn0 - 1) l_dp 0).
  {
    rewrite <- PreH26.
    change (UINT_MOD / 2) with 2147483648.
    change (UINT_MOD ÷ 2) with 2147483648 in PreH28.
    exact PreH28.
  }
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
  }
  assert (Hfit_norm:
    retval * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_out <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    replace (retval * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_out)
      with (list_to_Z UINT_MOD l_out + retval * UINT_MOD ^ nn0) by ring.
    rewrite PreH13.
    exact Hfit.
  }
  repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia;
    try exact Hdp_pos;
    try (rewrite PreH22; exact Htop_half);
    try (rewrite PreH22; rewrite <- PreH26; exact PreH29);
    try (rewrite PreH22; rewrite <- PreH27; exact PreH30);
    try (rewrite PreH22; rewrite <- PreH27; exact PreH31);
    try (rewrite PreH22; rewrite <- PreH26; rewrite <- PreH27; exact PreH34);
    try (rewrite PreH22; rewrite <- PreH26; rewrite <- PreH27; exact PreH35);
    try (rewrite PreH11; rewrite PreH22; exact Hfit_norm);
    try exact Hfit_norm.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure : mpn_div_qr_preinv_partial_solve_wit_6_pure.
Proof.
  unfold mpn_div_qr_preinv_partial_solve_wit_6_pure.
  right.
  intros d_orig l_np dn0 nn0 inv0 dp0 np0 qp0 l_dp shift_orig d1_orig
    d0_orig di_orig PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
    PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  assert (Hshift0: shift_orig = 0) by lia.
  assert (Hdp_pos: 0 < list_to_Z UINT_MOD l_dp).
  {
    rewrite PreH22, Hshift0.
    simpl.
    replace (d_orig * 1) with d_orig by ring.
    exact PreH15.
  }
  assert (Htop_half: UINT_MOD / 2 <= Znth (dn0 - 1) l_dp 0).
  {
    rewrite <- PreH23.
    change (UINT_MOD / 2) with 2147483648.
    change (UINT_MOD ÷ 2) with 2147483648 in PreH25.
    exact PreH25.
  }
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
  }
  assert (Hfit0:
    list_to_Z UINT_MOD l_np <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    rewrite Hshift0 in Hfit.
    simpl in Hfit.
    replace (list_to_Z UINT_MOD l_np * 1)
      with (list_to_Z UINT_MOD l_np) in Hfit by ring.
    exact Hfit.
  }
  repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia;
    try exact Hdp_pos;
    try (rewrite PreH19; exact Htop_half);
    try (rewrite PreH19; rewrite <- PreH23; exact PreH26);
    try (rewrite PreH19; rewrite <- PreH24; exact PreH27);
    try (rewrite PreH19; rewrite <- PreH24; exact PreH28);
    try (rewrite PreH19; rewrite <- PreH23; rewrite <- PreH24; exact PreH31);
    try (rewrite PreH19; rewrite <- PreH23; rewrite <- PreH24; exact PreH32);
    try (rewrite PreH18; rewrite PreH19; exact Hfit0);
    try exact Hfit0.
Qed.
