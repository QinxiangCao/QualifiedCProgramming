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

(*
Lemma proof_of_mpn_div_qr_preinv_entail_wit_1_split_goal_1 :
  mpn_div_qr_preinv_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_mpn_div_qr_preinv_entail_wit_1_split_goal_spatial :
  mpn_div_qr_preinv_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  replace (Zlength l_np - 1 + 1) with (Zlength l_np) by lia.
  sep_apply (store_preinv_divisor_dn1_project dp_pre inv_pre d_orig).
  cancel.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_1 : mpn_div_qr_preinv_entail_wit_1.
Proof.
  aggressive_pre_process.
  + subst.
    replace (Zlength l_np - 1 + 1) with (Zlength l_np) by lia.
    sep_apply (store_preinv_divisor_dn1_project dp_pre inv_pre d_orig).
    cancel.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_2 : mpn_div_qr_preinv_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpd_store_Z_compact_bound dp0 d_orig 1).
  Exists retval qv_2 (sublist 1 nn0 (replace_Znth 0 retval l_np))
    (retval :: nil) l_q_2.
  split_pure_spatial.
  - Intros_p Hbound.
    subst dn0.
    replace (nn0 - 1 + 1) with nn0 by lia.
    sep_apply (store_preinv_divisor_dn1_intro dp0 inv0 d_orig).
    sep_apply_l_atomic (UIntArray.full_split_to_seg np0 1 nn0 (replace_Znth 0 retval l_np)).
    + dump_pre_spatial; lia.
    + replace (sublist 0 1 (replace_Znth 0 retval l_np)) with (retval :: nil).
      * cancel (optional_q_full qp0 nn0 l_q_2).
        cancel (UIntArray.seg np0 0 1 (retval :: nil)).
        cancel (UIntArray.seg np0 1 nn0
          (sublist 1 nn0 (replace_Znth 0 retval l_np))).
        cancel (store_preinv_divisor dp0 inv0 1 d_orig).
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
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. rewrite list_to_Z_single. reflexivity.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
Qed.

(*
Lemma proof_of_mpn_div_qr_preinv_entail_wit_3_split_goal_1 :
  mpn_div_qr_preinv_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_mpn_div_qr_preinv_entail_wit_3_split_goal_spatial :
  mpn_div_qr_preinv_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst.
  replace (Zlength l_np - 2 + 1) with (Zlength l_np - 1) by lia.
  sep_apply (store_preinv_divisor_dn2_project dp_pre inv_pre d_orig).
  cancel.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_3 : mpn_div_qr_preinv_entail_wit_3.
Proof.
  aggressive_pre_process.
  + subst.
    replace (Zlength l_np - 2 + 1) with (Zlength l_np - 1) by lia.
    sep_apply (store_preinv_divisor_dn2_project dp_pre inv_pre d_orig).
    cancel.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_4 : mpn_div_qr_preinv_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - sep_apply (store_preinv_divisor_dn2_intro dp0 inv0 d_orig).
    rewrite PreH12.
    replace (nn0 - 2 + 1) with (nn0 - 1) by ring.
    cancel (optional_q_full qp0 (nn0 - 1) l_q_2).
    cancel (UIntArray.seg np0 0 2 l_rem_2).
    cancel (UIntArray.seg np0 2 nn0 l_tail_2).
    cancel (store_preinv_divisor dp0 inv0 2 d_orig).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia;
      try rewrite PreH12; try rewrite PreH7; try rewrite PreH8; try ring.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_5 : mpn_div_qr_preinv_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst qp0 np0 dp0 inv0 nn0 dn0.
  assert (Hdn_gt2: dn_pre > 2) by lia.
  sep_apply (store_preinv_divisor_gt2_project dp_pre inv_pre dn_pre d_orig Hdn_gt2).
  Intros di_orig l_dp shift_orig.
  Exists di_orig (Znth (dn_pre - 2) l_dp 0)
    (Znth (dn_pre - 1) l_dp 0) l_dp shift_orig.
  split_pure_spatial.
  -
    unfold div_inverse_fields.
    cancel ((( &( "qp" ) )) # Ptr |-> qp_pre).
    cancel ((( &( "np" ) )) # Ptr |-> np_pre).
    cancel ((( &( "dp" ) )) # Ptr |-> dp_pre).
    cancel ((( &( "inv" ) )) # Ptr |-> inv_pre).
    cancel ((( &( "nn" ) )) # Int |-> nn_pre).
    cancel ((( &( "dn" ) )) # Int |-> dn_pre).
    cancel (optional_q_undef qp_pre ((nn_pre - dn_pre) + 1)).
    cancel (UIntArray.full np_pre nn_pre l_np).
    cancel (UIntArray.full dp_pre dn_pre l_dp).
    cancel ((&((inv_pre) # "gmp_div_inverse" ->ₛ "shift")) # UInt |-> shift_orig).
    cancel ((&((inv_pre) # "gmp_div_inverse" ->ₛ "d1")) # UInt
      |-> Znth (dn_pre - 1) l_dp 0).
    cancel ((&((inv_pre) # "gmp_div_inverse" ->ₛ "d0")) # UInt
      |-> Znth (dn_pre - 2) l_dp 0).
    cancel ((&((inv_pre) # "gmp_div_inverse" ->ₛ "di")) # UInt |-> di_orig).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_6 : mpn_div_qr_preinv_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2 l_out di_orig_2 d0_orig_2
    l_dp_2 d1_orig_2.
  split_pure_spatial.
  - sep_apply (UIntArray.seg_to_full np0 0 dn0 l_rem_2).
    replace (np0 + 0 * sizeof(UINT)) with np0 by ring.
    replace (dn0 - 0) with dn0 by ring.
    cancel (optional_q_full qp0 ((nn0 - dn0) + 1) l_q_2).
    cancel (UIntArray.full np0 dn0 l_rem_2).
    cancel (UIntArray.seg np0 dn0 nn0 l_tail_2).
    cancel (UIntArray.full dp0 dn0 l_dp_2).
    cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "shift")) # UInt |-> shift_orig).
    cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "d1")) # UInt |-> d1_orig_2).
    cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "d0")) # UInt |-> d0_orig_2).
    cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "di")) # UInt |-> di_orig_2).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_7_split_goal_1 :
  mpn_div_qr_preinv_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  assert (Hretval: retval = 0).
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
  exact Hretval.
Qed.

Lemma proof_of_mpn_div_qr_preinv_entail_wit_7 :
  mpn_div_qr_preinv_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_preinv_entail_wit_7_split_goal_1.
Qed.

(* Already discharged by mpn_div_qr_preinv_proof_auto after solver regeneration.
Lemma proof_of_mpn_div_qr_preinv_return_wit_1 : mpn_div_qr_preinv_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.
*)

(* Already discharged by mpn_div_qr_preinv_proof_auto after solver regeneration.
Lemma proof_of_mpn_div_qr_preinv_return_wit_2 : mpn_div_qr_preinv_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.
*)

Lemma proof_of_mpn_div_qr_preinv_return_wit_3 : mpn_div_qr_preinv_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (list_to_Z UINT_MOD l_out) qv_2 l_tail_2 l_out l_q_2.
  assert (Hdiv:
    list_to_Z UINT_MOD l_np * 2 ^ shift =
      qv_2 * list_to_Z UINT_MOD l_dp + rv_2).
  {
    rewrite <- PreH45.
    replace (list_to_Z UINT_MOD l_norm + nh_orig * UINT_MOD ^ nn0)
      with (nh_orig * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_norm) by ring.
    exact PreH48.
  }
  assert (Hrem_mult:
    list_to_Z UINT_MOD l_rem_2 =
      (list_to_Z UINT_MOD l_np - qv_2 * d_orig) * 2 ^ shift).
  {
    rewrite PreH47.
    rewrite PreH44 in Hdiv.
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
    - rewrite PreH36. lia.
    - exact PreH42.
    - exact PreH14.
    - exact PreH15.
    - exact Hrem_mult.
  }
  assert (Hrem_decomp_zero:
    list_to_Z UINT_MOD l_rem_2 = list_to_Z UINT_MOD l_out * 2 ^ shift).
  {
    rewrite PreH15, Hretval0.
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
    pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_out PreH13) as Hbound.
    exact (proj1 Hbound).
  }
  assert (Hout_lt: list_to_Z UINT_MOD l_out < d_orig).
  {
    rewrite PreH47 in Hrem_decomp_zero.
    rewrite PreH44 in PreH50.
    assert (Hpow_pos: 0 < 2 ^ shift) by (apply Z.pow_pos_nonneg; lia).
    nia.
  }
  assert (Hvalid: gmp_div_inverse_valid dn0 d_orig shift d1_orig d0_orig di_orig).
  {
    unfold gmp_div_inverse_valid, div_inverse_den.
    split; [lia |].
    split; [exact PreH19 |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    - pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp PreH40) as Hbound.
      rewrite PreH34 in Hbound.
      rewrite PreH44 in Hbound.
      exact (proj2 Hbound).
    - split.
      + right.
      split; [lia |].
      pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn0 PreH34 ltac:(lia) PreH40) as Hhigh.
      rewrite PreH44 in Hhigh.
      rewrite PreH22, PreH23.
      rewrite Hhigh.
      ring.
      + split; [exact PreH24 |].
        split.
        * destruct (Z.eq_dec dn0 1); [lia | exact PreH30].
        * destruct (Z.eq_dec dn0 1); [lia | exact PreH31].
  }
  split_pure_spatial.
  - unfold store_preinv_divisor, div_inverse_store.
    Exists l_dp shift d1_orig d0_orig di_orig.
    unfold preinv_dp_value.
    destruct (Z.gtb_spec dn0 2); [|lia].
    destruct (Z.eq_dec dn0 1) as [Heq | Hneq]; [lia |].
    split_pure_spatial.
    + sep_apply_l_atomic (UIntArray.full_to_seg np0 dn0 l_out).
      cancel (optional_q_full qp0 ((nn0 - dn0) + 1) l_q_2).
      cancel (UIntArray.seg np0 0 dn0 l_out).
      cancel (UIntArray.seg np0 dn0 nn0 l_tail_2).
      cancel (UIntArray.full dp0 dn0 l_dp).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "shift")) # UInt |-> shift).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "d1")) # UInt |-> d1_orig).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "d0")) # UInt |-> d0_orig).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "di")) # UInt |-> di_orig).
    + split_pures; dump_pre_spatial;
        try assumption; try reflexivity; try lia.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpn_div_qr_preinv_return_wit_4 : mpn_div_qr_preinv_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists rv_2 qv_2 l_tail_2 l_rem_2 l_q_2.
  assert (Hshift0: shift_orig = 0) by lia.
  split_pure_spatial.
  - assert (Hvalid: gmp_div_inverse_valid dn0 d_orig shift_orig d1_orig d0_orig di_orig).
    {
      unfold gmp_div_inverse_valid, div_inverse_den.
      repeat split; try (unfold UINT_MOD in *; lia).
      + pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos l_dp PreH23) as Hbound.
        rewrite PreH21 in Hbound.
        rewrite PreH24 in Hbound.
        exact (proj2 Hbound).
      + right.
        split; [lia |].
        pose proof (list_to_Z_high2_quot_uint_for_div l_dp dn0 PreH21 ltac:(lia) PreH23) as Hhigh.
        rewrite PreH24 in Hhigh.
        rewrite PreH25, PreH26.
        rewrite Hhigh.
        ring.
      + exact PreH27.
      + destruct (Z.eq_dec dn0 1); [lia |].
        exact PreH33.
      + destruct (Z.eq_dec dn0 1); [lia |].
        exact PreH34.
    }
    unfold store_preinv_divisor, div_inverse_store.
    Exists l_dp shift_orig d1_orig d0_orig di_orig.
    unfold preinv_dp_value.
    destruct (Z.gtb_spec dn0 2); [|lia].
    destruct (Z.eq_dec dn0 1) as [Heq | Hneq]; [lia |].
    split_pure_spatial.
    + cancel (optional_q_full qp0 ((nn0 - dn0) + 1) l_q_2).
      cancel (UIntArray.seg np0 0 dn0 l_rem_2).
      cancel (UIntArray.seg np0 dn0 nn0 l_tail_2).
      cancel (UIntArray.full dp0 dn0 l_dp).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "shift")) # UInt |-> shift_orig).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "d1")) # UInt |-> d1_orig).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "d0")) # UInt |-> d0_orig).
      cancel ((&((inv0) # "gmp_div_inverse" ->ₛ "di")) # UInt |-> di_orig).
    + split_pures; dump_pre_spatial;
        try assumption; try reflexivity; try lia.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + rewrite PreH24 in PreH10.
      rewrite Hshift0 in PreH10.
      simpl in PreH10.
      replace (d_orig * 1) with d_orig in PreH10 by ring.
      replace (0 * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_np)
        with (list_to_Z UINT_MOD l_np) in PreH10 by ring.
      exact PreH10.
    + rewrite PreH24 in PreH12.
      rewrite Hshift0 in PreH12.
      simpl in PreH12.
      replace (d_orig * 1) with d_orig in PreH12 by ring.
      exact PreH12.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_1 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_2 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
    rewrite <- PreH26.
    exact PreH28.
  }
  replace (retval * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_out)
    with (list_to_Z UINT_MOD l_out + retval * UINT_MOD ^ nn0) by ring.
  rewrite PreH13.
  exact Hfit.
Qed.

(* These split goals no longer exist in the generated goal interface.
Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_3 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH22, <- PreH26.
  exact PreH29.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_4 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH22, <- PreH27.
  exact PreH30.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_5 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH22, <- PreH27.
  exact PreH31.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_6 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH22, <- PreH26, <- PreH27.
  exact PreH34.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_7 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH22, <- PreH26, <- PreH27.
  exact PreH35.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_8 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
    rewrite <- PreH26.
    exact PreH28.
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
  rewrite PreH11, PreH22.
  exact Hfit_norm.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_9 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
    rewrite <- PreH26.
    exact PreH28.
  }
  replace (retval * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_out)
    with (list_to_Z UINT_MOD l_out + retval * UINT_MOD ^ nn0) by ring.
  rewrite PreH13.
  exact Hfit.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_10 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_11 :
  mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure :
  mpn_div_qr_preinv_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_1.
  Goal_apply proof_of_mpn_div_qr_preinv_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_1 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_2 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hshift0: shift_orig = 0) by lia.
  assert (Hfit:
    list_to_Z UINT_MOD l_np <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    assert (Hfit_shift:
      list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
        list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
    {
      eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
      rewrite <- PreH23.
      exact PreH25.
    }
    rewrite Hshift0 in Hfit_shift.
    change (2 ^ 0) with 1 in Hfit_shift.
    rewrite Z.mul_1_r in Hfit_shift.
    exact Hfit_shift.
  }
  assert (Hdp_pos: 0 < list_to_Z UINT_MOD l_dp).
  {
    rewrite PreH22.
    apply Z.mul_pos_pos; [lia | apply Z.pow_pos_nonneg; lia].
  }
  split_pures; dump_pre_spatial;
    try solve
      [ rewrite <- PreH23; exact PreH25
      | rewrite <- PreH23; exact PreH26
      | rewrite <- PreH24; exact PreH27
      | rewrite <- PreH24; exact PreH28
      | rewrite <- PreH23, <- PreH24; exact PreH31
      | rewrite <- PreH23, <- PreH24; exact PreH32
      | replace (0 * UINT_MOD ^ nn0 + list_to_Z UINT_MOD l_np)
          with (list_to_Z UINT_MOD l_np) by ring; exact Hfit
      | exact Hdp_pos
      | assumption
      | reflexivity
      | lia ].
Qed.

(* These split goals no longer exist in the generated goal interface.
Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_3 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH19, <- PreH23.
  exact PreH26.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_4 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH19, <- PreH24.
  exact PreH27.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_5 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH19, <- PreH24.
  exact PreH28.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_6 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH19, <- PreH23, <- PreH24.
  exact PreH31.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_7 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  rewrite PreH19, <- PreH23, <- PreH24.
  exact PreH32.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_8 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  assert (Hshift0: shift_orig = 0) by lia.
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
    rewrite <- PreH23.
    exact PreH25.
  }
  rewrite Hshift0 in Hfit.
  simpl in Hfit.
  replace (list_to_Z UINT_MOD l_np * 1)
    with (list_to_Z UINT_MOD l_np) in Hfit by ring.
  rewrite PreH18, PreH19.
  simpl.
  exact Hfit.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_9 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  assert (Hshift0: shift_orig = 0) by lia.
  assert (Hfit:
    list_to_Z UINT_MOD l_np * 2 ^ shift_orig <
      list_to_Z UINT_MOD l_dp * UINT_MOD ^ (nn0 - dn0 + 1)).
  {
    eapply mpn_div_qr_preinv_quotient_fit; try eassumption; try lia.
    rewrite <- PreH23.
    exact PreH25.
  }
  rewrite Hshift0 in Hfit.
  simpl in Hfit.
  replace (list_to_Z UINT_MOD l_np * 1)
    with (list_to_Z UINT_MOD l_np) in Hfit by ring.
  simpl.
  exact Hfit.
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_10 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_11 :
  mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure :
  mpn_div_qr_preinv_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_1.
  Goal_apply proof_of_mpn_div_qr_preinv_partial_solve_wit_6_pure_split_goal_2.
Qed.
