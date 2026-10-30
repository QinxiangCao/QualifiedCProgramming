From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_sub_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_sub_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_sub_entail_wit_4_rp_eq_bp : mpn_sub_entail_wit_4_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists val_r.
  sep_apply_l_atomic (UIntArray.undef_seg_to_undef_full rp_pre bn_pre an_pre).
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_entail_wit_12_1_rp_eq_bp : mpn_sub_entail_wit_12_1_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (mpd_join__recombine : forall p lo hi n m,
    0 <= n <= m ->
    mpd_store_Z UINT_MOD p lo n **
    mpd_store_Z UINT_MOD (p + n * sizeof(UINT)) hi (m-n) |--
    mpd_store_Z UINT_MOD p (lo + hi * UINT_MOD ^ n) m).
  {
  intros p lo hi n m Hnm.
  unfold mpd_store_Z, mpd_store_list.
  Intros low high.
  Exists (List.app low high).
  rewrite <- H0, <- H2.
  sep_apply_l_atomic (UIntArray.full_merge_to_full p n m low high).
  { dump_pre_spatial. lia. }
  rewrite Zlength_app.
  rewrite <- H0, <- H2.
  replace (n + (m-n)) with m by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + split.
      * rewrite list_to_Z_app by exact UINT_MOD_pos.
        rewrite <- H0.
        destruct H as [Hl Hb]; destruct H1 as [Hh Hhb].
        rewrite Hl, Hh. reflexivity.
      * apply list_within_bound_concat; tauto.
    + lia.
  }
  Exists (val_r_low + val' * UINT_MOD ^ bn_pre).
  sep_apply_l_atomic (mpd_join__recombine ap_pre val_a_low val_a_high bn_pre an_pre ltac:(lia)).
  sep_apply_l_atomic (mpd_join__recombine rp_pre val_r_low val' bn_pre an_pre ltac:(lia)).
  rewrite <- PreH16.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia.
    assert (Hpow : UINT_MOD ^ an_pre = UINT_MOD ^ bn_pre * UINT_MOD ^ (an_pre - bn_pre)).
    { rewrite <- Z.pow_add_r by lia. f_equal; lia. }
    rewrite Hpow.
    nia.
Qed.

Lemma proof_of_mpn_sub_entail_wit_12_2_rp_eq_bp : mpn_sub_entail_wit_12_2_rp_eq_bp.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Heq : an_pre = bn_pre) by lia.
  subst an_pre.
  replace (bn_pre - bn_pre) with 0 by lia.
  sep_apply (mpd_store_Z_zero_to_emp (ap_pre + bn_pre * sizeof(UINT)) val_a_high).
  Intros.
  assert (Hval : val_a_rp_eq_bp = val_a_low) by nia.
  rewrite Hval.
  rewrite UIntArray.undef_full_empty.
  Exists val_r_low.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_sub_entail_wit_13_1_rp_eq_ap : mpn_sub_entail_wit_13_1_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (mpd_join__recombine : forall p lo hi n m,
    0 <= n <= m ->
    mpd_store_Z UINT_MOD p lo n **
    mpd_store_Z UINT_MOD (p + n * sizeof(UINT)) hi (m-n) |--
    mpd_store_Z UINT_MOD p (lo + hi * UINT_MOD ^ n) m).
  {
  intros p lo hi n m Hnm.
  unfold mpd_store_Z, mpd_store_list.
  Intros low high.
  Exists (List.app low high).
  rewrite <- H0, <- H2.
  sep_apply_l_atomic (UIntArray.full_merge_to_full p n m low high).
  { dump_pre_spatial. lia. }
  rewrite Zlength_app.
  rewrite <- H0, <- H2.
  replace (n + (m-n)) with m by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + split.
      * rewrite list_to_Z_app by exact UINT_MOD_pos.
        rewrite <- H0.
        destruct H as [Hl Hb]; destruct H1 as [Hh Hhb].
        rewrite Hl, Hh. reflexivity.
      * apply list_within_bound_concat; tauto.
    + lia.
  }
  Exists (val_r_low + val' * UINT_MOD ^ bn_pre).
  sep_apply_l_atomic (mpd_join__recombine rp_pre val_r_low val' bn_pre an_pre ltac:(lia)).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia.
    assert (Hpow : UINT_MOD ^ an_pre = UINT_MOD ^ bn_pre * UINT_MOD ^ (an_pre - bn_pre)).
    { rewrite <- Z.pow_add_r by lia. f_equal; lia. }
    rewrite Hpow.
    nia.
Qed.

Lemma proof_of_mpn_sub_entail_wit_13_2_rp_eq_ap : mpn_sub_entail_wit_13_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Heq : an_pre = bn_pre) by lia.
  subst an_pre.
  replace (bn_pre - bn_pre) with 0 by lia.
  sep_apply (mpd_store_Z_zero_to_emp (ap_pre + bn_pre * sizeof(UINT)) val_a_high).
  Intros.
  assert (Hval : val_a_rp_eq_ap = val_a_low) by nia.
  rewrite Hval.
  Exists val_r_low.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_sub_return_wit_1_non_alias : mpn_sub_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (mpd_join__recombine : forall p lo hi n m,
    0 <= n <= m ->
    mpd_store_Z UINT_MOD p lo n **
    mpd_store_Z UINT_MOD (p + n * sizeof(UINT)) hi (m-n) |--
    mpd_store_Z UINT_MOD p (lo + hi * UINT_MOD ^ n) m).
  {
  intros p lo hi n m Hnm.
  unfold mpd_store_Z, mpd_store_list.
  Intros low high.
  Exists (List.app low high).
  rewrite <- H0, <- H2.
  sep_apply_l_atomic (UIntArray.full_merge_to_full p n m low high).
  { dump_pre_spatial. lia. }
  rewrite Zlength_app.
  rewrite <- H0, <- H2.
  replace (n + (m-n)) with m by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + split.
      * rewrite list_to_Z_app by exact UINT_MOD_pos.
        rewrite <- H0.
        destruct H as [Hl Hb]; destruct H1 as [Hh Hhb].
        rewrite Hl, Hh. reflexivity.
      * apply list_within_bound_concat; tauto.
    + lia.
  }
  Exists (val_r_low + val' * UINT_MOD ^ bn_pre).
  sep_apply_l_atomic (mpd_join__recombine ap_pre val_a_low val_a_high bn_pre an_pre ltac:(lia)).
  sep_apply_l_atomic (mpd_join__recombine rp_pre val_r_low val' bn_pre an_pre ltac:(lia)).
  rewrite <- PreH15.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia.
    assert (Hpow : UINT_MOD ^ an_pre = UINT_MOD ^ bn_pre * UINT_MOD ^ (an_pre - bn_pre)).
    { rewrite <- Z.pow_add_r by lia. f_equal; lia. }
    rewrite Hpow.
    nia.
Qed.

Lemma proof_of_mpn_sub_return_wit_2_rp_eq_ap : mpn_sub_return_wit_2_rp_eq_ap.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists val_r_out_2.
  replace ap_pre with rp_pre by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_mpn_sub_return_wit_4_non_alias : mpn_sub_return_wit_4_non_alias.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Heq : an_pre = bn_pre) by lia.
  subst an_pre.
  replace (bn_pre - bn_pre) with 0 by lia.
  sep_apply (mpd_store_Z_zero_to_emp (ap_pre + bn_pre * sizeof(UINT)) val_a_high).
  Intros.
  assert (Hval : val_a_non_alias = val_a_low) by nia.
  rewrite Hval.
  rewrite UIntArray.undef_full_empty.
  Exists val_r_low.
  split_pure_spatial.
  - repeat progress cancel.

  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpn_sub_partial_solve_wit_8_non_alias_pure_split_goal_1 : mpn_sub_partial_solve_wit_8_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (mpd_store_Z_to_undef_full (ap_pre + bn_pre * sizeof(UINT))
    val_a_high (an_pre - bn_pre)).
  sep_apply (UIntArray.undef_full_split_to_undef_missing_i
    (ap_pre + bn_pre * sizeof(UINT)) 0 (an_pre - bn_pre) ltac:(lia)).
  sep_apply (UIntArray.undef_full_split_to_undef_missing_i
    (rp_pre + bn_pre * sizeof(UINT)) 0 (an_pre - bn_pre) ltac:(lia)).
  unfold StoreUIntAsElement.undefstoreA.
  rewrite !Z.mul_0_l, !Z.add_0_r.
  destruct (Z.eq_dec (rp_pre + bn_pre * sizeof(UINT))
    (ap_pre + bn_pre * sizeof(UINT))) as [Heq | Hneq].
  - rewrite Heq.
    assert (Hdup : forall p, (p # UInt |->_) ** (p # UInt |->_) |-- “ False ”).
    { intro p. apply dup_undef_store_int. }
    sep_apply (Hdup (ap_pre + bn_pre * sizeof(UINT))).
    Intros_p Hfalse. contradiction.
  - dump_pre_spatial. exact Hneq.
Qed.

Lemma proof_of_mpn_sub_partial_solve_wit_8_non_alias_pure : mpn_sub_partial_solve_wit_8_non_alias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_partial_solve_wit_8_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_mpn_sub_partial_solve_wit_10_rp_eq_bp_pure_split_goal_1 : mpn_sub_partial_solve_wit_10_rp_eq_bp_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (mpd_store_Z_to_undef_full (ap_pre + bn_pre * sizeof(UINT))
    val_a_high (an_pre - bn_pre)).
  sep_apply (UIntArray.undef_full_split_to_undef_missing_i
    (ap_pre + bn_pre * sizeof(UINT)) 0 (an_pre - bn_pre) ltac:(lia)).
  sep_apply (UIntArray.undef_full_split_to_undef_missing_i
    (rp_pre + bn_pre * sizeof(UINT)) 0 (an_pre - bn_pre) ltac:(lia)).
  unfold StoreUIntAsElement.undefstoreA.
  rewrite !Z.mul_0_l, !Z.add_0_r.
  destruct (Z.eq_dec (rp_pre + bn_pre * sizeof(UINT))
    (ap_pre + bn_pre * sizeof(UINT))) as [Heq | Hneq].
  - rewrite Heq.
    assert (Hdup : forall p, (p # UInt |->_) ** (p # UInt |->_) |-- “ False ”).
    { intro p. apply dup_undef_store_int. }
    sep_apply (Hdup (ap_pre + bn_pre * sizeof(UINT))).
    Intros_p Hfalse. contradiction.
  - dump_pre_spatial. exact Hneq.
Qed.

Lemma proof_of_mpn_sub_partial_solve_wit_10_rp_eq_bp_pure : mpn_sub_partial_solve_wit_10_rp_eq_bp_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_partial_solve_wit_10_rp_eq_bp_pure_split_goal_1.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_1 : mpn_sub_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Require Import SimpleC.EE.Applications_human.gmp.minigmp.mpn_sub_lib.
  apply mpn_sub_lib.mpd_partition__partition. lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_2 : mpn_sub_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Require Import SimpleC.EE.Applications_human.gmp.minigmp.mpn_sub_lib.
  apply mpn_sub_lib.mpd_partition__partition. lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_3 : mpn_sub_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Require Import SimpleC.EE.Applications_human.gmp.minigmp.mpn_sub_lib.
  apply mpn_sub_lib.mpd_partition__partition. lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_4_split_goal_spatial : mpn_sub_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply UIntArray.undef_full_split_to_undef_full; lia.
Qed.

Lemma proof_of_mpn_sub_which_implies_wit_4 : mpn_sub_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_sub_which_implies_wit_4_split_goal_spatial.
Qed.

