From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_tdiv_q_2exp_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_tdiv_q_2exp_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_1 : mpz_div_q_2exp_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_2 : mpz_div_q_2exp_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_safety_wit_5 : mpz_div_q_2exp_safety_wit_5.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_1.
  + Goal_apply proof_of_mpz_div_q_2exp_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_1 : mpz_div_q_2exp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre.
  unfold store_Z.
  Intros ptr size cap.
  prop_apply (store_int_range (&(u_pre # "__mpz_struct" ->ₛ"_mp_alloc")) cap).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  Exists ptr cap size.
  split_pure_spatial.
  - normalize.
    Intros.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_2_1 : mpz_div_q_2exp_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed in *.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  destruct H as [Hdata_val [Hdata_last Hdata_bound]].
  Exists retval_2.
  Exists z__mp_alloc.
  Exists size.
  Exists data.
  Exists cap_2.
  subst u_pre z__mp_alloc.
  pose proof (Z.rem_bound_pos bit_index_pre 32 ltac:(lia) ltac:(lia)) as [Hrem_low Hrem_high].
  replace (retval - bit_index_pre ÷ 32 + bit_index_pre ÷ 32)
    with (Zlength data) by lia.
  rewrite H0.
  assert (Hretval_len : retval = Zlength data) by lia.
  assert (Hcap_len : Zlength data <= cap_2) by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_2_2 : mpz_div_q_2exp_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  rewrite Hlimb_signed in *.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  destruct H as [Hdata_val [Hdata_last Hdata_bound]].
  Exists retval_2.
  Exists z__mp_alloc.
  Exists size.
  Exists data.
  Exists cap_2.
  subst u_pre z__mp_alloc.
  pose proof (Z.rem_bound_pos bit_index_pre 32 ltac:(lia) ltac:(lia)) as [Hrem_low Hrem_high].
  replace (retval - bit_index_pre ÷ 32 + bit_index_pre ÷ 32)
    with (Zlength data) by lia.
  rewrite H0.
  assert (Hretval_len : retval = Zlength data) by lia.
  assert (Hcap_len : Zlength data <= cap_2) by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_1 : mpz_div_q_2exp_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre.
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  assert (Hsize_le_limb : Zabs size <= bit_index_pre ÷ 32).
  { rewrite Hlimb_signed in PreH2; lia. }
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs z_eq_trunc) (Zabs size)).
  Intros.
  assert (Hquot_zero :
    Z.quot (Zabs z_eq_trunc) (2 ^ bit_index_pre) = 0).
  {
    apply (mpz_tdiv_q_2exp_zero_by_limb_bound
      (Zabs z_eq_trunc) size bit_index_pre);
    [lia | exact Hsize_le_limb | assumption].
  }
  rewrite Hquot_zero.
  sep_apply_l_atomic (store_Z_zero_from_fields u_pre ptr size cap z_eq_trunc).
  - dump_pre_spatial; lia.
  - dump_pre_spatial; assumption.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") (bit_index_pre % 32)).
    sep_apply (store_int_undef_store_int &( "qn") 0).
    sep_apply (store_int_undef_store_int &( "limb_cnt") (signed_last_nbits (bit_index_pre ÷ 32) 32)).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_2 : mpz_div_q_2exp_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) qn).
  {
    replace (Zlength l_out) with qn by lia.
    apply (mpz_tdiv_q_2exp_rshift_nonzero
      l l_out (Zabs z_eq_trunc) bit_index_pre limb_cnt
      bit_index qn retval);
    try assumption; try lia.
    - replace (qn - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  split_pure_spatial.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") bit_index).
    sep_apply (store_int_undef_store_int &( "qn") qn).
    sep_apply (store_int_undef_store_int &( "limb_cnt") limb_cnt).
    sep_apply (store_ptr_undef_store_ptr &( "qp") qp).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_3 : mpz_div_q_2exp_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) (qn - 1)).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_rshift_high_zero
      l l_out (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      bit_index (Zabs un - bit_index_pre ÷ 32) retval);
    try assumption; try lia.
    - replace (Zabs un - bit_index_pre ÷ 32 - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
    - rewrite <- PreH21.
      exact PreH5.
    - rewrite <- PreH21.
      replace (Zabs un - limb_cnt) with qn by lia.
      exact PreH6.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hhigh0 : Znth (qn - 1) l_out 0 = 0).
  {
    replace (qn - 1) with (qn - 1 - 0) by lia.
    exact PreH2.
  }
  unfold store_Z.
  Exists qp (qn - 1) (Z.max qn cap).
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs (qn - 1)) with (qn - 1) by lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    qn
    (qn + limb_cnt)); try lia.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  split_pure_spatial.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") bit_index).
    sep_apply (store_int_undef_store_int &( "qn") (qn - 1)).
    sep_apply (store_int_undef_store_int &( "limb_cnt") limb_cnt).
    sep_apply (store_ptr_undef_store_ptr &( "qp") qp).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_entail_wit_3_4 : mpz_div_q_2exp_entail_wit_3_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre u__mp_alloc u__mp_d bit_index adjust mode_pre.
  assert (Hn_pos : 0 < qn) by lia.
  assert (Hbit_quot_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hshift :
    list_to_Z UINT_MOD
      (sublist limb_cnt (limb_cnt + qn) l) =
      Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD
      (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre)
      qn).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_suffix_shift0
      l (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      (Zabs un - bit_index_pre ÷ 32));
    try assumption; try lia.
  }
  destruct Hshift as [Hsuffix_val Hsuffix_compact].
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0
    qn
    (sublist limb_cnt (limb_cnt + qn) l)).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn
    (sublist limb_cnt (limb_cnt + qn) l)
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption;
    try (rewrite Zlength_sublist by lia; lia);
    try (apply list_within_bound_sublist; [lia | lia | assumption]).
  split_pure_spatial.
  - sep_apply (store_uint64_undef_store_uint64 &( "bit_index") 0).
    sep_apply (store_int_undef_store_int &( "qn") qn).
    sep_apply (store_int_undef_store_int &( "limb_cnt") limb_cnt).
    sep_apply (store_ptr_undef_store_ptr &( "qp") qp).
    sep_apply (store_int_undef_store_int &( "adjust") 0).
    cancel (mpd_store_Z_compact UINT_MOD qp
      (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) qn).
    cancel (UIntArray.undef_seg qp qn (Z.max qn cap)).
    cancel ((&((u_pre) # "__mpz_struct" ->ₛ "_mp_size")) # Int |-> qn).
    cancel ((&((u_pre) # "__mpz_struct" ->ₛ "_mp_alloc")) # Int
      |-> Z.max qn cap).
    cancel ((&((u_pre) # "__mpz_struct" ->ₛ "_mp_d")) # Ptr |-> qp).
    cancel ((( &( "bit_index" ) )) # UInt64 |->_).
    cancel ((( &( "qn" ) )) # Int |->_).
    cancel ((( &( "limb_cnt" ) )) # Int |->_).
    cancel ((( &( "qp" ) )) # Ptr |->_).
    cancel ((( &( "adjust" ) )) # Int |->_).
  - split_pures; dump_pre_spatial;
      try assumption;
      try (apply list_within_bound_sublist; [lia | lia | assumption]);
      try (unfold same_sign; lia);
      try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_1 : mpz_div_q_2exp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre size.
  prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs z_eq_trunc)).
  Intros.
  assert (Hzero : z_eq_trunc = 0) by lia.
  subst z_eq_trunc.
  change (0 ÷ 2 ^ bit_index_pre) with 0.
  unfold store_Z.
  Exists ptr 0 cap.
  replace (Zabs 0) with 0 by lia.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_2_split_goal_spatial : mpz_div_q_2exp_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hz_neg : z_eq_trunc < 0).
  { unfold same_sign in PreH4; lia. }
  assert (Hden_pos : 0 < 2 ^ bit_index_pre).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hz_abs : z_eq_trunc = - Zabs z_eq_trunc).
  {
    rewrite Z.abs_neq by lia.
    lia.
  }
  rewrite Hz_abs.
  replace (Zabs (- Zabs z_eq_trunc)) with (Zabs z_eq_trunc) by
    (rewrite Z.abs_neq; lia).
  rewrite Z.quot_opp_l by lia.
  cancel.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_2 : mpz_div_q_2exp_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_3 : mpz_div_q_2exp_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre.
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hlimb_signed :
    signed_last_nbits (bit_index_pre ÷ 32) 32 = bit_index_pre ÷ 32).
  {
    apply signed_last_nbits_eq.
    - lia.
    - change (2 ^ (32 - 1)) with 2147483648.
      lia.
  }
  assert (Hsize_le_limb : Zabs size <= bit_index_pre ÷ 32).
  { rewrite Hlimb_signed in PreH2; lia. }
  prop_apply (mpd_store_Z_compact_bound ptr (Zabs z_eq_trunc) (Zabs size)).
  Intros.
  assert (Hquot_zero :
    Z.quot (Zabs z_eq_trunc) (2 ^ bit_index_pre) = 0).
  {
    apply (mpz_tdiv_q_2exp_zero_by_limb_bound
      (Zabs z_eq_trunc) size bit_index_pre);
    [lia | exact Hsize_le_limb | assumption].
  }
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH14; lia. }
  replace (Z.quot z_eq_trunc (2 ^ bit_index_pre)) with 0.
  2: {
    rewrite <- (Z.abs_eq z_eq_trunc) by lia.
    symmetry; exact Hquot_zero.
  }
  sep_apply_l_atomic (store_Z_zero_from_fields u_pre ptr size cap z_eq_trunc).
  - dump_pre_spatial; lia.
  - dump_pre_spatial; assumption.
  - split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_4 : mpz_div_q_2exp_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) qn).
  {
    replace (Zlength l_out) with qn by lia.
    apply (mpz_tdiv_q_2exp_rshift_nonzero
      l l_out (Zabs z_eq_trunc) bit_index_pre limb_cnt
      bit_index qn retval);
    try assumption; try lia.
    - replace (qn - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH19; lia. }
  assert (Hquot_eq :
    Z.quot z_eq_trunc (2 ^ bit_index_pre) =
    Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    rewrite (Z.abs_eq z_eq_trunc) by lia.
    reflexivity.
  }
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  rewrite Hquot_eq.
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_5 : mpz_div_q_2exp_return_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hbit_pos : 1 <= bit_index < 32) by lia.
  assert (Hshift :
    list_to_Z UINT_MOD l_out = Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) (qn - 1)).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_rshift_high_zero
      l l_out (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      bit_index (Zabs un - bit_index_pre ÷ 32) retval);
    try assumption; try lia.
    - replace (Zabs un - bit_index_pre ÷ 32 - 1)
        with (qn - 1 - 0) by lia.
      exact PreH2.
    - rewrite <- PreH21.
      exact PreH5.
    - rewrite <- PreH21.
      replace (Zabs un - limb_cnt) with qn by lia.
      exact PreH6.
  }
  destruct Hshift as [Hout_val Hout_compact].
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH19; lia. }
  assert (Hquot_eq :
    Z.quot z_eq_trunc (2 ^ bit_index_pre) =
    Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    rewrite (Z.abs_eq z_eq_trunc) by lia.
    reflexivity.
  }
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hhigh0 : Znth (qn - 1) l_out 0 = 0).
  {
    replace (qn - 1) with (qn - 1 - 0) by lia.
    exact PreH2.
  }
  unfold store_Z.
  Exists qp (qn - 1) (Z.max qn cap).
  rewrite Hquot_eq.
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs (qn - 1)) with (qn - 1) by lia.
  sep_apply (UIntArray.seg_to_full qp 0 qn l_out).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_high_zero_to_mpd_store_Z_compact_exact qp
    qn l_out
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption; try lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    qn
    (qn + limb_cnt)); try lia.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    (qn - 1)
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_return_wit_6 : mpz_div_q_2exp_return_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst q_pre mode_pre bit_index adjust u__mp_size u__mp_alloc u__mp_d.
  assert (Hn_pos : 0 < qn) by lia.
  assert (Hbit_quot_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  assert (Hshift :
    list_to_Z UINT_MOD
      (sublist limb_cnt (limb_cnt + qn) l) =
      Zabs z_eq_trunc ÷ 2 ^ bit_index_pre /\
    is_compact_Z UINT_MOD
      (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre)
      qn).
  {
    replace limb_cnt with (bit_index_pre ÷ 32) by lia.
    replace qn with (Zabs un - bit_index_pre ÷ 32) by lia.
    apply (mpz_tdiv_q_2exp_suffix_shift0
      l (Zabs z_eq_trunc) bit_index_pre (bit_index_pre ÷ 32)
      (Zabs un - bit_index_pre ÷ 32));
    try assumption; try lia.
  }
  destruct Hshift as [Hsuffix_val Hsuffix_compact].
  assert (Hz_nonneg : 0 <= z_eq_trunc).
  { unfold same_sign in PreH14; lia. }
  assert (Hquot_eq :
    Z.quot z_eq_trunc (2 ^ bit_index_pre) =
    Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    rewrite (Z.abs_eq z_eq_trunc) by lia.
    reflexivity.
  }
  assert (Hquot_nonneg : 0 <= Zabs z_eq_trunc ÷ 2 ^ bit_index_pre).
  {
    apply Z.quot_pos.
    - apply Z.abs_nonneg.
    - apply Z.pow_pos_nonneg; lia.
  }
  unfold store_Z.
  Exists qp qn (Z.max qn cap).
  rewrite Hquot_eq.
  replace (Zabs (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre))
    with (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre) by lia.
  replace (Zabs qn) with qn by lia.
  sep_apply (UIntArray.seg_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (sublist qn (qn + limb_cnt) l)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg qp
    qn
    (qn + limb_cnt)
    (Z.max qn cap)); try lia.
  sep_apply (UIntArray.seg_to_full qp 0
    qn
    (sublist limb_cnt (limb_cnt + qn) l)).
  replace (qp + 0 * sizeof(UINT)) with qp by lia.
  replace (qn - 0) with qn by lia.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact qp
    qn
    (sublist limb_cnt (limb_cnt + qn) l)
    (Zabs z_eq_trunc ÷ 2 ^ bit_index_pre));
    try assumption;
    try (rewrite Zlength_sublist by lia; lia);
    try (apply list_within_bound_sublist; [lia | lia | assumption]).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try lia;
      try (unfold same_sign; left; lia).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_2_pure_split_goal_1 : mpz_div_q_2exp_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_2_pure : mpz_div_q_2exp_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1 : mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2 : mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3 : mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4 : mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure : mpz_div_q_2exp_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_2.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_3.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_4.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1 : mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2 : mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlimb_nonneg : 0 <= bit_index_pre ÷ 32).
  { apply Z.quot_pos; lia. }
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure : mpz_div_q_2exp_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1.
  Goal_apply proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_2.
Qed.

