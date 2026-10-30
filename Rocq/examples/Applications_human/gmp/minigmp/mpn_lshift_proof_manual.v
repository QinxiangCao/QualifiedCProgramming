From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_lshift_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_lshift_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_1 : mpn_lshift_entail_wit_3_nonalias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite list_to_Z_nil.
  replace (n_pre - (n_pre-1)) with 1 by lia.
  rewrite Z.pow_1_r, Z.mul_0_l, Z.add_0_r.
  pose proof (sublist_single 0 (n_pre-1) l_up_nonalias ltac:(lia)) as E.
  replace (n_pre-1+1) with n_pre in E by lia.
  rewrite E, list_to_Z_single.
  unfold unsigned_last_nbits.
  assert (Hp : 2^(32-cnt_pre) * 2^cnt_pre = UINT_MOD).
  { rewrite <- Z.pow_add_r by lia. replace (32-cnt_pre+cnt_pre) with 32 by lia. reflexivity. }
  assert (Hpow : 0 < 2^cnt_pre) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (Znth (n_pre-1) l_up_nonalias 0 * 2^cnt_pre) / UINT_MOD = Znth (n_pre-1) l_up_nonalias 0 / 2^(32-cnt_pre)).
  { rewrite <- Hp. apply Z.div_mul_cancel_r; [apply Z.pow_nonzero; lia | lia]. }
  pose proof (Z.div_mod (Znth (n_pre-1) l_up_nonalias 0 * 2^cnt_pre) UINT_MOD ltac:(unfold UINT_MOD; lia)) as Hdm.
  change (2^32) with UINT_MOD.
  rewrite Hdiv in Hdm. nia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_2 : mpn_lshift_entail_wit_3_nonalias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_3 : mpn_lshift_entail_wit_3_nonalias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.quot_div_nonneg; try reflexivity.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_4 : mpn_lshift_entail_wit_3_nonalias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_5 : mpn_lshift_entail_wit_3_nonalias_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_6 : mpn_lshift_entail_wit_3_nonalias_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_7 : mpn_lshift_entail_wit_3_nonalias_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_spatial : mpn_lshift_entail_wit_3_nonalias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: replace (n_pre - 1 + 1) with n_pre by lia.
  all: cancel.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_3_nonalias : mpn_lshift_entail_wit_3_nonalias.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_spatial l_up_nonalias rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_1 l_up_nonalias rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_2 l_up_nonalias rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_3 l_up_nonalias rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_5 l_up_nonalias rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_6 l_up_nonalias rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_3_nonalias_split_goal_7 l_up_nonalias rp_pre up_pre n_pre cnt_pre).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_1 : mpn_lshift_entail_wit_4_inplace_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite list_to_Z_nil.
  replace (n_pre - (n_pre-1)) with 1 by lia.
  rewrite Z.pow_1_r, Z.mul_0_l, Z.add_0_r.
  pose proof (sublist_single 0 (n_pre-1) l_up_inplace ltac:(lia)) as E.
  replace (n_pre-1+1) with n_pre in E by lia.
  rewrite E, list_to_Z_single.
  unfold unsigned_last_nbits.
  assert (Hp : 2^(32-cnt_pre) * 2^cnt_pre = UINT_MOD).
  { rewrite <- Z.pow_add_r by lia. replace (32-cnt_pre+cnt_pre) with 32 by lia. reflexivity. }
  assert (Hpow : 0 < 2^cnt_pre) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (Znth (n_pre-1) l_up_inplace 0 * 2^cnt_pre) / UINT_MOD = Znth (n_pre-1) l_up_inplace 0 / 2^(32-cnt_pre)).
  { rewrite <- Hp. apply Z.div_mul_cancel_r; [apply Z.pow_nonzero; lia | lia]. }
  pose proof (Z.div_mod (Znth (n_pre-1) l_up_inplace 0 * 2^cnt_pre) UINT_MOD ltac:(unfold UINT_MOD; lia)) as Hdm.
  change (2^32) with UINT_MOD.
  rewrite Hdiv in Hdm. nia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_2 : mpn_lshift_entail_wit_4_inplace_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_3 : mpn_lshift_entail_wit_4_inplace_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.quot_div_nonneg; try reflexivity.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_4 : mpn_lshift_entail_wit_4_inplace_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_5 : mpn_lshift_entail_wit_4_inplace_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_6 : mpn_lshift_entail_wit_4_inplace_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_7 : mpn_lshift_entail_wit_4_inplace_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_8 : mpn_lshift_entail_wit_4_inplace_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  replace (n_pre-1+1) with n_pre by lia. rewrite app_nil_r. reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_9 : mpn_lshift_entail_wit_4_inplace_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_spatial : mpn_lshift_entail_wit_4_inplace_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: rewrite UIntArray.seg_empty.
  all: Intros_p Heq.
  all: split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto].
Qed.

Lemma proof_of_mpn_lshift_entail_wit_4_inplace : mpn_lshift_entail_wit_4_inplace.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_spatial l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_1 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_2 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_3 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_5 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_6 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_7 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_8 l_up_inplace rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_4_inplace_split_goal_9 l_up_inplace rp_pre up_pre n_pre cnt_pre).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_1 : mpn_lshift_entail_wit_5_off_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite list_to_Z_nil.
  replace (n_pre - (n_pre-1)) with 1 by lia.
  rewrite Z.pow_1_r, Z.mul_0_l, Z.add_0_r.
  pose proof (sublist_single 0 (n_pre-1) l_up_shifted ltac:(lia)) as E.
  replace (n_pre-1+1) with n_pre in E by lia.
  rewrite E, list_to_Z_single.
  unfold unsigned_last_nbits.
  assert (Hp : 2^(32-cnt_pre) * 2^cnt_pre = UINT_MOD).
  { rewrite <- Z.pow_add_r by lia. replace (32-cnt_pre+cnt_pre) with 32 by lia. reflexivity. }
  assert (Hpow : 0 < 2^cnt_pre) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (Znth (n_pre-1) l_up_shifted 0 * 2^cnt_pre) / UINT_MOD = Znth (n_pre-1) l_up_shifted 0 / 2^(32-cnt_pre)).
  { rewrite <- Hp. apply Z.div_mul_cancel_r; [apply Z.pow_nonzero; lia | lia]. }
  pose proof (Z.div_mod (Znth (n_pre-1) l_up_shifted 0 * 2^cnt_pre) UINT_MOD ltac:(unfold UINT_MOD; lia)) as Hdm.
  change (2^32) with UINT_MOD.
  rewrite Hdiv in Hdm. nia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_2 : mpn_lshift_entail_wit_5_off_zero_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_3 : mpn_lshift_entail_wit_5_off_zero_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.quot_div_nonneg; try reflexivity.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_4 : mpn_lshift_entail_wit_5_off_zero_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_5 : mpn_lshift_entail_wit_5_off_zero_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_6 : mpn_lshift_entail_wit_5_off_zero_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_7 : mpn_lshift_entail_wit_5_off_zero_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_spatial : mpn_lshift_entail_wit_5_off_zero_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: replace (n_pre - 1 + 1) with n_pre by lia.
  all: rewrite UIntArray.seg_empty.
  all: split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto].
Qed.

Lemma proof_of_mpn_lshift_entail_wit_5_off_zero : mpn_lshift_entail_wit_5_off_zero.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_spatial off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_1 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_2 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_3 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_4 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_6 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_5_off_zero_split_goal_7 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_1 : mpn_lshift_entail_wit_6_off_pos_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite list_to_Z_nil.
  replace (n_pre - (n_pre-1)) with 1 by lia.
  rewrite Z.pow_1_r, Z.mul_0_l, Z.add_0_r.
  pose proof (sublist_single 0 (n_pre-1) l_up_shifted ltac:(lia)) as E.
  replace (n_pre-1+1) with n_pre in E by lia.
  rewrite E, list_to_Z_single.
  unfold unsigned_last_nbits.
  assert (Hp : 2^(32-cnt_pre) * 2^cnt_pre = UINT_MOD).
  { rewrite <- Z.pow_add_r by lia. replace (32-cnt_pre+cnt_pre) with 32 by lia. reflexivity. }
  assert (Hpow : 0 < 2^cnt_pre) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (Znth (n_pre-1) l_up_shifted 0 * 2^cnt_pre) / UINT_MOD = Znth (n_pre-1) l_up_shifted 0 / 2^(32-cnt_pre)).
  { rewrite <- Hp. apply Z.div_mul_cancel_r; [apply Z.pow_nonzero; lia | lia]. }
  pose proof (Z.div_mod (Znth (n_pre-1) l_up_shifted 0 * 2^cnt_pre) UINT_MOD ltac:(unfold UINT_MOD; lia)) as Hdm.
  change (2^32) with UINT_MOD.
  rewrite Hdiv in Hdm. nia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_2 : mpn_lshift_entail_wit_6_off_pos_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_3 : mpn_lshift_entail_wit_6_off_pos_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.quot_div_nonneg; try reflexivity.
  - pose proof (list_within_bound_Znth_bound UINT_MOD l_up_shifted (n_pre-1) ltac:(lia) ltac:(assumption)); unfold UINT_MOD in *; lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_4 : mpn_lshift_entail_wit_6_off_pos_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try dump_pre_spatial.
  rewrite (sublist_self l_up_shifted n_pre) by lia. rewrite Z.sub_0_r.
  reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_5 : mpn_lshift_entail_wit_6_off_pos_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_6 : mpn_lshift_entail_wit_6_off_pos_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_spatial : mpn_lshift_entail_wit_6_off_pos_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: replace (n_pre - 1 + 1) with n_pre by lia.
  all: rewrite UIntArray.seg_empty.
  all: split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto].
Qed.

Lemma proof_of_mpn_lshift_entail_wit_6_off_pos : mpn_lshift_entail_wit_6_off_pos.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_spatial off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_1 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_2 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_3 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_4 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
  - Goal_apply (proof_of_mpn_lshift_entail_wit_6_off_pos_split_goal_6 off_shifted l_up_shifted rp_pre up_pre n_pre cnt_pre).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_11_nonalias_inv : mpn_lshift_entail_wit_11_nonalias_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists l_done_3.
  replace (i - 1 + 1) with i by lia.
  replace (i - 1 + 2) with (i + 1) by lia.
  assert (Hloaded : 0 <= Znth (i - 1) l_up_nonalias 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (i - 1));
      [lia | assumption]. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
      unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_12_inplace_inv : mpn_lshift_entail_wit_12_inplace_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists l_done_3.
  replace (i - 1 + 1) with i by lia.
  replace (i - 1 + 2) with (i + 1) by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  rewrite Znth_sublist0 by lia.
  assert (Hloaded : 0 <= Znth (i - 1) l_up_inplace 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up_inplace (i - 1));
      [lia | assumption]. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
      unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_13_off_zero_inv : mpn_lshift_entail_wit_13_off_zero_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists l_done_3.
  replace (i - 1 + 1) with i by lia.
  replace (i - 1 + 2) with (i + 1) by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  rewrite Znth_sublist0 by lia.
  assert (Hloaded : 0 <= Znth (i - 1) l_up_shifted 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted (i - 1));
      [lia | assumption]. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
      unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_14_off_pos_inv : mpn_lshift_entail_wit_14_off_pos_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists l_done_3.
  replace (i - 1 + 1) with i by lia.
  replace (i - 1 + 2) with (i + 1) by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  rewrite Znth_sublist0 by lia.
  replace (off_shifted + (i - 1) + 2) with (off_shifted + i + 1) by lia.
  assert (Hloaded : 0 <= Znth (i - 1) l_up_shifted 0 < UINT_MOD).
  { apply (list_within_bound_Znth_bound UINT_MOD l_up_shifted (i - 1));
      [lia | assumption]. }
  split_pure_spatial.
  - cancel (UIntArray.undef_seg up_pre (i + 1) (off_shifted + i + 1)). cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
      unfold UINT_MOD in *; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_15_nonalias_inv : mpn_lshift_entail_wit_15_nonalias_inv.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: l_done_3)
    (unsigned_last_nbits (Znth (n_pre - 1) l_up_nonalias 0 * 2 ^ cnt_pre) 32)
    (Znth (n_pre - 1) l_up_nonalias 0 ÷ 2 ^ tnc_2)
    (@nil Z) (n_pre - 1) (Znth (n_pre - 1) l_up_nonalias 0) tnc_2.
  split_pure_spatial.
  - sep_apply (UIntArray.seg_single rp_pre (i_2 + 1) (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))).
    replace (i_2 + 1 + 1) with (i_2 + 2) by lia.
    sep_apply (UIntArray.seg_merge_to_seg rp_pre (i_2 + 1) (i_2 + 2) n_pre
      ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: nil) l_done_3).
    simpl.
    cancel.
    lia.
  - Intros.
    repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + rewrite Zlength_cons.
      rewrite PreH10.
      unfold Z.succ.
      ring.
    + simpl.
      split.
      * rewrite PreH1.
        apply (mpn_lshift_join_limb_bound high_limb_2 low_limb_2
                 (Znth (i_2 + 1) l_up_nonalias 0) cnt_pre);
          try lia; try assumption.
      * exact PreH12.
    + rewrite PreH6.
      rewrite Z.shiftl_mul_pow2 by nia.
      reflexivity.
    + apply (mpn_lshift_step_equation_cons l_up_nonalias l_done_3 n_pre i_2 cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH9. nia.
      * split; assumption.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1) ltac:(rewrite PreH9; nia) PreH11) as Hb.
      unfold UINT_MOD in Hb. nia.
    + pose proof (list_within_bound_Znth_bound UINT_MOD l_up_nonalias (n_pre - 1) ltac:(rewrite PreH9; nia) PreH11) as Hb.
      unfold UINT_MOD in Hb.
      nia.
    + rewrite Zlength_nil. nia.
    + rewrite PreH1.
      apply mpn_lshift_initial_equation; try assumption.
      * nia.
      * split; assumption.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_1 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply mpn_lshift_initial_equation; try assumption.
  - lia.
  - split; assumption.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_2 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_3 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_4 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace
    (n_pre - 1) ltac:(rewrite PreH9; lia) PreH11) as Hb.
  unfold UINT_MOD in Hb; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_5 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (list_within_bound_Znth_bound UINT_MOD l_up_inplace
    (n_pre - 1) ltac:(rewrite PreH9; lia) PreH11) as Hb.
  lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_6 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH1.
  apply (mpn_lshift_step_equation l_up_inplace l_done_3 n_pre i_2
    cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2); try assumption.
  - rewrite PreH9; lia.
  - split; assumption.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_7 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite PreH6.
  rewrite Z.shiftl_mul_pow2 by lia.
  reflexivity.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_8 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH1.
  apply (mpn_lshift_done_bound l_up_inplace l_done_3 n_pre i_2
    cnt_pre high_limb_2 low_limb_2 tnc_2); try assumption.
  - rewrite PreH9; lia.
  - split; assumption.
  - split; assumption.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_9 : mpn_lshift_entail_wit_16_inplace_inv_split_goal_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH1.
  apply (mpn_lshift_done_length l_up_inplace l_done_3 n_pre i_2
    (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))); try assumption.
  rewrite PreH9; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_16_inplace_inv : mpn_lshift_entail_wit_16_inplace_inv.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_1.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_3.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_4.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_5.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_6.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_7.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_8.
  Goal_apply proof_of_mpn_lshift_entail_wit_16_inplace_inv_split_goal_9.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_17_off_zero_inv : mpn_lshift_entail_wit_17_off_zero_inv.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (replace_Znth ((i_2 + 1) - (i_2 + 1))
            (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))
            (sublist (i_2 + 1) (i_2 + 2) l_up_shifted) ++ l_done_3).
  Exists (unsigned_last_nbits ((Znth (n_pre - 1) l_up_shifted 0) * (Z.pow 2 cnt_pre)) 32)
    ((Znth (n_pre - 1) l_up_shifted 0) ÷ (Z.pow 2 tnc_2))
    (Znth (n_pre - 1) l_up_shifted 0)
    (@nil Z) (n_pre - 1) tnc_2.
  split_pure_spatial.
  - rewrite PreH2.
    sep_apply_l_atomic (UIntArray.seg_merge_to_seg up_pre (i_2 + 1) (i_2 + 2) n_pre
      (replace_Znth ((i_2 + 1) - (i_2 + 1))
         (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))
         (sublist (i_2 + 1) (i_2 + 2) l_up_shifted)) l_done_3).
    + dump_pre_spatial; lia.
    + cancel (UIntArray.seg up_pre (i_2 + 1) n_pre
        (replace_Znth (i_2 + 1 - (i_2 + 1))
           (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))
           (sublist (i_2 + 1) (i_2 + 2) l_up_shifted) ++ l_done_3)).
      repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + apply (mpn_lshift_done_length l_up_shifted l_done_3 n_pre i_2
               (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)));
        try assumption.
      rewrite PreH11. nia.
    + apply (mpn_lshift_done_bound l_up_shifted l_done_3 n_pre i_2 cnt_pre
               high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH11. nia.
      * split; assumption.
      * split; assumption.
    + rewrite PreH8.
      rewrite Z.shiftl_mul_pow2 by nia.
      reflexivity.
    + apply (mpn_lshift_step_equation l_up_shifted l_done_3 n_pre i_2
               cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
        try assumption.
      rewrite PreH11. nia.
      split; assumption.
    + rewrite Zlength_nil. nia.
    + rewrite PreH3.
      apply mpn_lshift_initial_equation; try assumption.
      * nia.
      * split; assumption.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_18_off_pos_inv : mpn_lshift_entail_wit_18_off_pos_inv.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: l_done_3).
  Exists (unsigned_last_nbits ((Znth (n_pre - 1) l_up_shifted 0) * (Z.pow 2 cnt_pre)) 32)
    ((Znth (n_pre - 1) l_up_shifted 0) ÷ (Z.pow 2 tnc_2))
    (Znth (n_pre - 1) l_up_shifted 0)
    (@nil Z) (n_pre - 1) tnc_2.
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_split_to_seg up_pre 0 (i_2 + 1) (i_2 + 2)
      (sublist 0 (i_2 + 2) l_up_shifted)).
    + dump_pre_spatial; lia.
    + sep_apply_l_atomic (UIntArray.seg_to_undef_seg up_pre (i_2 + 1) (i_2 + 2)
        (sublist (i_2 + 1 - 0) (i_2 + 2 - 0) (sublist 0 (i_2 + 2) l_up_shifted))).
      sep_apply_l_atomic (UIntArray.undef_seg_merge_to_undef_seg up_pre
        (i_2 + 1) (i_2 + 2) (off_shifted + i_2 + 1)).
      * dump_pre_spatial; lia.
      * sep_apply_l_atomic (UIntArray.seg_single rp_pre (i_2 + 1)
          (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))).
        replace (i_2 + 1 + 1) with (i_2 + 2) by lia.
        sep_apply (UIntArray.seg_merge_to_seg rp_pre (i_2 + 1)
          (i_2 + 2) n_pre
          ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) :: nil)
          l_done_3).
        -- simpl.
           rewrite Zsublist_Zsublist by lia.
           replace (0 + 0) with 0 by lia.
           replace (i_2 + 1 - 0 + 0) with (i_2 + 1) by lia.
           cancel.
        -- lia.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + rewrite Zlength_cons.
      rewrite PreH14.
      unfold Z.succ.
      ring.
    + simpl.
      split.
      * rewrite PreH5.
        apply (mpn_lshift_join_limb_bound high_limb_2 low_limb_2
                 (Znth (i_2 + 1) l_up_shifted 0) cnt_pre);
          try assumption; split; assumption.
      * exact PreH16.
    + rewrite PreH10.
      rewrite Z.shiftl_mul_pow2 by nia.
      reflexivity.
    + apply (mpn_lshift_step_equation_cons l_up_shifted l_done_3 n_pre i_2
               cnt_pre retval_2 high_limb_2 low_limb_2 tnc_2);
        try assumption.
      * rewrite PreH13. nia.
      * split; assumption.
    + rewrite Zlength_nil. nia.
    + rewrite PreH5.
      apply mpn_lshift_initial_equation; try assumption.
      * nia.
      * split; assumption.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_19_nonalias_inv : mpn_lshift_entail_wit_19_nonalias_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 0) by lia.
  subst i.
  replace (0 + 1) with 1 in * by lia.
  rewrite Z.sub_0_r in *.
  rewrite (sublist_self l_up_nonalias n_pre ltac:(lia)) in *.

  Exists l_done_3.
  split_pure_spatial.
  - repeat rewrite Z.add_0_r. cancel (UIntArray.full up_pre n_pre l_up_nonalias). cancel (UIntArray.undef_seg rp_pre 0 1). cancel (UIntArray.seg rp_pre 1 n_pre l_done_3).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_20_inplace_inv : mpn_lshift_entail_wit_20_inplace_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 0) by lia.
  subst i.
  replace (0 + 1) with 1 in * by lia.
  rewrite Z.sub_0_r in *.
  rewrite (sublist_self l_up_inplace n_pre ltac:(lia)) in *.

  Exists l_done_3.
  split_pure_spatial.
  - repeat rewrite Z.add_0_r. cancel (UIntArray.seg up_pre 0 1 (sublist 0 1 l_up_inplace)). cancel (UIntArray.seg up_pre 1 n_pre l_done_3).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_21_off_zero_inv : mpn_lshift_entail_wit_21_off_zero_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 0) by lia.
  subst i.
  replace (0 + 1) with 1 in * by lia.
  rewrite Z.sub_0_r in *.
  rewrite (sublist_self l_up_shifted n_pre ltac:(lia)) in *.
  assert (Hbound : 0 <= Znth 0 l_up_shifted 0 < UINT_MOD).
  { apply list_within_bound_Znth_bound; auto; lia. }
  assert (Hlow : 0 <= low_limb <= UINT_MAX).
  { unfold UINT_MOD in Hbound; lia. }
  Exists l_done_3.
  split_pure_spatial.
  - repeat rewrite Z.add_0_r. cancel (UIntArray.seg up_pre 0 1 (sublist 0 1 l_up_shifted)). cancel (UIntArray.seg rp_pre 1 n_pre l_done_3).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mpn_lshift_entail_wit_22_off_pos_inv : mpn_lshift_entail_wit_22_off_pos_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 0) by lia.
  subst i.
  replace (0 + 1) with 1 in * by lia.
  rewrite Z.sub_0_r in *.
  rewrite (sublist_self l_up_shifted n_pre ltac:(lia)) in *.
  assert (Hbound : 0 <= Znth 0 l_up_shifted 0 < UINT_MOD).
  { apply list_within_bound_Znth_bound; auto; lia. }
  assert (Hlow : 0 <= low_limb <= UINT_MAX).
  { unfold UINT_MOD in Hbound; lia. }
  Exists l_done_3.
  split_pure_spatial.
  - repeat rewrite Z.add_0_r. cancel (UIntArray.seg up_pre 0 1 (sublist 0 1 l_up_shifted)). cancel (UIntArray.undef_seg up_pre 1 (off_shifted + 1)). cancel (UIntArray.seg rp_pre 1 n_pre l_done_3).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_mpn_lshift_return_wit_1_nonalias_inv : mpn_lshift_return_wit_1_nonalias_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (store_uint_range (rp_pre + 0 * sizeof(UINT)) high_limb).
  Intros_p Hhead.
  Exists (high_limb :: l_done).
  split_pure_spatial.
  - rewrite (UIntArray.full_unfold rp_pre n_pre l_done high_limb).
    unfold StoreUIntAsElement.storeA. cancel (UIntArray.seg rp_pre 1 n_pre l_done). cancel.
  - split_pures; dump_pre_spatial.
    + rewrite Zlength_cons. lia.
    + cbn [list_within_bound]. split; [change (0 <= high_limb < 4294967296); change (0 <= high_limb <= 4294967295) in Hhead; lia | exact PreH10].
    + rewrite list_to_Z_cons. rewrite Z.mul_comm with (n := UINT_MOD). exact PreH12.
Qed.

Lemma proof_of_mpn_lshift_return_wit_2_inplace_inv : mpn_lshift_return_wit_2_inplace_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Zlength_nonneg l_done) as Hlen.
  assert (Hsingle : replace_Znth 0 high_limb (sublist 0 1 l_up_inplace) = high_limb :: nil).
  { destruct l_up_inplace; [rewrite Zlength_nil in PreH7; lia | reflexivity]. }
  rewrite Hsingle, (UIntArray.full_unfold up_pre 1 nil high_limb), UIntArray.seg_empty.
  unfold StoreUIntAsElement.storeA.
  Intros.
  prop_apply_p (store_uint_range (up_pre + 0 * sizeof(UINT)) high_limb).
  Intros_p Hhead.
  Exists (high_limb :: l_done).
  split_pure_spatial.
  - rewrite PreH13, (UIntArray.full_unfold up_pre n_pre l_done high_limb). unfold StoreUIntAsElement.storeA. cancel (UIntArray.seg up_pre 1 n_pre l_done). cancel.
  - split_pures; dump_pre_spatial.
    + rewrite Zlength_cons. lia.
    + cbn [list_within_bound]. split; [change (0 <= high_limb < 4294967296); change (0 <= high_limb <= 4294967295) in Hhead; lia | exact PreH10].
    + rewrite list_to_Z_cons. rewrite Z.mul_comm with (n := UINT_MOD). exact PreH12.
Qed.

Lemma proof_of_mpn_lshift_return_wit_3_off_zero_inv : mpn_lshift_return_wit_3_off_zero_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Zlength_nonneg l_done) as Hlen.
  assert (Hsingle : replace_Znth 0 high_limb (sublist 0 1 l_up_shifted) = high_limb :: nil).
  { destruct l_up_shifted; [rewrite Zlength_nil in PreH9; lia | reflexivity]. }
  rewrite Hsingle, (UIntArray.full_unfold up_pre 1 nil high_limb), UIntArray.seg_empty.
  unfold StoreUIntAsElement.storeA.
  Intros.
  prop_apply_p (store_uint_range (up_pre + 0 * sizeof(UINT)) high_limb).
  Intros_p Hhead.
  Exists (high_limb :: l_done).
  split_pure_spatial.
  - rewrite PreH1, PreH2, UIntArray.undef_seg_empty.
    sep_apply_l_atomic (UIntArray.seg_single up_pre 0 high_limb). cbn [Z.add].
    sep_apply (UIntArray.seg_merge_to_seg up_pre 0 1 n_pre (high_limb :: nil) l_done ltac:(lia)).
    cbn [app]. cancel.
  - split_pures; dump_pre_spatial.
    + rewrite Zlength_cons. lia.
    + cbn [list_within_bound]. split; [change (0 <= high_limb < 4294967296); change (0 <= high_limb <= 4294967295) in Hhead; lia | exact PreH12].
    + rewrite list_to_Z_cons. rewrite Z.mul_comm with (n := UINT_MOD). exact PreH14.
Qed.

Lemma proof_of_mpn_lshift_return_wit_4_off_pos_inv : mpn_lshift_return_wit_4_off_pos_inv.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Zlength_nonneg l_done) as Hlen.
  prop_apply_p (store_uint_range (rp_pre + 0 * sizeof(UINT)) high_limb).
  Intros_p Hhead.
  Exists (high_limb :: l_done).
  split_pure_spatial.
  - sep_apply_l_atomic (UIntArray.seg_single rp_pre 0 high_limb). cbn [Z.add].
    sep_apply (UIntArray.seg_merge_to_seg rp_pre 0 1 n_pre (high_limb :: nil) l_done ltac:(lia)).
    sep_apply_l_atomic (UIntArray.seg_to_undef_seg up_pre 0 1 (sublist 0 1 l_up_shifted)).
    sep_apply (UIntArray.undef_seg_merge_to_undef_seg up_pre 0 1 off_shifted ltac:(lia)).
    cbn [app]. cancel.
  - split_pures; dump_pre_spatial.
    + rewrite Zlength_cons. lia.
    + cbn [list_within_bound]. split; [change (0 <= high_limb < 4294967296); change (0 <= high_limb <= 4294967295) in Hhead; lia | exact PreH14].
    + rewrite list_to_Z_cons. rewrite Z.mul_comm with (n := UINT_MOD). exact PreH16.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_1_split_goal_spatial : mpn_lshift_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (UIntArray.full_Zlength up n l_up_shifted).
  Intros_p Hlen.
  rewrite sublist_self by lia.
  apply UIntArray.full_to_seg.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_1 : mpn_lshift_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_lshift_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_3_split_goal_spatial : mpn_lshift_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite sublist_self by lia.
  apply UIntArray.full_to_seg.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_3 : mpn_lshift_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_lshift_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_5_split_goal_1 : mpn_lshift_which_implies_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_lshift_which_implies_wit_5_split_goal_2 : mpn_lshift_which_implies_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_mpn_lshift_which_implies_wit_5 : mpn_lshift_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (UIntArray.seg_split_to_seg up_pre 0 (i+1) (i+2) (sublist 0 (i+2) l_up_inplace) ltac:(lia)).
  repeat rewrite Z.sub_0_r.
  repeat rewrite Zsublist_Zsublist0 by lia.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia].
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_6_split_goal_1 : mpn_lshift_which_implies_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_mpn_lshift_which_implies_wit_6_split_goal_2 : mpn_lshift_which_implies_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_mpn_lshift_which_implies_wit_6 : mpn_lshift_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (UIntArray.seg_split_to_seg up_pre 0 (i+1) (i+2) (sublist 0 (i+2) l_up_shifted) ltac:(lia)).
  repeat rewrite Z.sub_0_r.
  repeat rewrite Zsublist_Zsublist0 by lia.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia].
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_7_split_goal_spatial : mpn_lshift_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg up_pre (i+2) (off_shifted+i+1) (off_shifted+i+2) ltac:(lia)).
  replace (off_shifted+i+1) with (off_shifted+(i+1)) by lia.
  replace (off_shifted+i+2) with (off_shifted+(i+2)) by lia.
  rewrite (UIntArray.undef_seg_shift up_pre off_shifted (i+1) (i+2)).
  subst rp_pre. cancel.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_7 : mpn_lshift_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_lshift_which_implies_wit_7_split_goal_spatial.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_11_split_goal_spatial : mpn_lshift_which_implies_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (UIntArray.undef_seg_split_to_undef_seg up_pre 1 off_shifted (off_shifted+1) ltac:(lia)).
  replace off_shifted with (off_shifted+0) at 2 by lia.
  rewrite (UIntArray.undef_seg_shift up_pre off_shifted 0 1).
  subst rp_pre. cancel.
Qed.

Lemma proof_of_mpn_lshift_which_implies_wit_11 : mpn_lshift_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_lshift_which_implies_wit_11_split_goal_spatial.
Qed.

