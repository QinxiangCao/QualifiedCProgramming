From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_realloc_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_realloc_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_realloc_return_wit_1_preserving_split_goal_spatial : mpz_realloc_return_wit_1_preserving_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hold_zero: old_preserving = 0) by lia.
  subst old_preserving.
  change (Zabs 0) with 0 in *.
  rewrite PreH3.
  sep_apply (UIntArray.undef_full_to_undef_seg retval); try lia.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l.
  assert (l = nil).
  { apply Zlength_nil_inv. lia. }
  subst l.
  destruct H as [Hval [Hlast Hbound]].
  rewrite list_to_Z_nil in Hval.
  assert (Hn_abs_zero: Zabs n_preserving = 0) by lia.
  rewrite Hn_abs_zero in *.
  rewrite UIntArray.full_empty.
  rewrite PreH10.
  rewrite UIntArray.undef_seg_empty.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  try rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - cancel.
    normalize.
    Intros.
    cancel.
  - repeat split_pures; dump_pre_spatial; simpl; try reflexivity; try lia.
    rewrite list_to_Z_nil; tauto.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_preserving : mpz_realloc_return_wit_1_preserving.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_1_preserving_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_return_wit_2_raw_split_goal_spatial : mpz_realloc_return_wit_2_raw_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH3.
  rewrite PreH9.
  rewrite UIntArray.undef_full_empty.
  repeat cancel.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_2_raw : mpz_realloc_return_wit_2_raw.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_realloc_return_wit_2_raw_split_goal_spatial cap_raw sz_raw ptr_raw size_pre retval_2 retval retval_3).
Qed.

Lemma proof_of_mpz_realloc_return_wit_4_raw_split_goal_spatial : mpz_realloc_return_wit_4_raw_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH3.
  cancel.
Qed.

Lemma proof_of_mpz_realloc_return_wit_4_raw : mpz_realloc_return_wit_4_raw.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_mpz_realloc_return_wit_4_raw_split_goal_spatial cap_raw sz_raw size_pre retval_2 retval retval_3).
Qed.

Lemma proof_of_mpz_realloc_return_wit_5_preserving_split_goal_1 : mpz_realloc_return_wit_5_preserving_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_5_preserving_split_goal_spatial : mpz_realloc_return_wit_5_preserving_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_5_preserving : mpz_realloc_return_wit_5_preserving.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_5_preserving_split_goal_spatial.
  Goal_apply proof_of_mpz_realloc_return_wit_5_preserving_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_return_wit_6_preserving_split_goal_1 : mpz_realloc_return_wit_6_preserving_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_6_preserving : mpz_realloc_return_wit_6_preserving.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_6_preserving_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_raw_pure_split_goal_1 : mpz_realloc_partial_solve_wit_4_raw_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_raw_pure : mpz_realloc_partial_solve_wit_4_raw_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_4_raw_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_preserving_pure_split_goal_1 : mpz_realloc_partial_solve_wit_5_preserving_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_preserving_pure : mpz_realloc_partial_solve_wit_5_preserving_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_5_preserving_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_7_raw_pure_split_goal_1 : mpz_realloc_partial_solve_wit_7_raw_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_7_raw_pure : mpz_realloc_partial_solve_wit_7_raw_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_7_raw_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_8_preserving_pure_split_goal_1 : mpz_realloc_partial_solve_wit_8_preserving_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_8_preserving_pure : mpz_realloc_partial_solve_wit_8_preserving_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_8_preserving_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_9_raw_pure_split_goal_1 : mpz_realloc_partial_solve_wit_9_raw_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_9_raw_pure : mpz_realloc_partial_solve_wit_9_raw_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_9_raw_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_10_preserving_pure_split_goal_1 : mpz_realloc_partial_solve_wit_10_preserving_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_10_preserving_pure : mpz_realloc_partial_solve_wit_10_preserving_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_10_preserving_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_11_raw_pure_split_goal_1 : mpz_realloc_partial_solve_wit_11_raw_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_11_raw_pure : mpz_realloc_partial_solve_wit_11_raw_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_11_raw_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_12_preserving_pure_split_goal_1 : mpz_realloc_partial_solve_wit_12_preserving_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_12_preserving_pure : mpz_realloc_partial_solve_wit_12_preserving_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_partial_solve_wit_12_preserving_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_1_split_goal_spatial : mpz_realloc_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      rewrite list_to_Z_nil.
      repeat split; simpl; try lia; try exact I.
    + dump_pre_spatial.
      simpl.
      rewrite Zlength_nil.
      lia.
    + dump_pre_spatial.
      simpl.
      rewrite Zlength_nil.
      reflexivity.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_1 : mpz_realloc_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_2_split_goal_spatial : mpz_realloc_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (mpd_store_Z_compact_to_mpd_store_Z r__mp_d 0 0).
  sep_apply_l_atomic (mpd_store_Z_to_undef_full r__mp_d 0 0).
  rewrite UIntArray.undef_full_empty.
  sep_apply_l_atomic (UIntArray.undef_seg_to_undef_full r__mp_d 0 size).
  replace (r__mp_d + 0 * sizeof(UINT)) with r__mp_d by lia.
  replace (size - 0) with size by lia.
  repeat cancel.
Qed.

Lemma proof_of_mpz_realloc_which_implies_wit_2 : mpz_realloc_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_which_implies_wit_2_split_goal_spatial.
Qed.

