From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P041_1054C_candies_distribution_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P041_1054C_candies_distribution_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P041_1054C_candies_distribution_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply candy_candidate_prefix_nil__candidate_construction.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  apply PreH5.
  rewrite PreH3.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  apply PreH4.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (CandyCandidatePrefix n_pre l_data r_data (i + 1)
    (prefix_2 ++ CandyCandidateAt n_pre l_data r_data i :: nil)).
  apply candy_candidate_prefix_snoc__candidate_construction.
  - exact PreH10.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  Exists prefix.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full a_pre 0 n_pre prefix).
  replace (a_pre + 0 * sizeof (INT)) with a_pre by lia.
  rewrite Z.sub_0_r.
  split_pure_spatial.
  - cancel (IntArray.full l_pre n_pre l_data).
    cancel (IntArray.full r_pre n_pre r_data).
    cancel (IntArray.full a_pre n_pre prefix).
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold CandyCheckedPrefix.
      intros k Hk.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(apply candy_left_count_zero__checking_entry).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7; assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6; assumption.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply candy_left_count_step_false__left_scan; eauto).
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(eapply candy_left_count_step_true__left_scan; eauto).
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply candy_right_count_empty__left_scan.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = i) by lia.
  subst j.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_4 : solver_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH6.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (cr + 0) with cr by lia.
  eapply candy_right_count_step_false__right_scan_commit; eauto.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply candy_right_count_step_true__right_scan_commit; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (candy_checked_prefix_succ__right_scan_commit
    n_pre l_data r_data candidate_2 i j cl cr).
  - exact PreH20.
  - exact PreH11.
  - lia.
  - lia.
  - exact PreH16.
  - exact PreH18.
  - exact PreH2.
  - exact PreH1.
  - exact PreH21.
  - exact PreH22.
  - lia.
  - exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  unfold Spec.
  left.
  exists candidate.
  split; [reflexivity |].
  eapply candy_checked_complete_explains__successful_return; eauto.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros a Hexplains.
  pose proof
    (candy_candidate_canonical_explains__rejected_return
      n_pre l_data r_data a candidate PreH4 Hexplains PreH10)
    as Hcandidate_explains.
  assert (Hcandidate_length : Zlength candidate = n_pre).
  { destruct PreH10 as [Hlength _]. exact Hlength. }
  destruct Hcandidate_explains as [_ [_ Hreports]].
  specialize (Hreports i) as [Hleft _].
  - rewrite Hcandidate_length. lia.
  - unfold CandyLeftCount in PreH20.
    apply PreH1.
    lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros a Hexplains.
  pose proof
    (candy_candidate_canonical_explains__rejected_return
      n_pre l_data r_data a candidate PreH3 Hexplains PreH9)
    as Hcandidate_explains.
  assert (Hcandidate_length : Zlength candidate = n_pre).
  { destruct PreH9 as [Hlength _]. exact Hlength. }
  pose proof
    (candy_explains_value_bound__rejected_return
      l_data r_data candidate i Hcandidate_explains)
    as Hbound.
  specialize (Hbound ltac:(rewrite Hcandidate_length; lia)).
  lia.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  right.
  split; [reflexivity |].
  intros a Hexplains.
  pose proof
    (candy_candidate_canonical_explains__rejected_return
      n_pre l_data r_data a candidate PreH5 Hexplains PreH11)
    as Hcandidate_explains.
  assert (Hcandidate_length : Zlength candidate = n_pre).
  { destruct PreH11 as [Hlength _]. exact Hlength. }
  destruct Hcandidate_explains as [_ [_ Hreports]].
  specialize (Hreports i) as [_ Hright].
  - rewrite Hcandidate_length. lia.
  - assert (j = n_pre) by lia.
    subst j.
    unfold CandyRightCount in PreH22.
    rewrite Hcandidate_length in Hright.
    apply PreH1.
    lia.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.
