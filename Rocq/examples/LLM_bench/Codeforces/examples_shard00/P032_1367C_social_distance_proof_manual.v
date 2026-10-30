From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P032_1367C_social_distance_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P032_1367C_social_distance_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P032_1367C_social_distance_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_15_split_goal_1 : solver_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  cancel.
  unfold RightNearestSuffix in PreH20.
  destruct PreH20 as [Hlen Hsuffix].
  specialize (Hsuffix i ltac:(lia)).
  pose proof
    (right_nearest_bounds__nearest_suffix seats k_pre i
       (Znth i next_values 0) ltac:(lia) Hsuffix) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_15_split_goal_2 : solver_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  cancel.
  unfold RightNearestSuffix in PreH20.
  destruct PreH20 as [Hlen Hsuffix].
  specialize (Hsuffix i ltac:(lia)).
  pose proof
    (right_nearest_bounds__nearest_suffix seats k_pre i
       (Znth i next_values 0) ltac:(lia) Hsuffix) as Hbounds.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (@nil Z).
  replace (n_pre - 1 + 1) with n_pre by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval n_pre).
    rewrite IntArray.seg_empty.
    IntArray.ArraySimplify.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + intros j Hj. apply PreH6. lia.
    + unfold RightNearest.
      split; [lia |].
      left. split; [lia |].
      intros j Hj. lia.
    + replace n_pre with (Zlength seats) by lia.
      apply right_nearest_suffix_empty__nearest_suffix.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hseat : Znth i seats 48 = 49).
  {
    rewrite (Znth_indep seats i 48 0) by lia.
    rewrite <- (app_Znth1 0 seats (0 :: nil) i) by lia.
    exact PreH1.
  }
  Exists (i :: suffix_2).
  replace ((i - 1) + 1) with i by lia.
  split_pure_spatial.
  - rewrite IntArray.seg_unfold.
    cancel (CharArray.full s_pre (n_pre + 1) (seats ++ 0 :: nil)).
    cancel (IntArray.undef_seg next 0 i).
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + unfold RightNearest.
      split; [lia |].
      right. repeat split; try lia; auto.
    + apply right_nearest_suffix_cons_hit__nearest_suffix; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hseat : Znth i seats 48 <> 49).
  {
    rewrite (Znth_indep seats i 48 0) by lia.
    rewrite <- (app_Znth1 0 seats (0 :: nil) i) by lia.
    exact PreH1.
  }
  Exists (nearest :: suffix_2).
  replace ((i - 1) + 1) with i by lia.
  split_pure_spatial.
  - rewrite IntArray.seg_unfold.
    cancel (CharArray.full s_pre (n_pre + 1) (seats ++ 0 :: nil)).
    cancel (IntArray.undef_seg next 0 i).
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + unfold RightNearest in *.
      destruct PreH15 as [Hrange [[Hsent Hnone] | [Hbounds [Hhit Hnone]]]].
      * split; [lia |].
        left. split; [exact Hsent |].
        intros j Hj.
        destruct (Z.eq_dec j i) as [-> | Hneq]; [exact Hseat |].
        apply Hnone. lia.
      * split; [lia |].
        right. repeat split; try lia; auto.
        intros j Hj.
        destruct (Z.eq_dec j i) as [-> | Hneq]; [exact Hseat |].
        apply Hnone. lia.
    + apply right_nearest_suffix_cons_miss__nearest_suffix; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = -1) by lia.
  subst i.
  Exists suffix.
  replace (-1 + 1) with 0 in * by lia.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.seg_to_full next 0 n_pre suffix).
    IntArray.ArraySimplify.
    cancel (CharArray.full s_pre (n_pre + 1) (seats ++ 0 :: nil)).
    replace (next + 0 * sizeof(INT)) with next by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply prefix_placement_initial__greedy_transitions.
  exact PreH6.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH3 by lia.
  assert (Hseat0 : Znth i seats 0 = 48) by (specialize (PreH9 i); intuition lia).
  assert (Hseat48 : Znth i seats 48 = 48).
  { rewrite (Znth_indep seats i 48 0) by lia. exact Hseat0. }
  eapply prefix_placement_add__greedy_transitions.
  - exact PreH10.
  - lia.
  - exact Hseat48.
  - exact PreH20.
  - lia.
  - exact PreH21.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH2 by lia.
  assert (Hseat0 : Znth i seats 0 = 48) by (specialize (PreH8 i); intuition lia).
  assert (Hseat48 : Znth i seats 48 = 48).
  { rewrite (Znth_indep seats i 48 0) by lia. exact Hseat0. }
  eapply prefix_placement_skip_left__greedy_transitions.
  - exact PreH9.
  - lia.
  - exact Hseat48.
  - exact PreH19.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH3 by lia.
  assert (Hseat0 : Znth i seats 0 = 48) by (specialize (PreH9 i); intuition lia).
  assert (Hseat48 : Znth i seats 48 = 48).
  { rewrite (Znth_indep seats i 48 0) by lia. exact Hseat0. }
  eapply prefix_placement_skip_right__greedy_transitions.
  - exact PreH10.
  - lia.
  - exact Hseat48.
  - exact PreH20.
  - exact PreH21.
  - exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_4_split_goal_1 : solver_entail_wit_5_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH1 by lia.
  assert (Hseat48 : Znth i seats 48 = 49).
  { rewrite (Znth_indep seats i 48 0) by lia. exact PreH1. }
  eapply prefix_placement_original_occupied__greedy_transitions.
  - exact PreH8.
  - lia.
  - exact Hseat48.
  - exact PreH18.
Qed.

Lemma proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (prefix_placement_complete_spec__final_result
    seats k_pre i last answer).
  - lia.
  - assumption.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.
