From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P021_2030C_a_true_battle_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P021_2030C_a_true_battle_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NoAdjacentOnesBefore.
  intros k Hk.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro Hlast.
  apply PreH1.
  unfold Znth.
  rewrite app_nth1.
  - exact Hlast.
  - rewrite Zlength_correct in PreH3, PreH4.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intro Hfirst.
  apply PreH2.
  unfold Znth.
  rewrite app_nth1.
  - exact Hfirst.
  - rewrite Zlength_correct in PreH4.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply no_adjacent_ones_before_succ__loop_transition; eauto.
  left.
  rewrite <- app_Znth1 with (l' := (0 :: nil)); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply no_adjacent_ones_before_succ__loop_transition; eauto.
  right.
  rewrite <- app_Znth1 with (l' := (0 :: nil)); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply spec_zero_from_completed_scan__final_results; eauto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec, WinningCriterion, HasAdjacentOnes.
  split.
  - right; reflexivity.
  - split.
    + intro; right; right; exists i.
      repeat split.
      * exact PreH10.
      * lia.
      * rewrite app_Znth1 in PreH2 by lia; exact PreH2.
      * rewrite app_Znth1 in PreH1 by lia; exact PreH1.
    + intro; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec, WinningCriterion.
  split.
  - right; reflexivity.
  - split.
    + intro; left.
      rewrite app_Znth1 in PreH1 by lia; exact PreH1.
    + intro; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec, WinningCriterion.
  split.
  - right; reflexivity.
  - split.
    + intro; right; left.
      rewrite <- PreH3.
      rewrite app_Znth1 in PreH1 by lia; exact PreH1.
    + intro; reflexivity.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.
