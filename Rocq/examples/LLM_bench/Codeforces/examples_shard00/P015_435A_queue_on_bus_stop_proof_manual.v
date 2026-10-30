From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P015_435A_queue_on_bus_stop_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P015_435A_queue_on_bus_stop_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P015_435A_queue_on_bus_stop_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyPrefixState.
  rewrite Zsublist_nil by lia.
  left.
  repeat split; reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH5 k H).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (greedy_prefix_state_overflow_step__greedy_transitions
    groups_data capacity_pre buses used i).
  - lia.
  - apply PreH7. lia.
  - lia.
  - exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (greedy_prefix_state_fit_step__greedy_transitions
    groups_data capacity_pre buses used i).
  - lia.
  - apply PreH7. lia.
  - lia.
  - exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = Zlength groups_data) by lia.
  replace (sublist 0 i groups_data) with groups_data in PreH14.
  2: { symmetry. apply sublist_self. exact Hi. }
  unfold GreedyPrefixState in PreH14.
  destruct PreH14 as [[Hnil [Hbuses Hused]] |
    [cuts [Hgreedy [Hcuts HUsed]]]].
  - subst groups_data. rewrite Zlength_nil in PreH2. lia.
  - unfold Spec.
    replace buses with (Zlength cuts - 1) by lia.
    apply greedy_bus_loading_optimal_positive__final_result.
    + exact PreH6.
    + exact Hgreedy.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
