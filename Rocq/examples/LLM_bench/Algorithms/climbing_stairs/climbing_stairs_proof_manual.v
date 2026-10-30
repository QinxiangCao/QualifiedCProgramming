From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.climbing_stairs Require Import climbing_stairs_goal.
From SimpleC.EE.LLM_bench.Algorithms.climbing_stairs Require Import climbing_stairs_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.climbing_stairs.climbing_stairs_lib.
Local Open Scope sac.


Lemma proof_of_climbStairs_safety_wit_4_split_goal_1 : climbStairs_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcount : ClimbingStairsCount i (prev + curr)).
  { replace i with ((i - 2) + 2) by lia.
    apply ClimbingStairsCount_next; try lia; auto.
    replace (i - 2 + 1) with (i - 1) by lia. exact PreH9. }
  pose proof (ClimbingStairsCount_int_range_upto_45__loop_transition i (prev + curr) ltac:(lia) ltac:(lia) Hcount).
  entailer!.
Qed.
Lemma proof_of_climbStairs_safety_wit_4_split_goal_2 : climbStairs_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.
Lemma proof_of_climbStairs_safety_wit_4 : climbStairs_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_climbStairs_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_climbStairs_entail_wit_1_split_goal_1 : climbStairs_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_climbStairs_entail_wit_1_split_goal_2 : climbStairs_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_climbStairs_entail_wit_1 : climbStairs_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_climbStairs_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_climbStairs_entail_wit_2_split_goal_1 : climbStairs_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((i + 1) - 1) with ((i - 2) + 2) by lia.
  eapply ClimbingStairsCount_next.
  - lia.
  - exact PreH8.
  - replace (i - 2 + 1) with (i - 1) by lia.
    exact PreH9.
Qed.

Lemma proof_of_climbStairs_entail_wit_2_split_goal_2 : climbStairs_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((i + 1) - 2) with (i - 1) by lia.
  exact PreH9.
Qed.

Lemma proof_of_climbStairs_entail_wit_2 : climbStairs_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_climbStairs_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_climbStairs_return_wit_1_split_goal_1 : climbStairs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre + 1) by lia.
  replace n_pre with (i - 1) by lia.
  exact PreH9.
Qed.

Lemma proof_of_climbStairs_return_wit_1 : climbStairs_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_climbStairs_return_wit_1_split_goal_1.
Qed.
