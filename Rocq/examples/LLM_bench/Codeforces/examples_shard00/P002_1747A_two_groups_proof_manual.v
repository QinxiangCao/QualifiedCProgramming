From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P002_1747A_two_groups_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P002_1747A_two_groups_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P002_1747A_two_groups_lib.
Local Open Scope sac.

Lemma proof_of_llabs_return_wit_1_split_goal_1 : llabs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Z.abs_neq by lia; lia).
Qed.

Lemma proof_of_llabs_return_wit_1 : llabs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_llabs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_llabs_return_wit_2_split_goal_1 : llabs_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Z.abs_eq by lia; lia).
Qed.

Lemma proof_of_llabs_return_wit_2 : llabs_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_llabs_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH5 i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite ListLib.sum_app.
  rewrite (sublist_single 0 i input) by lia.
  simpl.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = n_pre) by lia.
  subst i.
  rewrite (sublist_self input n_pre) in PreH9 by
    (symmetry; exact PreH5).
  subst sum.
  subst retval.
  apply spec_abs_total__final_result.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
