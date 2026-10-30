From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P038_1903C_theofanis_nightmare_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P038_1903C_theofanis_nightmare_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P038_1903C_theofanis_nightmare_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH1.
  replace (Zlength input - 1 + 1) with (Zlength input) by lia.
  apply suffix_contribution_sum_at_length__suffix_initialization.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH1.
  replace (Zlength input - 1 + 1) with (Zlength input) by lia.
  symmetry.
  apply suffix_sum_at_length__suffix_initialization.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH4 j H).
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
  subst i.
  destruct PreH15 as [Hrange Hanswer].
  unfold SuffixContributionSum.
  split; [lia |].
  rewrite zrange_cons_step__suffix_transitions by lia.
  simpl.
  unfold SuffixContribution at 1.
  destruct (Z.eq_dec 0 0); [| contradiction].
  rewrite suffix_sum_step__suffix_transitions by lia.
  rewrite <- PreH14.
  replace (0 + 1) with 1 in Hanswer by lia.
  rewrite Hanswer.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  replace (0 - 1 + 1) with 0 by lia.
  rewrite suffix_sum_step__suffix_transitions by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_3 : solver_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  specialize (PreH6 0 ltac:(lia)) as [Hlower Hupper].
  nia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_4 : solver_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  specialize (PreH6 0 ltac:(lia)) as [Hlower Hupper].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 < i < Zlength input) by lia.
  assert (Hsum : SuffixSum input i = Znth i input 0 + suffix).
  { rewrite suffix_sum_step__suffix_transitions by lia.
    rewrite <- PreH15. reflexivity. }
  replace ((i - 1) + 1) with i by lia.
  replace (answer + (suffix + Znth i input 0))
    with (answer + SuffixSum input i) by lia.
  apply suffix_contribution_sum_positive_step__suffix_transitions;
    try assumption.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i - 1) + 1) with i by lia.
  rewrite suffix_sum_step__suffix_transitions by lia.
  rewrite <- PreH15.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 i ltac:(lia)) as [Hlower Hupper].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_4 : solver_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: specialize (PreH7 i ltac:(lia)) as [Hlower Hupper]; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : 0 < i < Zlength input) by lia.
  assert (Hsum : SuffixSum input i = Znth i input 0 + suffix).
  { rewrite suffix_sum_step__suffix_transitions by lia.
    rewrite <- PreH15. reflexivity. }
  replace ((i - 1) + 1) with i by lia.
  apply suffix_contribution_sum_nonpositive_step__suffix_transitions;
    try assumption.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_2 : solver_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i - 1) + 1) with i by lia.
  rewrite suffix_sum_step__suffix_transitions by lia.
  rewrite <- PreH15.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_3_split_goal_3 : solver_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH7 i ltac:(lia)) as [Hlower Hupper].
  nia.
Qed.

Lemma proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_3_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply suffix_contribution_sum_spec__final_optimality.
  - apply pre_from_pointwise_bounds__final_optimality.
    + lia.
    + intros j Hj. apply PreH5. lia.
  - replace (i + 1) with 0 in PreH14 by lia.
    exact PreH14.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

