From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P045_569A_music_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P045_569A_music_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P045_569A_music_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MusicLoopInvariant.
  split; [lia |].
  split.
  - rewrite Z.pow_0_r. lia.
  - intros i Hi. lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MusicLoopInvariant in *.
  destruct PreH11 as [Hcount [Hcurrent Hold]].
  split; [lia |].
  split.
  - replace (starts + 1) with (Z.succ starts) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
  - intros i Hi.
    assert (i < starts \/ i = starts) as [Hiold | ->] by lia.
    + apply Hold. lia.
    + nia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
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
  eapply music_loop_invariant_implies_spec__final_result.
  - lia.
  - lia.
  - eauto.
  - eauto.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
