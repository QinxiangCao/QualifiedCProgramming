From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P023_985A_chess_placing_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P023_985A_chess_placing_proof_auto.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P023_985A_chess_placing_lib.
Local Open Scope sac.

Lemma proof_of_iabs_return_wit_1_split_goal_1 : iabs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_iabs_return_wit_1 : iabs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_iabs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_iabs_return_wit_2_split_goal_1 : iabs_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_iabs_return_wit_2 : iabs_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_iabs_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH8 i ltac:(lia)) as Hentry.
  pose proof (ChessDistance_bounds (Znth i sorted 0) i half_pre
    ltac:(lia) Hentry ltac:(lia)) as Hdist.
  destruct Hdist as [[Hodd_nonneg Hodd_upper] [Heven_nonneg Heven_upper]].
  dump_pre_spatial.
  rewrite PreH1.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH9 i ltac:(lia)) as Hentry.
  pose proof (ChessDistance_bounds (Znth i sorted 0) i half_pre
    ltac:(lia) Hentry ltac:(lia)) as Hdist.
  destruct Hdist as [[Hodd_nonneg Hodd_upper] [Heven_nonneg Heven_upper]].
  dump_pre_spatial.
  rewrite PreH1.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply ChessCostPrefix_zero.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (Permutation_preserves_Znth_bounds positions l1 half_pre 1 (2 * half_pre));
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_correct, PreH7, Zlength_correct.
  symmetry.
  f_equal.
  apply Permutation_length.
  exact PreH1.
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
  rewrite PreH1, PreH2.
  unfold OddTarget, EvenTarget.
  apply ChessCostPrefix_step; assumption.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (ChessDistance_bounds (Znth i sorted_2 0) i half_pre
                ltac:(lia) (PreH9 i ltac:(lia)) PreH5) as [_ Heven].
  unfold EvenTarget in Heven.
  rewrite PreH1.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_4 : solver_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (ChessDistance_bounds (Znth i sorted_2 0) i half_pre
                ltac:(lia) (PreH9 i ltac:(lia)) PreH5) as [Hodd _].
  unfold OddTarget in Hodd.
  rewrite PreH2.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_5 : solver_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply ChessCostPrefix_Spec_odd with (sorted := sorted) (even := even).
  - lia.
  - lia.
  - exact PreH7.
  - exact PreH8.
  - exact PreH5.
  - exact PreH9.
  - exact PreH10.
  - replace half_pre with i by lia.
    exact PreH17.
  - exact PreH1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply ChessCostPrefix_Spec_even with (sorted := sorted) (odd := odd).
  - lia.
  - lia.
  - exact PreH7.
  - exact PreH8.
  - exact PreH5.
  - exact PreH9.
  - exact PreH10.
  - replace half_pre with i by lia.
    exact PreH17.
  - lia.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
