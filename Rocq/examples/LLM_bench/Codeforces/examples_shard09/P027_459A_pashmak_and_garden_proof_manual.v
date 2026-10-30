From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P027_459A_pashmak_and_garden_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P027_459A_pashmak_and_garden_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib.
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

Lemma proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold Pre in *; lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply no_completion_of_nonaxis_unequal_abs_diffs__final_results; eauto.
  congruence.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists x1_pre y2_pre x2_pre y1_pre.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_unfold.
    rewrite IntArray.seg_empty.
    simpl.
    cancel.
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + eapply completes_square_diagonal__final_results; eauto; congruence.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists x1_pre (y1_pre + retval) x2_pre (y2_pre + retval).
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_unfold.
    rewrite IntArray.seg_empty.
    simpl.
    cancel.
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + eapply completes_square_horizontal__final_results; eauto.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (x1_pre + retval) y1_pre (x2_pre + retval) y2_pre.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    rewrite IntArray.full_unfold.
    repeat rewrite IntArray.seg_unfold.
    rewrite IntArray.seg_empty.
    simpl.
    cancel.
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial.
    + lia.
    + eapply completes_square_vertical__final_results; eauto.
Qed.
