From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mrz_realloc_if_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mrz_realloc_if_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mrz_realloc_if_return_wit_1_preserving_split_goal_1 : mrz_realloc_if_return_wit_1_preserving_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_preserving_split_goal_2 : mrz_realloc_if_return_wit_1_preserving_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_preserving_split_goal_spatial : mrz_realloc_if_return_wit_1_preserving_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.max_r by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_preserving : mrz_realloc_if_return_wit_1_preserving.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_preserving_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_preserving_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_preserving_split_goal_2.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_raw_split_goal_1 : mrz_realloc_if_return_wit_2_raw_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_raw_split_goal_2 : mrz_realloc_if_return_wit_2_raw_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_raw_split_goal_spatial : mrz_realloc_if_return_wit_2_raw_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.max_r by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_raw : mrz_realloc_if_return_wit_2_raw.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_raw_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_raw_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_raw_split_goal_2.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_3_raw_split_goal_1 : mrz_realloc_if_return_wit_3_raw_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_3_raw_split_goal_2 : mrz_realloc_if_return_wit_3_raw_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_3_raw_split_goal_spatial : mrz_realloc_if_return_wit_3_raw_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_3_raw : mrz_realloc_if_return_wit_3_raw.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_3_raw_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_3_raw_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_3_raw_split_goal_2.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_4_preserving_split_goal_1 : mrz_realloc_if_return_wit_4_preserving_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_4_preserving_split_goal_2 : mrz_realloc_if_return_wit_4_preserving_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_4_preserving_split_goal_spatial : mrz_realloc_if_return_wit_4_preserving_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_4_preserving : mrz_realloc_if_return_wit_4_preserving.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_4_preserving_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_4_preserving_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_4_preserving_split_goal_2.
Qed.

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_raw_pure_split_goal_1 : mrz_realloc_if_partial_solve_wit_1_raw_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite !Z.max_l in * by lia.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_raw_pure : mrz_realloc_if_partial_solve_wit_1_raw_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mrz_realloc_if_partial_solve_wit_1_raw_pure_split_goal_1.
Qed.

