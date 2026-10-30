From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P078_1967B2_reverse_card_hard_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P078_1967B2_reverse_card_hard_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard_lib.
Local Open Scope sac.

Lemma proof_of_gcd_int_entail_wit_2_split_goal_1 : gcd_int_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  rewrite RCgcd_step by lia. assumption.
Qed.

Lemma proof_of_gcd_int_entail_wit_2_split_goal_2 : gcd_int_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

Lemma proof_of_gcd_int_entail_wit_2_split_goal_3 : gcd_int_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

Lemma proof_of_gcd_int_entail_wit_2 : gcd_int_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gcd_int_entail_wit_2_split_goal_1.
  Goal_apply proof_of_gcd_int_entail_wit_2_split_goal_2.
  Goal_apply proof_of_gcd_int_entail_wit_2_split_goal_3.
Qed. 

Lemma proof_of_gcd_int_return_wit_1_split_goal_1 : gcd_int_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst b. rewrite RCgcd_finish in * by lia. assumption.
Qed.

Lemma proof_of_gcd_int_return_wit_1 : gcd_int_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gcd_int_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.quot_pos n_pre p ltac:(lia) ltac:(lia)) as Hquot0.
  pose proof (Z.quot_le_upper_bound n_pre p n_pre ltac:(lia) ltac:(nia)) as Hquot1.
  pose proof (Z.quot_pos (n_pre ÷ p) (p+q) ltac:(lia) ltac:(lia)) as Hinc0.
  pose proof (Z.quot_le_upper_bound (n_pre ÷ p) (p+q) n_pre ltac:(lia) ltac:(nia)) as Hinc1.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.quot_pos n_pre p ltac:(lia) ltac:(lia)) as Hquot0.
  pose proof (Z.quot_le_upper_bound n_pre p n_pre ltac:(lia) ltac:(nia)) as Hquot1.
  pose proof (Z.quot_pos (n_pre ÷ p) (p+q) ltac:(lia) ltac:(lia)) as Hinc0.
  pose proof (Z.quot_le_upper_bound (n_pre ÷ p) (p+q) n_pre ltac:(lia) ltac:(nia)) as Hinc1.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.quot_pos m_pre q ltac:(lia) ltac:(lia)) as Hquot0.
  pose proof (Z.quot_le_upper_bound m_pre q m_pre ltac:(lia) ltac:(nia)) as Hquot1.
  pose proof (Z.quot_pos (m_pre ÷ q) (p+q) ltac:(lia) ltac:(lia)) as Hinc0.
  pose proof (Z.quot_le_upper_bound (m_pre ÷ q) (p+q) m_pre ltac:(lia) ltac:(nia)) as Hinc1.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (Z.quot_pos m_pre q ltac:(lia) ltac:(lia)) as Hquot0.
  pose proof (Z.quot_le_upper_bound m_pre q m_pre ltac:(lia) ltac:(nia)) as Hquot1.
  pose proof (Z.quot_pos (m_pre ÷ q) (p+q) ltac:(lia) ltac:(lia)) as Hinc0.
  pose proof (Z.quot_le_upper_bound (m_pre ÷ q) (p+q) m_pre ltac:(lia) ltac:(nia)) as Hinc1.
  int_auto.
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed. 

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply RC_progress_initial__prefix_boundaries.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply RC_progress_row__prefix_boundaries; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hg : Z.gcd p q = 1) by (unfold RCgcd in *; lia).
  rewrite (Z.quot_div_nonneg n_pre p) in * by lia.
  rewrite (Z.quot_div_nonneg m_pre q) in * by lia.
  assert (Hdiv : 0 <= n_pre/p) by (apply Z.div_pos; lia).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (RC_progress_step__fiber_step n_pre m_pre p q ans ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hg PreH16) as Hstep.
  rewrite Z.min_l in Hstep by lia. exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (RC_quot_bounds__fiber_step n_pre p (p+q) ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (RC_quot_bounds__fiber_step n_pre p (p+q) ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hg : Z.gcd p q = 1) by (unfold RCgcd in *; lia).
  rewrite (Z.quot_div_nonneg n_pre p) in * by lia.
  rewrite (Z.quot_div_nonneg m_pre q) in * by lia.
  assert (Hdiv : 0 <= m_pre/q) by (apply Z.div_pos; lia).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (RC_progress_step__fiber_step n_pre m_pre p q ans ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hg PreH16) as Hstep.
  rewrite Z.min_r in Hstep by lia. exact Hstep.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (RC_quot_bounds__fiber_step m_pre q (p+q) ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (RC_quot_bounds__fiber_step m_pre q (p+q) ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_3.
Qed. 

Lemma proof_of_solver_entail_wit_4_3_split_goal_1 : solver_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply RC_progress_skip__prefix_boundaries; [unfold RCgcd in *; congruence|eassumption].
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_3_split_goal_1.
Qed. 

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply RC_progress_finish__prefix_boundaries; eauto; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed. 
