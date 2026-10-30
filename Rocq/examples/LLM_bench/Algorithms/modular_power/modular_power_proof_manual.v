From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.modular_power Require Import modular_power_goal.
From SimpleC.EE.LLM_bench.Algorithms.modular_power Require Import modular_power_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.
Local Open Scope sac.

Lemma proof_of_modular_power_entail_wit_1_split_goal_1 : modular_power_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  unfold ModularPowerProgress.
  rewrite Z.mul_1_l.
  reflexivity.
Qed.

Lemma proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_power_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_1 : modular_power_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite zdiv_equiv by lia.
  eapply modular_power_progress_odd_step__loop_transitions; eauto; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_2 : modular_power_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * a) modulus_pre ltac:(lia)) as Hresult_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_3 : modular_power_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * a) modulus_pre ltac:(lia)) as Hresult_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_4 : modular_power_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_5 : modular_power_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_6 : modular_power_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_6.
Qed. 

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_1 : modular_power_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite zdiv_equiv by lia.
  pose proof (Z.mod_pos_bound b 2 ltac:(lia)) as Hb_mod.
  assert (b mod 2 = 0) by lia.
  eapply modular_power_progress_even_step__loop_transitions; eauto; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_2 : modular_power_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_3 : modular_power_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_4 : modular_power_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_4.
Qed. 

Lemma proof_of_modular_power_return_wit_1_split_goal_1 : modular_power_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (rewrite !modular_residue_int in * by lia).
  unfold ModularPowerProgress in PreH9.
  unfold ModularPower.
  assert (b = 0) by lia.
  subst b.
  simpl in PreH9.
  rewrite Z.mul_1_r in PreH9.
  rewrite Z.mod_small in PreH9 by lia.
  exact PreH9.
Qed.

Lemma proof_of_modular_power_return_wit_1 : modular_power_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_power_return_wit_1_split_goal_1.
Qed. 
