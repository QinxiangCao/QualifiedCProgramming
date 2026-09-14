Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.modular_power Require Import modular_power_goal.
From SimpleC.EE.LLM_bench.Algorithms.modular_power Require Import modular_power_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.
Local Open Scope sac.

Lemma proof_of_modular_power_entail_wit_1_split_goal_1 : modular_power_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularPowerProgress.
  rewrite Z.mul_1_l.
  reflexivity.
Qed.

Lemma proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_power_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_1 : modular_power_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.rem_mod_nonneg in PreH1 by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  rewrite zdiv_equiv by lia.
  eapply modular_power_progress_odd_step__loop_transitions; eauto; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_2 : modular_power_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * a) modulus_pre ltac:(lia)) as Hresult_mod.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_3 : modular_power_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * a) modulus_pre ltac:(lia)) as Hresult_mod.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_4 : modular_power_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_5 : modular_power_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_6 : modular_power_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * a) modulus_pre ltac:(lia)) as Hresult_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_7 : modular_power_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (result * a) modulus_pre ltac:(lia)) as Hresult_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_8 : modular_power_entail_wit_2_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  pose proof
    (Z.div_le_upper_bound b 2 b ltac:(lia) ltac:(nia)) as Hhalf_le.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_9 : modular_power_entail_wit_2_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_10 : modular_power_entail_wit_2_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_1_split_goal_11 : modular_power_entail_wit_2_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
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
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_7.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_8.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_9.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_10.
  - Goal_apply proof_of_modular_power_entail_wit_2_1_split_goal_11.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_1 : modular_power_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
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
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_3 : modular_power_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_4 : modular_power_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_5 : modular_power_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_6 : modular_power_entail_wit_2_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  pose proof
    (Z.div_le_upper_bound b 2 b ltac:(lia) ltac:(nia)) as Hhalf_le.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_7 : modular_power_entail_wit_2_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zdiv_equiv by lia.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_8 : modular_power_entail_wit_2_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.rem_mod_nonneg by lia.
  pose proof
    (Z.mod_pos_bound (a * a) modulus_pre ltac:(lia)) as Ha_mod.
  lia.
Qed.

Lemma proof_of_modular_power_entail_wit_2_2_split_goal_9 : modular_power_entail_wit_2_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
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
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_5.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_6.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_7.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_8.
  - Goal_apply proof_of_modular_power_entail_wit_2_2_split_goal_9.
Qed.

Lemma proof_of_modular_power_return_wit_1_split_goal_1 : modular_power_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularPowerProgress in PreH17.
  unfold ModularPower.
  assert (b = 0) by lia.
  subst b.
  simpl in PreH17.
  rewrite Z.mul_1_r in PreH17.
  rewrite Z.mod_small in PreH17 by lia.
  exact PreH17.
Qed.

Lemma proof_of_modular_power_return_wit_1 : modular_power_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_modular_power_return_wit_1_split_goal_1.
Qed.
