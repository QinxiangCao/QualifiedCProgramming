From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.modular_inverse Require Import modular_inverse_goal.
From SimpleC.EE.LLM_bench.Algorithms.modular_inverse Require Import modular_inverse_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib.
Local Open Scope sac.

Lemma proof_of_modular_inverse_return_wit_1_split_goal_1 : modular_inverse_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularInverse.
  exists (a_pre * Z.quot x_v modulus_pre + y_v - a_pre).
  pose proof (Z.quot_rem x_v modulus_pre ltac:(lia)) as Hquot_rem.
  nia.
Qed.

Lemma proof_of_modular_inverse_return_wit_1_split_goal_2 : modular_inverse_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_abs x_v modulus_pre ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_inverse_return_wit_1_split_goal_1.
  - Goal_apply proof_of_modular_inverse_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_modular_inverse_return_wit_2_split_goal_1 : modular_inverse_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularInverse.
  exists (a_pre * Z.quot x_v modulus_pre + y_v).
  pose proof (Z.quot_rem x_v modulus_pre ltac:(lia)) as Hquot_rem.
  nia.
Qed.

Lemma proof_of_modular_inverse_return_wit_2_split_goal_2 : modular_inverse_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_abs x_v modulus_pre ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_inverse_return_wit_2_split_goal_1.
  - Goal_apply proof_of_modular_inverse_return_wit_2_split_goal_2.
Qed. 

