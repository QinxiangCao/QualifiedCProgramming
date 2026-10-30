From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import delta_goal.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import delta_proof_auto.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_delta_return_wit_1 : delta_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_delta_return_wit_2 : delta_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
