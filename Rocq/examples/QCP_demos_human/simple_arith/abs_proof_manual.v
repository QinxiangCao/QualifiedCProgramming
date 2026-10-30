From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.QCP_demos_human.simple_arith Require Import abs_goal.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
