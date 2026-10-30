From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple2_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple2_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.

Lemma proof_of_swap_int_pair_return_wit_1 : swap_int_pair_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed. 
