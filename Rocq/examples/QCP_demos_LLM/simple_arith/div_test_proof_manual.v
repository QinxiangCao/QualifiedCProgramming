From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import div_test_goal.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import PDiv_lib.
Local Open Scope sac.

Lemma proof_of_div_test_return_wit_3 : div_test_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
  unfold Pos_Div.
  subst c_pre. simpl. lia.
Qed.

Lemma proof_of_div_test_return_wit_2 : div_test_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
  unfold Pos_Div.
  destruct (Z.eq_dec c_pre 0) ; try lia.
  destruct (Z_lt_ge_dec (a_pre * b_pre ÷ c_pre) 0) ; try lia.
Qed. 

Lemma proof_of_div_test_return_wit_1 : div_test_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
  unfold Pos_Div.
  destruct (Z.eq_dec c_pre 0) ; try lia.
  destruct (Z_lt_ge_dec (a_pre * b_pre ÷ c_pre) 0) ; try lia.
Qed.
