From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_goal.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope sac.

Lemma proof_of_create_hashtbl_return_wit_1_split_goal_spatial : create_hashtbl_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (store_map_empty store_uint).
  apply derivable1_sepcon_emp_r.
Qed.

Lemma proof_of_create_hashtbl_return_wit_1 : create_hashtbl_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_create_hashtbl_return_wit_1_split_goal_spatial.
Qed.

