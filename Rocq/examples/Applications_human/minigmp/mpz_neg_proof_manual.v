From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minigmp Require Import mpz_neg_goal.
From SimpleC.EE.Applications_human.minigmp Require Import mpz_neg_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Require Import SimpleC.EE.Applications_human.minigmp.mpz_neg_lib.
Local Open Scope sac.

Lemma proof_of_mpz_neg_safety_wit_1_split_goal_1 : mpz_neg_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (store_int_range (&( v_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap).
  Intros_p Hcap.
  dump_pre_spatial.
  change (-2147483648 <= cap <= 2147483647) in Hcap.
  destruct (Z.abs_spec size) as [[Hsgn Habs] | [Hsgn Habs]].
  all: lia.

Qed.

Lemma proof_of_mpz_neg_safety_wit_1 : mpz_neg_safety_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_neg_safety_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpz_neg_return_wit_1_split_goal_1 : mpz_neg_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_neg_return_wit_1_split_goal_2 : mpz_neg_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial. apply same_sign_opp_compact_abs; assumption.
Qed.

Lemma proof_of_mpz_neg_return_wit_1_split_goal_spatial : mpz_neg_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite !Z.abs_opp, PreH4.
  rewrite UIntArray.undef_seg_empty.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact ptr (Zabs m) (Zabs size) PreH1).
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact retval_2 (Zabs m) (Zabs size) PreH1).
  cancel.
Qed.

Lemma proof_of_mpz_neg_return_wit_1 : mpz_neg_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mpz_neg_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mpz_neg_return_wit_1_split_goal_1.
  - Goal_apply proof_of_mpz_neg_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_mpz_neg_partial_solve_wit_2_pure_split_goal_1 : mpz_neg_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_neg_partial_solve_wit_2_pure : mpz_neg_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_neg_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_neg_partial_solve_wit_5_pure_split_goal_1 : mpz_neg_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_mpz_neg_partial_solve_wit_5_pure : mpz_neg_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_neg_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_neg_default_entail_exported : mpz_neg_default_entail_exported.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists n_exported m_exported.
  cancel (store_Z u_pre n_exported).
  cancel (store_Z v_pre m_exported).
  apply_sepcon_adjoint.
  cancel.
  cancel (store_Z u_pre (-m_exported)).
  cancel emp.
Qed.

