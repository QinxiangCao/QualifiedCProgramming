From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P056_630I_parking_lot_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P056_630I_parking_lot_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P056_630I_parking_lot_lib.
Local Open Scope sac.

Lemma proof_of_power4_safety_wit_5_split_goal_1 : power4_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_power4_safety_wit_5_split_goal_2 : power4_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_power4_safety_wit_5 : power4_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power4_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_power4_safety_wit_5_split_goal_2.
Qed. 

Lemma proof_of_power4_entail_wit_1 : power4_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec e_pre (-1)) as [Heq | Hneq].
  - Left.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; lia.
  - Right.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial;
        rewrite ?Z.sub_diag, ?Z.pow_0_r; lia.
Qed. 

Lemma proof_of_power4_entail_wit_2_split_goal_1 : power4_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst r.
  assert (Hexp_nonnegative : 0 <= e_pre - e) by lia.
  assert (Hexp_upper : e_pre - e <= 25) by lia.
  assert (Hpow_upper : Z.pow 4 (e_pre - e) <= Z.pow 4 25).
  { apply Z.pow_le_mono_r; lia. }
  change (Z.pow 4 (e_pre - e) <= 1125899906842624) in Hpow_upper.
  change (Z.pow 4 (e_pre - e) * 4 <= 1125899906842624 * 4).
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_power4_entail_wit_2_split_goal_2 : power4_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_power4_entail_wit_2_split_goal_3 : power4_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst r.
  replace (e_pre - (e - 1)) with (Z.succ (e_pre - e)) by lia.
  rewrite Z.pow_succ_r by lia.
  ring.
Qed.

Lemma proof_of_power4_entail_wit_2 : power4_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power4_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_power4_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_power4_entail_wit_2_split_goal_3.
Qed. 

Lemma proof_of_power4_return_wit_2_split_goal_1 : power4_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (e = 0) by lia.
  subst e.
  rewrite Z.sub_0_r in PreH5.
  exact PreH5.
Qed.

Lemma proof_of_power4_return_wit_2 : power4_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_power4_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hn : n_pre = 3) by lia.
  subst n_pre.
  subst retval_2.
  subst retval.
  cbn.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst retval_2.
  subst retval.
  assert (Hpow1 : 4 ^ (n_pre - 3) <= 4 ^ 27).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hpow2 : 4 ^ (n_pre - 4) <= 4 ^ 26).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hnon1 : 0 <= 4 ^ (n_pre - 3)).
  { apply Z.pow_nonneg; lia. }
  assert (Hnon2 : 0 <= 4 ^ (n_pre - 4)).
  { apply Z.pow_nonneg; lia. }
  cbn in Hpow1, Hpow2.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_7_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_9_split_goal_1 : solver_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst retval.
  assert (Hpow : 4 ^ (n_pre - 4) <= 4 ^ 26).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hnon : 0 <= 4 ^ (n_pre - 4)).
  { apply Z.pow_nonneg; lia. }
  cbn in Hpow.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_9_split_goal_2 : solver_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_9_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hn : n_pre = 3) by lia.
  subst n_pre.
  subst retval.
  cbn.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_15_split_goal_1 : solver_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst retval.
  assert (Hpow : 4 ^ (n_pre - 3) <= 4 ^ 27).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hnon : 0 <= 4 ^ (n_pre - 3)).
  { apply Z.pow_nonneg; lia. }
  cbn in Hpow.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_15_split_goal_2 : solver_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_15_split_goal_2.
Qed. 

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    subst retval; subst retval_2;
    apply Spec_closed_form__solver_result; lia).
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    subst retval; subst retval_2;
    assert (n_pre = 3) by lia; subst n_pre;
    apply Spec_closed_form__solver_result; lia).
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed. 
