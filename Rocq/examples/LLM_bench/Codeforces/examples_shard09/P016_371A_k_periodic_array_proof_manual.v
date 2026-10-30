From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P016_371A_k_periodic_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P016_371A_k_periodic_array_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P016_371A_k_periodic_array_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  unfold PrefixCost, ProcessedChangeCost.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(idtac).
  Exists 0.
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    dump_pre_spatial.
    unfold ResidueScan.
    rewrite !residue_value_count_initial_zero__initialization by lia.
    auto.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH3 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as [len_factor Hlen_factor].
  pose proof (residue_scan_step__residue_accounting
    k_pre r i q_2 values ones twos PreH4 ltac:(lia) PreH15 PreH14
    ltac:(lia) PreH21) as Hstep.
  pose proof ((proj1 Hstep) PreH1) as Hscan_next.
  pose proof (residue_scan_bounds__residue_accounting
    k_pre r (i + k_pre) values (ones + 1) twos Hscan_next)
    as (Hones_next & Htwos_next & Hcount_next).
  assert (Hqfactor : q_2 + 1 <= len_factor) by nia.
  assert (Hnext_bound : i + k_pre <= n_pre + r) by nia.
  Exists (q_2 + 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi0 : 0 <= i) by nia.
  assert (Hvalue : Znth i values 0 = 2).
  {
    specialize (PreH8 i ltac:(lia)).
    destruct PreH8; [contradiction | assumption].
  }
  pose proof PreH3 as Hpre.
  unfold Pre in Hpre.
  destruct Hpre as [len_factor Hlen_factor].
  pose proof (residue_scan_step__residue_accounting
    k_pre r i q_2 values ones twos PreH4 ltac:(lia) PreH15 PreH14
    ltac:(lia) PreH21) as Hstep.
  pose proof ((proj2 Hstep) Hvalue) as Hscan_next.
  pose proof (residue_scan_bounds__residue_accounting
    k_pre r (i + k_pre) values ones (twos + 1) Hscan_next)
    as (Hones_next & Htwos_next & Hcount_next).
  assert (Hqfactor : q_2 + 1 <= len_factor) by nia.
  assert (Hnext_bound : i + k_pre <= n_pre + r) by nia.
  Exists (q_2 + 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixCost in *.
  rewrite processed_change_cost_succ__residue_accounting by lia.
  unfold ResidueChangeCost.
  destruct (residue_scan_complete__residue_accounting
    k_pre r i values ones twos ltac:(lia) PreH21) as [Hones Htwos].
  rewrite <- Hones, <- Htwos.
  rewrite Z.min_l by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ones with (Z.min ones twos) by (rewrite Z.min_l; lia).
  pose proof (processed_change_cost_partial_bound__residue_accounting
    k_pre r i values changes ones twos PreH3 ltac:(lia) PreH13
    ltac:(lia) PreH21) as Hbound.
  rewrite <- PreH7 in Hbound. exact Hbound.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixCost in *.
  rewrite processed_change_cost_succ__residue_accounting by lia.
  unfold ResidueChangeCost.
  destruct (residue_scan_complete__residue_accounting
    k_pre r i values ones twos ltac:(lia) PreH21) as [Hones Htwos].
  rewrite <- Hones, <- Htwos.
  rewrite Z.min_r by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace twos with (Z.min ones twos) by (rewrite Z.min_r; lia).
  pose proof (processed_change_cost_partial_bound__residue_accounting
    k_pre r i values changes ones twos PreH3 ltac:(lia) PreH13
    ltac:(lia) PreH21) as Hbound.
  rewrite <- PreH7 in Hbound. exact Hbound.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_3 : solver_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hr : r = k_pre) by lia.
  subst r.
  apply prefix_cost_implies_spec__final_result.
  - lia.
  - lia.
  - exact PreH2.
  - intros j Hj. apply PreH7. lia.
  - exact PreH12.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
