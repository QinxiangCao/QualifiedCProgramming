From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P036_1201C_maximum_median_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P036_1201C_maximum_median_proof_auto.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P036_1201C_maximum_median_lib.
Local Open Scope sac.

Lemma proof_of_cost_safety_wit_4_split_goal_1 : cost_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    specialize (PreH9 i ltac:(lia)); destruct PreH9; nia).
  specialize (PreH9 i ltac:(lia)).
  assert (0 <= n_pre ÷ 2) by (apply Z.quot_pos; lia).
  dump_pre_spatial.
  assert (i - n_pre ÷ 2 <= 200000) by lia.
  assert ((i - n_pre ÷ 2) * 2000000000 <= 400000000000000) by nia.
  assert (need <= 400000000000000) by lia.
  assert (m_pre - Znth i sorted 0 <= 2000000000) by lia.
  lia.
Qed.

Lemma proof_of_cost_safety_wit_4_split_goal_2 : cost_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_cost_safety_wit_4 : cost_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_cost_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_cost_entail_wit_1_split_goal_1 : cost_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    apply median_cost_prefix_init__cost_prefix).
  rewrite quot_div_pos__cost_prefix by lia.
  rewrite <- PreH5.
  apply median_cost_prefix_init__cost_prefix.
Qed.

Lemma proof_of_cost_entail_wit_1_split_goal_2 : cost_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_le_upper_bound; lia.
Qed.

Lemma proof_of_cost_entail_wit_1_split_goal_3 : cost_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_pos; lia.
Qed.

Lemma proof_of_cost_entail_wit_1_split_goal_4 : cost_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(assumption).
  exact (PreH7 j H).
Qed.

Lemma proof_of_cost_entail_wit_1 : cost_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cost_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_cost_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_cost_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_cost_entail_wit_2_split_goal_1 : cost_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    eapply median_cost_prefix_step_lt__cost_prefix; eauto; lia).
  apply median_cost_prefix_step_lt__cost_prefix.
  - split.
    + rewrite PreH7.
      rewrite <- quot_div_pos__cost_prefix by lia.
      exact PreH11.
    + rewrite PreH7.
      exact PreH2.
  - lia.
  - exact PreH15.
Qed.

Lemma proof_of_cost_entail_wit_2 : cost_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_cost_entail_wit_3_1_split_goal_1 : cost_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    eapply median_cost_prefix_at_end__cost_prefix; eauto; lia).
  eapply median_cost_prefix_at_end__cost_prefix with (i := i).
  - lia.
  - exact PreH14.
Qed.

Lemma proof_of_cost_entail_wit_3_1_split_goal_2 : cost_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(assumption).
  exact (PreH8 j H).
Qed.

Lemma proof_of_cost_entail_wit_3_1 : cost_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_cost_entail_wit_3_1_split_goal_2.
Qed.

Lemma proof_of_cost_entail_wit_3_2_split_goal_1 : cost_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(
    eapply median_cost_prefix_zero_tail__cost_prefix; eauto; lia).
  eapply median_cost_prefix_zero_tail__cost_prefix with (i := i).
  - exact PreH8.
  - split.
    + rewrite PreH7.
      rewrite <- quot_div_pos__cost_prefix by lia.
      exact PreH11.
    + rewrite PreH7.
      exact PreH2.
  - lia.
  - exact PreH15.
Qed.

Lemma proof_of_cost_entail_wit_3_2_split_goal_2 : cost_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(assumption).
  exact (PreH9 j H).
Qed.

Lemma proof_of_cost_entail_wit_3_2 : cost_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_cost_entail_wit_3_2_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hnonneg : 0 <= (hi - lo + 1) / 2).
  { apply Z.div_pos; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hpos : 1 <= (hi - lo + 1) / 2).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_lt; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply Z.quot_pos; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (permutation_preserves_zindexed_bounds__solver_sort
      values l1 n_pre 1 1000000000 PreH1 PreH9 PreH8) as [_ Hbounds].
  apply Hbounds.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (permutation_preserves_zindexed_bounds__solver_sort
      values l1 n_pre 1 1000000000 PreH1 PreH9 PreH8) as [Hlength _].
  exact Hlength.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH11, PreH12 by lia.
  unfold MedianSearchBounds. split.
  - unfold ReachMedian. exists values.
    split; [reflexivity |].
    split; [intros; lia |].
    split; [lia |].
    unfold MedianOf. exists sorted. split.
    + apply Permutation_sym. exact PreH9.
    + split; [exact PreH10 |].
      rewrite <- PreH6. reflexivity.
  - intros candidate Hcandidate Hreach.
    pose proof (median_raise_cost_le_of_reach__search_semantics
      values sorted k_pre candidate PreH9 PreH10 Hreach) as Hcost.
    assert (Hhalf : 0 <= Zlength sorted / 2 < Zlength sorted).
    { rewrite PreH7. exact (conj PreH11 PreH12). }
    assert (Hupper : forall j, 0 <= j < Zlength sorted ->
      Znth j sorted 0 <= 1000000000).
    { intros j Hj. rewrite PreH7 in Hj.
      exact (proj2 (PreH8 j Hj)). }
    pose proof (median_raise_cost_above_upper__search_semantics
      sorted candidate Hhalf Hupper ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH8 j H).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  unfold MedianSearchBounds in PreH17 |- *.
  destruct PreH17 as [HloReach HhiExclude]. split.
  - assert (Hhalf : 0 <= Zlength sorted_2 / 2 < Zlength sorted_2).
    { rewrite PreH10. split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    assert (Hbase : Znth (Zlength sorted_2 / 2) sorted_2 0 <= lo).
    { eapply reach_median_ge_original__search_semantics; eauto. }
    eapply median_raise_cost_reaches__search_semantics; eauto.
    + assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia). lia.
    + rewrite <- PreH2. exact PreH1.
  - exact HhiExclude.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_2 : solver_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_3 : solver_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= (hi - lo + 1) / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_3_1_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_3_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg in PreH2 by lia.
  unfold MedianSearchBounds in PreH17 |- *.
  destruct PreH17 as [HloReach HhiExclude]. split.
  - exact HloReach.
  - intros candidate Hcandidate Hreach.
    pose proof (median_raise_cost_le_of_reach__search_semantics
      values sorted_2 k_pre candidate PreH12 PreH13 Hreach) as HcandidateCost.
    pose proof (median_raise_cost_monotone__search_semantics sorted_2
      (lo + (hi - lo + 1) / 2) candidate ltac:(lia)) as HmonoCost.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_2 : solver_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_3 : solver_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv : 1 <= (hi - lo + 1) / 2).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_3_2_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (hi = lo) by lia.
  subst hi.
  unfold MedianSearchBounds in PreH15.
  unfold Spec, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  destruct PreH15 as [Hreachable Hmaximal].
  exists lo.
  split.
  - split.
    + exact Hreachable.
    + intros candidate Hcandidate.
      destruct (Z_le_gt_dec candidate lo) as [Hle | Hgt].
      * exact Hle.
      * exfalso.
        apply (Hmaximal candidate ltac:(lia) Hcandidate).
  - reflexivity.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_1 : solver_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hnonneg : 0 <= (hi - lo + 1) / 2).
  { apply Z.div_pos; lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_2 : solver_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure_split_goal_3 : solver_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_3_pure_split_goal_3.
Qed.
