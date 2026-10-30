From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P030_1113B_sasha_and_magnetic_machines_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P030_1113B_sasha_and_magnetic_machines_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH4 i ltac:(lia)) as Hsource.
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv_nonnegative : 0 <= Znth i values 0 / x) by
    (apply Z.div_pos; lia).
  assert (Hdiv_upper : Znth i values 0 / x <= Znth i values 0) by
    (apply Z.div_le_upper_bound; nia).
  pose proof
    (prefix_summary_total_dominates_source_and_least__arithmetic_safety
       values n_pre sum mn i PreH2 PreH5
       (fun k Hk => proj1 (PreH4 k Hk)) PreH6 ltac:(lia)) as Htotal.
  assert (Hsum_upper : sum <= 5000000) by nia.
  assert (Hproduct_upper : mn * x <= 10000) by nia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH4 i ltac:(lia)) as Hsource.
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv_nonnegative : 0 <= Znth i values 0 / x) by
    (apply Z.div_pos; lia).
  pose proof
    (prefix_summary_total_dominates_source_and_least__arithmetic_safety
       values n_pre sum mn i PreH2 PreH5
       (fun k Hk => proj1 (PreH4 k Hk)) PreH6 ltac:(lia)) as Htotal.
  assert (Hproduct_nonnegative : 0 <= mn * x) by nia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(specialize (PreH4 i ltac:(lia)); nia).
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(specialize (PreH4 i ltac:(lia)); nia).
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH4 i ltac:(lia)) as Hsource.
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv_upper : Znth i values 0 / x <= Znth i values 0) by
    (apply Z.div_le_upper_bound; nia).
  pose proof
    (prefix_summary_total_dominates_source_and_least__arithmetic_safety
       values n_pre sum mn i PreH2 PreH5
       (fun k Hk => proj1 (PreH4 k Hk)) PreH6 ltac:(lia)) as Htotal.
  assert (Hsum_upper : sum <= 5000000) by nia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH4 i ltac:(lia)) as Hsource.
  rewrite Z.quot_div_nonneg by lia.
  assert (Hdiv_nonnegative : 0 <= Znth i values 0 / x) by
    (apply Z.div_pos; lia).
  pose proof
    (prefix_summary_total_dominates_source_and_least__arithmetic_safety
       values n_pre sum mn i PreH2 PreH5
       (fun k Hk => proj1 (PreH4 k Hk)) PreH6 ltac:(lia)) as Htotal.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(specialize (PreH5 i ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(specialize (PreH5 i ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(specialize (PreH5 i ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(specialize (PreH5 i ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(specialize (PreH4 i ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(specialize (PreH4 i ltac:(lia)); lia).
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixSummary, TotalPower, sublist.
  split; [lia |].
  split; [reflexivity |].
  left.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH3.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (prefix_summary_step_lt__prefix_summary values i sum mn);
    try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hvalue : 1 <= Znth i values 0 <= 100).
  { apply PreH5. lia. }
  assert (Hi_positive : 0 < i).
  {
    destruct (Z.eq_dec i 0) as [Hi_zero | Hi_nonzero]; [subst i | lia].
    unfold PrefixSummary in PreH13.
    destruct PreH13 as [_ [_ [[_ Hmn] | [Hpositive _]]]].
    - subst mn. lia.
    - lia.
  }
  apply (prefix_summary_step_ge__prefix_summary values i sum mn);
    try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SearchMinimum, MaxMin.min_value_of_subset,
    MaxMin.min_object_of_subset,
    EnumeratedCost.
  exists sum.
  split.
  - split.
    + left. reflexivity.
    + intros cost Hcost.
      destruct Hcost as [Hsame |
        [source [factor [Hsource [Hfactor [Hdivisor [Hbefore Hformula]]]]]]].
      * subst cost. lia.
      * destruct Hbefore as [Hsource_before | [Hsource_here Hfactor_before]];
          lia.
  - reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  unfold PrefixSummary in PreH12.
  destruct PreH12 as [_ [_ [[Hempty _] |
    [Hnonempty [least_index [Hleast_index [Hleast_value Hminimum]]]]]]].
  - lia.
  - assert (Hrange : 1 <= Znth least_index values 0 <= 100).
    { apply PreH4. lia. }
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH5 i ltac:(lia)) as Hvalue_i.
  rewrite Z.quot_div_nonneg in PreH1 |- * by lia.
  apply search_minimum_extend_factor_lower__search_transitions
    with (answer := answer); auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH5 i ltac:(lia)) as Hvalue_i.
  rewrite Z.quot_div_nonneg by lia.
  apply enumerated_candidate_nonnegative__search_transitions
    with (a := values) (i := i) (x := x).
  - exact PreH3.
  - subst n_pre. lia.
  - exact PreH14.
  - intros k Hk. specialize (PreH5 k Hk). lia.
  - subst n_pre. exact PreH7.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH5 i ltac:(lia)) as Hvalue_i.
  rewrite Z.quot_div_nonneg in PreH1 by lia.
  apply search_minimum_extend_factor_upper__search_transitions
    with (answer := answer); auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_3_split_goal_1 : solver_entail_wit_5_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply search_minimum_skip_nondivisor__search_transitions; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply search_minimum_advance_source__search_transitions with (x := x); auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  assert (Hi : i = Zlength values) by lia.
  subst i.
  unfold PrefixSummary in PreH6.
  destruct PreH6 as [_ [Hsum [Hzero | Hnonempty]]].
  - destruct Hzero as [Hlength_zero _]. lia.
  - destruct Hnonempty as [_ [least_index
      [Hleast_index [Hleast Hleast_bound]]]].
    assert (Hsublist : sublist 0 (Zlength values) values = values).
    { pose proof (sublist_app_exact1 values (@nil Z)) as H.
      rewrite app_nil_r in H. exact H. }
    rewrite Hsublist in Hsum.
    assert (Hpositive : forall k,
      0 <= k < Zlength values -> 1 <= Znth k values 0).
    { intros k Hk. specialize (PreH4 k Hk). lia. }
    unfold SearchMinimum, MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in PreH15.
    destruct PreH15 as [chosen [[Hchosen Hminimum] Hanswer]].
    cbn in Hanswer, Hminimum. subst chosen.
    destruct
      (enumerated_cost_realizable_or_no_better__final_spec
        values sum mn answer least_index Hsum Hleast_index Hleast Hchosen)
      as [best_after [Hbest_transfer Hbest_upper]].
    assert (Hanswer_lower : answer <= TotalPower best_after).
    { destruct
        (magnetic_transfer_dominated_by_enumeration__final_spec
          values sum mn least_index best_after Hsum Hleast_index Hleast
          Hpositive Hleast_bound Hbest_transfer)
        as [candidate [Hcandidate Hcandidate_upper]].
      specialize (Hminimum candidate Hcandidate).
      cbn in Hminimum. lia. }
    unfold Spec, MaxMin.min_value_of_subset, MaxMin.min_object_of_subset.
    exists best_after. split.
    + split.
      * exact Hbest_transfer.
      * intros other Hother.
        destruct
          (magnetic_transfer_dominated_by_enumeration__final_spec
            values sum mn least_index other Hsum Hleast_index Hleast
            Hpositive Hleast_bound Hother)
          as [candidate [Hcandidate Hcandidate_upper]].
        specialize (Hminimum candidate Hcandidate).
        cbn in Hminimum. lia.
    + lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
