From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P046_1082C_multi_subject_competition_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P046_1082C_multi_subject_competition_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P046_1082C_multi_subject_competition_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_8_split_goal_1 : solver_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 j ltac:(lia)) as Hraw_skill.
  pose proof (PreH16 j ltac:(lia)) as Hsorted_skill.
  destruct Hraw_skill as [_ Hraw_skill].
  destruct Hsorted_skill as [_ [_ Hskill_upper]].
  rewrite Hraw_skill.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_8_split_goal_2 : solver_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 j ltac:(lia)) as Hraw_skill.
  pose proof (PreH16 j ltac:(lia)) as Hsorted_skill.
  destruct Hraw_skill as [_ Hraw_skill].
  destruct Hsorted_skill as [_ [Hskill_lower _]].
  rewrite Hraw_skill.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH16 j ltac:(lia)) as Hraw_skill.
  pose proof (PreH17 j ltac:(lia)) as Hsorted_skill.
  pose proof (PreH25 (j + 1 - i) ltac:(lia)) as Htotal_bound.
  destruct Hraw_skill as [_ Hraw_skill].
  destruct Hsorted_skill as [_ [_ Hskill_upper]].
  destruct Htotal_bound as [_ Htotal_upper].
  rewrite Hraw_skill.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH25 (j + 1 - i) ltac:(lia)) as Htotal_bound.
  destruct Htotal_bound as [Htotal_nonnegative _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (repeat_Z 0 (n_pre + 1)) raw_sorted_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre (2 * n_pre) raw_sorted_2).
    cancel (Int64Array.full retval (n_pre + 1)
      (repeat_Z 0 (n_pre + 1))).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; intros; eauto; lia).
    all: try (dump_pre_spatial; intros k Hk; apply PreH11; lia).
    all: try (dump_pre_spatial; intros k Hk;
      eapply candidate_bounds_permutation__initialization; eauto; lia).
    + dump_pre_spatial.
      unfold CompetitionOuterState.
      refine (conj _ (conj _ (conj _ _))).
      * unfold SubjectBoundary.
        split.
        -- lia.
        -- left. reflexivity.
      * unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        lia.
      * unfold repeat_Z.
        rewrite Znth_repeat by lia.
        reflexivity.
      * intros k Hk.
        unfold repeat_Z.
        rewrite Znth_repeat by lia.
        rewrite completed_contribution_at_zero__initialization.
        reflexivity.
    + dump_pre_spatial.
      intros k Hk.
      unfold repeat_Z.
      rewrite Znth_repeat by lia.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre (2 * n_pre) raw_sorted_2).
    cancel (Int64Array.full total (n_pre + 1) totals_2).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; intros; eauto; lia).
    all: try (dump_pre_spatial;
      eapply competition_inner_from_outer_empty__initialization; eauto).
    dump_pre_spatial.
    intros k Hk.
    specialize (PreH19 k ltac:(lia)).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH16 j ltac:(lia)) as Hjraw.
  pose proof (PreH16 i ltac:(lia)) as Hiraw.
  assert (Hsubject :
      CandidateSubject sorted_2 j = CandidateSubject sorted_2 i).
  { unfold CandidateSubject.
    rewrite <- (Znth_indep sorted_2 j __default__Prod_Z_Z (0, 0)) by lia.
    rewrite <- (Znth_indep sorted_2 i __default__Prod_Z_Z (0, 0)) by lia.
    lia. }
  assert (Hskill :
      Znth (2 * j + 1) raw_sorted_2 0 = CandidateSkill sorted_2 j).
  { unfold CandidateSkill.
    rewrite <- (Znth_indep sorted_2 j __default__Prod_Z_Z (0, 0)) by lia.
    exact (proj2 Hjraw). }
  pose proof (competition_inner_step_positive__inner_update
    sorted_2 i j prefix totals_2 (Znth (2 * j + 1) raw_sorted_2 0)
    PreH24 ltac:(lia) Hsubject Hskill ltac:(lia)) as Hstate_new.
  pose proof PreH24 as Hstate_parts.
  unfold CompetitionInnerState in Hstate_parts.
  destruct Hstate_parts as
      [_ [_ [_ [_ [_ [_ [Htotlen [_ _]]]]]]]].
  pose proof (PreH17 j ltac:(lia)) as Hcandidate_bounds.
  assert (Hskill_bounds :
      -10000 <= Znth (2 * j + 1) raw_sorted_2 0 <= 10000) by lia.
  assert (Hbounds_new : forall k,
      0 <= k <= n_pre ->
      0 <= Znth k
        (replace_Znth (j + 1 - i)
          (Znth (j + 1 - i) totals_2 0 +
           (prefix + Znth (2 * j + 1) raw_sorted_2 0)) totals_2) 0
      <= (j + 1) * 10000).
  { intros k Hk.
    destruct (Z.eq_dec k (j + 1 - i)) as [Heq | Hneq].
    - subst k.
      rewrite Znth_replace_Znth_Same by lia.
      pose proof (PreH25 (j + 1 - i) ltac:(lia)) as Hbefore.
      pose proof (PreH26 (j + 1 - i) ltac:(lia)) as Hbefore_upper.
      lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      pose proof (PreH25 k Hk) as Hbefore.
      lia. }
  assert (Htail_new : forall k,
      j + 1 - i < k <= n_pre ->
      Znth k
        (replace_Znth (j + 1 - i)
          (Znth (j + 1 - i) totals_2 0 +
           (prefix + Znth (2 * j + 1) raw_sorted_2 0)) totals_2) 0
      <= i * 10000).
  { intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia.
    apply PreH26; lia. }
  Exists (replace_Znth (j + 1 - i)
      (Znth (j + 1 - i) totals_2 0 +
       (prefix + Znth (2 * j + 1) raw_sorted_2 0)) totals_2)
    raw_sorted_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH16 j ltac:(lia)) as Hjraw.
  pose proof (PreH16 i ltac:(lia)) as Hiraw.
  assert (Hsubject :
      CandidateSubject sorted_2 j = CandidateSubject sorted_2 i).
  { unfold CandidateSubject.
    rewrite <- (Znth_indep sorted_2 j __default__Prod_Z_Z (0, 0)) by lia.
    rewrite <- (Znth_indep sorted_2 i __default__Prod_Z_Z (0, 0)) by lia.
    lia. }
  assert (Hskill :
      Znth (2 * j + 1) raw_sorted_2 0 = CandidateSkill sorted_2 j).
  { unfold CandidateSkill.
    rewrite <- (Znth_indep sorted_2 j __default__Prod_Z_Z (0, 0)) by lia.
    exact (proj2 Hjraw). }
  pose proof (competition_inner_step_nonpositive__inner_update
    sorted_2 i j prefix totals_2 (Znth (2 * j + 1) raw_sorted_2 0)
    PreH24 ltac:(lia) Hsubject Hskill PreH1) as Hstate_new.
  pose proof (PreH17 j ltac:(lia)) as Hcandidate_bounds.
  assert (Hskill_bounds :
      -10000 <= Znth (2 * j + 1) raw_sorted_2 0 <= 10000) by lia.
  assert (Hbounds_new : forall k,
      0 <= k <= n_pre ->
      0 <= Znth k totals_2 0 <= (j + 1) * 10000).
  { intros k Hk.
    pose proof (PreH25 k Hk) as Hbefore.
    lia. }
  assert (Htail_new : forall k,
      j + 1 - i < k <= n_pre ->
      Znth k totals_2 0 <= i * 10000).
  { intros k Hk. apply PreH26; lia. }
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = n_pre) by lia.
  assert (Hboundary : SubjectBoundary sorted_2 j).
  {
    unfold SubjectBoundary.
    split.
    - rewrite PreH12. lia.
    - right; left. rewrite PreH12. exact Hj.
  }
  assert (Houter : CompetitionOuterState sorted_2 j totals_2).
  {
    eapply (competition_outer_from_inner_boundary__outer_advance
      sorted_2 i j prefix totals_2).
    - lia.
    - exact Hboundary.
    - exact PreH22.
  }
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre (2 * n_pre) raw_sorted_2).
    cancel (Int64Array.full total (n_pre + 1) totals_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH15 i ltac:(lia)) as Hiraw.
  pose proof (PreH15 j ltac:(lia)) as Hjraw.
  assert (Hchange :
    CandidateSubject sorted_2 j <> CandidateSubject sorted_2 i).
  {
    intro Heq.
    apply PreH1.
    unfold CandidateSubject in Heq.
    rewrite (proj1 Hiraw), (proj1 Hjraw).
    rewrite (Znth_indep sorted_2 j __default__Prod_Z_Z (0, 0)) by
      (rewrite PreH13; lia).
    rewrite (Znth_indep sorted_2 i __default__Prod_Z_Z (0, 0)) by
      (rewrite PreH13; lia).
    exact Heq.
  }
  assert (Hij : i < j).
  {
    assert (i <> j).
    { intro Heq. subst j. apply Hchange. reflexivity. }
    lia.
  }
  pose proof PreH23 as Hinner_parts.
  unfold CompetitionInnerState in Hinner_parts.
  destruct Hinner_parts as
    [Hstart [Hstart_done [Hdone [Hstart_boundary
    [Hsame [Hprefix [Hlength [Hzero Htotals]]]]]]]].
  assert (Hboundary : SubjectBoundary sorted_2 j).
  {
    eapply (subject_boundary_from_sorted_change__outer_advance
      sorted_2 i j).
    - exact PreH12.
    - lia.
    - rewrite PreH13. lia.
    - exact (Hsame Hij).
    - exact Hchange.
  }
  assert (Houter : CompetitionOuterState sorted_2 j totals_2).
  {
    eapply (competition_outer_from_inner_boundary__outer_advance
      sorted_2 i j prefix totals_2).
    - exact Hij.
    - exact Hboundary.
    - exact PreH23.
  }
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - cancel (IntArray.full a_pre (2 * n_pre) raw_sorted_2).
    cancel (Int64Array.full total (n_pre + 1) totals_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  pose proof PreH18 as Houter_parts.
  unfold CompetitionOuterState in Houter_parts.
  destruct Houter_parts as [_ [Hlen [Hzero _]]].
  rewrite PreH12 in Hlen.
  pose proof
    (competition_answer_prefix_zero__answer_scan
       totals_2 n_pre ltac:(lia) Hlen Hzero) as Hanswer.
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH23 k ltac:(lia)) as Htotal_bounds.
  pose proof
    (competition_answer_prefix_step_take__answer_scan
       totals_2 n_pre k answer PreH22 ltac:(lia) ltac:(lia)) as Hanswer.
  assert (Hanswer' :
    CompetitionAnswerPrefix totals_2 n_pre ((k + 1) - 1)
      (Znth k totals_2 0)).
  { replace ((k + 1) - 1) with k by lia. exact Hanswer. }
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (competition_answer_prefix_step_keep__answer_scan
       totals_2 n_pre k answer PreH22 ltac:(lia) ltac:(lia)) as Hanswer.
  assert (Hanswer' :
    CompetitionAnswerPrefix totals_2 n_pre ((k + 1) - 1) answer).
  { replace ((k + 1) - 1) with k by lia. exact Hanswer. }
  Exists totals_2 raw_sorted_2 sorted_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists raw_sorted sorted.
  split_pure_spatial.
  - cancel (IntArray.full a_pre (2 * n_pre) raw_sorted).
  - split_pures.
    + dump_pre_spatial.
      eapply competition_full_state_implies_spec__final_result
        with (sorted := sorted) (totals := totals).
      * rewrite PreH12. lia.
      * exact PreH10.
      * exact PreH11.
      * rewrite PreH12. exact PreH20.
      * rewrite PreH12. replace (k - 1) with n_pre in PreH21 by lia.
        exact PreH21.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. intros i Hi. apply PreH14. exact Hi.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
Qed.
