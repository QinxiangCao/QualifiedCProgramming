From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P054_1776F_train_splitting_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P054_1776F_train_splitting_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P054_1776F_train_splitting_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (PreH10 i ltac:(int_auto)) as Hends.
  destruct Hends as [[[Hu Hv] Hequ] Heqv].
  destruct PreH14 as [Hlen Hprefix].
  destruct (Z.eq_dec (Znth i v_data 0) (Znth i u_data 0)) as [Heq | Hneq].
  - rewrite Heq.
    rewrite Znth_replace_Znth_Same by int_auto.
    specialize (PreH15 (Znth i u_data 0) ltac:(int_auto)).
    int_auto.
  - rewrite Znth_replace_Znth_Diff by int_auto.
    specialize (PreH15 (Znth i v_data 0) ltac:(int_auto)).
    int_auto.
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof (PreH10 i ltac:(int_auto)) as Hends.
  destruct Hends as [[[Hu Hv] Hequ] Heqv].
  destruct PreH14 as [Hlen Hprefix].
  destruct (Z.eq_dec (Znth i v_data 0) (Znth i u_data 0)) as [Heq | Hneq].
  - rewrite Heq.
    rewrite Znth_replace_Znth_Same by int_auto.
    specialize (PreH15 (Znth i u_data 0) ltac:(int_auto)).
    int_auto.
  - rewrite Znth_replace_Znth_Diff by int_auto.
    specialize (PreH15 (Znth i v_data 0) ltac:(int_auto)).
    int_auto.
Qed.

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold repeat_Z.
  rewrite Znth_repeat.
  int_auto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold DegreePrefix.
  split.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by int_auto.
    reflexivity.
  - intros x Hx.
    unfold repeat_Z.
    rewrite Znth_repeat.
    unfold EdgeDegree, sublist.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (PreH11 k H) as [Hu Hv].
  pose proof (PreH6 k ltac:(int_auto)) as [Hru Hrv].
  repeat split; try assumption; int_auto.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH10 i ltac:(lia)).
  destruct PreH10 as [[_ Hu] Hv].
  assert (Hz : Znth i e __default__Prod_Z_Z = Znth i e (0, 0)).
  { apply Znth_indep. lia. }
  rewrite Hz in Hu, Hv.
  rewrite Hu, Hv.
  apply degree_prefix_step__degree_update_exit; auto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH14 as [_ Hdegree].
  specialize (Hdegree x H).
  replace i with m_pre in Hdegree by lia.
  rewrite PreH7 in Hdegree.
  rewrite sublist_self in Hdegree by reflexivity.
  rewrite Hdegree.
  split.
  - unfold EdgeDegree. lia.
  - apply edge_degree_simple_bound__degree_update_exit; auto.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PivotPrefix.
  intros.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace m_pre with i by lia.
  exact PreH14.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
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
  unfold PivotPrefix in *.
  intros x Hx.
  destruct (Z_lt_ge_dec x i) as [Hlt | Hge].
  - apply PreH17. lia.
  - assert (x = i) by lia.
    subst x. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PivotChoice, PivotPrefix in *.
  right.
  split.
  - lia.
  - intros x Hx.
    apply PreH16.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH11.
  lia.
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
  unfold PivotChoice.
  left.
  split.
  - lia.
  - split.
    + exact PreH1.
    + exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH12.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PivotColorPrefix.
  split.
  - reflexivity.
  - intros j Hj.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_3 : solver_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PivotChoice in PreH13.
  destruct PreH13 as [[Hbounds Hrest] | [Heq Hprefix]].
  - lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pivot_color_prefix_incident_step__pivot_color; auto.
  destruct (PreH15 i ltac:(lia)) as [[[_ _] Hu_edge] Hv_edge].
  rewrite (Znth_indep e i __default__Prod_Z_Z (0, 0)) in Hu_edge, Hv_edge
    by lia.
  right.
  rewrite <- Hv_edge.
  exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pivot_color_prefix_incident_step__pivot_color; auto.
  destruct (PreH14 i ltac:(lia)) as [[[_ _] Hu_edge] Hv_edge].
  rewrite (Znth_indep e i __default__Prod_Z_Z (0, 0)) in Hu_edge, Hv_edge
    by lia.
  left.
  rewrite <- Hu_edge.
  exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_3_split_goal_1 : solver_entail_wit_7_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply pivot_color_prefix_nonincident_step__pivot_color; auto.
  - destruct (PreH15 i ltac:(lia)) as [[[_ _] Hu_edge] Hv_edge].
    rewrite (Znth_indep e i __default__Prod_Z_Z (0, 0)) in Hu_edge, Hv_edge
      by lia.
    intro Hfst.
    apply PreH2.
    rewrite Hu_edge.
    exact Hfst.
  - destruct (PreH15 i ltac:(lia)) as [[[_ _] Hu_edge] Hv_edge].
    rewrite (Znth_indep e i __default__Prod_Z_Z (0, 0)) in Hu_edge, Hv_edge
      by lia.
    intro Hsnd.
    apply PreH1.
    rewrite Hv_edge.
    exact Hsnd.
Qed.

Lemma proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CompleteColorPrefix.
  split; [reflexivity |].
  left. split; [reflexivity |].
  intros j Hj. lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10. assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PivotChoice in PreH13.
  destruct PreH13 as [[Hpivot _] | [Hpivot _]]; lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply complete_color_prefix_later_incident_step__complete_color_incident.
  - lia.
  - subst first. exact PreH21.
  - specialize (PreH14 i ltac:(lia)) as [[[_ _] Hu] Hv].
    assert (Heq : Znth i e __default__Prod_Z_Z = Znth i e (0, 0)).
    { apply Znth_indep. lia. }
    unfold Incident. left. rewrite <- Heq. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply complete_color_prefix_first_incident_step__complete_color_incident.
  - lia.
  - subst first. exact PreH21.
  - specialize (PreH14 i ltac:(lia)) as [[[_ _] Hu] Hv].
    assert (Heq : Znth i e __default__Prod_Z_Z = Znth i e (0, 0)).
    { apply Znth_indep. lia. }
    unfold Incident. left. rewrite <- Heq. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_3_split_goal_1 : solver_entail_wit_9_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply complete_color_prefix_first_incident_step__complete_color_incident.
  - lia.
  - subst first. exact PreH22.
  - specialize (PreH15 i ltac:(lia)) as [[[_ _] Hu] Hv].
    assert (Heq : Znth i e __default__Prod_Z_Z = Znth i e (0, 0)).
    { apply Znth_indep. lia. }
    unfold Incident. right. rewrite <- Heq. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_4_split_goal_1 : solver_entail_wit_9_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply complete_color_prefix_later_incident_step__complete_color_incident.
  - lia.
  - subst first. exact PreH22.
  - specialize (PreH15 i ltac:(lia)) as [[[_ _] Hu] Hv].
    assert (Heq : Znth i e __default__Prod_Z_Z = Znth i e (0, 0)).
    { apply Znth_indep. lia. }
    unfold Incident. right. rewrite <- Heq. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_5_split_goal_1 : solver_entail_wit_9_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply complete_color_prefix_nonincident_step__complete_color_nonincident.
  - lia.
  - lia.
  - unfold Incident.
    pose proof (PreH14 i ltac:(lia)) as Hedge.
    destruct Hedge as [[[[_ _] [_ _]] Hu] Hv].
    assert (Hdefault : Znth i e (0, 0) = Znth i e __default__Prod_Z_Z).
    { apply Znth_indep. lia. }
    intros [Hfst | Hsnd].
    + apply PreH2.
      rewrite Hu.
      rewrite <- Hdefault.
      exact Hfst.
    + apply PreH1.
      rewrite Hv.
      rewrite <- Hdefault.
      exact Hsnd.
  - rewrite <- PreH20.
    exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_9_5 : solver_entail_wit_9_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_5_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_6_split_goal_1 : solver_entail_wit_9_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply complete_color_prefix_nonincident_step__complete_color_nonincident.
  - lia.
  - lia.
  - unfold Incident.
    pose proof (PreH14 i ltac:(lia)) as Hedge.
    destruct Hedge as [[[[_ _] [_ _]] Hu] Hv].
    assert (Hdefault : Znth i e (0, 0) = Znth i e __default__Prod_Z_Z).
    { apply Znth_indep. lia. }
    intros [Hfst | Hsnd].
    + apply PreH2.
      rewrite Hu.
      rewrite <- Hdefault.
      exact Hfst.
    + apply PreH1.
      rewrite Hv.
      rewrite <- Hdefault.
      exact Hsnd.
  - rewrite <- PreH20.
    exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_9_6 : solver_entail_wit_9_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia. subst i.
  pose proof PreH19 as Hcolor_copy.
  destruct Hcolor_copy as [Hlabelslen _].
  assert (Hvalid : ValidTrainPlan n_pre e 2 labels).
  {
    apply (pivot_coloring_valid__final_pivot_two_color
      n_pre e degrees_2 pivot labels).
    - exact PreH14.
    - rewrite <- PreH10. exact PreH15.
    - lia.
    - exact PreH16.
    - rewrite <- PreH10. exact PreH19.
  }
  assert (Hspec : Spec n_pre e (kinds, labels)).
  { unfold Spec. simpl. rewrite PreH3. exact Hvalid. }
  Exists degrees_2 labels.
  rewrite IntArray.undef_seg_empty.
  sep_apply_l_atomic (IntArray.seg_to_full colors_pre 0 m_pre labels).
  replace (colors_pre + 0 * sizeof(INT)) with colors_pre by lia.
  replace (m_pre - 0) with m_pre by lia.
  split_pure_spatial.
  - cancel (IntArray.full u_pre m_pre u_data).
    cancel (IntArray.full v_pre m_pre v_data).
    cancel (IntArray.full colors_pre m_pre labels).
    cancel (IntArray.full deg n_pre degrees_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia. subst i.
  subst kinds. subst pivot. subst first.
  assert (Hlabels_len : Zlength labels = m_pre).
  { unfold CompleteColorPrefix in PreH19. tauto. }
  assert (Hvalid : Spec n_pre e (3, labels)).
  {
    unfold Spec; simpl.
    eapply complete_coloring_valid__final_complete_three_color; eauto.
    - rewrite <- PreH9. exact PreH14.
    - rewrite <- PreH9. exact PreH19.
  }
  Exists degrees_2 labels.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full colors_pre 0 m_pre labels).
    IntArray.ArraySimplify.
    replace (colors_pre + 0 * sizeof(INT)) with colors_pre by lia.
    replace (m_pre - 0) with m_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia. subst i.
  subst kinds. subst pivot. subst first.
  assert (Hlabels_len : Zlength labels = m_pre).
  { unfold CompleteColorPrefix in PreH19. tauto. }
  assert (Hvalid : Spec n_pre e (3, labels)).
  {
    unfold Spec; simpl.
    eapply complete_coloring_valid__final_complete_three_color; eauto.
    - rewrite <- PreH9. exact PreH14.
    - rewrite <- PreH9. exact PreH19.
  }
  Exists degrees_2 labels.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full colors_pre 0 m_pre labels).
    IntArray.ArraySimplify.
    replace (colors_pre + 0 * sizeof(INT)) with colors_pre by lia.
    replace (m_pre - 0) with m_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.
