From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

Require Import AUXLib.MonotonicList.
From SumLib Require Import ZRange.

Ltac inns_math :=
  try solve [assumption | reflexivity];
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  try lia;
  repeat match goal with
  | H : Forall ?P ?xs |- _ => rewrite (Forall_Znth P 0 xs) in H
  | |- Forall ?P ?xs => apply (proj2 (Forall_Znth P 0 xs))
  end;
  try solve [assumption | congruence | intuition lia];
  try solve [intros; match goal with H : forall j : Z, _ -> _ |- _ => apply H; lia end];
  try solve [intros; match goal with |- context[Znth ?i ?xs 0] =>
    repeat match goal with H : forall j : Z, _ -> _ |- _ =>
      let K := fresh "AtIndex" in pose proof (H i ltac:(lia)) as K; clear H
    end; lia
  end];
  try nia.

(* Current generated split goals; the witnesses below use the whole-goal route. *)
Lemma proof_of_initCounts_entail_wit_1_split_goal_1 : initCounts_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_1_split_goal_2 : initCounts_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_1_split_goal_3 : initCounts_entail_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_1_split_goal_4 : initCounts_entail_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_2_split_goal_1 : initCounts_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_2_split_goal_2 : initCounts_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_2_split_goal_3 : initCounts_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_2_split_goal_4 : initCounts_entail_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_1_split_goal_1 : copyCounts_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_1 : copyCounts_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_2 : copyCounts_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_3 : copyCounts_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_4 : copyCounts_entail_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_copyCounts_return_wit_1_split_goal_1 : copyCounts_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_1_split_goal_spatial : countChoosingInns_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_1 : countChoosingInns_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_2 : countChoosingInns_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_3 : countChoosingInns_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_4 : countChoosingInns_entail_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_5 : countChoosingInns_entail_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_6 : countChoosingInns_entail_wit_3_split_goal_6.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_7 : countChoosingInns_entail_wit_3_split_goal_7.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_8 : countChoosingInns_entail_wit_3_split_goal_8.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_9 : countChoosingInns_entail_wit_3_split_goal_9.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_10 : countChoosingInns_entail_wit_3_split_goal_10.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_11 : countChoosingInns_entail_wit_3_split_goal_11.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_8_split_goal_1 : countChoosingInns_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_countChoosingInns_entail_wit_8_split_goal_spatial : countChoosingInns_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  Exists (@nil Z) (@nil Z).
  sep_apply (IntArray.undef_full_to_undef_seg seen_pre k_pre).
  sep_apply (IntArray.undef_full_to_undef_seg good_pre k_pre).
  repeat rewrite IntArray.seg_empty.
  split_pure_spatial; [repeat cancel; try reflexivity |].
  split_pures; dump_pre_spatial; first [constructor | reflexivity | lia].
Qed.

Lemma proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Proof.
  LLM_pre_process ltac:(assumption).
  Exists (good_l_2 ++ 0 :: nil) (seen_l_2 ++ 0 :: nil).
  split_pure_spatial; [repeat cancel; try reflexivity |].
  assert (Hgood : Forall (eq 0) (good_l_2 ++ (0 :: nil))).
  { apply Forall_app; split; [assumption | repeat constructor]. }
  assert (Hseen : Forall (eq 0) (seen_l_2 ++ (0 :: nil))).
  { apply Forall_app; split; [assumption | repeat constructor]. }
  split_pures; dump_pre_spatial; try solve [assumption | lia];
    rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcopy : InnsCopiedPrefix seen_l good_old good_old 0 k_pre).
  { apply CopyCountsPrefix_zero; assumption. }
  Exists good_old.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcopy : InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre) by inns_math.
  assert (Hnext : InnsCopiedPrefix seen_l good_old
    (replace_Znth i (Znth i seen_l 0) good_cur_2) (i + 1) k_pre).
  { eapply CopyCountsPrefix_step_replace; eauto; lia. }
  assert (Hseen : (Zlength seen_l = k_pre /\ Forall (fun value : Z => 0 <= value <= 200000) seen_l)) by inns_math.
  assert (Hgood : (Zlength good_cur_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= 200000) good_cur_2))
    by inns_math.
  assert (Hupdated : (Zlength (replace_Znth i (Znth i seen_l 0) good_cur_2) = k_pre /\ Forall (fun value : Z
    => 0 <= value <= 200000) (replace_Znth i (Znth i seen_l 0) good_cur_2))).
  { destruct Hseen as [Hseen_len Hseen_bounds].
    destruct Hgood as [Hgood_len Hgood_bounds].
    pose proof (proj1 (Forall_Znth _ 0 seen_l) Hseen_bounds i ltac:(lia)) as Hseen_at_i.
    cbn in Hseen_at_i.
    split.
    - rewrite Zlength_replace_Znth. exact Hgood_len.
    - eapply replace_Znth_preserves_bounds with
        (xs := good_cur_2) (i := i) (v := Znth i seen_l 0)
        (k := k_pre) (lo := 0) (hi := 200000); eauto; lia. }
  Exists (replace_Znth i (Znth i seen_l 0) good_cur_2).
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcopy : InnsCopiedPrefix seen_l good_old good_cur i k_pre) by inns_math.
  assert (Heq : good_cur = seen_l).
  { eapply CopyCountsPrefix_full_eq; eauto; lia. }
  subst good_cur. cancel.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2.
Proof.
  LLM_pre_process ltac:(assumption). subst answer.
  assert (Hseen : (Zlength seen_l_2 = k_pre /\ Forall (eq 0) seen_l_2)) by inns_math.
  assert (Hgood : (Zlength good_l_2 = k_pre /\ Forall (eq 0) good_l_2)) by inns_math.
  assert (Hstate : InnsPrefixCounts colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2).
  { eapply CountsZeroFull_to_ChoosingPrefixState_zero; eauto. }
  Exists good_l_2 seen_l_2.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial;
      first [assumption | lia |
        eapply Forall_impl with (P := eq 0);
          [intros x Hx; subst x; lia | eassumption]].
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcolor : 0 <= Znth i colors_l 0 < k_pre) by inns_math.
  assert (Hseen : 0 <= Znth (Znth i colors_l 0) seen_l_2 0 <= i) by inns_math.
  assert (Hgood : 0 <= Znth (Znth i colors_l 0) good_l_2 0 <= i) by inns_math.
  Exists good_l_2 seen_l_2.
  split_pure_spatial; [repeat cancel; try reflexivity |].
  split_pures; dump_pre_spatial; inns_math; try int_auto; lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext20 : ((0 <= i <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength seen_l =
    k_pre /\ Forall (fun value : Z => 0 <= value <= i) seen_l) /\ (Zlength good_l_2 = k_pre /\ Forall (fun
    value : Z => 0 <= value <= i) good_l_2)) )) by inns_math.
  assert (Hcontext21 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) by inns_math.
  assert (Hnext_data :
    (0 <= (i + 1) <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength (replace_Znth c (Znth
      c seen_l 0 + 1) seen_l) = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1)) (replace_Znth c (Znth
      c seen_l 0 + 1) seen_l)) /\ (Zlength good_l_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1))
      good_l_2))).
  {
    eapply ChoosingPrefixDataSafe_step_expensive; eauto.
    all: lia.
  }
  assert (Hnext_full_data :
    (0 <= (i + 1) <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength (replace_Znth c (Znth
      c seen_l 0 + 1) seen_l) = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1)) (replace_Znth c (Znth
      c seen_l 0 + 1) seen_l)) /\ (Zlength (replace_Znth c (Znth c seen_l 0 + 1) seen_l) = k_pre /\ Forall
      (fun value : Z => 0 <= value <= (i + 1)) (replace_Znth c (Znth c seen_l 0 + 1) seen_l)))).
  {
    eapply ChoosingPrefixDataSafe_step_affordable_after_copy; eauto.
    all: lia.
  }
  assert (Hnext_state :
    InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c seen_l 0)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)).
  {
    eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer) (good := good_l_2) (c := c);
      try exact Hcontext20; try exact Hcontext21; try exact PreH2;
      try reflexivity; try lia.
    all: lia.
  }
  assert (Hnext_bound :
    0 <= answer + Znth c seen_l 0 <= 19999900000).
  {
    eapply ChoosingPrefixState_answer_bound
      with (seen := replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (good := replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (n := n_pre); eauto.
    all: lia.
  }
  pose proof Hnext_data as Hnext_data_parts.
  destruct Hnext_data_parts as
    [Hnext_limit [_ [Hnext_seen_safe Hnext_good_safe]]].
  assert (Hnext_seen_200 :
    (Zlength (replace_Znth c (Znth c seen_l 0 + 1) seen_l) = k_pre /\ Forall (fun value : Z => 0 <= value <=
      200000) (replace_Znth c (Znth c seen_l 0 + 1) seen_l))).
  {
    eapply CountArraySafe_weaken_limit; [exact Hnext_seen_safe |].
    all: lia.
  }
  assert (Hnext_good_200 : (Zlength good_l_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= 200000) good_l_2)).
  {
    eapply CountArraySafe_weaken_limit; [exact Hnext_good_safe |].
    all: lia.
  }
  subst c.
  Exists good_l_2 seen_l
    (replace_Znth (Znth i colors_l 0) (Znth (Znth i colors_l 0) seen_l 0 + 1) seen_l).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
  replace (answer + Znth (Znth i colors_l 0) seen_l 0 -
    Znth (Znth i colors_l 0) seen_l 0) with answer by lia.
  assumption.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext1 : ((Zlength seen_next_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= 200000)
    seen_next_2) )) by inns_math.
  assert (Hcontext14 : ((0 <= i <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength seen_l =
    k_pre /\ Forall (fun value : Z => 0 <= value <= i) seen_l) /\ (Zlength good_l = k_pre /\ Forall (fun value
    : Z => 0 <= value <= i) good_l)) )) by inns_math.
  assert (Hcontext15 : ((0 <= (i + 1 ) <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength
    seen_next_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1 )) seen_next_2) /\ (Zlength good_l =
    k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1 )) good_l)) )) by inns_math.
  assert (Hcontext16 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l
    good_l )) by inns_math.
  assert (Hcontext17 : ((Zlength seen_next_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= 200000)
    seen_next_2) )) by inns_math.
  assert (Hcontext18 : ((Zlength good_l = k_pre /\ Forall (fun value : Z => 0 <= value <= 200000) good_l) ))
    by inns_math.
  assert (Hstate : InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre
    answer seen_next_2 seen_next_2).
  { eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer - Znth c seen_l 0)
           (seen := seen_l) (good := good_l) (c := c);
      try exact Hcontext14; try exact Hcontext16; try exact PreH1;
      try exact PreH23; try lia.
    all: lia. }
  assert (Hdata : (0 <= (i + 1) <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength
    seen_next_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1)) seen_next_2) /\ (Zlength
    seen_next_2 = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1)) seen_next_2))).
  { subst seen_next_2.
    eapply ChoosingPrefixDataSafe_step_affordable_after_copy; eauto.
    all: lia. }
  Exists seen_next_2.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext20 : ((0 <= i <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength seen_l_2
    = k_pre /\ Forall (fun value : Z => 0 <= value <= i) seen_l_2) /\ (Zlength good_l = k_pre /\ Forall (fun
    value : Z => 0 <= value <= i) good_l)) )) by inns_math.
  assert (Hcontext21 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) by inns_math.
  assert (Hnext_data :
    (0 <= (i + 1) <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength (replace_Znth c (Znth
      c seen_l_2 0 + 1) seen_l_2) = k_pre /\ Forall (fun value : Z => 0 <= value <= (i + 1)) (replace_Znth c
      (Znth c seen_l_2 0 + 1) seen_l_2)) /\ (Zlength good_l = k_pre /\ Forall (fun value : Z => 0 <= value <=
      (i + 1)) good_l))).
  {
    eapply ChoosingPrefixDataSafe_step_expensive; eauto.
    all: lia.
  }
  assert (Hnext_state :
    InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c good_l 0)
      (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l).
  {
    eapply ChoosingPrefixState_step_expensive
      with (old_answer := answer) (c := c);
      try exact Hcontext20; try exact Hcontext21; try exact PreH2;
      try reflexivity; try lia.
    all: lia.
  }
  assert (Hnext_bound :
    0 <= answer + Znth c good_l 0 <= 19999900000).
  {
    eapply ChoosingPrefixState_answer_bound
      with (seen := replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2)
           (good := good_l) (n := n_pre); eauto.
    all: lia.
  }
  subst c.
  Exists good_l seen_l_2
    (replace_Znth (Znth i colors_l 0) (Znth (Znth i colors_l 0) seen_l_2 0 + 1) seen_l_2).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
  replace (answer + Znth (Znth i colors_l 0) good_l 0 -
    Znth (Znth i colors_l 0) good_l 0) with answer by lia.
  try rewrite PreH34. assumption.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8.
Proof.
  LLM_pre_process ltac:(assumption).
  assert (Hcontext7 : ((0 <= i <= Zlength colors_l /\ Zlength costs_l = Zlength colors_l /\ (Zlength seen_l =
    k_pre /\ Forall (fun value : Z => 0 <= value <= i) seen_l) /\ (Zlength good_l = k_pre /\ Forall (fun value
    : Z => 0 <= value <= i) good_l)) )) by inns_math.
  assert (Hcontext8 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) by inns_math.
  assert (Hanswer : (InnsPairAnswer colors_l costs_l n_pre p_pre answer)).
  { unfold InnsPairAnswer. replace n_pre with i by lia.
    exact (proj1 Hcontext8). }
  sep_apply (IntArray.full_to_undef_full (&("seen")) k_pre seen_l).
  sep_apply (IntArray.full_to_undef_full (&("good")) k_pre good_l).
  sep_apply (IntArray.undef_full_to_undef_seg (&("seen")) k_pre).
  sep_apply (IntArray.undef_full_to_undef_seg (&("good")) k_pre).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("seen")) 0 k_pre 50); try lia.
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("good")) 0 k_pre 50); try lia.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1.
Proof.
  LLM_pre_process ltac:(assumption).
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("seen")) k_pre 50); try lia.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("good")) k_pre 50); try lia.
  sep_apply (IntArray.undef_seg_to_undef_full (&("seen")) 0 k_pre).
  sep_apply (IntArray.undef_seg_to_undef_full (&("good")) 0 k_pre).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  split_pure_spatial; [repeat cancel; try reflexivity |].
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.
