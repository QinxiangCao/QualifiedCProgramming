Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn Require Import container_with_most_water_nlogn_goal.
From SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn Require Import container_with_most_water_nlogn_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib.
Local Open Scope sac.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply merge_prefix_init__merge_core; eauto; lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_1 : mergeHeightIndexRunsNLogN_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply (merge_prefix_take_left__merge_core
    source_h source_i dest0_h dest0_i dest_h_2 dest_i_2
    left_pre middle_pre right_pre i j
    (left_pre + (i - left_pre) + (j - middle_pre))).
  - exact PreH5.
  - lia.
  - lia.
  - exact PreH8.
  - exact PreH9.
  - exact PreH10.
  - exact PreH11.
  - exact PreH3.
  - exact PreH13.
  - exact PreH14.
  - lia.
  - reflexivity.
  - rewrite <- PreH16. exact PreH19.
  - right. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 : mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 : mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply (merge_prefix_take_right__merge_core
    source_h source_i dest0_h dest0_i dest_h_2 dest_i_2
    left_pre middle_pre right_pre i j
    (left_pre + (i - left_pre) + (j - middle_pre))).
  - exact PreH5.
  - lia.
  - lia.
  - exact PreH8.
  - exact PreH9.
  - exact PreH10.
  - exact PreH11.
  - exact PreH12.
  - exact PreH13.
  - exact PreH2.
  - lia.
  - reflexivity.
  - rewrite <- PreH16. exact PreH19.
  - right. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 : mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_4 : mergeHeightIndexRunsNLogN_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hnext :
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      (replace_Znth output (Znth i source_h 0) dest_h_2)
      (replace_Znth output (Znth i source_i 0) dest_i_2)
      left_pre middle_pre right_pre (i + 1) j (output + 1)).
  {
    eapply (merge_prefix_take_left__merge_core
      source_h source_i dest0_h dest0_i dest_h_2 dest_i_2
      left_pre middle_pre right_pre i j output).
    - exact PreH3.
    - lia.
    - lia.
    - exact PreH6.
    - exact PreH7.
    - exact PreH9.
    - exact PreH10.
    - exact PreH1.
    - exact PreH12.
    - exact PreH13.
    - lia.
    - exact PreH15.
    - exact PreH18.
    - left. exact PreH8.
  }
  Right.
  Exists (replace_Znth output (Znth i source_i 0) dest_i_2)
         (replace_Znth output (Znth i source_h 0) dest_h_2).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try (rewrite Zlength_replace_Znth; lia); lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 : mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  subst i.
  eapply (merge_prefix_take_right__merge_core
    source_h source_i dest0_h dest0_i dest_h_2 dest_i_2
    left_pre middle_pre right_pre middle_pre j
    (left_pre + (middle_pre - left_pre) + (j - middle_pre))).
  - exact PreH3.
  - lia.
  - lia.
  - exact PreH6.
  - exact PreH7.
  - exact PreH9.
  - lia.
  - lia.
  - exact PreH12.
  - exact PreH1.
  - lia.
  - lia.
  - rewrite <- PreH15. exact PreH18.
  - left. reflexivity.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 : mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 : mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_entail_wit_6 : mergeHeightIndexRunsNLogN_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 : mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  subst i.
  assert (j = right_pre) by lia. subst j.
  assert (output = right_pre) by lia. subst output.
  eapply (merge_prefix_finish__merge_core
    source_h source_i dest0_h dest0_i dest_h_2 dest_i_2
    left_pre middle_pre right_pre).
  - exact PreH3.
  - lia.
  - lia.
  - exact PreH6.
  - exact PreH7.
  - exact PreH9.
  - lia.
  - lia.
  - lia.
  - rewrite <- H at 3. exact PreH18.
Qed.

Lemma proof_of_mergeHeightIndexRunsNLogN_return_wit_1 : mergeHeightIndexRunsNLogN_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 : sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  dump_pre_spatial.
  assert (Hhalf_le :
    Z.quot (right_pre - left_pre) 2 <= right_pre - left_pre).
  { apply Z.quot_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 : sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (Hhalf_pos : 0 <= (right_pre - left_pre) / 2).
  { apply Z.div_pos; lia. }
  lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_safety_wit_3 : sortHeightIndexRangeNLogN_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_entail_wit_1 : sortHeightIndexRangeNLogN_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  prop_apply_p
    (IntArray.full_Zlength bufferHeight_pre count_pre buffer_h_2).
  prop_apply_p
    (IntArray.full_Zlength bufferIndex_pre count_pre buffer_i_2).
  Intros_p Hbuffer_h_len.
  Intros_p Hbuffer_i_len.
  assert (Hquot_div :
    Z.quot (right_pre - left_pre) 2 = (right_pre - left_pre) / 2).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hhalf_pos : 0 < Z.quot (right_pre - left_pre) 2).
  { rewrite Hquot_div.
    assert (1 <= (right_pre - left_pre) / 2).
    { apply Z.div_le_lower_bound; lia. }
    lia. }
  assert (Hhalf_lt : Z.quot (right_pre - left_pre) 2 < right_pre - left_pre).
  { apply Z.quot_lt_upper_bound; lia. }
  pose proof
    (range_sort_left_desc__sort_recursion
      work0_h work0_i work_h_2 work_i_2 work_h_3 work_i_3
      left_pre (left_pre + Z.quot (right_pre - left_pre) 2) right_pre
      PreH2 PreH1) as Hleft_desc.
  pose proof PreH2 as Hleft_result.
  pose proof PreH1 as Hright_result.
  unfold HeightIndexRangeSortResultNLogN in Hleft_result, Hright_result.
  destruct Hleft_result as
    [Hleft_before_len [Hleft_after_len [Hleft0 [Hleft_mid
      [Hleft_result_len [Hsame_left [Hleft_perm Hleft_desc_result]]]]]]].
  destruct Hsame_left as [Hmid_h_len [Hmid_i_len _]].
  destruct Hright_result as
    [Hright_before_len [Hright_after_len [Hmid0 [Hmid_right
      [Hright_result_len [Hsame_right [Hright_perm Hright_desc]]]]]]].
  destruct Hsame_right as [Hwork_h_len [Hwork_i_len _]].
  Exists buffer_i_2 buffer_h_2 work_i_3 work_h_3 work_i_2 work_h_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_entail_wit_2 : sortHeightIndexRangeNLogN_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  prop_apply_p (IntArray.full_Zlength bufferHeight_pre count_pre dest_h).
  prop_apply_p (IntArray.full_Zlength bufferIndex_pre count_pre dest_i).
  Intros_p Hdest_h_len.
  Intros_p Hdest_i_len.
  pose proof PreH1 as Hmerge.
  unfold HeightIndexRangeMergeResultNLogN in Hmerge.
  destruct Hmerge as
    [Hleft0 [Hleft_middle [Hmiddle_right [Hright_len
      [Hmerge_perm [Hmerge_desc Hmerge_outside]]]]]].
  Exists buffer_h_2 buffer_i_2 dest_i dest_h work_i_2 work_h_2
    work_mid_i_2 work_mid_h_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_entail_wit_3 : sortHeightIndexRangeNLogN_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hcopy :
    CopyHeightIndexPrefixNLogN
      buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h_2 work_i_2
      left_pre right_pre left_pre).
  { unfold CopyHeightIndexPrefixNLogN. split.
    - intros p Hp. lia.
    - intros p Hp Houtside. split; reflexivity. }
  Exists buffer0_h_2 buffer0_i_2 buffer_i_2 buffer_h_2
    work_i_2 work_h_2 work_i_2 work_h_2 work_mid_i_2 work_mid_h_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_entail_wit_4 : sortHeightIndexRangeNLogN_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hcopy_next :
    CopyHeightIndexPrefixNLogN
      buffer_h_2 buffer_i_2 work_h_2 work_i_2
      (replace_Znth k (Znth k buffer_h_2 0) work_h1_2)
      (replace_Znth k (Znth k buffer_i_2 0) work_i1_2)
      left_pre right_pre (k + 1)).
  { unfold CopyHeightIndexPrefixNLogN in PreH20 |- *.
    destruct PreH20 as [Hprefix Houtside]. split.
    - intros p Hp. destruct (Z.eq_dec p k) as [-> | Hpk].
      + split; rewrite (Znth_replace_Znth_Same 0) by lia; reflexivity.
      + destruct (Hprefix p ltac:(lia)) as [Hph Hpi].
        split.
        * rewrite (Znth_replace_Znth_Diff 0) by lia. exact Hph.
        * rewrite (Znth_replace_Znth_Diff 0) by lia. exact Hpi.
    - intros p Hp Hrange.
      destruct (Houtside p Hp ltac:(lia)) as [Hph Hpi].
      split.
      + rewrite (Znth_replace_Znth_Diff 0) by lia. exact Hph.
      + rewrite (Znth_replace_Znth_Diff 0) by lia. exact Hpi. }
  Exists buffer0_h_2 buffer0_i_2 buffer_i_2 buffer_h_2
    (replace_Znth k (Znth k buffer_i_2 0) work_i1_2)
    (replace_Znth k (Znth k buffer_h_2 0) work_h1_2)
    work_i_2 work_h_2 work_mid_i_2 work_mid_h_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try rewrite Zlength_replace_Znth; try lia; try assumption.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 : sortHeightIndexRangeNLogN_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  unfold HeightIndexRangeSortResultNLogN,
    SameHeightIndexOutsideNLogN,
    HeightIndexRangePermutationNLogN,
    HeightIndexRangeDescendingNLogN.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split.
  - split; [reflexivity |].
    split; [reflexivity |].
    intros p Hp Houtside. split; reflexivity.
  - split.
    + apply Permutation_refl.
    + split; [lia |].
      split; [lia |].
      split; [lia |].
      intros p q Hp Hpq Hq.
      assert (p = q) by lia. subst q. lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_return_wit_1 : sortHeightIndexRangeNLogN_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 : sortHeightIndexRangeNLogN_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hk : k = right_pre) by lia. subst k.
  assert (HoutH : Zlength work_h1 = Zlength work0_h).
  {
    pose proof PreH17 as Hsort.
    unfold HeightIndexRangeSortResultNLogN,
      SameHeightIndexOutsideNLogN in Hsort.
    intuition lia.
  }
  assert (HoutI : Zlength work_i1 = Zlength work0_i).
  {
    pose proof PreH17 as Hsort.
    unfold HeightIndexRangeSortResultNLogN,
      SameHeightIndexOutsideNLogN in Hsort.
    intuition lia.
  }
  eapply sort_range_after_merge_copy__sort_copy with
    (mid_h := work_mid_h) (mid_i := work_mid_i)
    (work_h := work_h_2) (work_i := work_i_2)
    (buffer0_h := buffer0_h) (buffer0_i := buffer0_i)
    (buffer_h := buffer_h_2) (buffer_i := buffer_i_2)
    (middle := middle); eauto; lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_return_wit_2 : sortHeightIndexRangeNLogN_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hhalf : 0 <= (right_pre - left_pre) / 2).
  { apply Z.div_pos; lia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia. lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hhalf : (right_pre - left_pre) / 2 <= right_pre - left_pre).
  { apply Z.div_le_upper_bound; lia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia. lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  prop_apply_p (IntArray.full_Zlength workHeight_pre count_pre work_h).
  Intros_p Hlen. dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  prop_apply_p (IntArray.full_Zlength workIndex_pre count_pre work_i).
  Intros_p Hlen. dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  prop_apply_p (IntArray.full_Zlength bufferHeight_pre count_pre buffer_h).
  Intros_p Hlen. dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  prop_apply_p (IntArray.full_Zlength bufferIndex_pre count_pre buffer_i).
  Intros_p Hlen. dump_pre_spatial. exact Hlen.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hhalf : 0 <= (right_pre - left_pre) / 2).
  { apply Z.div_pos; lia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia. lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hhalf : (right_pre - left_pre) / 2 <= right_pre - left_pre).
  { apply Z.div_le_upper_bound; lia. }
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia. lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1 : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof PreH18 as Hsort.
  unfold HeightIndexRangeSortResultNLogN in Hsort.
  destruct Hsort as [_ [_ [Hleft0 _]]].
  dump_pre_spatial. exact Hleft0.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2 : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof PreH19 as Hsort.
  unfold HeightIndexRangeSortResultNLogN in Hsort.
  destruct Hsort as [_ [_ [_ [_ [Hright _]]]]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_maxAreaNLogN_safety_wit_8_split_goal_1 : maxAreaNLogN_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH13 as [Hminimum [Hmaximum Hall]].
  pose proof (sorted_index_bounds__max_init
    l sorted_h sorted_i k PreH12 ltac:(lia)) as [Hindex0 Hindexlt].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_safety_wit_8_split_goal_2 : maxAreaNLogN_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH13 as [Hminimum [Hmaximum Hall]].
  pose proof (sorted_index_bounds__max_init
    l sorted_h sorted_i k PreH12 ltac:(lia)) as [Hindex0 Hindexlt].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_safety_wit_8 : maxAreaNLogN_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_maxAreaNLogN_safety_wit_9_split_goal_1 : maxAreaNLogN_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH13 as [Hminimum [Hmaximum Hall]].
  pose proof (sorted_index_bounds__max_init
    l sorted_h sorted_i k PreH12 ltac:(lia)) as [Hindex0 Hindexlt].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_safety_wit_9_split_goal_2 : maxAreaNLogN_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH13 as [Hminimum [Hmaximum Hall]].
  pose proof (sorted_index_bounds__max_init
    l sorted_h sorted_i k PreH12 ltac:(lia)) as [Hindex0 Hindexlt].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_safety_wit_9 : maxAreaNLogN_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_1 : maxAreaNLogN_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  exact (PreH4 p H).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_2 : maxAreaNLogN_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  unfold WorkspacePrefixNLogN.
  split; intros p Hp; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_3 : maxAreaNLogN_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  unfold WorkspacePrefixNLogN.
  split; intros p Hp; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_4 : maxAreaNLogN_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_5 : maxAreaNLogN_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_6 : maxAreaNLogN_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1_split_goal_7 : maxAreaNLogN_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_1 : maxAreaNLogN_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_1_split_goal_7.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2_split_goal_1 : maxAreaNLogN_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (workspace_prefix_snoc__max_init
    l buffer_h_2 buffer_i_2 k PreH9 PreH10 PreH12 ltac:(lia))
    as [_ [_ Hprefix]].
  exact Hprefix.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2_split_goal_2 : maxAreaNLogN_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (workspace_prefix_snoc__max_init
    l work_h_2 work_i_2 k PreH7 PreH8 PreH11 ltac:(lia))
    as [_ [_ Hprefix]].
  exact Hprefix.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2_split_goal_3 : maxAreaNLogN_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2_split_goal_4 : maxAreaNLogN_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2_split_goal_5 : maxAreaNLogN_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2_split_goal_6 : maxAreaNLogN_entail_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_2 : maxAreaNLogN_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_2_split_goal_6.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_3 : maxAreaNLogN_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof
    (workspace_prefix_complete__max_sort_boundary
      l work_h work_i k heightSize_pre
      PreH1 PreH6 PreH7 PreH8 PreH11) as
    [Hwork_h_len [Hwork_i_len Hwork_prefix]].
  pose proof
    (workspace_prefix_complete__max_sort_boundary
      l buffer_h buffer_i k heightSize_pre
      PreH1 PreH6 PreH9 PreH10 PreH12) as
    [Hbuffer_h_len [Hbuffer_i_len Hbuffer_prefix]].
  assert (Hk : k = heightSize_pre) by lia.
  subst k.
  Exists buffer_i buffer_h work_i work_h.
  split_pure_spatial.
  - rewrite Hk.
    rewrite (IntArray.undef_seg_empty bufferIndex_pre heightSize_pre).
    rewrite sepcon_emp_equiv.
    cancel (IntArray.full bufferIndex_pre heightSize_pre buffer_i).
    rewrite (IntArray.undef_seg_empty bufferHeight_pre heightSize_pre).
    rewrite sepcon_emp_equiv.
    cancel (IntArray.full bufferHeight_pre heightSize_pre buffer_h).
    rewrite (IntArray.undef_seg_empty workIndex_pre heightSize_pre).
    rewrite sepcon_emp_equiv.
    cancel (IntArray.full workIndex_pre heightSize_pre work_i).
    rewrite (IntArray.undef_seg_empty workHeight_pre heightSize_pre).
    rewrite sepcon_emp_equiv.
    cancel (IntArray.full workHeight_pre heightSize_pre work_h).
    cancel (IntArray.full height_pre heightSize_pre l).
  - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_4_split_goal_1 : maxAreaNLogN_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  exact (PreH11 p H).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_4_split_goal_2 : maxAreaNLogN_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  exact (full_sort_workspace__max_loop_setup
    l work0_h work0_i work_h work_i heightSize_pre
    PreH4 PreH5 PreH6 PreH9 PreH1).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_4 : maxAreaNLogN_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_5_split_goal_1 : maxAreaNLogN_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  exact (PreH5 p H).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_5_split_goal_2 : maxAreaNLogN_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply processed_maximum_initial__max_loop_setup.
  unfold SortedHeightIndexWorkspaceNLogN in PreH4.
  destruct PreH4 as [[_ [Hlen_i _]] _]. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_5_split_goal_3 : maxAreaNLogN_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  unfold ProcessedIndexEndpointsNLogN.
  split.
  - exists 0. split; [lia | reflexivity].
  - split.
    + exists 0. split; [lia | reflexivity].
    + intros p Hp. assert (p = 0) by lia. subst p. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_5_split_goal_4 : maxAreaNLogN_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h_2 sorted_i 0 PreH4 ltac:(lia)) as [Hidx Heq].
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_5_split_goal_5 : maxAreaNLogN_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h_2 sorted_i 0 PreH4 ltac:(lia)) as [Hidx Heq].
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_5 : maxAreaNLogN_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_5_split_goal_5.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_1 : maxAreaNLogN_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  exact (PreH18 p H).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_2 : maxAreaNLogN_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_3 : maxAreaNLogN_entail_wit_6_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_4 : maxAreaNLogN_entail_wit_6_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_5 : maxAreaNLogN_entail_wit_6_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  specialize (PreH18 (Znth k sorted_i 0) ltac:(lia)).
  rewrite Heq. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_6 : maxAreaNLogN_entail_wit_6_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  specialize (PreH18 (Znth k sorted_i 0) ltac:(lia)).
  rewrite Heq. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_7 : maxAreaNLogN_entail_wit_6_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_8 : maxAreaNLogN_entail_wit_6_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_loop_setup
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hidx Heq].
  exact Heq.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_1 : maxAreaNLogN_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_3.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_4.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_5.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_6.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_7.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_6_1_split_goal_8.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_2 : maxAreaNLogN_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_width_selection
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hindex Hheight].
  assert (Hendpoint_bounds :
    0 <= minimumIndex /\ minimumIndex <= maximumIndex /\
    maximumIndex < heightSize_pre).
  {
    eapply processed_endpoint_bounds__max_width_selection
      with (indices := sorted_i) (k := k).
    - exact PreH16.
    - intros p Hp.
      pose proof (sorted_workspace_lookup__max_width_selection
        l sorted_h sorted_i p PreH15 ltac:(lia)) as [Hpindex _].
      lia.
  }
  pose proof (PreH18 (Znth k sorted_i 0) ltac:(lia)) as Hheight_bounds.
  Right.
  Exists buffer_i_2 buffer_h_2 sorted_h sorted_i.
  split_pure_spatial.
  - cancel (IntArray.full height_pre heightSize_pre l).
    cancel (IntArray.full workHeight_pre heightSize_pre sorted_h).
    cancel (IntArray.full workIndex_pre heightSize_pre sorted_i).
    cancel (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2).
    cancel (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2).
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_3 : maxAreaNLogN_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_width_selection
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hindex Hheight].
  assert (Hendpoint_bounds :
    0 <= minimumIndex /\ minimumIndex <= maximumIndex /\
    maximumIndex < heightSize_pre).
  {
    eapply processed_endpoint_bounds__max_width_selection
      with (indices := sorted_i) (k := k).
    - exact PreH16.
    - intros p Hp.
      pose proof (sorted_workspace_lookup__max_width_selection
        l sorted_h sorted_i p PreH15 ltac:(lia)) as [Hpindex _].
      lia.
  }
  pose proof (PreH18 (Znth k sorted_i 0) ltac:(lia)) as Hheight_bounds.
  Right.
  Exists buffer_i_2 buffer_h_2 sorted_h sorted_i.
  split_pure_spatial.
  - cancel (IntArray.full height_pre heightSize_pre l).
    cancel (IntArray.full workHeight_pre heightSize_pre sorted_h).
    cancel (IntArray.full workIndex_pre heightSize_pre sorted_i).
    cancel (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2).
    cancel (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2).
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_4 : maxAreaNLogN_entail_wit_6_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_width_selection
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hindex Hheight].
  assert (Hendpoint_bounds :
    0 <= minimumIndex /\ minimumIndex <= maximumIndex /\
    maximumIndex < heightSize_pre).
  {
    eapply processed_endpoint_bounds__max_width_selection
      with (indices := sorted_i) (k := k).
    - exact PreH16.
    - intros p Hp.
      pose proof (sorted_workspace_lookup__max_width_selection
        l sorted_h sorted_i p PreH15 ltac:(lia)) as [Hpindex _].
      lia.
  }
  pose proof (PreH18 (Znth k sorted_i 0) ltac:(lia)) as Hheight_bounds.
  Right.
  Exists buffer_i_2 buffer_h_2 sorted_h sorted_i.
  split_pure_spatial.
  - cancel (IntArray.full height_pre heightSize_pre l).
    cancel (IntArray.full workHeight_pre heightSize_pre sorted_h).
    cancel (IntArray.full workIndex_pre heightSize_pre sorted_i).
    cancel (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2).
    cancel (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2).
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_6_5 : maxAreaNLogN_entail_wit_6_5.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (sorted_workspace_lookup__max_width_selection
    l sorted_h sorted_i k PreH15 ltac:(lia)) as [Hindex Hheight].
  assert (Hendpoint_bounds :
    0 <= minimumIndex /\ minimumIndex <= maximumIndex /\
    maximumIndex < heightSize_pre).
  {
    eapply processed_endpoint_bounds__max_width_selection
      with (indices := sorted_i) (k := k).
    - exact PreH16.
    - intros p Hp.
      pose proof (sorted_workspace_lookup__max_width_selection
        l sorted_h sorted_i p PreH15 ltac:(lia)) as [Hpindex _].
      lia.
  }
  pose proof (PreH18 (Znth k sorted_i 0) ltac:(lia)) as Hheight_bounds.
  Left.
  Left.
  Left.
  Left.
  Right.
  Exists buffer_i_2 buffer_h_2 sorted_h sorted_i.
  split_pure_spatial.
  - cancel (IntArray.full height_pre heightSize_pre l).
    cancel (IntArray.full workHeight_pre heightSize_pre sorted_h).
    cancel (IntArray.full workIndex_pre heightSize_pre sorted_i).
    cancel (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2).
    cancel (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2).
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_7_1 : maxAreaNLogN_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  Left.
  Left.
  replace distanceToMaximum with width by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_7_2 : maxAreaNLogN_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  Left.
  Right.
  replace width_2 with distanceToMaximum_2 by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_7_3 : maxAreaNLogN_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  Left.
  Right.
  replace distanceToMaximum with width by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_7_4 : maxAreaNLogN_entail_wit_7_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  Right.
  replace width_2 with distanceToMaximum_2 by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_8_1 : maxAreaNLogN_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  subst width.
  Left. Left.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_8_2 : maxAreaNLogN_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hdist : distanceToMinimum_2 = distanceToMaximum_2) by lia.
  rewrite Hdist in *.
  subst width_2.
  Left. Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_8_3 : maxAreaNLogN_entail_wit_8_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  subst width.
  Left. Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_8_4 : maxAreaNLogN_entail_wit_8_4.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  assert (Hdist : distanceToMinimum_2 = distanceToMaximum_2) by lia.
  rewrite Hdist in *.
  subst width_2.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try nia; try assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_1 : maxAreaNLogN_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH51. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_2 : maxAreaNLogN_entail_wit_9_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMinimum * currentHeight)
    with (Z.max maximumArea (width * currentHeight)).
  2: { rewrite Z.max_r by nia. lia. }
  eapply processed_max_extend__max_endpoint_a.
  - exact PreH48.
  - exact PreH49.
  - exact PreH50.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH26.
  - lia.
  - left. split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_3 : maxAreaNLogN_entail_wit_9_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH48 as [[Hheight_length [Hindex_length Hperm]] Hdescending].
  eapply processed_endpoints_extend__max_endpoint_a.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH49.
  - right. left. repeat split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_1 : maxAreaNLogN_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_1_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_1 : maxAreaNLogN_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH51. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_2 : maxAreaNLogN_entail_wit_9_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMaximum * currentHeight)
    with (Z.max maximumArea (width * currentHeight)).
  2: { rewrite Z.max_r by nia. lia. }
  eapply processed_max_extend__max_endpoint_a.
  - exact PreH48.
  - exact PreH49.
  - exact PreH50.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH26.
  - lia.
  - left. split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_3 : maxAreaNLogN_entail_wit_9_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH48 as [[Hheight_length [Hindex_length Hperm]] Hdescending].
  eapply processed_endpoints_extend__max_endpoint_a.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH49.
  - right. left. repeat split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_2 : maxAreaNLogN_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_2_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_1 : maxAreaNLogN_entail_wit_9_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH53. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_2 : maxAreaNLogN_entail_wit_9_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace maximumArea with (Z.max maximumArea (width * currentHeight)).
  2: { rewrite Z.max_l by nia. reflexivity. }
  eapply processed_max_extend__max_endpoint_a.
  - exact PreH50.
  - exact PreH51.
  - exact PreH52.
  - lia.
  - lia.
  - exact PreH27.
  - exact PreH28.
  - lia.
  - left. split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_3 : maxAreaNLogN_entail_wit_9_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH50 as [[Hheight_length [Hindex_length Hperm]] Hdescending].
  eapply processed_endpoints_extend__max_endpoint_a.
  - lia.
  - lia.
  - exact PreH27.
  - exact PreH51.
  - right. left. repeat split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_3 : maxAreaNLogN_entail_wit_9_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_3_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_1 : maxAreaNLogN_entail_wit_9_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH53. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_2 : maxAreaNLogN_entail_wit_9_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace maximumArea with (Z.max maximumArea (width * currentHeight)).
  2: { rewrite Z.max_l by nia. reflexivity. }
  eapply processed_max_extend__max_endpoint_a.
  - exact PreH50.
  - exact PreH51.
  - exact PreH52.
  - lia.
  - lia.
  - exact PreH27.
  - exact PreH28.
  - lia.
  - left. split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_3 : maxAreaNLogN_entail_wit_9_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH50 as [[Hheight_length [Hindex_length Hperm]] Hdescending].
  eapply processed_endpoints_extend__max_endpoint_a.
  - lia.
  - lia.
  - exact PreH27.
  - exact PreH51.
  - right. left. repeat split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_4 : maxAreaNLogN_entail_wit_9_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_4_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_1 : maxAreaNLogN_entail_wit_9_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH51. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_2 : maxAreaNLogN_entail_wit_9_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMinimum * currentHeight)
    with (Z.max maximumArea (width * currentHeight)).
  2: { rewrite Z.max_r by nia. lia. }
  eapply processed_max_extend__max_endpoint_a.
  - exact PreH48.
  - exact PreH49.
  - exact PreH50.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH26.
  - lia.
  - right. split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_3 : maxAreaNLogN_entail_wit_9_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH48 as [[Hheight_length [Hindex_length Hperm]] Hdescending].
  eapply processed_endpoints_extend__max_endpoint_a.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH49.
  - left. repeat split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_5 : maxAreaNLogN_entail_wit_9_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_5_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_1 : maxAreaNLogN_entail_wit_9_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH51. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_2 : maxAreaNLogN_entail_wit_9_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMaximum * currentHeight)
    with (Z.max maximumArea (width * currentHeight)).
  2: { rewrite Z.max_r by nia. lia. }
  eapply processed_max_extend__max_endpoint_a.
  - exact PreH48.
  - exact PreH49.
  - exact PreH50.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH26.
  - lia.
  - right. split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_3 : maxAreaNLogN_entail_wit_9_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH48 as [[Hheight_length [Hindex_length Hperm]] Hdescending].
  eapply processed_endpoints_extend__max_endpoint_a.
  - lia.
  - lia.
  - exact PreH25.
  - exact PreH49.
  - left. repeat split; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_6 : maxAreaNLogN_entail_wit_9_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_6_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_1 : maxAreaNLogN_entail_wit_9_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH53. exact H.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_2 : maxAreaNLogN_entail_wit_9_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace maximumArea with (Z.max maximumArea (width * currentHeight))
    by (apply Z.max_l; lia).
  eapply (processed_max_extend__max_endpoint_b
    l sorted_h_2 sorted_i_2 k index currentHeight
    minimumIndex maximumIndex maximumArea width).
  - lia.
  - lia.
  - exact PreH50.
  - exact PreH51.
  - exact PreH52.
  - exact PreH27.
  - exact PreH28.
  - exact PreH29.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.abs_eq by lia. lia.
  - left. rewrite Z.abs_eq by lia. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_3 : maxAreaNLogN_entail_wit_9_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (processed_endpoints_extend__max_endpoint_b
    sorted_i_2 k minimumIndex maximumIndex ltac:(lia) PreH51) as Hextend.
  rewrite Z.min_r in Hextend by lia.
  rewrite Z.max_l in Hextend by lia.
  rewrite <- PreH27 in Hextend.
  exact Hextend.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_7 : maxAreaNLogN_entail_wit_9_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_7_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_1 : maxAreaNLogN_entail_wit_9_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH53. exact H.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_2 : maxAreaNLogN_entail_wit_9_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace maximumArea with (Z.max maximumArea (width * currentHeight))
    by (apply Z.max_l; lia).
  eapply (processed_max_extend__max_endpoint_b
    l sorted_h_2 sorted_i_2 k index currentHeight
    minimumIndex maximumIndex maximumArea width).
  - lia.
  - lia.
  - exact PreH50.
  - exact PreH51.
  - exact PreH52.
  - exact PreH27.
  - exact PreH28.
  - exact PreH29.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.abs_eq by lia. lia.
  - right. rewrite Z.abs_eq by lia. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_3 : maxAreaNLogN_entail_wit_9_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (processed_endpoints_extend__max_endpoint_b
    sorted_i_2 k minimumIndex maximumIndex ltac:(lia) PreH51) as Hextend.
  rewrite Z.min_r in Hextend by lia.
  rewrite Z.max_l in Hextend by lia.
  rewrite <- PreH27 in Hextend.
  exact Hextend.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_8 : maxAreaNLogN_entail_wit_9_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_8_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_1 : maxAreaNLogN_entail_wit_9_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35. exact H.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_2 : maxAreaNLogN_entail_wit_9_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMinimum * currentHeight)
    with (Z.max maximumArea (width * currentHeight))
    by (rewrite Z.max_r by nia; nia).
  eapply (processed_max_extend__max_endpoint_b
    l sorted_h_2 sorted_i_2 k index currentHeight
    minimumIndex maximumIndex maximumArea width).
  - lia.
  - lia.
  - exact PreH32.
  - exact PreH33.
  - exact PreH34.
  - exact PreH9.
  - exact PreH10.
  - exact PreH11.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.abs_neq by lia. lia.
  - left. rewrite Z.abs_neq by lia. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_3 : maxAreaNLogN_entail_wit_9_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (processed_endpoints_extend__max_endpoint_b
    sorted_i_2 k minimumIndex maximumIndex ltac:(lia) PreH33) as Hextend.
  rewrite Z.min_l in Hextend by lia.
  rewrite Z.max_l in Hextend by lia.
  exact Hextend.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_9 : maxAreaNLogN_entail_wit_9_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_9_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_1 : maxAreaNLogN_entail_wit_9_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_2 : maxAreaNLogN_entail_wit_9_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_3 : maxAreaNLogN_entail_wit_9_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_10 : maxAreaNLogN_entail_wit_9_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_10_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_1 : maxAreaNLogN_entail_wit_9_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35. exact H.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_2 : maxAreaNLogN_entail_wit_9_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMinimum * currentHeight)
    with (Z.max maximumArea (width * currentHeight))
    by (rewrite Z.max_r by nia; nia).
  eapply (processed_max_extend__max_endpoint_b
    l sorted_h_2 sorted_i_2 k index currentHeight
    minimumIndex maximumIndex maximumArea width).
  - lia.
  - lia.
  - exact PreH32.
  - exact PreH33.
  - exact PreH34.
  - exact PreH9.
  - exact PreH10.
  - exact PreH11.
  - lia.
  - lia.
  - intros x Hx. destruct (Z_le_gt_dec x index).
    + rewrite Z.abs_neq by lia. lia.
    + rewrite Z.abs_eq by lia. lia.
  - left. rewrite Z.abs_neq by lia. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_3 : maxAreaNLogN_entail_wit_9_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (processed_endpoints_extend__max_endpoint_b
    sorted_i_2 k minimumIndex maximumIndex ltac:(lia) PreH33) as Hextend.
  rewrite Z.min_l in Hextend by lia.
  rewrite Z.max_l in Hextend by lia.
  exact Hextend.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_11 : maxAreaNLogN_entail_wit_9_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_11_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_1 : maxAreaNLogN_entail_wit_9_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35. exact H.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_2 : maxAreaNLogN_entail_wit_9_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  replace (distanceToMaximum * currentHeight)
    with (Z.max maximumArea (width * currentHeight))
    by (rewrite Z.max_r by nia; nia).
  eapply (processed_max_extend__max_endpoint_b
    l sorted_h_2 sorted_i_2 k index currentHeight
    minimumIndex maximumIndex maximumArea width).
  - lia.
  - lia.
  - exact PreH32.
  - exact PreH33.
  - exact PreH34.
  - exact PreH9.
  - exact PreH10.
  - exact PreH11.
  - lia.
  - lia.
  - intros x Hx. destruct (Z_le_gt_dec x index).
    + rewrite Z.abs_neq by lia. lia.
    + rewrite Z.abs_eq by lia. lia.
  - right. rewrite Z.abs_eq by lia. lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_3 : maxAreaNLogN_entail_wit_9_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  pose proof (processed_endpoints_extend__max_endpoint_b
    sorted_i_2 k minimumIndex maximumIndex ltac:(lia) PreH33) as Hextend.
  rewrite Z.min_l in Hextend by lia.
  rewrite Z.max_l in Hextend by lia.
  exact Hextend.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_12 : maxAreaNLogN_entail_wit_9_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_12_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_1 : maxAreaNLogN_entail_wit_9_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [apply PreH35; lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_2 : maxAreaNLogN_entail_wit_9_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_max_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_3 : maxAreaNLogN_entail_wit_9_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_endpoints_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_13 : maxAreaNLogN_entail_wit_9_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_13_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_1 : maxAreaNLogN_entail_wit_9_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [apply PreH35; lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_2 : maxAreaNLogN_entail_wit_9_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_max_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_3 : maxAreaNLogN_entail_wit_9_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_endpoints_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_14 : maxAreaNLogN_entail_wit_9_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_14_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_1 : maxAreaNLogN_entail_wit_9_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [apply PreH35; lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_2 : maxAreaNLogN_entail_wit_9_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_max_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_3 : maxAreaNLogN_entail_wit_9_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_endpoints_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_15 : maxAreaNLogN_entail_wit_9_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_15_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_1 : maxAreaNLogN_entail_wit_9_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [apply PreH35; lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_2 : maxAreaNLogN_entail_wit_9_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_max_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_3 : maxAreaNLogN_entail_wit_9_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_endpoints_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_16 : maxAreaNLogN_entail_wit_9_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_16_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_1 : maxAreaNLogN_entail_wit_9_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [apply PreH35; lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_2 : maxAreaNLogN_entail_wit_9_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_max_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_3 : maxAreaNLogN_entail_wit_9_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_endpoints_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_17 : maxAreaNLogN_entail_wit_9_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_17_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_1 : maxAreaNLogN_entail_wit_9_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [apply PreH35; lia].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_2 : maxAreaNLogN_entail_wit_9_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_max_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_3 : maxAreaNLogN_entail_wit_9_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto);
    solve [eapply processed_endpoints_extend__max_endpoint_c;
           eauto; try lia; first [left; lia | right; lia]].
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_18 : maxAreaNLogN_entail_wit_9_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_18_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_1 : maxAreaNLogN_entail_wit_9_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35; assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_2 : maxAreaNLogN_entail_wit_9_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH32 as [[Hheights [Hindices Hperm]] Hdescending].
  eapply processed_max_extend__max_endpoint_d with
    (index := index) (currentHeight := currentHeight)
    (minimum := minimumIndex) (maximum := maximumIndex) (width := width);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_3 : maxAreaNLogN_entail_wit_9_19_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_endpoints_extend__max_endpoint_d with (index := index);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_19 : maxAreaNLogN_entail_wit_9_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_19_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_1 : maxAreaNLogN_entail_wit_9_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35; assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_2 : maxAreaNLogN_entail_wit_9_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH32 as [[Hheights [Hindices Hperm]] Hdescending].
  eapply processed_max_extend__max_endpoint_d with
    (index := index) (currentHeight := currentHeight)
    (minimum := minimumIndex) (maximum := maximumIndex) (width := width);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_3 : maxAreaNLogN_entail_wit_9_20_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_endpoints_extend__max_endpoint_d with (index := index);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_20 : maxAreaNLogN_entail_wit_9_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_20_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_1 : maxAreaNLogN_entail_wit_9_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35; assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_2 : maxAreaNLogN_entail_wit_9_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH32 as [[Hheights [Hindices Hperm]] Hdescending].
  eapply processed_max_extend__max_endpoint_d with
    (index := index) (currentHeight := currentHeight)
    (minimum := minimumIndex) (maximum := maximumIndex) (width := width);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_3 : maxAreaNLogN_entail_wit_9_21_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_endpoints_extend__max_endpoint_d with (index := index);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_21 : maxAreaNLogN_entail_wit_9_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_21_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_1 : maxAreaNLogN_entail_wit_9_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35; assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_2 : maxAreaNLogN_entail_wit_9_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH32 as [[Hheights [Hindices Hperm]] Hdescending].
  eapply processed_max_extend__max_endpoint_d with
    (index := index) (currentHeight := currentHeight)
    (minimum := minimumIndex) (maximum := maximumIndex) (width := width);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_3 : maxAreaNLogN_entail_wit_9_22_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_endpoints_extend__max_endpoint_d with (index := index);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_22 : maxAreaNLogN_entail_wit_9_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_22_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_1 : maxAreaNLogN_entail_wit_9_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35; assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_2 : maxAreaNLogN_entail_wit_9_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH32 as [[Hheights [Hindices Hperm]] Hdescending].
  eapply processed_max_extend__max_endpoint_d with
    (index := index) (currentHeight := currentHeight)
    (minimum := minimumIndex) (maximum := maximumIndex) (width := width);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_3 : maxAreaNLogN_entail_wit_9_23_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_endpoints_extend__max_endpoint_d with (index := index);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_23 : maxAreaNLogN_entail_wit_9_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_23_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_1 : maxAreaNLogN_entail_wit_9_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  apply PreH35; assumption.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_2 : maxAreaNLogN_entail_wit_9_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  destruct PreH32 as [[Hheights [Hindices Hperm]] Hdescending].
  eapply processed_max_extend__max_endpoint_d with
    (index := index) (currentHeight := currentHeight)
    (minimum := minimumIndex) (maximum := maximumIndex) (width := width);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_3 : maxAreaNLogN_entail_wit_9_24_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_endpoints_extend__max_endpoint_d with (index := index);
    eauto; lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_9_24 : maxAreaNLogN_entail_wit_9_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_1.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_2.
  - Goal_apply proof_of_maxAreaNLogN_entail_wit_9_24_split_goal_3.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_10_split_goal_1 : maxAreaNLogN_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia ||  int_auto).
  eapply processed_full_prefix_maximum__max_final_result
    with (heights := sorted_h_2) (indices := sorted_i_2).
  - lia.
  - unfold SortedHeightIndexWorkspaceNLogN in PreH12.
    tauto.
  - replace (Zlength l) with k by lia.
    exact PreH14.
  - intros p Hp.
    assert (Hp' : 0 <= p < heightSize_pre) by lia.
    specialize (PreH15 p Hp').
    lia.
Qed.

Lemma proof_of_maxAreaNLogN_entail_wit_10 : maxAreaNLogN_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxAreaNLogN_entail_wit_10_split_goal_1.
Qed.
