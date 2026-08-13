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
From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_goal.
From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib.
Local Open Scope sac.

Lemma proof_of_initCounts_entail_wit_1_split_goal_1 : initCounts_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  apply CountsZeroPrefix_nil.
Qed.

Lemma proof_of_initCounts_entail_wit_1_split_goal_2 : initCounts_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  apply CountsZeroPrefix_nil.
Qed.

Lemma proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_initCounts_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_initCounts_entail_wit_1_split_goal_2.
Qed. 

Lemma proof_of_initCounts_entail_wit_2_split_goal_1 : initCounts_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply CountsZeroPrefix_snoc_zero; eauto; lia.
Qed.

Lemma proof_of_initCounts_entail_wit_2_split_goal_2 : initCounts_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  eapply CountsZeroPrefix_snoc_zero; eauto; lia.
Qed.

Lemma proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_initCounts_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_initCounts_entail_wit_2_split_goal_2.
Qed. 

Lemma proof_of_initCounts_return_wit_1 : initCounts_return_wit_1.
Proof.
  aggressive_pre_process.
  replace i with k_pre in * by lia.
  Exists good_l_2 seen_l_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full seen_pre 0 k_pre seen_l_2).
    replace (seen_pre + 0 * sizeof(INT)) with seen_pre by lia.
    replace (k_pre - 0) with k_pre by lia.
    sep_apply (IntArray.seg_to_full good_pre 0 k_pre good_l_2).
    replace (good_pre + 0 * sizeof(INT)) with good_pre by lia.
    replace (k_pre - 0) with k_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia.
    + apply CountsZeroPrefix_to_full. exact PreH6.
    + apply CountsZeroPrefix_to_full. exact PreH7.
Qed. 

Lemma proof_of_copyCounts_entail_wit_1_split_goal_1 : copyCounts_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  apply CopyCountsPrefix_zero.
  - exact (proj1 PreH3).
  - exact (proj1 PreH4).
Qed.

Lemma proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copyCounts_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_copyCounts_entail_wit_2_split_goal_1 : copyCounts_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply CopyCountsPrefix_step_replace; eauto.
  unfold CountArraySafe in PreH8.
  tauto.
Qed.

Lemma proof_of_copyCounts_entail_wit_2_split_goal_2 : copyCounts_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold CountArraySafe in *.
  destruct PreH6 as [Hseen_len Hseen_bounds].
  destruct PreH8 as [Hgood_len Hgood_bounds].
  split.
  - rewrite Zlength_replace_Znth. exact Hgood_len.
  - eapply replace_Znth_preserves_bounds with
        (xs := good_cur_2) (i := i) (v := Znth i seen_l 0)
        (k := k_pre) (lo := 0) (hi := 200000); eauto; lia.
Qed.

Lemma proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_copyCounts_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_copyCounts_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_copyCounts_return_wit_1_split_goal_1 : copyCounts_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold CountArraySafe in PreH6, PreH8.
  destruct PreH6 as [Hseen_len _].
  destruct PreH8 as [Hgood_len _].
  eapply CopyCountsPrefix_full_eq; eauto; lia.
Qed.

Lemma proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copyCounts_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_1_split_goal_1 : countChoosingInns_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply CountsZeroFull_to_ChoosingPrefixState_zero; eauto.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_1_split_goal_2 : countChoosingInns_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH3.
  destruct PreH3 as [_ [_ [_ [Hcolors_len [Hcosts_len _]]]]].
  eapply CountsZeroFull_to_ChoosingPrefixDataSafe_zero; eauto; lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_2_split_goal_1 : countChoosingInns_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_1 : countChoosingInns_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [Hn [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  int_auto; lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_2 : countChoosingInns_entail_wit_3_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [Hn [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [_ [_ Hgood]]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hgood (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_3 : countChoosingInns_entail_wit_3_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [Hn [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_4 : countChoosingInns_entail_wit_3_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [_ [_ Hgood]]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hgood (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_5 : countChoosingInns_entail_wit_3_split_goal_5.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [_ [_ Hgood]]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hgood (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_6 : countChoosingInns_entail_wit_3_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_7 : countChoosingInns_entail_wit_3_split_goal_7.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_8 : countChoosingInns_entail_wit_3_split_goal_8.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [_ Hcosts]]]]]].
  specialize (Hcosts i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_9 : countChoosingInns_entail_wit_3_split_goal_9.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [_ Hcosts]]]]]].
  specialize (Hcosts i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_10 : countChoosingInns_entail_wit_3_split_goal_10.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  specialize (Hcolors i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_11 : countChoosingInns_entail_wit_3_split_goal_11.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  specialize (Hcolors i ltac:(lia)).
  lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_6.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_7.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_8.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_9.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_10.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_11.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4.
Proof.
  aggressive_pre_process.
  assert (Hnext_data :
    ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      good_l_2).
  {
    eapply ChoosingPrefixDataSafe_step_expensive; eauto.
    all: unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  assert (Hnext_full_data :
    ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)).
  {
    eapply ChoosingPrefixDataSafe_step_affordable_after_copy; eauto.
    all: unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  assert (Hnext_state :
    ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c seen_l 0)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)).
  {
    eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer) (good := good_l_2) (c := c);
      try exact PreH20; try exact PreH21; try exact PreH2;
      try reflexivity; try lia.
    unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  assert (Hnext_bound :
    0 <= answer + Znth c seen_l 0 <= 19999900000).
  {
    eapply ChoosingPrefixState_answer_bound
      with (seen := replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (good := replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (n := n_pre); eauto.
    all: unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  pose proof Hnext_data as Hnext_data_parts.
  unfold ChoosingPrefixDataSafe in Hnext_data_parts.
  destruct Hnext_data_parts as
    [Hnext_limit [_ [Hnext_seen_safe Hnext_good_safe]]].
  assert (Hnext_seen_200 :
    CountArraySafe (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      k_pre 200000).
  {
    eapply CountArraySafe_weaken_limit; [exact Hnext_seen_safe |].
    unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  assert (Hnext_good_200 : CountArraySafe good_l_2 k_pre 200000).
  {
    eapply CountArraySafe_weaken_limit; [exact Hnext_good_safe |].
    unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  subst c.
  Exists seen_l.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption;
      try exact Hnext_data; try exact Hnext_state; try lia.
    + replace
        (answer + Znth (Znth i colors_l 0) seen_l 0 -
         Znth (Znth i colors_l 0) seen_l 0)
        with answer by lia.
      exact PreH21.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_5_split_goal_1 : countChoosingInns_entail_wit_5_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer - Znth c seen_l 0)
           (seen := seen_l) (good := good_l) (c := c);
    try exact PreH14; try exact PreH16; try exact PreH2;
    try exact PreH13; try lia.
  unfold ChoosingInputSafe in PreH4; intuition; lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_5_split_goal_2 : countChoosingInns_entail_wit_5_split_goal_2.
Proof.
  aggressive_pre_process.
  subst seen_next_2.
  eapply ChoosingPrefixDataSafe_step_affordable_after_copy; eauto.
  unfold ChoosingInputSafe in PreH4; intuition; lia.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_entail_wit_5_split_goal_2.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6.
Proof.
  aggressive_pre_process.
  assert (Hnext_data :
    ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre
      (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l).
  {
    eapply ChoosingPrefixDataSafe_step_expensive; eauto.
    unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  assert (Hnext_state :
    ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c good_l 0)
      (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l).
  {
    eapply ChoosingPrefixState_step_expensive
      with (old_answer := answer) (c := c);
      try exact PreH20; try exact PreH21; try exact PreH2;
      try reflexivity; try lia.
    unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  assert (Hnext_bound :
    0 <= answer + Znth c good_l 0 <= 19999900000).
  {
    eapply ChoosingPrefixState_answer_bound
      with (seen := replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2)
           (good := good_l) (n := n_pre); eauto.
    all: unfold ChoosingInputSafe in PreH4; intuition; lia.
  }
  subst c.
  Exists seen_l_2.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption;
      try exact Hnext_data; try exact Hnext_state; try lia.
    replace
      (answer + Znth (Znth i colors_l 0) good_l 0 -
       Znth (Znth i colors_l 0) good_l 0)
      with answer by lia.
    exact PreH21.
Qed. 

Lemma proof_of_countChoosingInns_entail_wit_8_split_goal_1 : countChoosingInns_entail_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ChoosingInnsAnswer.
  replace n_pre with i by lia.
  exact (proj1 PreH8).
Qed.

Lemma proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_countChoosingInns_entail_wit_8_split_goal_1.
Qed. 

Lemma proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_1 : countChoosingInns_partial_solve_wit_1_pure_split_goal_1.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold ChoosingInputSafe in PreH9.
  lia.
Qed.

Lemma proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_2 : countChoosingInns_partial_solve_wit_1_pure_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold ChoosingInputSafe in PreH9.
  lia.
Qed.

Lemma proof_of_countChoosingInns_partial_solve_wit_1_pure : countChoosingInns_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_2.
Qed. 

Lemma proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1 : countChoosingInns_partial_solve_wit_7_pure_split_goal_1.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold ChoosingInputSafe in PreH17.
  lia.
Qed.

Lemma proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1.
Qed. 
