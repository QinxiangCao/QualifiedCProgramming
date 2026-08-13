Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index Require Import quicksort_goal.
From SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index Require Import quicksort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib.
Local Open Scope sac.

Lemma proof_of_partition_entail_wit_1_split_goal_1 : partition_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_2 : partition_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_3 : partition_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  apply same_outside_range_refl.
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_4 : partition_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_partition_entail_wit_2_1_split_goal_1 : partition_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  rewrite !Zlength_replace_Znth in PreH1.
  rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth in *; lia).
  rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth in *; lia).
  rewrite PreH13, PreH4.
  reflexivity.
Qed.

Lemma proof_of_partition_entail_wit_2_1_split_goal_2 : partition_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  rewrite !Zlength_replace_Znth in PreH1.
  eapply same_outside_range_trans.
  - exact PreH12.
  - apply same_outside_range_swap_inside; lia.
Qed.

Lemma proof_of_partition_entail_wit_2_1_split_goal_3 : partition_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  rewrite !Zlength_replace_Znth in PreH1.
  eapply Permutation_trans.
  - exact PreH11.
  - apply lomuto_permutation_swap_Znth; lia.
Qed.

Lemma proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_1 : partition_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hlenarr : high_pre < Zlength l1_2).
  {
    rewrite !Zlength_replace_Znth in PreH1.
    lia.
  }
  assert (Hj : j = high_pre) by lia.
  subst j.
  rewrite <- PreH12.
  apply (partitioned_at_after_lomuto_final_swap l1_2 low_pre high_pre pivot i) ; auto.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_2 : partition_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hlenarr : high_pre < Zlength l1_2).
  {
    rewrite !Zlength_replace_Znth in PreH1.
    lia.
  }
  assert (Hj : j = high_pre) by lia.
  subst j.
  eapply same_outside_range_trans.
  - exact PreH11.
  - rewrite <- PreH12.
    apply same_outside_range_swap_inside; lia.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_3 : partition_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hlenarr : high_pre < Zlength l1_2).
  {
    rewrite !Zlength_replace_Znth in PreH1.
    lia.
  }
  assert (Hj : j = high_pre) by lia.
  subst j.
  eapply Permutation_trans.
  - exact PreH10.
  - rewrite <- PreH12.
    apply lomuto_permutation_swap_Znth; lia.
Qed.

Lemma proof_of_partition_return_wit_1 : partition_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_return_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_return_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_quicksort_range_return_wit_1_split_goal_1 : quicksort_range_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof PreH3 as Hsame34_len.
  destruct Hsame34_len as [Hlen34 Heq34].
  pose proof PreH7 as Hsame23_len.
  destruct Hsame23_len as [Hlen23 _].
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_left_local.
    + exact PreH6.
    + exact PreH17.
    + exact PreH7.
    + rewrite Hlen23, Hlen34, PreH1; lia.
    + exact PreH14.
  }
  assert (Hpart : partitioned_at l1_4 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_right_local.
    + exact PreH2.
    + exact PreH17.
    + exact PreH3.
    + rewrite Hlen34, PreH1; lia.
    + exact Hpart3.
  }
  assert (Hleft_sorted4 : range_nondecreasing l1_4 left_pre (retval - 1)).
  {
    eapply range_nondecreasing_ext_local.
    + exact Hlen34.
    + intros k Hk.
      apply Heq34.
      * rewrite Hlen34, PreH1; lia.
      * left. lia.
    + exact PreH8.
  }
  eapply quicksort_partition_combine_both_sides_local with (p := retval).
  + exact PreH17.
  + rewrite PreH1. exact PreH19.
  + lia.
  + exact Hpart.
  + exact Hleft_sorted4.
  + exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_1_split_goal_2 : quicksort_range_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
  {
    eapply (same_outside_range_weaken
              l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
    + lia.
    + lia.
    + exact PreH7.
  }
  assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
  {
    eapply (same_outside_range_weaken
              l1_3 l1_4 (retval + 1) right_pre left_pre right_pre).
    + lia.
    + lia.
    + exact PreH3.
  }
  eapply same_outside_range_trans.
  - exact PreH13.
  - eapply same_outside_range_trans.
    + exact Hsame23_full.
    + exact Hsame34_full.
Qed.

Lemma proof_of_quicksort_range_return_wit_1_split_goal_3 : quicksort_range_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  eapply Permutation_trans.
  - exact PreH12.
  - eapply Permutation_trans.
    + exact PreH6.
    + exact PreH2.
Qed.

Lemma proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_range_return_wit_1_split_goal_1.
  - Goal_apply proof_of_quicksort_range_return_wit_1_split_goal_2.
  - Goal_apply proof_of_quicksort_range_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_quicksort_range_return_wit_2_split_goal_1 : quicksort_range_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof PreH3 as Hsame23_len.
  destruct Hsame23_len as [Hlen23 _].
  assert (Hpart : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_right_local.
    + exact PreH2.
    + exact PreH14.
    + exact PreH3.
    + rewrite Hlen23, PreH1; lia.
    + exact PreH11.
  }
  eapply quicksort_partition_combine_right_only_local with (p := retval).
  + exact PreH14.
  + rewrite PreH1. exact PreH16.
  + lia.
  + exact Hpart.
  + exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_2_split_goal_2 : quicksort_range_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
  {
    eapply (same_outside_range_weaken
              l1_2 l1_3 (retval + 1) right_pre left_pre right_pre).
    + lia.
    + lia.
    + exact PreH3.
  }
  eapply same_outside_range_trans.
  - exact PreH10.
  - exact Hsame23_full.
Qed.

Lemma proof_of_quicksort_range_return_wit_2_split_goal_3 : quicksort_range_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  eapply Permutation_trans.
  - exact PreH9.
  - exact PreH2.
Qed.

Lemma proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_range_return_wit_2_split_goal_1.
  - Goal_apply proof_of_quicksort_range_return_wit_2_split_goal_2.
  - Goal_apply proof_of_quicksort_range_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_quicksort_range_return_wit_3_split_goal_1 : quicksort_range_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof PreH4 as Hsame23_len.
  destruct Hsame23_len as [Hlen23 _].
  assert (Hpart : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_left_local.
    + exact PreH3.
    + exact PreH14.
    + exact PreH4.
    + rewrite Hlen23, PreH1; lia.
    + exact PreH11.
  }
  eapply quicksort_partition_combine_left_only_local with (p := retval).
  + exact PreH14.
  + rewrite PreH1. exact PreH16.
  + lia.
  + exact Hpart.
  + exact PreH5.
Qed.

Lemma proof_of_quicksort_range_return_wit_3_split_goal_2 : quicksort_range_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
  {
    eapply (same_outside_range_weaken
              l1_2 l1_3 left_pre (retval - 1) left_pre right_pre).
    + lia.
    + lia.
    + exact PreH4.
  }
  eapply same_outside_range_trans.
  - exact PreH10.
  - exact Hsame23_full.
Qed.

Lemma proof_of_quicksort_range_return_wit_3_split_goal_3 : quicksort_range_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
  eapply Permutation_trans.
  - exact PreH9.
  - exact PreH3.
Qed.

Lemma proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_range_return_wit_3_split_goal_1.
  - Goal_apply proof_of_quicksort_range_return_wit_3_split_goal_2.
  - Goal_apply proof_of_quicksort_range_return_wit_3_split_goal_3.
Qed.

Lemma proof_of_quicksort_range_return_wit_4_split_goal_1 : quicksort_range_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  unfold range_nondecreasing.
  intros i j Hi Hij Hj.
  assert (i = j) by lia.
  subst; lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_4_split_goal_2 : quicksort_range_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  apply same_outside_range_refl.
Qed.

Lemma proof_of_quicksort_range_return_wit_4_split_goal_3 : quicksort_range_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(auto).
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_range_return_wit_4_split_goal_1.
  - Goal_apply proof_of_quicksort_range_return_wit_4_split_goal_2.
  - Goal_apply proof_of_quicksort_range_return_wit_4_split_goal_3.
Qed.

Lemma proof_of_quicksort_return_wit_1_split_goal_1 : quicksort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  apply range_nondecreasing_full_to_increasing.
  rewrite PreH1.
  exact PreH4.
Qed.

Lemma proof_of_quicksort_return_wit_1 : quicksort_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_return_wit_1_split_goal_1.
Qed.
