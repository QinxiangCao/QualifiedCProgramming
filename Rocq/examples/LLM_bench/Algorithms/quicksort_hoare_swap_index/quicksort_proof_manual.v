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
From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index Require Import quicksort_goal.
From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index Require Import quicksort_proof_auto.
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
  LLM_pre_process ltac:(int_auto).
  unfold same_outside_range.
  split.
  - reflexivity.
  - intros; reflexivity.
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_4 : partition_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_partition_entail_wit_5_split_goal_1 : partition_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite H.
  apply Z.lt_le_incl.
  apply PreH18.
  lia.
Qed.

Lemma proof_of_partition_entail_wit_5 : partition_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_partition_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_partition_entail_wit_6_1_split_goal_1 : partition_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  rewrite Znth_replace_Znth_Diff.
  - rewrite Znth_replace_Znth_Diff.
    + rewrite <- PreH5. apply PreH18. lia.
    + rewrite Hlen_l1. lia.
    + rewrite Hlen_l1. lia.
    + intro Heq; subst; lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - intro Heq; subst; lia.
Qed.

Lemma proof_of_partition_entail_wit_6_1_split_goal_2 : partition_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  rewrite Znth_replace_Znth_Diff.
  - rewrite Znth_replace_Znth_Diff.
    + rewrite <- PreH5. apply PreH17. lia.
    + rewrite Hlen_l1. lia.
    + rewrite Hlen_l1. lia.
    + intro Heq; subst; lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - intro Heq; subst; lia.
Qed.

Lemma proof_of_partition_entail_wit_6_1_split_goal_3 : partition_entail_wit_6_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  rewrite Znth_replace_Znth_Diff.
  - rewrite Znth_replace_Znth_Same.
    + apply Z.lt_le_incl.
      apply PreH19. lia.
    + rewrite Hlen_l1. lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - intro Heq; subst; lia.
Qed.

Lemma proof_of_partition_entail_wit_6_1_split_goal_4 : partition_entail_wit_6_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH16 as Hsame.
  destruct PreH16 as [Hlen _].
  eapply same_outside_range_trans_local.
  - exact Hsame.
  - apply same_outside_range_swap_inside_local; rewrite ?Hlen_l1; try lia.
Qed.

Lemma proof_of_partition_entail_wit_6_1_split_goal_5 : partition_entail_wit_6_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  eapply Permutation_trans.
  - exact PreH15.
  - apply swap_Znth_perm_local.
    rewrite Hlen_l1. lia.
Qed.

Lemma proof_of_partition_entail_wit_6_1_split_goal_6 : partition_entail_wit_6_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  rewrite Znth_replace_Znth_Diff.
  - rewrite Znth_replace_Znth_Diff.
    + exact PreH14.
    + rewrite Hlen_l1. lia.
    + rewrite Hlen_l1. lia.
    + intro Heq; subst; lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - rewrite Zlength_replace_Znth.
    rewrite Hlen_l1. lia.
  - intro Heq; subst; lia.
Qed.

Lemma proof_of_partition_entail_wit_6_1 : partition_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_6_1_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_6_1_split_goal_3.
  - Goal_apply proof_of_partition_entail_wit_6_1_split_goal_4.
  - Goal_apply proof_of_partition_entail_wit_6_1_split_goal_5.
  - Goal_apply proof_of_partition_entail_wit_6_1_split_goal_6.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_1 : partition_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH14 as Hsame.
  destruct Hsame as [Hsame_len Hsame_eq].
  assert (Hlen_l : Zlength l = n) by (rewrite Hsame_len; exact Hlen_l1).
  rewrite <- PreH12.
  eapply partition_outer_exit_swap_yields_partitioned_at; try eassumption; try lia.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_2 : partition_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH14 as Hsame.
  destruct PreH14 as [Hlen _].
  eapply same_outside_range_trans_local.
  - exact Hsame.
  - rewrite <- PreH12.
    apply same_outside_range_swap_inside_local; rewrite ?Hlen_l1; try lia.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_3 : partition_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite !Zlength_replace_Znth in PreH1; exact PreH1).
  destruct PreH14 as [Hlen _].
  destruct (Z.eq_dec low_pre i) as [Heq | Hneq].
  - subst i.
    rewrite <- PreH12.
    rewrite replace_Znth_Znth by (rewrite Zlength_replace_Znth; rewrite Hlen_l1; lia).
    rewrite replace_Znth_Znth by (rewrite Hlen_l1; lia).
    exact PreH13.
  - eapply Permutation_trans.
    + exact PreH13.
    + rewrite <- PreH12.
      apply swap_Znth_perm_local.
      rewrite Hlen_l1.
      lia.
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
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [Hlen12 Heq12].
  destruct PreH7 as [Hlen23 Heq23].
  destruct PreH3 as [Hlen34 Heq34].
  assert (Hlen3 : Zlength l1_3 = n) by (rewrite Hlen34; exact PreH1).
  assert (Hlen2 : Zlength l1_2 = n) by (rewrite Hlen23; exact Hlen3).
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_left_local.
    - exact PreH6.
    - exact PreH17.
    - exact (conj Hlen23 Heq23).
    - rewrite Hlen2. exact PreH19.
    - exact PreH14.
  }
  assert (Hpart4 : partitioned_at l1_4 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_right_local.
    - exact PreH2.
    - exact PreH17.
    - exact (conj Hlen34 Heq34).
    - rewrite Hlen3. exact PreH19.
    - exact Hpart3.
  }
  assert (Hleft4 : range_nondecreasing l1_4 left_pre (retval - 1)).
  {
    eapply range_nondecreasing_ext_local.
    - exact Hlen34.
    - intros k Hk.
      assert (Hklen : 0 <= k < Zlength l1_3).
      { rewrite Hlen3. lia. }
      apply Heq34.
      + exact Hklen.
      + left. lia.
    - exact PreH8.
  }
  eapply quicksort_partition_combine_both_sides_local.
  - exact PreH17.
  - rewrite PreH1. exact PreH19.
  - split; [exact PreH10 | exact PreH11].
  - exact Hpart4.
  - exact Hleft4.
  - exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_1_split_goal_2 : quicksort_range_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct PreH13 as [Hlen12 Heq12].
  destruct PreH7 as [Hlen23 Heq23].
  destruct PreH3 as [Hlen34 Heq34].
  assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
  {
    split.
    - exact Hlen23.
    - intros k Hk Hout.
      apply Heq23.
      + exact Hk.
      + destruct Hout as [Hlt | Hgt]; [left | right]; lia.
  }
  assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
  {
    split.
    - exact Hlen34.
    - intros k Hk Hout.
      apply Heq34.
      + exact Hk.
      + destruct Hout as [Hlt | Hgt]; [left | right]; lia.
  }
  eapply same_outside_range_trans_local.
  - exact (conj Hlen12 Heq12).
  - eapply same_outside_range_trans_local.
    + exact Hsame23_full.
    + exact Hsame34_full.
Qed.

Lemma proof_of_quicksort_range_return_wit_1_split_goal_3 : quicksort_range_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  LLM_pre_process ltac:(int_auto).
  assert (Heqret : retval = left_pre) by lia.
  subst retval.
  destruct PreH10 as [Hlen12 Heq12].
  destruct PreH3 as [Hlen23 Heq23].
  assert (Hlen2 : Zlength l1_2 = n) by (rewrite Hlen23; exact PreH1).
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre left_pre).
  {
    eapply partitioned_at_preserved_by_right_local.
    - exact PreH2.
    - exact PreH14.
    - exact (conj Hlen23 Heq23).
    - rewrite Hlen2. exact PreH16.
    - exact PreH11.
  }
  eapply quicksort_partition_combine_right_only_local.
  - exact PreH14.
  - rewrite PreH1. exact PreH16.
  - reflexivity.
  - exact Hpart3.
  - exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_2_split_goal_2 : quicksort_range_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Heqret : retval = left_pre) by lia.
  subst retval.
  destruct PreH10 as [Hlen12 Heq12].
  destruct PreH3 as [Hlen23 Heq23].
  split.
  - rewrite Hlen12. exact Hlen23.
  - intros k Hk Hout.
    rewrite (Heq23 k).
    + apply Heq12. exact Hk. exact Hout.
    + rewrite <- Hlen12. exact Hk.
    + destruct Hout as [Hlt | Hgt]; [left | right]; lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_2_split_goal_3 : quicksort_range_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  LLM_pre_process ltac:(int_auto).
  assert (Heqret : retval = right_pre) by lia.
  subst retval.
  destruct PreH10 as [Hlen12 Heq12].
  destruct PreH4 as [Hlen23 Heq23].
  assert (Hlen2 : Zlength l1_2 = n) by (rewrite Hlen23; exact PreH1).
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre right_pre).
  {
    eapply partitioned_at_preserved_by_left_local.
    - exact PreH3.
    - exact PreH14.
    - exact (conj Hlen23 Heq23).
    - rewrite Hlen2. exact PreH16.
    - exact PreH11.
  }
  eapply quicksort_partition_combine_left_only_local.
  - exact PreH14.
  - rewrite PreH1. exact PreH16.
  - reflexivity.
  - exact Hpart3.
  - exact PreH5.
Qed.

Lemma proof_of_quicksort_range_return_wit_3_split_goal_2 : quicksort_range_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Heqret : retval = right_pre) by lia.
  subst retval.
  destruct PreH10 as [Hlen12 Heq12].
  destruct PreH4 as [Hlen23 Heq23].
  split.
  - rewrite Hlen12. exact Hlen23.
  - intros k Hk Hout.
    rewrite (Heq23 k).
    + apply Heq12. exact Hk. exact Hout.
    + rewrite <- Hlen12. exact Hk.
    + destruct Hout as [Hlt | Hgt]; [left | right]; lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_3_split_goal_3 : quicksort_range_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  LLM_pre_process ltac:(int_auto).
  unfold range_nondecreasing.
  intros i j Hi Hij Hj.
  assert (i = j) by lia.
  subst; lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_range_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_quicksort_return_wit_1_split_goal_1 : quicksort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply range_nondecreasing_full_to_increasing.
  rewrite PreH1.
  exact PreH4.
Qed.

Lemma proof_of_quicksort_return_wit_1 : quicksort_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_quicksort_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_quicksort_return_wit_2_split_goal_1 : quicksort_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hn0 : n_pre = 0) by lia.
  apply range_nondecreasing_full_to_increasing.
  rewrite PreH1, Hn0.
  unfold range_nondecreasing.
  intros i j Hi Hij Hj.
  lia.
Qed.

Lemma proof_of_quicksort_return_wit_2_split_goal_2 : quicksort_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_quicksort_return_wit_2 : quicksort_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_return_wit_2_split_goal_1.
  - Goal_apply proof_of_quicksort_return_wit_2_split_goal_2.
Qed.
