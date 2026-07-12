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
From SimpleC.EE.QCP_demos_LLM Require Import bubble_sort_goal.
From SimpleC.EE.QCP_demos_LLM Require Import bubble_sort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.bubble_sort_lib.
Local Open Scope sac.

(*----- Function bubble_sort -----*)

Lemma proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1.
Proof.
  pre_process.
  destruct (Z.eq_dec n_pre 0) as [Hz | Hz].
  - subst. Left. entailer!.
  - Right. Exists l. entailer!.
    replace (n_pre - 0) with n_pre by lia.
    apply increasing_sublist_same.
Qed.

Lemma proof_of_bubble_sort_entail_wit_2_split_goal_1 : bubble_sort_entail_wit_2_split_goal_1.
Proof. pre_process. Qed.

Lemma proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Proof.
  aggressive_pre_process.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_1 : bubble_sort_entail_wit_3_1_split_goal_1.
Proof.
  pre_process.
  change (((Znth 0 (adjacent_swap a_2 j) 0) <= (Znth (j + 1) (adjacent_swap a_2 j) 0)) /\
          ((Znth ((j + 1) - 1) (adjacent_swap a_2 j) 0) <=
           (Znth (j + 1) (adjacent_swap a_2 j) 0))).
  assert (Hj1 : j + 1 < Zlength a_2) by lia.
  split.
  - rewrite Znth_adjacent_swap by lia.
    rewrite Znth_adjacent_swap by lia.
    destruct (Z.eq_dec 0 j) as [H0j | H0j].
    + subst j.
      destruct (Z.eq_dec 0 0) as [_ | Hbad]; [|contradiction Hbad; reflexivity].
      destruct (Z.eq_dec (0 + 1) 0) as [Hbad | _]; [lia|].
      destruct (Z.eq_dec (0 + 1) (0 + 1)) as [_ | Hbad]; [lia|contradiction Hbad; reflexivity].
    + destruct (Z.eq_dec 0 j); [lia|].
      destruct (Z.eq_dec 0 (j + 1)); [lia|].
      destruct (Z.eq_dec (j + 1) j); [lia|].
      destruct (Z.eq_dec (j + 1) (j + 1)); [|lia].
      apply PreH11; lia.
  - replace ((j + 1) - 1) with j by lia.
    rewrite Znth_adjacent_swap by lia.
    rewrite Znth_adjacent_swap by lia.
    destruct (Z.eq_dec j j) as [_ | Hbad]; [|contradiction Hbad; reflexivity].
    destruct (Z.eq_dec (j + 1) j) as [Hbad | _]; [lia|].
    destruct (Z.eq_dec (j + 1) (j + 1)) as [_ | Hbad]; [lia|contradiction Hbad; reflexivity].
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_2 : bubble_sort_entail_wit_3_1_split_goal_2.
Proof.
  pre_process.
  change (increasing (sublist (n_pre - i) n_pre (adjacent_swap a_2 j))).
  rewrite sublist_after_adjacent_swap by lia.
  exact PreH9.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_3 : bubble_sort_entail_wit_3_1_split_goal_3.
Proof.
  pre_process.
  change (Permutation l (adjacent_swap a_2 j)).
  eapply Permutation_trans.
  - exact PreH8.
  - unfold adjacent_swap.
    apply permutation_swap_Znth; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_4 : bubble_sort_entail_wit_3_1_split_goal_4.
Proof.
  pre_process.
  repeat rewrite Zlength_replace_Znth.
  auto.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - entailer!.
    + pose proof (proof_of_bubble_sort_entail_wit_3_1_split_goal_1
        n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) as [Hleft _].
      exact Hleft.
    + pose proof (proof_of_bubble_sort_entail_wit_3_1_split_goal_1
        n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) as [_ Hright].
      exact Hright.
  -
    pose proof (proof_of_bubble_sort_entail_wit_3_1_split_goal_1
      n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) as [Hleft Hright].
    entailer!.
    exact (proof_of_bubble_sort_entail_wit_3_1_split_goal_2
      n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11).
  - entailer!.
    exact (proof_of_bubble_sort_entail_wit_3_1_split_goal_3
      n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11).
  - entailer!.
    exact (proof_of_bubble_sort_entail_wit_3_1_split_goal_4
      n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11).
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_2_split_goal_1 : bubble_sort_entail_wit_3_2_split_goal_1.
Proof.
  pre_process.
  split.
  - destruct (Z.eq_dec j 0) as [-> | Hj0].
    + exact PreH1.
    + pose proof (PreH11 0 ltac:(lia)).
      lia.
  - replace ((j + 1) - 1) with j by lia.
    exact PreH1.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_2 : bubble_sort_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - entailer!.
    + pose proof (proof_of_bubble_sort_entail_wit_3_2_split_goal_1
        n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) as [Hleft _].
      exact Hleft.
    + pose proof (proof_of_bubble_sort_entail_wit_3_2_split_goal_1
        n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) as [_ Hright].
      exact Hright.
Qed.

Lemma proof_of_bubble_sort_entail_wit_4_split_goal_1 : bubble_sort_entail_wit_4_split_goal_1.
Proof.
  pre_process.
  assert (Hj : j = (n_pre - 1) - i) by lia.
  destruct H as [[[Hp0 Hplt] Hqlo] Hqhi].
  destruct (Z.eq_dec q (n_pre - (i + 1))) as [Hqeq | Hqneq].
  - subst q.
    replace (n_pre - (i + 1)) with j by lia.
    apply PreH10; lia.
  - apply PreH9; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_4_split_goal_2 : bubble_sort_entail_wit_4_split_goal_2.
Proof.
  pre_process.
  assert (Hj : j = (n_pre - 1) - i) by lia.
  replace (n_pre - (i + 1)) with (j) by lia.
  apply increasing_sublist_extend_left.
  - lia.
  - lia.
  - replace (j + 1) with (n_pre - i) by lia.
    exact PreH8.
  - intros q Hq.
    apply PreH9; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4.
Proof.
  aggressive_pre_process.
  - exact (proof_of_bubble_sort_entail_wit_4_split_goal_1
      n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10).
  - exact (proof_of_bubble_sort_entail_wit_4_split_goal_2
      n_pre l j i a_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10).
Qed.

Lemma proof_of_bubble_sort_return_wit_1_split_goal_1 : bubble_sort_return_wit_1_split_goal_1.
Proof.
  pre_process.
  apply increasing_length_le_1; lia.
Qed.

Lemma proof_of_bubble_sort_return_wit_1_split_goal_2 : bubble_sort_return_wit_1_split_goal_2.
Proof. pre_process. Qed.

Lemma proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_return_wit_1_split_goal_1
    n_pre l i PreH1 PreH2 PreH3 PreH4).
Qed.

Lemma proof_of_bubble_sort_return_wit_2_split_goal_1 : bubble_sort_return_wit_2_split_goal_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre - 1) by lia.
  destruct (Z.eq_dec n_pre 1) as [Hn1 | Hn1].
  - subst n_pre.
    apply increasing_length_le_1; lia.
  - replace a with (sublist 0 n_pre a).
    2:{ rewrite sublist_self; auto. }
    apply increasing_sublist_extend_left.
    + lia.
    + lia.
    + replace (0 + 1) with (n_pre - i) by lia.
      exact PreH7.
    + intros q Hq.
      apply PreH8; lia.
Qed.

Lemma proof_of_bubble_sort_return_wit_2 : bubble_sort_return_wit_2.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_return_wit_2_split_goal_1
      n_pre l i a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
Qed.

(*----- Function bubble_sort_alter -----*)

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_1 : bubble_sort_alter_entail_wit_2_normal_split_goal_1.
Proof. pre_process. Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_2 : bubble_sort_alter_entail_wit_2_normal_split_goal_2.
Proof.
  pre_process.
  replace (n_pre - 0) with n_pre by lia.
  apply increasing_sublist_same.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_3 : bubble_sort_alter_entail_wit_2_normal_split_goal_3.
Proof. pre_process. Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal : bubble_sort_alter_entail_wit_2_normal.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_2
      n_pre l PreH1 PreH2 PreH3 PreH4).
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_3_normal_split_goal_1 : bubble_sort_alter_entail_wit_3_normal_split_goal_1.
Proof. pre_process. Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_3_normal : bubble_sort_alter_entail_wit_3_normal.
Proof.
  aggressive_pre_process.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_1 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_1.
Proof.
  pre_process.
  change (((Znth 0 (adjacent_swap a_3 j) 0) <= (Znth (j + 1) (adjacent_swap a_3 j) 0)) /\
          ((Znth ((j + 1) - 1) (adjacent_swap a_3 j) 0) <=
           (Znth (j + 1) (adjacent_swap a_3 j) 0))).
  assert (Hj1 : j + 1 < Zlength a_3) by lia.
  split.
  - rewrite Znth_adjacent_swap by lia.
    rewrite Znth_adjacent_swap by lia.
    destruct (Z.eq_dec 0 j) as [H0j | H0j].
    + subst j.
      destruct (Z.eq_dec 0 0) as [_ | Hbad]; [|contradiction Hbad; reflexivity].
      destruct (Z.eq_dec (0 + 1) 0) as [Hbad | _]; [lia|].
      destruct (Z.eq_dec (0 + 1) (0 + 1)) as [_ | Hbad]; [lia|contradiction Hbad; reflexivity].
    + destruct (Z.eq_dec 0 j); [lia|].
      destruct (Z.eq_dec 0 (j + 1)); [lia|].
      destruct (Z.eq_dec (j + 1) j); [lia|].
      destruct (Z.eq_dec (j + 1) (j + 1)); [|lia].
      apply PreH11; lia.
  - replace ((j + 1) - 1) with j by lia.
    rewrite Znth_adjacent_swap by lia.
    rewrite Znth_adjacent_swap by lia.
    destruct (Z.eq_dec j j) as [_ | Hbad]; [|contradiction Hbad; reflexivity].
    destruct (Z.eq_dec (j + 1) j) as [Hbad | _]; [lia|].
    destruct (Z.eq_dec (j + 1) (j + 1)) as [_ | Hbad]; [lia|contradiction Hbad; reflexivity].
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_2 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_2.
Proof.
  pre_process.
  change (increasing (sublist (n_pre - i_2) n_pre (adjacent_swap a_3 j))).
  rewrite sublist_after_adjacent_swap by lia.
  exact PreH9.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_3 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_3.
Proof.
  pre_process.
  change (Permutation l (adjacent_swap a_3 j)).
  eapply Permutation_trans.
  - exact PreH8.
  - unfold adjacent_swap.
    apply permutation_swap_Znth; lia.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_4 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_4.
Proof.
  pre_process.
  repeat rewrite Zlength_replace_Znth.
  auto.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal : bubble_sort_alter_entail_wit_4_1_normal.
Proof.
  aggressive_pre_process.
  - exact (proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_1
      n_pre l i a j i_2 a_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
  - exact (proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_2
      n_pre l i a j i_2 a_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
  - exact (proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_3
      n_pre l i a j i_2 a_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
  - exact (proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_4
      n_pre l i a j i_2 a_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_2_normal_split_goal_1 : bubble_sort_alter_entail_wit_4_2_normal_split_goal_1.
Proof.
  pre_process.
  split.
  - destruct (Z.eq_dec j 0) as [-> | Hj0].
    + exact PreH1.
    + pose proof (PreH11 0 ltac:(lia)).
      lia.
  - replace ((j + 1) - 1) with j by lia.
    exact PreH1.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_2_normal : bubble_sort_alter_entail_wit_4_2_normal.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_alter_entail_wit_4_2_normal_split_goal_1
      n_pre l i a j i_2 a_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23).
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_5_normal_split_goal_1 : bubble_sort_alter_entail_wit_5_normal_split_goal_1.
Proof.
  pre_process.
  assert (Hj : j = (n_pre - 1) - i) by lia.
  replace (n_pre - (i + 1)) with j by lia.
  apply increasing_sublist_extend_left.
  - lia.
  - lia.
  - replace (j + 1) with (n_pre - i) by lia.
    exact PreH8.
  - intros q Hq.
    apply PreH9; lia.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_5_normal : bubble_sort_alter_entail_wit_5_normal.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_alter_entail_wit_5_normal_split_goal_1
      n_pre l i_2 a_2 j i a_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
      PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_1 : bubble_sort_alter_return_wit_1_zero_split_goal_1.
Proof.
  pre_process.
  apply increasing_length_le_1; lia.
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_2 : bubble_sort_alter_return_wit_1_zero_split_goal_2.
Proof. pre_process. Qed.

Lemma proof_of_bubble_sort_alter_return_wit_1_zero : bubble_sort_alter_return_wit_1_zero.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_1
    n_pre l i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8).
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_2_normal_split_goal_1 : bubble_sort_alter_return_wit_2_normal_split_goal_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre - 1) by lia.
  destruct (Z.eq_dec n_pre 1) as [Hn1 | Hn1].
  - subst n_pre.
    apply increasing_length_le_1; lia.
  - replace a with (sublist 0 n_pre a).
    2:{ rewrite sublist_self; auto. }
    apply increasing_sublist_extend_left.
    + lia.
    + lia.
    + replace (0 + 1) with (n_pre - i) by lia.
      exact PreH7.
    + intros q Hq.
      apply PreH8; lia.
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_2_normal : bubble_sort_alter_return_wit_2_normal.
Proof.
  aggressive_pre_process.
  exact (proof_of_bubble_sort_alter_return_wit_2_normal_split_goal_1
      n_pre l i a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12).
Qed.

(*----- Function bubble_sort_alter1 -----*)

Lemma proof_of_bubble_sort_alter1_entail_wit_2_normal : bubble_sort_alter1_entail_wit_2_normal.
Proof. exact proof_of_bubble_sort_alter_entail_wit_2_normal. Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_3_normal : bubble_sort_alter1_entail_wit_3_normal.
Proof. exact proof_of_bubble_sort_alter_entail_wit_3_normal. Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_4_1_normal : bubble_sort_alter1_entail_wit_4_1_normal.
Proof. exact proof_of_bubble_sort_alter_entail_wit_4_1_normal. Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_4_2_normal : bubble_sort_alter1_entail_wit_4_2_normal.
Proof. exact proof_of_bubble_sort_alter_entail_wit_4_2_normal. Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_5_normal : bubble_sort_alter1_entail_wit_5_normal.
Proof. exact proof_of_bubble_sort_alter_entail_wit_5_normal. Qed.

Lemma proof_of_bubble_sort_alter1_return_wit_1_zero : bubble_sort_alter1_return_wit_1_zero.
Proof. exact proof_of_bubble_sort_alter_return_wit_1_zero. Qed.

Lemma proof_of_bubble_sort_alter1_return_wit_2_normal : bubble_sort_alter1_return_wit_2_normal.
Proof. exact proof_of_bubble_sort_alter_return_wit_2_normal. Qed.
