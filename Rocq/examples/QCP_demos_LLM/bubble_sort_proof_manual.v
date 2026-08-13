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
  LLM_pre_process ltac:(int_auto).
  destruct (Z.eq_dec n_pre 0) as [Hz | Hz].
  - subst. Left.
    repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; reflexivity.
    + dump_pre_spatial; lia.
  - Right. Exists l.
    repeat (split_pure_spatial || split_pures).
    + cancel.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; exact PreH3.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; apply Permutation_refl.
    + dump_pre_spatial.
      replace (n_pre - 0) with n_pre by lia.
      apply increasing_sublist_same.
    + dump_pre_spatial.
      intros p q [[Hp Hq] Hq']; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_2_split_goal_1 : bubble_sort_entail_wit_2_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_entail_wit_2_split_goal_2 : bubble_sort_entail_wit_2_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bubble_sort_entail_wit_2_split_goal_1.
  Goal_apply proof_of_bubble_sort_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_1 : bubble_sort_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (increasing (sublist (n_pre - i) n_pre (adjacent_swap a_2 j))).
  rewrite sublist_after_adjacent_swap by lia.
  exact PreH9.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_2 : bubble_sort_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (Permutation l (adjacent_swap a_2 j)).
  eapply Permutation_trans.
  - exact PreH8.
  - unfold adjacent_swap.
    apply permutation_swap_Znth; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1_split_goal_3 : bubble_sort_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth.
  auto.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_bubble_sort_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_bubble_sort_entail_wit_3_1_split_goal_3.
Qed.

Lemma proof_of_bubble_sort_entail_wit_4_split_goal_1 : bubble_sort_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  LLM_pre_process ltac:(int_auto).
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
  - Goal_apply proof_of_bubble_sort_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_bubble_sort_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_return_wit_1_split_goal_1 : bubble_sort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply increasing_length_le_1; lia.
Qed.

Lemma proof_of_bubble_sort_return_wit_1_split_goal_2 : bubble_sort_return_wit_1_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_return_wit_1_split_goal_1.
  - Goal_apply proof_of_bubble_sort_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_return_wit_2_split_goal_1 : bubble_sort_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  Goal_apply proof_of_bubble_sort_return_wit_2_split_goal_1.
Qed.

(*----- Function bubble_sort_alter -----*)

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_1 : bubble_sort_alter_entail_wit_2_normal_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_2 : bubble_sort_alter_entail_wit_2_normal_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (n_pre - 0) with n_pre by lia.
  apply increasing_sublist_same.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_3 : bubble_sort_alter_entail_wit_2_normal_split_goal_3.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_2_normal : bubble_sort_alter_entail_wit_2_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_2.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_2_normal_split_goal_3.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_3_normal_split_goal_1 : bubble_sort_alter_entail_wit_3_normal_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_3_normal_split_goal_2 : bubble_sort_alter_entail_wit_3_normal_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_3_normal : bubble_sort_alter_entail_wit_3_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_3_normal_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_3_normal_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_1 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (increasing (sublist (n_pre - i_2) n_pre (adjacent_swap a_3 j))).
  rewrite sublist_after_adjacent_swap by lia.
  exact PreH9.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_2 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (Permutation l (adjacent_swap a_3 j)).
  eapply Permutation_trans.
  - exact PreH8.
  - unfold adjacent_swap.
    apply permutation_swap_Znth; lia.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_3 : bubble_sort_alter_entail_wit_4_1_normal_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth.
  auto.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_4_1_normal : bubble_sort_alter_entail_wit_4_1_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_2.
  - Goal_apply proof_of_bubble_sort_alter_entail_wit_4_1_normal_split_goal_3.
Qed.

Lemma proof_of_bubble_sort_alter_entail_wit_5_normal_split_goal_1 : bubble_sort_alter_entail_wit_5_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  Goal_apply proof_of_bubble_sort_alter_entail_wit_5_normal_split_goal_1.
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_1 : bubble_sort_alter_return_wit_1_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply increasing_length_le_1; lia.
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_2 : bubble_sort_alter_return_wit_1_zero_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter_return_wit_1_zero : bubble_sort_alter_return_wit_1_zero.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter_return_wit_1_zero_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_alter_return_wit_2_normal_split_goal_1 : bubble_sort_alter_return_wit_2_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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
  Goal_apply proof_of_bubble_sort_alter_return_wit_2_normal_split_goal_1.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_2_normal_split_goal_1 : bubble_sort_alter1_entail_wit_2_normal_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_2_normal_split_goal_2 : bubble_sort_alter1_entail_wit_2_normal_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (n_pre - 0) with n_pre by lia.
  apply increasing_sublist_same.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_2_normal_split_goal_3 : bubble_sort_alter1_entail_wit_2_normal_split_goal_3.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_2_normal : bubble_sort_alter1_entail_wit_2_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_2_normal_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_2_normal_split_goal_2.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_2_normal_split_goal_3.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_3_normal_split_goal_1 : bubble_sort_alter1_entail_wit_3_normal_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_3_normal_split_goal_2 : bubble_sort_alter1_entail_wit_3_normal_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_3_normal : bubble_sort_alter1_entail_wit_3_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_3_normal_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_3_normal_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_4_1_normal_split_goal_1 : bubble_sort_alter1_entail_wit_4_1_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (increasing (sublist (n_pre - i_2) n_pre (adjacent_swap a_3 j))).
  rewrite sublist_after_adjacent_swap by lia.
  exact PreH9.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_4_1_normal_split_goal_2 : bubble_sort_alter1_entail_wit_4_1_normal_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  change (Permutation l (adjacent_swap a_3 j)).
  eapply Permutation_trans.
  - exact PreH8.
  - unfold adjacent_swap.
    apply permutation_swap_Znth; lia.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_4_1_normal_split_goal_3 : bubble_sort_alter1_entail_wit_4_1_normal_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat rewrite Zlength_replace_Znth.
  auto.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_4_1_normal : bubble_sort_alter1_entail_wit_4_1_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_4_1_normal_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_4_1_normal_split_goal_2.
  - Goal_apply proof_of_bubble_sort_alter1_entail_wit_4_1_normal_split_goal_3.
Qed.

Lemma proof_of_bubble_sort_alter1_entail_wit_5_normal_split_goal_1 : bubble_sort_alter1_entail_wit_5_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_bubble_sort_alter1_entail_wit_5_normal : bubble_sort_alter1_entail_wit_5_normal.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bubble_sort_alter1_entail_wit_5_normal_split_goal_1.
Qed.

Lemma proof_of_bubble_sort_alter1_return_wit_1_zero_split_goal_1 : bubble_sort_alter1_return_wit_1_zero_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply increasing_length_le_1; lia.
Qed.

Lemma proof_of_bubble_sort_alter1_return_wit_1_zero_split_goal_2 : bubble_sort_alter1_return_wit_1_zero_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). Qed.

Lemma proof_of_bubble_sort_alter1_return_wit_1_zero : bubble_sort_alter1_return_wit_1_zero.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bubble_sort_alter1_return_wit_1_zero_split_goal_1.
  - Goal_apply proof_of_bubble_sort_alter1_return_wit_1_zero_split_goal_2.
Qed.

Lemma proof_of_bubble_sort_alter1_return_wit_2_normal_split_goal_1 : bubble_sort_alter1_return_wit_2_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
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

Lemma proof_of_bubble_sort_alter1_return_wit_2_normal : bubble_sort_alter1_return_wit_2_normal.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bubble_sort_alter1_return_wit_2_normal_split_goal_1.
Qed.
