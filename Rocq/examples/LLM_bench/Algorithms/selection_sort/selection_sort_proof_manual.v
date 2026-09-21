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
Require Import Coq.micromega.Lia.
From SimpleC.EE.LLM_bench.Algorithms.selection_sort Require Import selection_sort_goal.
From SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort Require Import optimized_selection_sort_lib.
From SimpleC.EE.QCP_demos_LLM Require Import bubble_sort_lib.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Ltac selection_progress :=
  repeat match goal with
  | H : selection_minimum (sublist ?lo ?hi ?l) (Znth ?selected ?l 0) |- _ =>
      let HH := fresh "Hminimum" in
      pose proof (proj1 (selection_minimum_index l lo hi selected ltac:(lia) ltac:(lia)) H) as HH;
      clear H; rename HH into H
  end.

Lemma proof_of_sortArray_entail_wit_1_split_goal_1 : sortArray_entail_wit_1_split_goal_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
Qed.

Lemma proof_of_sortArray_entail_wit_1_split_goal_2 : sortArray_entail_wit_1_split_goal_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
Qed.

Lemma proof_of_sortArray_entail_wit_1_split_goal_3 : sortArray_entail_wit_1_split_goal_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
Qed.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Proof.
	aggressive_pre_process.
	- Goal_apply proof_of_sortArray_entail_wit_1_split_goal_1.
	- Goal_apply proof_of_sortArray_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_sortArray_entail_wit_2_split_goal_1 : sortArray_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply (proj2 (selection_minimum_index a_2 i_2 (i_2 + 1) i_2 ltac:(lia) ltac:(lia))).
  intros index Hindex. assert (index = i_2) by lia. subst index. lia.
Qed.

Lemma proof_of_sortArray_entail_wit_2_split_goal_2 : sortArray_entail_wit_2_split_goal_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	aggressive_pre_process.
	- Goal_apply proof_of_sortArray_entail_wit_2_split_goal_1.
	- Goal_apply proof_of_sortArray_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1_split_goal_2 : sortArray_entail_wit_3_1_split_goal_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
	assert (Hlen_a : Zlength a_2 = numsSize_pre).
	{ rewrite Zlength_replace_Znth in PreH1.
	  rewrite Zlength_replace_Znth in PreH1.
	  exact PreH1. }
	apply increasing_sublist_intro.
	- lia.
	- lia.
	- intros p q Hpq.
	  repeat rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
	  eapply (increasing_sublist_elim a_2 0 i_2 p q); eauto; lia.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1_split_goal_3 : sortArray_entail_wit_3_1_split_goal_3.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
	assert (Hlen_a : Zlength a_2 = numsSize_pre).
	{ rewrite Zlength_replace_Znth in PreH1.
	  rewrite Zlength_replace_Znth in PreH1.
	  exact PreH1. }
	eapply Permutation_trans.
	- exact PreH10.
	- apply permutation_swap_Znth_lt; lia.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1_split_goal_1 : sortArray_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlength : Zlength a_2 = numsSize_pre).
  { repeat rewrite Zlength_replace_Znth in PreH1. exact PreH1. }
  selection_progress.
  apply (proj2 (selection_minimum_index (replace_Znth j_2 (Znth i_2 a_2 0) (replace_Znth i_2 (Znth j_2 a_2 0) a_2)) i_2 (j_2 + 1) i_2 ltac:(lia)
    ltac:(repeat rewrite Zlength_replace_Znth; lia))).
  intros index Hindex.
  rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Same by lia.
  destruct (Z.eq_dec index j_2) as [Heq | Hneq].
  - subst index. rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia). lia.
  - rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    destruct (Z.eq_dec index i_2) as [Heq | Hneqi].
    + subst index. rewrite Znth_replace_Znth_Same by lia. lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      specialize (PreH13 index ltac:(lia)). lia.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Proof.
	aggressive_pre_process.
	- Goal_apply proof_of_sortArray_entail_wit_3_1_split_goal_1.
	- Goal_apply proof_of_sortArray_entail_wit_3_1_split_goal_2.
	- Goal_apply proof_of_sortArray_entail_wit_3_1_split_goal_3.
Qed.

Lemma proof_of_sortArray_entail_wit_3_2_split_goal_1 : sortArray_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  apply (proj2 (selection_minimum_index a_2 i_2 (j_2 + 1) i_2 ltac:(lia) ltac:(lia))).
  intros index Hindex. destruct (Z.eq_dec index j_2) as [Heq | Hneq].
  - subst index. lia.
  - apply PreH13. lia.
Qed.

Lemma proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Proof. aggressive_pre_process. Goal_apply proof_of_sortArray_entail_wit_3_2_split_goal_1. Qed.

Lemma proof_of_sortArray_entail_wit_4_split_goal_1 : sortArray_entail_wit_4_split_goal_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
	assert (Hj : j = numsSize_pre) by lia.
	destruct H as [[[Hp0 Hpi] Hiq] Hqn].
	destruct (Z_lt_ge_dec p i_2) as [Hplt | Hpge].
	- apply PreH11. lia.
	- assert (p = i_2) by lia.
	  subst p.
	  apply PreH12.
	  lia.
Qed.

Lemma proof_of_sortArray_entail_wit_4_split_goal_2 : sortArray_entail_wit_4_split_goal_2.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
	apply increasing_sublist_intro; try lia.
	intros p q [Hp0 [Hpq Hqi]].
	destruct (Z.eq_dec q i_2) as [Hqeq | Hqneq].
	- subst q.
	  destruct (Z.eq_dec p i_2) as [Hpeq | Hpneq].
	  + subst p. lia.
	  + apply PreH11. lia.
	- eapply (increasing_sublist_elim a_2 0 i_2 p q); eauto; lia.
Qed.

Lemma proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Proof.
	aggressive_pre_process.
	- Goal_apply proof_of_sortArray_entail_wit_4_split_goal_1.
	- Goal_apply proof_of_sortArray_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_sortArray_return_wit_1_split_goal_1 : sortArray_return_wit_1_split_goal_1.
Proof.
	LLM_pre_process ltac:(int_auto).
	all: selection_progress.
	assert (Hi : i = numsSize_pre) by lia.
	subst i.
	replace a with (sublist 0 numsSize_pre a).
	- exact PreH8.
	- rewrite sublist_self by lia. reflexivity.
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	aggressive_pre_process.
	Goal_apply proof_of_sortArray_return_wit_1_split_goal_1.
Qed.
