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
From SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort Require Import optimized_selection_sort_goal.
From SimpleC.EE.QCP_demos_LLM Require Import bubble_sort_lib.
From AUXLib Require Import MonotonicList.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib.
Local Open Scope sac.


Ltac selection_progress :=
  repeat match goal with
  | H : selection_minimum (sublist ?lo ?hi ?l) (Znth ?selected ?l 0) |- _ =>
      let HH := fresh "Hminimum" in
      pose proof (proj1 (selection_minimum_index l lo hi selected ltac:(lia) ltac:(lia)) H) as HH;
      clear H; rename HH into H
  end.
Ltac selection_read_swap :=
  repeat first [rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia)
               |rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia)].

Lemma proof_of_optimized_selection_sort_entail_wit_1_split_goal_1 : optimized_selection_sort_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_1_split_goal_2 : optimized_selection_sort_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_1_split_goal_3 : optimized_selection_sort_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_1 : optimized_selection_sort_entail_wit_1.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_entail_wit_1_split_goal_1 | Goal_apply proof_of_optimized_selection_sort_entail_wit_1_split_goal_2 | Goal_apply proof_of_optimized_selection_sort_entail_wit_1_split_goal_3 ].
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_2_split_goal_1 : optimized_selection_sort_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply (proj2 (selection_minimum_index cur_2 i_2 (i_2 + 1) i_2 ltac:(lia) ltac:(lia))).
  intros index Hindex. assert (index = i_2) by lia. subst index. lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_2_split_goal_2 : optimized_selection_sort_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_2 : optimized_selection_sort_entail_wit_2.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_entail_wit_2_split_goal_1 | Goal_apply proof_of_optimized_selection_sort_entail_wit_2_split_goal_2 ].
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_3_1_split_goal_1 : optimized_selection_sort_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  apply (proj2 (selection_minimum_index cur_2 i_2 (j_2 + 1) j_2 ltac:(lia) ltac:(lia))).
  intros index Hindex. destruct (Z.eq_dec index j_2) as [Heq | Hneq].
  - subst index. lia.
  - specialize (PreH16 index ltac:(lia)). lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_3_1 : optimized_selection_sort_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_entail_wit_3_1_split_goal_1 ].
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_3_2_split_goal_1 : optimized_selection_sort_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  apply (proj2 (selection_minimum_index cur_2 i_2 (j_2 + 1) min_index_2 ltac:(lia) ltac:(lia))).
  intros index Hindex. destruct (Z.eq_dec index j_2) as [Heq | Hneq].
  - subst index. lia.
  - apply PreH16. lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_3_2 : optimized_selection_sort_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_entail_wit_3_2_split_goal_1 ].
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_1 : optimized_selection_sort_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  assert (Hj : j = n_pre) by lia. subst j.
  destruct (Z.eq_dec p i_2) as [Heqp | Hneqp].
  - subst p. selection_read_swap.
    destruct (Z.eq_dec q min_index) as [Heqq | Hneqq].
    + subst q. selection_read_swap. apply PreH17. lia.
    + selection_read_swap. apply PreH17. lia.
  - assert (Hp : p < i_2) by lia. selection_read_swap.
    destruct (Z.eq_dec q min_index) as [Heqq | Hneqq].
    + subst q. selection_read_swap. apply PreH16. lia.
    + selection_read_swap. apply PreH16. lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_2 : optimized_selection_sort_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  apply increasing_sublist_intro; try (repeat rewrite Zlength_replace_Znth; lia).
  intros p q [Hp [Hpq Hq]].
  destruct (Z.eq_dec q i_2) as [Heqq | Hneqq].
  - subst q. destruct (Z.eq_dec p i_2) as [Heqp | Hneqp].
    + subst p. lia.
    + selection_read_swap. apply PreH16. lia.
  - selection_read_swap.
    eapply (increasing_sublist_elim cur_2 0 i_2 p q); eauto; lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_3 : optimized_selection_sort_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply Permutation_trans; [exact PreH14 |].
  apply permutation_swap_Znth_lt. lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_1 : optimized_selection_sort_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_1 | Goal_apply proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_2 | Goal_apply proof_of_optimized_selection_sort_entail_wit_4_1_split_goal_3 ].
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_1 : optimized_selection_sort_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  assert (Hj : j = n_pre) by lia. subst j.
  destruct (Z.eq_dec p i_2) as [Heqp | Hneqp].
  - subst p. subst min_index. apply PreH16. lia.
  - apply PreH15. lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_2 : optimized_selection_sort_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto). selection_progress.
  subst min_index.
  apply increasing_sublist_intro; try lia.
  intros p q [Hp [Hpq Hq]].
  destruct (Z.eq_dec q i_2) as [Heqq | Hneqq].
  - subst q. destruct (Z.eq_dec p i_2) as [Heqp | Hneqp].
    + subst p. lia.
    + apply PreH15. lia.
  - eapply (increasing_sublist_elim cur_2 0 i_2 p q); eauto; lia.
Qed.

Lemma proof_of_optimized_selection_sort_entail_wit_4_2 : optimized_selection_sort_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_1 | Goal_apply proof_of_optimized_selection_sort_entail_wit_4_2_split_goal_2 ].
Qed.

Lemma proof_of_optimized_selection_sort_return_wit_1_split_goal_1 : optimized_selection_sort_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold optimized_selection_sort_result. split; [assumption |].
  apply (proj1 (mono_nondec_iff_increasing cur)).
  unfold mono_nondec. intros p q Hp Hpq Hq.
  destruct (Z_lt_ge_dec q i) as [Hqi | Hiq].
  - eapply (increasing_sublist_elim cur 0 i p q); eauto; lia.
  - assert (Hqi : q = i) by lia. subst q.
    destruct (Z.eq_dec p i) as [Hpi | Hpi].
    + subst p. lia.
    + apply PreH11. lia.
Qed.

Lemma proof_of_optimized_selection_sort_return_wit_1 : optimized_selection_sort_return_wit_1.
Proof.
  aggressive_pre_process.
  all: first [ Goal_apply proof_of_optimized_selection_sort_return_wit_1_split_goal_1 ].
Qed.
