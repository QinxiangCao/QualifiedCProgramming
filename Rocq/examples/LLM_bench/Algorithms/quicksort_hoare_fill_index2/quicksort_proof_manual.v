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
From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_fill_index2 Require Import quicksort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib.
Local Open Scope sac.


(** Convert Forall segments only inside proofs when reusing indexed helpers. *)
Ltac quicksort_bounds :=
  try dump_pre_spatial;
  repeat rewrite Zlength_replace_Znth in *;
  repeat match goal with
  | H : Forall ?P (sublist ?lo ?hi ?values) |- _ =>
      rewrite (quicksort_Forall_sublist P values lo hi ltac:(lia) ltac:(repeat rewrite Zlength_replace_Znth; lia)) in H
  end;
  try match goal with
  | |- Forall ?P (sublist ?lo ?hi ?values) =>
      apply (proj2 (quicksort_Forall_sublist P values lo hi ltac:(lia) ltac:(repeat rewrite Zlength_replace_Znth; lia)))
  end;
  intros index Hindex;
  repeat match goal with
  | |- context [Znth ?k (replace_Znth ?j ?value ?values) 0] =>
      let Hequal := fresh "Hequal" in let Hdifferent := fresh "Hdifferent" in
      destruct (Z.eq_dec k j) as [Hequal | Hdifferent];
      [rewrite Hequal; rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia)
      |rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia)]
  end;
  repeat match goal with
  | H : forall k : Z, _ -> ?P (Znth k ?values 0) |- context [Znth ?k ?values 0] =>
      let T := constr:(P (Znth k values 0)) in
      match goal with
      | _ : T |- _ => fail 1
      | _ => let HH := fresh "Helement" in assert T as HH by (apply H; lia)
      end
  end;
  simpl in *; try lia; try congruence.

Lemma proof_of_partition_entail_wit_1_split_goal_1 : partition_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_2 : partition_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_3 : partition_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).

  apply same_outside_range_refl.
Qed.

Lemma proof_of_partition_entail_wit_1_split_goal_4 : partition_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).

  rewrite replace_Znth_Znth by (rewrite PreH1; lia).
  apply Permutation_refl.
Qed.

Lemma proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_partition_entail_wit_3_split_goal_1 : partition_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
  all: destruct (Z.eq_dec index j_2) as [Heq | Hneq]; [subst index; lia | apply PreH16; lia].
Qed.

Lemma proof_of_partition_entail_wit_3 : partition_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_partition_entail_wit_4_split_goal_1 : partition_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
Qed.

Lemma proof_of_partition_entail_wit_4_split_goal_2 : partition_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
Qed.

Lemma proof_of_partition_entail_wit_4_split_goal_3 : partition_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) by quicksort_bounds.
  assert (IndexedPreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  eapply same_outside_range_trans_local.
  - exact PreH15.
  - apply same_outside_range_replace_inside_local; try lia.
Qed.

Lemma proof_of_partition_entail_wit_4_split_goal_4 : partition_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) by quicksort_bounds.
  assert (IndexedPreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH15 as Hsame.
  destruct Hsame as [Hsame_len _].
  assert (Hhigh : high_pre < Zlength l) by (rewrite Hsame_len, Hlen_l1; exact PreH10).
  eapply partition_hole_outer_fill_left_perm_split_local; eauto; lia.
Qed.

Lemma proof_of_partition_entail_wit_4 : partition_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_partition_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_partition_entail_wit_5_split_goal_1 : partition_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
  all: destruct (Z.eq_dec index i_2) as [Heq | Hneq]; [subst index; lia | apply PreH15; lia].
Qed.

Lemma proof_of_partition_entail_wit_5 : partition_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_partition_entail_wit_6_split_goal_1 : partition_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
Qed.

Lemma proof_of_partition_entail_wit_6_split_goal_2 : partition_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: quicksort_bounds.
Qed.

Lemma proof_of_partition_entail_wit_6_split_goal_3 : partition_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) by quicksort_bounds.
  assert (IndexedPreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  eapply same_outside_range_trans_local.
  - exact PreH15.
  - apply same_outside_range_replace_inside_local; try lia.
Qed.

Lemma proof_of_partition_entail_wit_6_split_goal_4 : partition_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) by quicksort_bounds.
  assert (IndexedPreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH15 as Hsame.
  destruct Hsame as [Hsame_len _].
  assert (Hhigh : high_pre < Zlength l) by (rewrite Hsame_len, Hlen_l1; exact PreH10).
  eapply partition_hole_left_fill_right_perm_split_local; eauto; lia.
Qed.

Lemma proof_of_partition_entail_wit_6 : partition_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_partition_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_partition_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_partition_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_1 : partition_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) by quicksort_bounds.
  assert (IndexedPreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH14 as Hsame.
  destruct Hsame as [Hsame_len _].
  assert (Hhigh : high_pre < Zlength l) by (rewrite Hsame_len, Hlen_l1; exact PreH9).
  eapply partition_hole_outer_exit_partitioned_split_local; eauto; lia.
Qed.

Lemma proof_of_partition_return_wit_1_split_goal_2 : partition_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) by quicksort_bounds.
  assert (IndexedPreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  eapply same_outside_range_trans_local.
  - exact PreH14.
  - apply same_outside_range_replace_inside_local; try lia.
Qed.

Lemma proof_of_partition_return_wit_1 : partition_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_return_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_partition_return_wit_2_split_goal_1 : partition_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) by quicksort_bounds.
  assert (IndexedPreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  pose proof PreH14 as Hsame.
  destruct Hsame as [Hsame_len _].
  assert (Hhigh : high_pre < Zlength l) by (rewrite Hsame_len, Hlen_l1; exact PreH9).
  eapply partition_hole_left_exit_partitioned_split_local; eauto; lia.
Qed.

Lemma proof_of_partition_return_wit_2_split_goal_2 : partition_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) by quicksort_bounds.
  assert (IndexedPreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) by quicksort_bounds.

  assert (Hlen_l1 : Zlength l1_2 = n) by (rewrite Zlength_replace_Znth in PreH1; exact PreH1).
  eapply same_outside_range_trans_local.
  - exact PreH14.
  - apply same_outside_range_replace_inside_local; try lia.
Qed.

Lemma proof_of_partition_return_wit_2_split_goal_3 : partition_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (IndexedPreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) by quicksort_bounds.
  assert (IndexedPreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) by quicksort_bounds.

  assert (Hij_eq : i = j) by lia.
  subst j.
  exact PreH13.
Qed.

Lemma proof_of_partition_return_wit_2 : partition_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_return_wit_2_split_goal_1.
  - Goal_apply proof_of_partition_return_wit_2_split_goal_2.
  - Goal_apply proof_of_partition_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_quicksort_range_return_wit_1_split_goal_1 : quicksort_range_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).

  rewrite same_outside_range_unfold in PreH13.
  destruct PreH13 as [Hlen12 Heq12].
  rewrite same_outside_range_unfold in PreH7.
  destruct PreH7 as [Hlen23 Heq23].
  rewrite same_outside_range_unfold in PreH3.
  destruct PreH3 as [Hlen34 Heq34].
  assert (Hlen3 : Zlength l1_3 = n) by (rewrite Hlen34; exact PreH1).
  assert (Hlen2 : Zlength l1_2 = n) by (rewrite Hlen23; exact Hlen3).
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_left_local.
    - exact PreH6.
    - exact PreH17.
    - apply (proj2 (same_outside_range_unfold _ _ _ _)); exact (conj Hlen23 Heq23).
    - rewrite Hlen2. exact PreH19.
    - exact PreH14.
  }
  assert (Hpart4 : partitioned_at l1_4 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_right_local.
    - exact PreH2.
    - exact PreH17.
    - apply (proj2 (same_outside_range_unfold _ _ _ _)); exact (conj Hlen34 Heq34).
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

  rewrite same_outside_range_unfold in PreH13.
  destruct PreH13 as [Hlen12 Heq12].
  rewrite same_outside_range_unfold in PreH7.
  destruct PreH7 as [Hlen23 Heq23].
  rewrite same_outside_range_unfold in PreH3.
  destruct PreH3 as [Hlen34 Heq34].
  assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
  {
    rewrite same_outside_range_unfold.
    split.
    - exact Hlen23.
    - intros k Hk Hout.
      apply Heq23.
      + exact Hk.
      + destruct Hout as [Hlt | Hgt]; [left | right]; lia.
  }
  assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
  {
    rewrite same_outside_range_unfold.
    split.
    - exact Hlen34.
    - intros k Hk Hout.
      apply Heq34.
      + exact Hk.
      + destruct Hout as [Hlt | Hgt]; [left | right]; lia.
  }
  eapply same_outside_range_trans_local.
  - apply (proj2 (same_outside_range_unfold _ _ _ _)); exact (conj Hlen12 Heq12).
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

  rewrite same_outside_range_unfold in PreH10.
  destruct PreH10 as [Hlen12 Heq12].
  rewrite same_outside_range_unfold in PreH3.
  destruct PreH3 as [Hlen23 Heq23].
  assert (Hlen2 : Zlength l1_2 = n) by (rewrite Hlen23; exact PreH1).
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_right_local.
    - exact PreH2.
    - exact PreH14.
    - apply (proj2 (same_outside_range_unfold _ _ _ _)); exact (conj Hlen23 Heq23).
    - rewrite Hlen2. exact PreH16.
    - exact PreH11.
  }
  eapply (quicksort_partition_combine_right_guard_local l1_3 left_pre right_pre retval).
  - exact PreH14.
  - rewrite PreH1. exact PreH16.
  - split; [exact PreH7 | exact PreH8].
  - exact PreH6.
  - exact Hpart3.
  - exact PreH4.
Qed.

Lemma proof_of_quicksort_range_return_wit_2_split_goal_2 : quicksort_range_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).

  rewrite same_outside_range_unfold in PreH10.
  destruct PreH10 as [Hlen12 Heq12].
  rewrite same_outside_range_unfold in PreH3.
  destruct PreH3 as [Hlen23 Heq23].
  rewrite same_outside_range_unfold.
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

  rewrite same_outside_range_unfold in PreH10.
  destruct PreH10 as [Hlen12 Heq12].
  rewrite same_outside_range_unfold in PreH4.
  destruct PreH4 as [Hlen23 Heq23].
  assert (Hlen2 : Zlength l1_2 = n) by (rewrite Hlen23; exact PreH1).
  assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
  {
    eapply partitioned_at_preserved_by_left_local.
    - exact PreH3.
    - exact PreH14.
    - apply (proj2 (same_outside_range_unfold _ _ _ _)); exact (conj Hlen23 Heq23).
    - rewrite Hlen2. exact PreH16.
    - exact PreH11.
  }
  eapply (quicksort_partition_combine_left_guard_local l1_3 left_pre right_pre retval).
  - exact PreH14.
  - rewrite PreH1. exact PreH16.
  - lia.
  - lia.
  - exact Hpart3.
  - exact PreH5.
Qed.

Lemma proof_of_quicksort_range_return_wit_3_split_goal_2 : quicksort_range_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).

  rewrite same_outside_range_unfold in PreH10.
  destruct PreH10 as [Hlen12 Heq12].
  rewrite same_outside_range_unfold in PreH4.
  destruct PreH4 as [Hlen23 Heq23].
  rewrite same_outside_range_unfold.
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

  eapply (quicksort_partition_combine_short_local l1_2 left_pre right_pre retval); try eassumption; try lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_range_return_wit_4_split_goal_1.
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
  - Goal_apply proof_of_quicksort_return_wit_1_split_goal_1.
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

