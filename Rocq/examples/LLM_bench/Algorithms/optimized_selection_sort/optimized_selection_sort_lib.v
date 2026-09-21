(* Shared minimum predicate for both selection-sort implementations. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib MonotonicList.
Require Import MaxMinLib.MaxMin.
Local Open Scope Z_scope.

(** Minimum value of the mathematical candidate segment. *)
Definition selection_minimum (values : list Z) (value : Z) : Prop :=
  min_value_of_subset Z.le (fun x => In x values) (fun x : Z => x) value.

Lemma selection_minimum_index : forall values lo hi selected,
  0 <= lo <= selected -> selected < hi <= Zlength values ->
  (selection_minimum (sublist lo hi values) (Znth selected values 0) <->
   forall index, lo <= index < hi ->
     Znth selected values 0 <= Znth index values 0).
Proof.
  intros values lo hi selected Hlo Hhi.
  unfold selection_minimum, min_value_of_subset, min_object_of_subset.
  split.
  - intros [candidate [[Hcandidate Hbound] Heq]] index Hindex.
    subst candidate. apply Hbound.
    assert (Hin : In (Znth (index - lo) (sublist lo hi values) 0)
                     (sublist lo hi values)).
    { unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite <- Zlength_correct.
      rewrite Zlength_sublist by lia. lia. }
    rewrite Znth_sublist in Hin by lia.
    replace (index - lo + lo) with index in Hin by lia. exact Hin.
  - intros Hbound. exists (Znth selected values 0). split; [split | reflexivity].
    + assert (Hin : In (Znth (selected - lo) (sublist lo hi values) 0)
                       (sublist lo hi values)).
      { unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite <- Zlength_correct.
        rewrite Zlength_sublist by lia. lia. }
      rewrite Znth_sublist in Hin by lia.
      replace (selected - lo + lo) with selected in Hin by lia. exact Hin.
    + intros candidate Hcandidate.
      assert (Hall : Forall (Z.le (Znth selected values 0)) (sublist lo hi values)).
      { apply (proj2 (Forall_Znth _ 0 _)). intros index Hindex.
        rewrite Zlength_sublist in Hindex by lia.
        rewrite Znth_sublist by lia. apply Hbound. lia. }
      apply Forall_forall with (x := candidate) in Hall; assumption.
Qed.

From Coq Require Import ZArith List Sorting.Permutation.
From AUXLib Require Import ListLib.

(** Mathematical result relation for any in-place ascending-sort
    implementation.  It deliberately says nothing about selection-sort
    indices or loop transitions. *)
Definition optimized_selection_sort_result
    (input output : list Z) : Prop :=
  Permutation input output /\ increasing output.
