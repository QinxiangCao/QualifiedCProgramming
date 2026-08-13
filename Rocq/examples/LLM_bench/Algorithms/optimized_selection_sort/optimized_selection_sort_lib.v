From Coq Require Import ZArith List Sorting.Permutation.
From AUXLib Require Import ListLib.

(** Mathematical result relation for any in-place ascending-sort
    implementation.  It deliberately says nothing about selection-sort
    indices or loop transitions. *)
Definition optimized_selection_sort_result
    (input output : list Z) : Prop :=
  Permutation input output /\ increasing output.
