Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition OneSubsequenceAddition (before after : list Z) : Prop :=
  exists chosen prefix suffix,
    0 < Zlength before /\
    (exists i, 0 <= i < Zlength before /\ chosen i) /\
    before = prefix ++ suffix /\
    after = prefix ++
      [sum (fun i : Z => 0 <= i < Zlength before /\ chosen i)
         (fun i => Znth i before 0)] ++ suffix.

Definition Pre (final : list Z) : Prop :=
  1 <= Zlength final <= 200000 /\
  Forall (fun x => 1 <= x <= 200000) final.

Definition Spec (final : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> clos_refl_trans OneSubsequenceAddition [1] final).

Definition SortedAcceptance (sorted : list Z) : Prop :=
  0 < Zlength sorted /\
  Znth 0 sorted 0 = 1 /\
  forall i,
    1 <= i < Zlength sorted ->
    Znth i sorted 0 <= ListLib.sum (sublist 0 i sorted).

Definition PrefixAdditionState
    (sorted : list Z) (processed total : Z) : Prop :=
  1 <= processed <= Zlength sorted /\
  total = ListLib.sum (sublist 0 processed sorted) /\
  Znth 0 sorted 0 = 1 /\
  forall i,
    1 <= i < processed ->
    Znth i sorted 0 <= ListLib.sum (sublist 0 i sorted).

Definition FullDecisionSpecBridge
    (original sorted : list Z) : Prop :=
  forall out,
    Spec original out <->
      (out = 0 \/ out = 1) /\
      (out = 1 <-> SortedAcceptance sorted).

Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Lemma sorted_index_bounds_from_permutation__prefix_state :
  forall (input sorted : list Z) lo hi,
    (forall i, 0 <= i < Zlength input ->
      lo <= Znth i input 0 <= hi) ->
    Permutation input sorted ->
    forall i, 0 <= i < Zlength sorted ->
      lo <= Znth i sorted 0 <= hi.
Proof.
  intros input sorted lo hi Hbounds Hperm i Hi.
  apply (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 sorted)).
  - eapply Permutation_Forall.
    + exact Hperm.
    + apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 input)).
      exact Hbounds.
  - exact Hi.
Qed.
Lemma sum_sublist_succ__prefix_state :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    ListLib.sum (sublist 0 (i + 1) xs) =
      ListLib.sum (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app.
  simpl.
  lia.
Qed.
Lemma prefix_state_at_end_sorted_acceptance__decision_results :
  forall sorted processed total,
    Zlength sorted <= processed ->
    PrefixAdditionState sorted processed total ->
    SortedAcceptance sorted.
Proof.
  intros sorted processed total Hend Hstate.
  unfold PrefixAdditionState in Hstate.
  unfold SortedAcceptance.
  destruct Hstate as [[Hprocessed_pos Hprocessed_bound]
    [Htotal [Hhead Hprefix]]].
  repeat split.
  - lia.
  - exact Hhead.
  - intros j Hj.
    apply Hprefix.
    lia.
Qed.
Lemma prefix_state_violation_not_sorted_acceptance__decision_results :
  forall sorted processed total,
    processed < Zlength sorted ->
    PrefixAdditionState sorted processed total ->
    Znth processed sorted 0 > total ->
    ~ SortedAcceptance sorted.
Proof.
  intros sorted processed total Hprocessed_lt Hstate Hviolation Haccept.
  unfold PrefixAdditionState in Hstate.
  unfold SortedAcceptance in Haccept.
  destruct Hstate as [[Hprocessed_pos Hprocessed_bound]
    [Htotal [Hhead Hprefix]]].
  destruct Haccept as [Hlength [Haccepted_head Haccepted_prefix]].
  specialize (Haccepted_prefix processed).
  rewrite Htotal in Hviolation.
  lia.
Qed.
