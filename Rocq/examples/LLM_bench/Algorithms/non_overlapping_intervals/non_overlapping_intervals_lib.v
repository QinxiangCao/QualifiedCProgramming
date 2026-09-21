Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** A mathematical interval record.  The C representation is deliberately
    kept separate: its two fields live in the disjoint [st] and [ed] arrays. *)
Definition interval : Type := (Z * Z)%type.

Definition mk_interval (start finish : Z) : interval := (start, finish).
Definition interval_start (p : interval) : Z := fst p.
Definition interval_end (p : interval) : Z := snd p.
Definition default_interval : interval := mk_interval 0 1.

(** [PairIntervals starts ends ps] says that the two parallel logical arrays
    encode exactly the complete interval records in [ps], at the same indices.
    In particular, no specification is phrased through a flat array. *)
Definition PairIntervals
    (starts ends : list Z) (ps : list interval) : Prop :=
  Forall2 (fun start p => start = interval_start p) starts ps /\
  Forall2 (fun finish p => finish = interval_end p) ends ps.

Definition IntervalPermutation : list interval -> list interval -> Prop :=
  @Permutation interval.

(** Exact record-level swap used by both parallel arrays. *)
Definition interval_swap
    (ps : list interval) (i j : Z) : list interval :=
  replace_Znth j (Znth i ps default_interval)
    (replace_Znth i (Znth j ps default_interval) ps).

Definition IntervalSwappedAt
    (before after : list interval) (i j : Z) : Prop :=
  after = interval_swap before i j.

(** Quicksort changes only the requested complete-record range. *)
Definition IntervalSameOutsideRange
    (before after : list interval) (left right : Z) : Prop :=
  Zlength before = Zlength after /\
  forall k,
    0 <= k < Zlength before ->
    (k < left \/ right < k) ->
    Znth k after default_interval = Znth k before default_interval.

(** Lomuto partition places its pivot record between a non-strict left
    partition and a strict right partition, ordered by interval end. *)
Definition IntervalPartitionedAt
    (ps : list interval) (low high pivot : Z) : Prop :=
  low <= pivot <= high /\
  (forall k,
      low <= k < pivot ->
      interval_end (Znth k ps default_interval) <=
      interval_end (Znth pivot ps default_interval)) /\
  (forall k,
      pivot < k <= high ->
      interval_end (Znth pivot ps default_interval) <
      interval_end (Znth k ps default_interval)).

Definition IntervalsEndSortedRange
    (ps : list interval) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    interval_end (Znth i ps default_interval) <=
    interval_end (Znth j ps default_interval).

Definition IntervalsEndSorted (ps : list interval) : Prop :=
  forall i j,
    0 <= i -> i <= j -> j < Zlength ps ->
    interval_end (Znth i ps default_interval) <=
    interval_end (Znth j ps default_interval).

(** A retained schedule is ordered from left to right and therefore contains
    no overlapping pair.  Touching endpoints are explicitly permitted. *)
Definition NonOverlappingSchedule (kept : list interval) : Prop :=
  forall i j,
    0 <= i -> i < j -> j < Zlength kept ->
    interval_end (Znth i kept default_interval) <=
    interval_start (Znth j kept default_interval).

(** [kept] selects complete interval records from [input], with multiplicity. *)
Definition IntervalSelection
    (input kept : list interval) : Prop :=
  exists removed,
    Permutation input (kept ++ removed).

Definition FeasibleRemovalCount
    (input : list interval) (removed_count : Z) : Prop :=
  exists kept,
    IntervalSelection input kept /\
    NonOverlappingSchedule kept /\
    removed_count = Zlength input - Zlength kept.

(** The required optimum is stated directly through the repository MinMax
    library: [answer] is the minimum of all feasible removal counts. *)
Definition MinimumRemovals
    (input : list interval) (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (FeasibleRemovalCount input)
    (fun removed_count => removed_count)
    answer.

(** Predicate-first Lomuto scan state.  Machine index ranges, parallel-array
    ownership, record bounds, and array-read bindings stay in C annotations. *)
Definition LomutoScanState
    (before current : list interval)
    (low high placed scanned pivot_end : Z) : Prop :=
  IntervalPermutation before current /\
  IntervalSameOutsideRange before current low high /\
  interval_end (Znth high current default_interval) = pivot_end /\
  (forall k,
      low <= k <= placed ->
      interval_end (Znth k current default_interval) <= pivot_end) /\
  (forall k,
      placed < k < scanned ->
      pivot_end < interval_end (Znth k current default_interval)).

Definition schedule_finish (kept : list interval) : Z :=
  interval_end
    (Znth (Zlength kept - 1) kept default_interval).

(** On a finish-sorted prefix, the greedy schedule has maximum cardinality;
    among schedules of that cardinality it has the smallest last finish. *)
Definition GreedyPrefixState
    (ps : list interval) (processed kept_count last_finish : Z) : Prop :=
  exists kept,
    IntervalSelection (sublist 0 processed ps) kept /\
    NonOverlappingSchedule kept /\
    Zlength kept = kept_count /\
    (* This guards the last-element index used by schedule_finish. *)
    0 < Zlength kept /\
    last_finish = schedule_finish kept /\
    max_value_of_subset Z.le
      (fun alternative =>
         IntervalSelection (sublist 0 processed ps) alternative /\
         NonOverlappingSchedule alternative)
      (@Zlength interval) kept_count /\
    min_value_of_subset Z.le
      (fun alternative =>
         IntervalSelection (sublist 0 processed ps) alternative /\
         NonOverlappingSchedule alternative /\
         Zlength alternative = kept_count)
      schedule_finish last_finish.

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Sorted.
(** Proof adapters for the existing record-swap and greedy arguments. *)
Lemma pair_intervals_indexed : forall starts ends ps,
  PairIntervals starts ends ps <->
Zlength starts = Zlength ends /\
  Zlength ps = Zlength starts /\
  forall k,
    0 <= k < Zlength starts ->
    Znth k ps default_interval =
      mk_interval (Znth k starts 0) (Znth k ends 0).
Proof.
  intros starts ends ps. unfold PairIntervals.
  rewrite (Forall2_nth_iff _ _ _ starts ps 0 default_interval).
  rewrite (Forall2_nth_iff _ _ _ ends ps 0 default_interval).
  rewrite !Zlength_correct. unfold Znth, mk_interval.
  split.
  - intros [[Hs Hsfield] [He Hefield]].
    split; [lia|]. split; [lia|]. intros k Hk.
    specialize (Hsfield (Z.to_nat k) ltac:(lia)).
    specialize (Hefield (Z.to_nat k) ltac:(lia)).
    unfold interval_start, interval_end in *.
    apply injective_projections; simpl; congruence.
  - intros [Hse [Hps Hfield]].
    split; (split; [lia|]); intros k Hk;
      specialize (Hfield (Z.of_nat k) ltac:(lia));
      rewrite Nat2Z.id in Hfield; rewrite Hfield; reflexivity.
Qed.

Lemma greedy_prefix_state_facts : forall ps processed kept_count last_finish,
  GreedyPrefixState ps processed kept_count last_finish <->
exists kept,
    IntervalSelection (sublist 0 processed ps) kept /\
    NonOverlappingSchedule kept /\
    Zlength kept = kept_count /\
    0 < Zlength kept /\
    last_finish = schedule_finish kept /\
    (forall alternative,
        IntervalSelection (sublist 0 processed ps) alternative ->
        NonOverlappingSchedule alternative ->
        Zlength alternative <= kept_count) /\
    (forall alternative,
        IntervalSelection (sublist 0 processed ps) alternative ->
        NonOverlappingSchedule alternative ->
        Zlength alternative = kept_count ->
        last_finish <= schedule_finish alternative).
Proof.
  intros ps processed kept_count last_finish.
  unfold GreedyPrefixState, max_value_of_subset, max_object_of_subset,
    min_value_of_subset, min_object_of_subset.
  split.
  - intros [kept [Hsel [Hno [Hlen [Hpos [Hlast [Hmax Hmin]]]]]]].
    destruct Hmax as [a [[Ha Hupper] Halen]].
    destruct Hmin as [b [[Hb Hlower] Hbend]].
    exists kept. split; [exact Hsel|]. split; [exact Hno|].
    split; [exact Hlen|]. split; [exact Hpos|]. split; [exact Hlast|].
    split.
    + intros alternative Hs Hn.
      rewrite <- Halen. apply Hupper. split; assumption.
    + intros alternative Hs Hn Hl.
      rewrite <- Hbend. apply Hlower. repeat split; assumption.
  - intros [kept [Hsel [Hno [Hlen [Hpos [Hlast [Hmax Hmin]]]]]]].
    exists kept. split; [exact Hsel|]. split; [exact Hno|].
    split; [exact Hlen|]. split; [exact Hpos|]. split; [exact Hlast|].
    split; exists kept; split.
    + split; [split; assumption|]. intros alternative [Hs Hn].
      rewrite Hlen. apply Hmax; assumption.
    + exact Hlen.
    + split; [repeat split; assumption|]. intros alternative [Hs [Hn Hl]].
      rewrite <- Hlast. apply Hmin; assumption.
    + symmetry. exact Hlast.
Qed.

Lemma replace_Znth_swap_form__swap_records :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
      (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3))
    by (subst n1; lia).
  rewrite (replace_Znth_nothing n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
               xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with
      (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3))
    by (subst n2; lia).
  rewrite (replace_Znth_nothing (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3)
    by reflexivity.
  rewrite H1.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__swap_records :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
         (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj; lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat :
        (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite <- Hnat.
      replace (S (Z.to_nat i) + Z.to_nat (j - i - 1))%nat
        with (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat by lia.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3)
    by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form__swap_records.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
Lemma replace_nth_comm_Z__swap_records :
  forall {A : Type} ni nj (l : list A) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni.
  induction ni; intros nj l a b Hneq; destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.
Lemma replace_Znth_comm__swap_records :
  forall {A : Type} (l : list A) i j (a b : A),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_Z__swap_records.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma interval_swap_permutation__swap_records :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    IntervalPermutation ps (interval_swap ps i j).
Proof.
  intros ps i j Hi Hj.
  unfold IntervalPermutation, interval_swap.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt__swap_records; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm__swap_records by lia.
      apply permutation_swap_Znth_lt__swap_records; lia.
    + assert (i = j) by lia.
      subst j.
      rewrite !replace_Znth_Znth.
      apply Permutation_refl.
Qed.
Lemma interval_swap_bounds__swap_records :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) ps) ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (interval_swap ps i j)).
Proof.
  intros ps i j Hi Hj Hbounds.

  eapply Permutation_Forall.
  - apply interval_swap_permutation__swap_records; assumption.
  - exact Hbounds.
Qed.
Lemma pair_intervals_swap__swap_records :
  forall starts ends ps i j,
    PairIntervals starts ends ps ->
    0 <= i < Zlength starts ->
    0 <= j < Zlength starts ->
    PairIntervals
      (replace_Znth j (Znth i starts 0)
        (replace_Znth i (Znth j starts 0) starts))
      (replace_Znth j (Znth i ends 0)
        (replace_Znth i (Znth j ends 0) ends))
      (interval_swap ps i j).
Proof.
  intros starts ends ps i j Hpair Hi Hj.
  apply pair_intervals_indexed in Hpair.
  destruct Hpair as [Hse [Hps Hpoint]].
  assert (Hie : 0 <= i < Zlength ends) by lia.
  assert (Hje : 0 <= j < Zlength ends) by lia.
  assert (Hip : 0 <= i < Zlength ps) by lia.
  assert (Hjp : 0 <= j < Zlength ps) by lia.
  apply pair_intervals_indexed. unfold interval_swap.
  repeat rewrite Zlength_replace_Znth.
  split; [exact Hse|].
  split; [exact Hps|].
  intros k Hk.
  destruct (Z.eq_dec i j) as [Hij | Hij].
  - subst j.
    rewrite !replace_Znth_Znth.
    apply Hpoint; assumption.
  - destruct (Z.eq_dec k i) as [Hki | Hki].
    + subst k.
      rewrite (Znth_replace_Znth_Diff default_interval
        (replace_Znth i (Znth j ps default_interval) ps)
        j i (Znth i ps default_interval))
        by (repeat rewrite Zlength_replace_Znth; lia).
      rewrite (Znth_replace_Znth_Same default_interval ps i
        (Znth j ps default_interval)) by lia.
      rewrite (Znth_replace_Znth_Diff 0
        (replace_Znth i (Znth j starts 0) starts)
        j i (Znth i starts 0))
        by (repeat rewrite Zlength_replace_Znth; lia).
      rewrite (Znth_replace_Znth_Same 0 starts i
        (Znth j starts 0)) by lia.
      rewrite (Znth_replace_Znth_Diff 0
        (replace_Znth i (Znth j ends 0) ends)
        j i (Znth i ends 0))
        by (repeat rewrite Zlength_replace_Znth; lia).
      rewrite (Znth_replace_Znth_Same 0 ends i
        (Znth j ends 0)) by lia.
      apply Hpoint; assumption.
    + destruct (Z.eq_dec k j) as [Hkj | Hkj].
      * subst k.
        rewrite (Znth_replace_Znth_Same default_interval
          (replace_Znth i (Znth j ps default_interval) ps)
          j (Znth i ps default_interval))
          by (repeat rewrite Zlength_replace_Znth; lia).
        rewrite (Znth_replace_Znth_Same 0
          (replace_Znth i (Znth j starts 0) starts)
          j (Znth i starts 0))
          by (repeat rewrite Zlength_replace_Znth; lia).
        rewrite (Znth_replace_Znth_Same 0
          (replace_Znth i (Znth j ends 0) ends)
          j (Znth i ends 0))
          by (repeat rewrite Zlength_replace_Znth; lia).
        apply Hpoint; assumption.
      * rewrite (Znth_replace_Znth_Diff default_interval
          (replace_Znth i (Znth j ps default_interval) ps)
          j k (Znth i ps default_interval))
          by (repeat rewrite Zlength_replace_Znth; lia).
        rewrite (Znth_replace_Znth_Diff default_interval ps
          i k (Znth j ps default_interval)) by lia.
        rewrite (Znth_replace_Znth_Diff 0
          (replace_Znth i (Znth j starts 0) starts)
          j k (Znth i starts 0))
          by (repeat rewrite Zlength_replace_Znth; lia).
        rewrite (Znth_replace_Znth_Diff 0 starts
          i k (Znth j starts 0)) by lia.
        rewrite (Znth_replace_Znth_Diff 0
          (replace_Znth i (Znth j ends 0) ends)
          j k (Znth i ends 0))
          by (repeat rewrite Zlength_replace_Znth; lia).
        rewrite (Znth_replace_Znth_Diff 0 ends
          i k (Znth j ends 0)) by lia.
        apply Hpoint; assumption.
Qed.
Lemma pair_intervals_lengths_and_fields__partition_lomuto :
  forall starts ends ps,
    PairIntervals starts ends ps ->
    Zlength starts = Zlength ends /\
    Zlength ps = Zlength starts /\
    (forall k,
        0 <= k < Zlength starts ->
        interval_start (Znth k ps default_interval) = Znth k starts 0 /\
        interval_end (Znth k ps default_interval) = Znth k ends 0).
Proof.
  intros starts ends ps Hpair.
  apply pair_intervals_indexed in Hpair.
  destruct Hpair as [Hse [Hps Hfields]].
  split; [exact Hse|]. split; [exact Hps|].
  intros k Hk. specialize (Hfields k Hk).
  unfold interval_start, interval_end, mk_interval.
  rewrite Hfields. simpl. auto.
Qed.
Lemma interval_same_outside_range_refl__partition_lomuto :
  forall ps low high,
    IntervalSameOutsideRange ps ps low high.
Proof.
  intros. unfold IntervalSameOutsideRange.
  split; [reflexivity|]. intros. reflexivity.
Qed.
Lemma interval_swap_length__partition_lomuto :
  forall ps i j,
    Zlength (interval_swap ps i j) = Zlength ps.
Proof.
  intros. unfold interval_swap.
  repeat rewrite Zlength_replace_Znth. reflexivity.
Qed.
Lemma interval_swap_Znth_left__partition_lomuto :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    Znth i (interval_swap ps i j) default_interval =
    Znth j ps default_interval.
Proof.
  intros ps i j Hi Hj. destruct (Z.eq_dec i j) as [->|Hij].
  - unfold interval_swap.
    rewrite replace_Znth_Znth by exact Hj.
    rewrite replace_Znth_Znth by exact Hj. reflexivity.
  - unfold interval_swap.
    rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact Hj. }
    2:{ rewrite Zlength_replace_Znth. exact Hi. }
    2:{ lia. }
    rewrite Znth_replace_Znth_Same by exact Hi. reflexivity.
Qed.
Lemma interval_swap_Znth_right__partition_lomuto :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    Znth j (interval_swap ps i j) default_interval =
    Znth i ps default_interval.
Proof.
  intros ps i j Hi Hj. unfold interval_swap.
  rewrite Znth_replace_Znth_Same.
  - reflexivity.
  - rewrite Zlength_replace_Znth. exact Hj.
Qed.
Lemma interval_swap_Znth_other__partition_lomuto :
  forall ps i j k,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    0 <= k < Zlength ps ->
    k <> i ->
    k <> j ->
    Znth k (interval_swap ps i j) default_interval =
    Znth k ps default_interval.
Proof.
  intros ps i j k Hi Hj Hk Hki Hkj. unfold interval_swap.
  rewrite Znth_replace_Znth_Diff.
  2:{ rewrite Zlength_replace_Znth. exact Hj. }
  2:{ rewrite Zlength_replace_Znth. exact Hk. }
  2:{ lia. }
  rewrite Znth_replace_Znth_Diff; auto; lia.
Qed.
Lemma interval_same_outside_range_swap_inside__partition_lomuto :
  forall before cur low high i j,
    IntervalSameOutsideRange before cur low high ->
    low <= i <= high ->
    low <= j <= high ->
    0 <= i < Zlength cur ->
    0 <= j < Zlength cur ->
    IntervalSameOutsideRange before (interval_swap cur i j) low high.
Proof.
  intros before cur low high i j [Hlen Houtside]
    Hi_range Hj_range Hi_len Hj_len.
  unfold IntervalSameOutsideRange.
  split.
  - rewrite interval_swap_length__partition_lomuto. exact Hlen.
  - intros k Hk Hkout.
    rewrite interval_swap_Znth_other__partition_lomuto; try lia.
    apply Houtside; auto.
Qed.
Lemma lomuto_scan_init__partition_lomuto :
  forall starts ends ps low high,
    PairIntervals starts ends ps ->
    0 <= low ->
    low <= high ->
    high < Zlength starts ->
    LomutoScanState ps ps low high (low - 1) low (Znth high ends 0).
Proof.
  intros starts ends ps low high Hpair Hlow Hlh Hhigh.
  pose proof
    (pair_intervals_lengths_and_fields__partition_lomuto
       starts ends ps Hpair) as [_ [Hps Hfields]].
  unfold LomutoScanState.
  split; [apply Permutation_refl|].
  split; [apply interval_same_outside_range_refl__partition_lomuto|].
  split.
  - apply (proj2 (Hfields high ltac:(lia))).
  - split; intros; lia.
Qed.
Lemma lomuto_scan_accept__partition_lomuto :
  forall before cur after low high placed scanned pivot_end,
    0 <= low ->
    low <= high ->
    high < Zlength cur ->
    low - 1 <= placed ->
    placed < scanned ->
    scanned < high ->
    LomutoScanState before cur low high placed scanned pivot_end ->
    IntervalPermutation cur after ->
    IntervalSwappedAt cur after (placed + 1) scanned ->
    interval_end (Znth scanned cur default_interval) <= pivot_end ->
    LomutoScanState before after low high
      (placed + 1) (scanned + 1) pivot_end.
Proof.
  intros before cur after low high placed scanned pivot_end
    Hlow Hlh Hhigh Hplaced Hps Hsh
    [Hperm [Hsame [Hpivot [Hle Hgt]]]] Hperm_swap Hswapped Hguard.
  unfold IntervalSwappedAt in Hswapped. subst after.
  assert (Hi_len : 0 <= placed + 1 < Zlength cur) by lia.
  assert (Hj_len : 0 <= scanned < Zlength cur) by lia.
  unfold LomutoScanState.
  split.
  - eapply Permutation_trans; eauto.
  - split.
    + apply interval_same_outside_range_swap_inside__partition_lomuto;
        auto; lia.
    + split.
      * rewrite interval_swap_Znth_other__partition_lomuto; try lia.
      * split.
        -- intros k Hk. destruct (Z.eq_dec k (placed + 1)) as [->|Hneq].
           ++ rewrite interval_swap_Znth_left__partition_lomuto by assumption.
              exact Hguard.
           ++ rewrite interval_swap_Znth_other__partition_lomuto; try lia.
              apply Hle; lia.
        -- intros k Hk. destruct (Z.eq_dec k scanned) as [->|Hneq].
           ++ rewrite interval_swap_Znth_right__partition_lomuto by assumption.
              apply Hgt; lia.
           ++ rewrite interval_swap_Znth_other__partition_lomuto; try lia.
              apply Hgt; lia.
Qed.
Lemma lomuto_scan_skip__partition_lomuto :
  forall before cur low high placed scanned pivot_end,
    scanned < high ->
    LomutoScanState before cur low high placed scanned pivot_end ->
    pivot_end < interval_end (Znth scanned cur default_interval) ->
    LomutoScanState before cur low high placed (scanned + 1) pivot_end.
Proof.
  intros before cur low high placed scanned pivot_end Hsh
    [Hperm [Hsame [Hpivot [Hle Hgt]]]] Hguard.
  unfold LomutoScanState.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split; [exact Hle|].
  intros k Hk. destruct (Z.eq_dec k scanned) as [->|Hneq].
  - exact Hguard.
  - apply Hgt; lia.
Qed.
Lemma lomuto_scan_finish__partition_lomuto :
  forall before cur after low high placed scanned pivot_end,
    0 <= low ->
    low <= high ->
    high < Zlength cur ->
    low - 1 <= placed ->
    placed < scanned ->
    scanned <= high ->
    scanned >= high ->
    LomutoScanState before cur low high placed scanned pivot_end ->
    IntervalPermutation cur after ->
    IntervalSwappedAt cur after (placed + 1) high ->
    IntervalPermutation before after /\
    IntervalSameOutsideRange before after low high /\
    IntervalPartitionedAt after low high (placed + 1).
Proof.
  intros before cur after low high placed scanned pivot_end
    Hlow Hlh Hhigh Hplaced Hps Hsle Hsge
    [Hperm [Hsame [Hpivot [Hle Hgt]]]] Hperm_swap Hswapped.
  assert (Hscan : scanned = high) by lia. subst scanned.
  unfold IntervalSwappedAt in Hswapped. subst after.
  assert (Hi_len : 0 <= placed + 1 < Zlength cur) by lia.
  assert (Hh_len : 0 <= high < Zlength cur) by lia.
  assert (Hpivot_after :
      interval_end
        (Znth (placed + 1) (interval_swap cur (placed + 1) high)
          default_interval) = pivot_end).
  {
    rewrite interval_swap_Znth_left__partition_lomuto by assumption.
    exact Hpivot.
  }
  split.
  - eapply Permutation_trans; eauto.
  - split.
    + apply interval_same_outside_range_swap_inside__partition_lomuto;
        auto; lia.
    + unfold IntervalPartitionedAt. split; [lia|]. split.
      * intros k Hk. rewrite Hpivot_after.
        rewrite interval_swap_Znth_other__partition_lomuto; try lia.
        apply Hle; lia.
      * intros k Hk. rewrite Hpivot_after.
        destruct (Z.eq_dec k high) as [->|Hneq].
        -- rewrite interval_swap_Znth_right__partition_lomuto by assumption.
           apply Hgt; lia.
        -- rewrite interval_swap_Znth_other__partition_lomuto; try lia.
           apply Hgt; lia.
Qed.
Lemma Forall_Znth_interval__quicksort_left :
  forall (P : interval -> Prop) (l : list interval) i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l default_interval).
Proof.
  intros P l i HForall Hrange.
  apply Forall_forall with
    (x := Znth i l default_interval) in HForall.
  - exact HForall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.
Lemma Forall_sublist_interval__quicksort_left :
  forall (P : interval -> Prop) (l : list interval) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l default_interval)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhilen Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhilen Hpoint Hn.
  induction n; intros lo hi Hlohi Hhilen Hpoint Hn.
  - assert (hi = lo) by lia.
    subst hi.
    assert (Hnil : sublist lo lo l = nil).
    { apply sublist_nil. lia. }
    rewrite Hnil.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
    2: { split; lia. }
    rewrite (sublist_single default_interval lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.
Lemma sublist_interval_eq_from_Znth__quicksort_left :
  forall (l1 l2 : list interval) lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi ->
       Znth k l1 default_interval = Znth k l2 default_interval) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2
    (list_eq_ext (sublist lo hi l1) (sublist lo hi l2)
       default_interval)).
  split.
  - rewrite !Zlength_sublist by lia.
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    {
      rewrite Zlength_sublist in Hi by lia.
      exact Hi.
    }
    rewrite (@Znth_sublist_lt interval default_interval lo hi l1 i).
    2: exact Hlohi.
    2: exact Hhilen.
    2: exact Hi'.
    rewrite (@Znth_sublist_lt interval default_interval lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint.
    lia.
Qed.
Lemma list_interval_decompose_sublist__quicksort_left :
  forall (l : list interval) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = sublist 0 lo l ++ sublist lo hi l ++
        sublist hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhilen.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l).
  2: lia.
  2: { split; [transitivity hi |]; lia. }
  rewrite (sublist_split lo (Zlength l) hi l).
  2: lia.
  2: { split; lia. }
  reflexivity.
Qed.
Lemma interval_same_outside_prefix__quicksort_left :
  forall l l1 left right,
    IntervalSameOutsideRange l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right [Hlen Heq] Hrange.
  apply sublist_interval_eq_from_Znth__quicksort_left.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.
Lemma interval_same_outside_suffix__quicksort_left :
  forall l l1 left right,
    IntervalSameOutsideRange l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 =
      sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right [Hlen Heq] Hrange.
  rewrite <- Hlen.
  apply sublist_interval_eq_from_Znth__quicksort_left.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.
Lemma interval_middle_permutation__quicksort_left :
  forall l l1 left right,
    IntervalPermutation l l1 ->
    IntervalSameOutsideRange l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    Permutation (sublist left (right + 1) l)
                (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof
    (interval_same_outside_prefix__quicksort_left
       _ _ _ _ Hsame0) as Hpre.
  pose proof
    (interval_same_outside_suffix__quicksort_left
       _ _ _ _ Hsame0) as Hsuf.
  rewrite
    (list_interval_decompose_sublist__quicksort_left
       l left (right + 1)) in Hperm by lia.
  assert (Hlenr1 : right + 1 <= Zlength l1) by
    (rewrite <- Hlen; exact Hlenr).
  rewrite
    (list_interval_decompose_sublist__quicksort_left
       l1 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma partition_preserved_by_left_sort__quicksort_left :
  forall before after low high pivot,
    IntervalPermutation before after ->
    IntervalSameOutsideRange before after low (pivot - 1) ->
    0 <= low ->
    high < Zlength before ->
    IntervalPartitionedAt before low high pivot ->
    IntervalPartitionedAt after low high pivot.
Proof.
  intros before after low high pivot Hperm Hsame Hlow Hhigh Hpart.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpivot :
    Znth pivot after default_interval =
    Znth pivot before default_interval).
  {
    apply Heq.
    - lia.
    - right. lia.
  }
  split.
  - exact Hrange.
  - split.
    + intros k Hk.
      assert (Hmid :
        Permutation (sublist low pivot before)
                    (sublist low pivot after)).
      {
        replace pivot with (pivot - 1 + 1) by lia.
        eapply interval_middle_permutation__quicksort_left.
        - exact Hperm.
        - exact Hsame0.
        - lia.
        - lia.
      }
      assert (Hbefore_all :
        Forall
          (fun q =>
             interval_end q <=
             interval_end (Znth pivot before default_interval))
          (sublist low pivot before)).
      {
        eapply Forall_sublist_interval__quicksort_left.
        - lia.
        - lia.
        - intros i Hi. apply Hleft. exact Hi.
      }
      assert (Hafter_all :
        Forall
          (fun q =>
             interval_end q <=
             interval_end (Znth pivot before default_interval))
          (sublist low pivot after)).
      {
        eapply Permutation_Forall.
        - exact Hmid.
        - exact Hbefore_all.
      }
      rewrite Hpivot.
      pose proof
        (Forall_Znth_interval__quicksort_left
           (fun q =>
              interval_end q <=
              interval_end (Znth pivot before default_interval))
           (sublist low pivot after) (k - low)
           Hafter_all ltac:(rewrite Zlength_sublist by
             (rewrite <- Hlen; lia); lia)) as Hk_after.
      rewrite (@Znth_sublist_lt interval default_interval
        low pivot after (k - low)) in Hk_after.
      * replace (low + (k - low)) with k in Hk_after by lia.
        exact Hk_after.
      * lia.
      * lia.
      * lia.
    + intros k Hk.
      rewrite Hpivot.
      rewrite Heq.
      * apply Hright. exact Hk.
      * lia.
      * right. lia.
Qed.
Lemma outside_range_compose_nested__quicksort_left :
  forall original middle final left right nested_right,
    IntervalSameOutsideRange original middle left right ->
    IntervalSameOutsideRange middle final left nested_right ->
    nested_right <= right ->
    IntervalSameOutsideRange original final left right.
Proof.
  intros original middle final left right nested_right
    [Hlen1 Heq1] [Hlen2 Heq2] Hnested.
  split.
  - rewrite Hlen1. exact Hlen2.
  - intros k Hk Hout.
    assert (Hkmid : 0 <= k < Zlength middle) by
      (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hkmid).
    + apply Heq1; assumption.
    + destruct Hout as [Hout | Hout].
      * left. exact Hout.
      * right. lia.
Qed.
Lemma sorted_range_empty__quicksort_left :
  forall ps left right,
    right < left ->
    IntervalsEndSortedRange ps left right.
Proof.
  intros ps left right Hempty i j Hi Hij Hj.
  lia.
Qed.
Lemma outside_range_compose_nested__quicksort_finish :
  forall before middle after left inner_left right,
    left <= inner_left ->
    IntervalSameOutsideRange before middle left right ->
    IntervalSameOutsideRange middle after inner_left right ->
    IntervalSameOutsideRange before after left right.
Proof.
  intros before middle after left inner_left right Hinner
         [Hlen1 Heq1] [Hlen2 Heq2].
  split.
  - lia.
  - intros k Hk Hout.
    assert (Hkm : 0 <= k < Zlength middle) by (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hkm).
    + apply Heq1; assumption.
    + destruct Hout as [Hout | Hout].
      * left; lia.
      * right; exact Hout.
Qed.
Lemma Forall_interval_permutation__quicksort_finish :
  forall (P : interval -> Prop) l1 l2,
    IntervalPermutation l1 l2 ->
    Forall P l1 ->
    Forall P l2.
Proof.
  intros P l1 l2 Hperm Hforall.
  unfold IntervalPermutation in Hperm.
  eapply Permutation_Forall; eauto.
Qed.
Lemma Forall_Znth_interval__quicksort_finish :
  forall (P : interval -> Prop) (l : list interval) i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l default_interval).
Proof.
  intros P l i Hforall Hrange.
  apply Forall_forall with (x := Znth i l default_interval) in Hforall.
  - exact Hforall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.
Lemma Forall_sublist_interval_by_Znth__quicksort_finish :
  forall (P : interval -> Prop) (l : list interval) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l default_interval)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhilen Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhilen Hpoint Hn.
  induction n; intros lo hi Hlohi Hhilen Hpoint Hn.
  - assert (hi = lo) by lia.
    subst hi.
    rewrite Zsublist_nil by lia.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
    2: { split; [lia | exact Hhilen]. }
    rewrite (@sublist_single interval default_interval lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.
Lemma sublist_eq_from_Znth_interval__quicksort_finish :
  forall (l1 l2 : list interval) lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi ->
       Znth k l1 default_interval = Znth k l2 default_interval) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2)
          default_interval)).
  split.
  - repeat rewrite Zlength_correct.
    repeat rewrite sublist_length by
      (try exact Hlohi; try rewrite <- Hlen; exact Hhilen).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    { rewrite Zlength_sublist in Hi by lia. exact Hi. }
    rewrite (@Znth_sublist_lt interval default_interval lo hi l1 i).
    2: exact Hlohi.
    2: exact Hhilen.
    2: exact Hi'.
    rewrite (@Znth_sublist_lt interval default_interval lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint. lia.
Qed.
Lemma list_decompose_sublist_interval__quicksort_finish :
  forall (l : list interval) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = sublist 0 lo l ++ sublist lo hi l ++ sublist hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhilen.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l).
  2: lia.
  2: { split; [transitivity hi; lia | lia]. }
  rewrite (sublist_split lo (Zlength l) hi l).
  2: lia.
  2: { split; [exact Hhilen | lia]. }
  reflexivity.
Qed.
Lemma same_outside_prefix_interval__quicksort_finish :
  forall l1 l2 left right,
    IntervalSameOutsideRange l1 l2 left right ->
    0 <= left <= Zlength l1 ->
    sublist 0 left l2 = sublist 0 left l1.
Proof.
  intros l1 l2 left right [Hlen Heq] Hrange.
  apply sublist_eq_from_Znth_interval__quicksort_finish.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk. apply Heq; [lia | left; lia].
Qed.
Lemma same_outside_suffix_interval__quicksort_finish :
  forall l1 l2 left right,
    IntervalSameOutsideRange l1 l2 left right ->
    0 <= right + 1 <= Zlength l1 ->
    sublist (right + 1) (Zlength l2) l2 =
    sublist (right + 1) (Zlength l1) l1.
Proof.
  intros l1 l2 left right [Hlen Heq] Hrange.
  rewrite <- Hlen.
  apply sublist_eq_from_Znth_interval__quicksort_finish.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk. apply Heq; [rewrite Hlen; lia | right; lia].
Qed.
Lemma middle_permutation_interval__quicksort_finish :
  forall l1 l2 left right,
    IntervalPermutation l1 l2 ->
    IntervalSameOutsideRange l1 l2 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l1 ->
    IntervalPermutation
      (sublist left (right + 1) l1)
      (sublist left (right + 1) l2).
Proof.
  intros l1 l2 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (same_outside_prefix_interval__quicksort_finish
                _ _ _ _ Hsame0 ltac:(lia)) as Hpre.
  pose proof (same_outside_suffix_interval__quicksort_finish
                _ _ _ _ Hsame0 ltac:(lia)) as Hsuf.
  unfold IntervalPermutation in Hperm |- *.
  rewrite (list_decompose_sublist_interval__quicksort_finish
             l1 left (right + 1)) in Hperm by lia.
  assert (Hlenr2 : right + 1 <= Zlength l2) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist_interval__quicksort_finish
             l2 left (right + 1)) in Hperm by lia.
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma right_sort_preserves_left_partition__quicksort_finish :
  forall before after left right pivot,
    IntervalPermutation before after ->
    IntervalSameOutsideRange before after (pivot + 1) right ->
    0 <= left ->
    pivot <= right ->
    right < Zlength before ->
    IntervalPartitionedAt before left right pivot ->
    IntervalPartitionedAt after left right pivot.
Proof.
  intros before after left right pivot Hperm Hsame Hleft Hpivright Hright Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hpartleft Hpartright]].
  assert (Hpivot :
      Znth pivot after default_interval = Znth pivot before default_interval).
  { apply Heq; [lia | left; lia]. }
  split; [exact Hrange |].
  split.
  - intros k Hk.
    rewrite Hpivot.
    rewrite Heq.
    + apply Hpartleft. exact Hk.
    + lia.
    + left; lia.
  - assert (Hbefore_forall :
        Forall
          (fun x => interval_end (Znth pivot before default_interval) <
                    interval_end x)
          (sublist (pivot + 1) (right + 1) before)).
    {
      apply Forall_sublist_interval_by_Znth__quicksort_finish.
      - lia.
      - lia.
      - intros k Hk. apply Hpartright. lia.
    }
    assert (Hmiddle :
        IntervalPermutation
          (sublist (pivot + 1) (right + 1) before)
          (sublist (pivot + 1) (right + 1) after)).
    {
      eapply middle_permutation_interval__quicksort_finish.
      - exact Hperm.
      - exact (conj Hlen Heq).
      - lia.
      - lia.
    }
    pose proof (Forall_interval_permutation__quicksort_finish
      (fun x => interval_end (Znth pivot before default_interval) <
                interval_end x)
      _ _ Hmiddle Hbefore_forall) as Hafter_forall.
    intros k Hk.
    rewrite Hpivot.
    assert (Hindex :
        0 <= k - (pivot + 1) <
        Zlength (sublist (pivot + 1) (right + 1) after)).
    { rewrite Zlength_sublist by (rewrite <- Hlen; lia). lia. }
    pose proof (Forall_Znth_interval__quicksort_finish
      _ _ (k - (pivot + 1)) Hafter_forall Hindex) as Hz.
    rewrite (@Znth_sublist_lt interval default_interval
      (pivot + 1) (right + 1) after (k - (pivot + 1))) in Hz.
    2: lia.
    2: { rewrite <- Hlen. lia. }
    2: { rewrite Zlength_sublist in Hindex by (rewrite <- Hlen; lia).
         exact Hindex. }
    replace (pivot + 1 + (k - (pivot + 1))) with k in Hz by lia.
    exact Hz.
Qed.
Lemma sorted_range_preserved_on_left__quicksort_finish :
  forall before after left right pivot,
    IntervalSameOutsideRange before after (pivot + 1) right ->
    0 <= left ->
    pivot <= right ->
    right < Zlength before ->
    IntervalsEndSortedRange before left (pivot - 1) ->
    IntervalsEndSortedRange after left (pivot - 1).
Proof.
  intros before after left right pivot [Hlen Heq] Hleft Hpiv Hright Hsorted.
  intros i j Hi Hij Hj.
  rewrite Heq.
  2: lia.
  2: { left; lia. }
  rewrite Heq.
  2: lia.
  2: { left; lia. }
  apply Hsorted; assumption.
Qed.
Lemma partition_merge_sorted_ranges__quicksort_finish :
  forall ps left right pivot,
    IntervalPartitionedAt ps left right pivot ->
    IntervalsEndSortedRange ps left (pivot - 1) ->
    IntervalsEndSortedRange ps (pivot + 1) right ->
    IntervalsEndSortedRange ps left right.
Proof.
  intros ps left right pivot [Hpivot [Hpartleft Hpartright]]
         Hleft Hright i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j pivot) as [Hjp | Hjp].
  - apply Hleft; lia.
  - destruct (Z.eq_dec j pivot) as [-> | Hjpneq].
    + destruct (Z.eq_dec i pivot) as [-> | Hipneq].
      * apply Z.le_refl.
      * apply Hpartleft. lia.
    + assert (pivot < j) by lia.
      destruct (Z.eq_dec i pivot) as [-> | Hipneq].
      * apply Z.lt_le_incl. apply Hpartright. lia.
      * destruct (Z_lt_ge_dec i pivot) as [Hip | Hip].
        -- eapply Z.le_trans.
           ++ apply Hpartleft. lia.
           ++ apply Z.lt_le_incl. apply Hpartright. lia.
        -- assert (pivot < i) by lia.
           apply Hright; lia.
Qed.
Lemma sorted_range_trivial__quicksort_finish :
  forall ps left right,
    left >= right ->
    IntervalsEndSortedRange ps left right.
Proof.
  intros ps left right Hlr i j Hi Hij Hj.
  assert (i = j) by lia.
  subst j. apply Z.le_refl.
Qed.
Lemma same_outside_refl__quicksort_finish :
  forall ps left right,
    IntervalSameOutsideRange ps ps left right.
Proof.
  intros ps left right.
  split; [reflexivity |].
  intros; reflexivity.
Qed.
Lemma sorted_full_range__quicksort_finish :
  forall ps n,
    Zlength ps = n ->
    IntervalsEndSortedRange ps 0 (n - 1) ->
    IntervalsEndSorted ps.
Proof.
  intros ps n Hlen Hrange i j Hi Hij Hj.
  apply Hrange; lia.
Qed.
Lemma forall_znth__greedy_prefix :
  forall (A : Type) (P : A -> Prop) (d : A) (xs : list A),
    Forall P xs <->
    (forall i, 0 <= i < Zlength xs -> P (Znth i xs d)).
Proof.
  intros A P d xs. induction xs as [|x xs IH].
  - rewrite Zlength_nil. split.
    + intros _ i Hi. lia.
    + intros _. constructor.
  - pose proof (Zlength_nonneg xs) as Hnonneg.
    rewrite Zlength_cons. split.
    + intros Hall i Hi. inversion Hall as [|? ? Hx Hxs]; subst.
      destruct (Z.eq_dec i 0) as [-> | Hne].
      * rewrite Znth0_cons. exact Hx.
      * rewrite (Znth_cons d i x xs) by lia.
        apply (proj1 IH Hxs). lia.
    + intros H. constructor.
      * specialize (H 0 ltac:(lia)). rewrite Znth0_cons in H. exact H.
      * apply (proj2 IH). intros i Hi.
        specialize (H (i + 1) ltac:(lia)).
        rewrite (Znth_cons d (i + 1) x xs) in H by lia.
        replace (i + 1 - 1) with i in H by lia. exact H.
Qed.
Lemma nonoverlap_strongly_sorted__greedy_prefix :
  forall xs,
    NonOverlappingSchedule xs <->
    StronglySorted
      (fun x y => interval_end x <= interval_start y) xs.
Proof.
  induction xs as [|x xs IH].
  - split.
    + intros _. apply SSorted_nil.
    + intros _. unfold NonOverlappingSchedule.
      intros i j Hi Hij Hj. rewrite Zlength_nil in Hj. lia.
  - split.
    + intros Hno. constructor.
      * apply (proj1 IH). unfold NonOverlappingSchedule in *.
        intros i j Hi Hij Hj.
        specialize (Hno (i + 1) (j + 1) ltac:(lia) ltac:(lia)
                         ltac:(rewrite Zlength_cons; lia)).
        rewrite (Znth_cons default_interval (i + 1) x xs) in Hno by lia.
        rewrite (Znth_cons default_interval (j + 1) x xs) in Hno by lia.
        replace (i + 1 - 1) with i in Hno by lia.
        replace (j + 1 - 1) with j in Hno by lia. exact Hno.
      * apply (proj2 (forall_znth__greedy_prefix _
                        (fun y => interval_end x <= interval_start y)
                        default_interval xs)).
        intros j Hj.
        unfold NonOverlappingSchedule in Hno.
        specialize (Hno 0 (j + 1) ltac:(lia) ltac:(lia)
                         ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth0_cons in Hno.
        rewrite (Znth_cons default_interval (j + 1) x xs) in Hno by lia.
        replace (j + 1 - 1) with j in Hno by lia. exact Hno.
    + intros Hsorted.
      unfold NonOverlappingSchedule. intros i j Hi Hij Hj.
      inversion Hsorted as [|? ? Htail Hhead]; subst.
      destruct (Z.eq_dec i 0) as [-> | Hine].
      * rewrite Znth0_cons.
        rewrite (Znth_cons default_interval j x xs) by lia.
        apply (proj1 (forall_znth__greedy_prefix _
                        (fun y => interval_end x <= interval_start y)
                        default_interval xs) Hhead (j - 1)).
        rewrite Zlength_cons in Hj. lia.
      * rewrite (Znth_cons default_interval i x xs) by lia.
        rewrite (Znth_cons default_interval j x xs) by lia.
        apply (proj2 IH Htail (i - 1) (j - 1));
          rewrite Zlength_cons in Hj; lia.
Qed.
Lemma nonoverlap_remove_middle__greedy_prefix :
  forall left pivot right,
    NonOverlappingSchedule (left ++ pivot :: right) ->
    NonOverlappingSchedule (left ++ right).
Proof.
  intros left pivot right Hno.
  apply (proj2 (nonoverlap_strongly_sorted__greedy_prefix (left ++ right))).
  apply (proj1 (nonoverlap_strongly_sorted__greedy_prefix
                  (left ++ pivot :: right))) in Hno.
  revert pivot right Hno.
  induction left as [|x left IH]; intros pivot right Hno.
  - simpl in *. inversion Hno; assumption.
  - simpl in *. inversion Hno as [|? ? Htail Hhead]; subst.
    constructor.
    + apply (IH pivot right Htail).
    + apply Forall_forall. intros y Hy.
      apply Forall_forall with (x := y) in Hhead.
      * exact Hhead.
      * apply in_or_app. apply in_app_or in Hy.
        destruct Hy as [Hy | Hy].
        -- left. exact Hy.
        -- right. right. exact Hy.
Qed.
Lemma interval_selection_extend_cases__greedy_prefix :
  forall old p alternative,
    IntervalSelection (old ++ [p]) alternative ->
    IntervalSelection old alternative \/
    exists left right,
      alternative = left ++ p :: right /\
      IntervalSelection old (left ++ right).
Proof.
  intros old p alternative Hsel.
  unfold IntervalSelection in Hsel.
  destruct Hsel as [removed Hperm].
  assert (Hin : In p (alternative ++ removed)).
  { eapply Permutation_in; [exact Hperm |].
    apply in_or_app. right. simpl. auto. }
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - apply in_split in Hin. destruct Hin as [left [right Heq]].
    right. exists left, right. split; [exact Heq |].
    unfold IntervalSelection. exists removed. subst alternative.
    assert (Heqapp : (left ++ p :: right) ++ removed =
                     left ++ p :: (right ++ removed)).
    { symmetry. exact (app_assoc left (p :: right) removed). }
    rewrite Heqapp in Hperm.
    assert (Hcut : Permutation (old ++ []) (left ++ right ++ removed)).
    { apply (Permutation_app_inv old [] left (right ++ removed) p).
      simpl. exact Hperm. }
    rewrite app_nil_r in Hcut.
    rewrite (app_assoc left right removed) in Hcut. exact Hcut.
  - apply in_split in Hin. destruct Hin as [left [right Heq]].
    left. unfold IntervalSelection. exists (left ++ right). subst removed.
    assert (Heqapp : alternative ++ (left ++ p :: right) =
                     (alternative ++ left) ++ p :: right).
    { exact (app_assoc alternative left (p :: right)). }
    rewrite Heqapp in Hperm.
    apply (Permutation_app_inv old [] (alternative ++ left) right p) in Hperm.
    simpl in Hperm.
    assert (Heqrem : (alternative ++ left) ++ right =
                     alternative ++ (left ++ right)).
    { symmetry. exact (app_assoc alternative left right). }
    rewrite Heqrem in Hperm. rewrite app_nil_r in Hperm. exact Hperm.
Qed.
Lemma interval_selection_extend_schedule_cases__greedy_prefix :
  forall old p alternative,
    IntervalSelection (old ++ [p]) alternative ->
    NonOverlappingSchedule alternative ->
    (IntervalSelection old alternative /\
     NonOverlappingSchedule alternative) \/
    exists left right,
      alternative = left ++ p :: right /\
      IntervalSelection old (left ++ right) /\
      NonOverlappingSchedule (left ++ right).
Proof.
  intros old p alternative Hsel Hno.
  destruct (interval_selection_extend_cases__greedy_prefix
              old p alternative Hsel) as [Hold | [left [right [Heq Hold]]]].
  - left. auto.
  - right. exists left, right. repeat split; auto.
    subst alternative.
    apply (nonoverlap_remove_middle__greedy_prefix left p right Hno).
Qed.
Lemma prefix_snoc__greedy_prefix :
  forall ps i,
    0 <= i < Zlength ps ->
    sublist 0 (i + 1) ps =
      sublist 0 i ps ++ [Znth i ps default_interval].
Proof.
  intros ps i Hi.
  rewrite (sublist_split 0 (i + 1) i ps) by lia.
  rewrite (sublist_single default_interval i ps) by lia.
  reflexivity.
Qed.
Lemma interval_bounds_prefix__greedy_prefix :
  forall ps n,
    0 <= n <= Zlength ps ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) ps) ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (sublist 0 n ps)).
Proof.
  intros ps n Hn Hbounds.
  apply Forall_forall. intros p Hin.
  destruct (In_nth (sublist 0 n ps) p default_interval Hin)
    as [k [Hk Hnth]].
  assert (HkZ : 0 <= Z.of_nat k < n).
  { assert (Hkprefix : Z.of_nat k < Zlength (sublist 0 n ps)).
    { rewrite Zlength_correct. lia. }
    rewrite Zlength_sublist0 in Hkprefix by lia. lia. }
  pose proof
    (proj1 (forall_znth__greedy_prefix _
              (fun q =>
                 -10000 <= interval_start q /\
                 interval_start q < interval_end q /\
                 interval_end q <= 10000)
              default_interval ps) Hbounds (Z.of_nat k) ltac:(lia))
    as Hboundk.
  assert (Heq : Znth (Z.of_nat k) ps default_interval = p).
  { rewrite <- (Znth_sublist0 default_interval (Z.of_nat k) n ps) by lia.
    unfold Znth. rewrite Nat2Z.id. exact Hnth. }
  rewrite Heq in Hboundk. exact Hboundk.
Qed.
Lemma interval_bounds_selected__greedy_prefix :
  forall input kept,
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) input) ->
    IntervalSelection input kept ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) kept).
Proof.
  intros input kept Hbounds Hsel.
  unfold IntervalSelection in Hsel. destruct Hsel as [removed Hperm].
  apply Forall_forall. intros p Hin.
  apply Forall_forall with (x := p) in Hbounds.
  - exact Hbounds.
  - eapply Permutation_in.
    + apply Permutation_sym. exact Hperm.
    + apply in_or_app. left. exact Hin.
Qed.
Lemma selected_member_end_le_current__greedy_prefix :
  forall ps processed selected q,
    0 <= processed < Zlength ps ->
    IntervalsEndSorted ps ->
    IntervalSelection (sublist 0 processed ps) selected ->
    In q selected ->
    interval_end q <= interval_end (Znth processed ps default_interval).
Proof.
  intros ps processed selected q Hprocessed Hsorted Hsel Hinq.
  unfold IntervalSelection in Hsel. destruct Hsel as [removed Hperm].
  assert (Hinprefix : In q (sublist 0 processed ps)).
  { eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - apply in_or_app. left. exact Hinq. }
  destruct (In_nth (sublist 0 processed ps) q default_interval Hinprefix)
    as [k [Hk Hnth]].
  assert (HkZ : 0 <= Z.of_nat k < processed).
  { assert (Hkprefix : Z.of_nat k < Zlength (sublist 0 processed ps)).
    { rewrite Zlength_correct. lia. }
    rewrite Zlength_sublist0 in Hkprefix by lia. lia. }
  unfold IntervalsEndSorted in Hsorted.
  specialize (Hsorted (Z.of_nat k) processed ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- (Znth_sublist0 default_interval (Z.of_nat k) processed ps)
    in Hsorted by lia.
  unfold Znth at 1 in Hsorted. rewrite Nat2Z.id in Hsorted.
  rewrite Hnth in Hsorted. exact Hsorted.
Qed.
Lemma nonoverlap_member_end_le_finish__greedy_prefix :
  forall xs p,
    NonOverlappingSchedule xs ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) xs) ->
    In p xs ->
    interval_end p <= schedule_finish xs.
Proof.
  intros xs p Hno Hbounds Hin.
  destruct (In_nth xs p default_interval Hin) as [k [Hk Hnth]].
  assert (HkZ : 0 <= Z.of_nat k < Zlength xs).
  { rewrite Zlength_correct. lia. }
  assert (Hlast : 0 <= Zlength xs - 1 < Zlength xs) by lia.
  assert (HnthZ : Znth (Z.of_nat k) xs default_interval = p).
  { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
  destruct (Z.eq_dec (Z.of_nat k) (Zlength xs - 1)) as [Heq | Hne].
  - unfold schedule_finish. rewrite <- Heq. rewrite HnthZ. lia.
  - unfold NonOverlappingSchedule in Hno.
    specialize (Hno (Z.of_nat k) (Zlength xs - 1)
                  ltac:(lia) ltac:(lia) ltac:(lia)).
    apply (proj1 (forall_znth__greedy_prefix _
                    (fun q =>
                       -10000 <= interval_start q /\
                       interval_start q < interval_end q /\
                       interval_end q <= 10000)
                    default_interval xs) Hbounds (Zlength xs - 1)) in Hlast.
    unfold schedule_finish. rewrite HnthZ in Hno. lia.
Qed.
Lemma interval_selection_append__greedy_prefix :
  forall old kept p,
    IntervalSelection old kept ->
    IntervalSelection (old ++ [p]) (kept ++ [p]).
Proof.
  intros old kept p Hsel. unfold IntervalSelection in *.
  destruct Hsel as [removed Hperm]. exists removed.
  transitivity ((kept ++ removed) ++ [p]).
  - apply Permutation_app_tail. exact Hperm.
  - rewrite <- (app_assoc kept removed [p]).
    rewrite <- (app_assoc kept [p] removed).
    apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma nonoverlap_append__greedy_prefix :
  forall kept p,
    NonOverlappingSchedule kept ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) kept) ->
    0 < Zlength kept ->
    schedule_finish kept <= interval_start p ->
    NonOverlappingSchedule (kept ++ [p]).
Proof.
  intros kept p Hno Hbounds Hpos Hfinish.
  unfold NonOverlappingSchedule. intros i j Hi Hij Hj.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
  destruct (Z_lt_ge_dec j (Zlength kept)) as [Hjold | Hjnew].
  - rewrite (app_Znth1 default_interval kept [p] i) by lia.
    rewrite (app_Znth1 default_interval kept [p] j) by lia.
    apply Hno; lia.
  - assert (Hjeq : j = Zlength kept) by lia. subst j.
    rewrite (app_Znth1 default_interval kept [p] i) by lia.
    rewrite (app_Znth2 default_interval kept [p] (Zlength kept)) by lia.
    replace (Zlength kept - Zlength kept) with 0 by lia. rewrite Znth0_cons.
    destruct (Z.eq_dec i (Zlength kept - 1)) as [Heq | Hne].
    + subst i. unfold schedule_finish in Hfinish. exact Hfinish.
    + assert (Hlasti : i < Zlength kept - 1) by lia.
      specialize (Hno i (Zlength kept - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Hlastbounds :
                interval_start (Znth (Zlength kept - 1) kept default_interval) <
                interval_end (Znth (Zlength kept - 1) kept default_interval)).
      { apply (proj1 (forall_znth__greedy_prefix _
                        (fun q =>
                           -10000 <= interval_start q /\
                           interval_start q < interval_end q /\
                           interval_end q <= 10000)
                        default_interval kept) Hbounds (Zlength kept - 1)); lia. }
      unfold schedule_finish in Hfinish. lia.
Qed.
Lemma schedule_finish_snoc__greedy_prefix :
  forall xs p,
    schedule_finish (xs ++ [p]) = interval_end p.
Proof.
  intros xs p. unfold schedule_finish.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength xs + 1 - 1) with (Zlength xs) by lia.
  erewrite app_Znth2 by lia.
  replace (Zlength xs + Z.succ 0 - 1 - Zlength xs) with 0 by lia.
  rewrite Znth0_cons. reflexivity.
Qed.
Lemma nonoverlap_snoc_previous_finish__greedy_prefix :
  forall xs p,
    NonOverlappingSchedule (xs ++ [p]) ->
    0 < Zlength xs ->
    schedule_finish xs <= interval_start p.
Proof.
  intros xs p Hno Hpos. unfold NonOverlappingSchedule in Hno.
  specialize (Hno (Zlength xs - 1) (Zlength xs)
                ltac:(lia) ltac:(lia)).
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hno.
  specialize (Hno ltac:(lia)).
  rewrite (app_Znth1 default_interval xs [p] (Zlength xs - 1)) in Hno by lia.
  rewrite (app_Znth2 default_interval xs [p] (Zlength xs)) in Hno by lia.
  replace (Zlength xs - Zlength xs) with 0 in Hno by lia.
  rewrite Znth0_cons in Hno. unfold schedule_finish. exact Hno.
Qed.
Lemma latest_interval_right_nil__greedy_prefix :
  forall left p right,
    NonOverlappingSchedule (left ++ p :: right) ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) right) ->
    (forall q, In q right -> interval_end q <= interval_end p) ->
    right = [].
Proof.
  intros left p right Hno Hbounds Hend.
  destruct right as [|q right]; [reflexivity |]. exfalso.
  pose proof (Zlength_nonneg left) as Hleftnonneg.
  unfold NonOverlappingSchedule in Hno.
  specialize (Hno (Zlength left) (Zlength left + 1) ltac:(lia) ltac:(lia)).
  rewrite Zlength_app, !Zlength_cons in Hno.
  specialize (Hno ltac:(pose proof (Zlength_nonneg right); lia)).
  rewrite (app_Znth2 default_interval left (p :: q :: right)
             (Zlength left)) in Hno by lia.
  rewrite (app_Znth2 default_interval left (p :: q :: right)
             (Zlength left + 1)) in Hno by lia.
  replace (Zlength left - Zlength left) with 0 in Hno by lia.
  replace (Zlength left + 1 - Zlength left) with 1 in Hno by lia.
  rewrite Znth0_cons in Hno.
  rewrite (Znth_cons default_interval 1 p (q :: right)) in Hno by lia.
  replace (1 - 1) with 0 in Hno by lia. rewrite Znth0_cons in Hno.
  inversion Hbounds as [|? ? Hq ?]; subst.
  specialize (Hend q ltac:(simpl; auto)). lia.
Qed.
Lemma greedy_prefix_accept__greedy_prefix :
  forall ps i kept_count last_finish,
    0 <= i < Zlength ps ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) ps) ->
    GreedyPrefixState ps i kept_count last_finish ->
    last_finish <= interval_start (Znth i ps default_interval) ->
    GreedyPrefixState ps (i + 1) (kept_count + 1)
      (interval_end (Znth i ps default_interval)).
Proof.
  intros ps i kept_count last_finish Hi Hbounds Hstate Haccept.
  apply greedy_prefix_state_facts in Hstate.
  apply greedy_prefix_state_facts.
  destruct Hstate as
    [kept [Hsel [Hno [Hlen [Hpos [Hlast [Hmax Hfront]]]]]]].
  set (p := Znth i ps default_interval).
  assert (Hprefix : sublist 0 (i + 1) ps = sublist 0 i ps ++ [p]).
  { subst p. apply prefix_snoc__greedy_prefix. exact Hi. }
  assert (Hprefix_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (sublist 0 i ps))).
  { apply interval_bounds_prefix__greedy_prefix; auto. lia. }
  assert (Hkept_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) kept)).
  { eapply interval_bounds_selected__greedy_prefix; eauto. }
  exists (kept ++ [p]).
  split.
  - rewrite Hprefix. apply interval_selection_append__greedy_prefix. exact Hsel.
  - split.
    + apply nonoverlap_append__greedy_prefix; auto.
      subst p. rewrite <- Hlast. exact Haccept.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * split.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
        -- split.
           ++ rewrite schedule_finish_snoc__greedy_prefix. reflexivity.
           ++ split.
              ** intros alternative HaltSel HaltNo.
                 rewrite Hprefix in HaltSel.
                 destruct
                   (interval_selection_extend_schedule_cases__greedy_prefix
                      (sublist 0 i ps) p alternative HaltSel HaltNo)
                   as [[HoldSel HoldNo] |
                       [left [right [Heq [HoldSel HoldNo]]]]].
                 --- specialize (Hmax alternative HoldSel HoldNo). lia.
                 --- specialize (Hmax (left ++ right) HoldSel HoldNo).
                     subst alternative.
                     rewrite Zlength_app in Hmax.
                     rewrite Zlength_app, Zlength_cons. lia.
              ** intros alternative HaltSel HaltNo HaltLen.
                 rewrite Hprefix in HaltSel.
                 destruct
                   (interval_selection_extend_schedule_cases__greedy_prefix
                      (sublist 0 i ps) p alternative HaltSel HaltNo)
                   as [[HoldSel HoldNo] |
                       [left [right [Heq [HoldSel HoldNo]]]]].
                 --- specialize (Hmax alternative HoldSel HoldNo). lia.
                 --- assert (Hnew_bounds :
                               (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (sublist 0 (i + 1) ps))).
                     { apply interval_bounds_prefix__greedy_prefix; auto. lia. }
                     assert (Halt_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) alternative)).
                     { eapply interval_bounds_selected__greedy_prefix; eauto.
                       rewrite Hprefix. exact HaltSel. }
                     assert (Hin_p : In p alternative).
                     { rewrite Heq. apply in_or_app. right. simpl. auto. }
                     pose proof
                       (nonoverlap_member_end_le_finish__greedy_prefix
                          alternative p HaltNo Halt_bounds Hin_p) as Hend.
                     exact Hend.
Qed.
Lemma interval_selection_retain__greedy_prefix :
  forall old kept p,
    IntervalSelection old kept ->
    IntervalSelection (old ++ [p]) kept.
Proof.
  intros old kept p Hsel. unfold IntervalSelection in *.
  destruct Hsel as [removed Hperm]. exists (p :: removed).
  transitivity ((kept ++ removed) ++ [p]).
  - apply Permutation_app_tail. exact Hperm.
  - rewrite <- (app_assoc kept removed [p]).
    apply Permutation_app_head.
    apply Permutation_sym. apply Permutation_cons_append.
Qed.
Lemma selected_finish_end_le_current__greedy_prefix :
  forall ps processed kept,
    0 <= processed < Zlength ps ->
    IntervalsEndSorted ps ->
    IntervalSelection (sublist 0 processed ps) kept ->
    0 < Zlength kept ->
    schedule_finish kept <= interval_end (Znth processed ps default_interval).
Proof.
  intros ps processed kept Hprocessed Hsorted Hsel Hpos.
  set (q := Znth (Zlength kept - 1) kept default_interval).
  assert (Hinq : In q kept).
  { subst q. unfold Znth.
    apply nth_In. rewrite Zlength_correct. rewrite Zlength_correct in Hpos.
    assert (Hidx :
              Z.to_nat (Z.of_nat (length kept) - 1) =
              (length kept - 1)%nat) by lia.
    rewrite Hidx. lia. }
  pose proof
    (selected_member_end_le_current__greedy_prefix
       ps processed kept q Hprocessed Hsorted Hsel Hinq) as Hend.
  unfold schedule_finish. exact Hend.
Qed.
Lemma greedy_prefix_skip__greedy_prefix :
  forall ps i kept_count last_finish,
    0 <= i < Zlength ps ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) ps) ->
    IntervalsEndSorted ps ->
    GreedyPrefixState ps i kept_count last_finish ->
    interval_start (Znth i ps default_interval) < last_finish ->
    GreedyPrefixState ps (i + 1) kept_count last_finish.
Proof.
  intros ps i kept_count last_finish Hi Hbounds Hsorted Hstate Hskip.
  apply greedy_prefix_state_facts in Hstate.
  apply greedy_prefix_state_facts.
  destruct Hstate as
    [kept [Hsel [Hno [Hlen [Hpos [Hlast [Hmax Hfront]]]]]]].
  set (p := Znth i ps default_interval).
  assert (Hprefix : sublist 0 (i + 1) ps = sublist 0 i ps ++ [p]).
  { subst p. apply prefix_snoc__greedy_prefix. exact Hi. }
  assert (Hold_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (sublist 0 i ps))).
  { apply interval_bounds_prefix__greedy_prefix; auto. lia. }
  assert (Hnew_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (sublist 0 (i + 1) ps))).
  { apply interval_bounds_prefix__greedy_prefix; auto. lia. }
  assert (Hkept_end : schedule_finish kept <= interval_end p).
  { subst p. eapply selected_finish_end_le_current__greedy_prefix; eauto. }
  exists kept.
  split.
  - rewrite Hprefix. apply interval_selection_retain__greedy_prefix. exact Hsel.
  - split; [exact Hno |].
    split; [exact Hlen |].
    split; [exact Hpos |].
    split; [exact Hlast |].
    split.
    + intros alternative HaltSel HaltNo.
      rewrite Hprefix in HaltSel.
      destruct
        (interval_selection_extend_schedule_cases__greedy_prefix
           (sublist 0 i ps) p alternative HaltSel HaltNo)
        as [[HoldSel HoldNo] |
            [left [right [Heq [HoldSel HoldNo]]]]].
      * apply Hmax; auto.
      * assert (Hselected_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) (left ++ right))).
        { eapply interval_bounds_selected__greedy_prefix.
          - exact Hold_bounds.
          - exact HoldSel. }
        apply Forall_app in Hselected_bounds.
        destruct Hselected_bounds as [_ Hright_bounds].
        assert (Hright_end :
                  forall q, In q right -> interval_end q <= interval_end p).
        { intros q Hinq.
          eapply selected_member_end_le_current__greedy_prefix.
          - exact Hi.
          - exact Hsorted.
          - exact HoldSel.
          - apply in_or_app. right. exact Hinq. }
        assert (Hright_nil : right = []).
        { subst alternative.
          eapply latest_interval_right_nil__greedy_prefix; eauto. }
        subst right. simpl in Heq. rewrite app_nil_r in HoldSel, HoldNo.
        subst alternative. specialize (Hmax left HoldSel HoldNo).
        destruct (Z_le_gt_dec (Zlength (left ++ [p])) kept_count)
          as [Hle | Hgt]; [exact Hle |].
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hgt.
        assert (Hleft_len : Zlength left = kept_count) by lia.
        specialize (Hfront left HoldSel HoldNo Hleft_len).
        assert (Hleft_pos : 0 < Zlength left) by lia.
        pose proof
          (nonoverlap_snoc_previous_finish__greedy_prefix
             left p HaltNo Hleft_pos) as Hbefore.
        subst p. rewrite Hlast in Hskip. lia.
    + intros alternative HaltSel HaltNo HaltLen.
      rewrite Hprefix in HaltSel.
      destruct
        (interval_selection_extend_schedule_cases__greedy_prefix
           (sublist 0 i ps) p alternative HaltSel HaltNo)
        as [[HoldSel HoldNo] |
            [left [right [Heq [HoldSel HoldNo]]]]].
      * apply Hfront; auto.
      * assert (Halt_bounds : (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) alternative)).
        { eapply interval_bounds_selected__greedy_prefix; eauto.
          rewrite Hprefix. exact HaltSel. }
        assert (Hin_p : In p alternative).
        { rewrite Heq. apply in_or_app. right. simpl. auto. }
        pose proof
          (nonoverlap_member_end_le_finish__greedy_prefix
             alternative p HaltNo Halt_bounds Hin_p) as Hpfinish.
        rewrite Hlast. lia.
Qed.
Lemma pair_intervals_fields_at__greedy_prefix :
  forall starts ends ps k,
    PairIntervals starts ends ps ->
    (Forall (fun p => -10000 <= interval_start p /\ interval_start p < interval_end p /\ interval_end p <= 10000) ps) ->
    0 <= k < Zlength ps ->
    Znth k starts 0 = interval_start (Znth k ps default_interval) /\
    Znth k ends 0 = interval_end (Znth k ps default_interval) /\
    -10000 <= interval_start (Znth k ps default_interval) /\
    interval_start (Znth k ps default_interval) <
      interval_end (Znth k ps default_interval) /\
    interval_end (Znth k ps default_interval) <= 10000.
Proof.
  intros starts ends ps k Hpair Hbounds Hk.
  apply pair_intervals_indexed in Hpair.
  destruct Hpair as [Hlens [Hlenps Hfields]].
  assert (Hkstarts : 0 <= k < Zlength starts) by lia.
  specialize (Hfields k Hkstarts).
  pose proof
    (proj1 (forall_znth__greedy_prefix _
              (fun p =>
                 -10000 <= interval_start p /\
                 interval_start p < interval_end p /\
                 interval_end p <= 10000)
              default_interval ps) Hbounds k Hk) as Hb.
  change (Znth k ps default_interval =
            (Znth k starts 0, Znth k ends 0)) in Hfields.
  destruct (Znth k ps default_interval) as [s e] eqn:Hp.
  cbn [interval_start interval_end mk_interval] in *.
  inversion Hfields; subst. tauto.
Qed.
Lemma greedy_prefix_singleton__greedy_prefix :
  forall ps,
    0 < Zlength ps ->
    GreedyPrefixState ps 1 1
      (interval_end (Znth 0 ps default_interval)).
Proof.
  intros ps Hlen. apply greedy_prefix_state_facts.
  set (p := Znth 0 ps default_interval).
  assert (Hprefix : sublist 0 1 ps = [p]).
  { subst p. apply sublist_single. lia. }
  exists [p]. repeat split.
  - unfold IntervalSelection. rewrite Hprefix. exists []. simpl. reflexivity.
  - unfold NonOverlappingSchedule. intros x y Hx Hxy Hy.
    rewrite Zlength_cons, Zlength_nil in Hy. lia.
  - intros alternative Hsel _.
    unfold IntervalSelection in Hsel. rewrite Hprefix in Hsel.
    destruct Hsel as [removed Hperm]. apply Permutation_length in Hperm.
    rewrite length_app in Hperm. simpl in Hperm.
    rewrite !Zlength_correct. lia.
  - intros alternative Hsel _ Haltlen.
    unfold IntervalSelection in Hsel. rewrite Hprefix in Hsel.
    destruct Hsel as [removed Hperm].
    assert (Hrem : removed = []).
    { apply Permutation_length in Hperm. rewrite length_app in Hperm.
      rewrite Zlength_correct in Haltlen. simpl in *.
      apply length_zero_iff_nil. lia. }
    subst removed. rewrite app_nil_r in Hperm.
    apply Permutation_length_1_inv in Hperm. subst alternative.
    replace (schedule_finish [p]) with (interval_end p); [lia |].
    unfold schedule_finish.
    replace (Zlength [p] - 1) with 0 by
      (rewrite Zlength_cons, Zlength_nil; lia).
    rewrite Znth0_cons. reflexivity.
Qed.
Lemma greedy_prefix_yields_minimum_removals__optimum_returns :
  forall input sorted kept last_finish,
    Zlength input = Zlength sorted ->
    IntervalPermutation input sorted ->
    GreedyPrefixState sorted (Zlength input) kept last_finish ->
    MinimumRemovals input (Zlength input - kept).
Proof.
  intros input sorted kept last_finish Hlength Hperm Hgreedy.
  apply greedy_prefix_state_facts in Hgreedy.
  destruct Hgreedy as
    [chosen
      [Hchosen_selection
        [Hchosen_schedule
          [Hchosen_length
            [_ [_ [Hmaximal _]]]]]]].
  assert (Hfull : sublist 0 (Zlength input) sorted = sorted).
  { apply sublist_self. exact Hlength. }
  rewrite Hfull in Hchosen_selection, Hmaximal.
  unfold MinimumRemovals, min_value_of_subset, min_object_of_subset.
  exists (Zlength input - kept).
  split.
  - split.
    + unfold FeasibleRemovalCount.
      exists chosen.
      split.
      * unfold IntervalSelection in Hchosen_selection |- *.
        destruct Hchosen_selection as [removed Hchosen_perm].
        exists removed.
        eapply Permutation_trans; eauto.
      * split; [exact Hchosen_schedule | lia].
    + intros alternative_count Halternative_count.
      unfold FeasibleRemovalCount in Halternative_count.
      destruct Halternative_count as
        [alternative
          [Halternative_selection
            [Halternative_schedule Halternative_count]]].
      assert (Hsorted_selection : IntervalSelection sorted alternative).
      { unfold IntervalSelection in Halternative_selection |- *.
        destruct Halternative_selection as [removed Halternative_perm].
        exists removed.
        eapply Permutation_trans.
        - apply Permutation_sym. exact Hperm.
        - exact Halternative_perm. }
      specialize
        (Hmaximal alternative Hsorted_selection Halternative_schedule).
      lia.
  - reflexivity.
Qed.
Lemma minimum_removals_empty__optimum_returns :
  forall input,
    Zlength input = 0 ->
    MinimumRemovals input 0.
Proof.
  intros input Hlength.
  destruct input as [|x xs].
  - unfold MinimumRemovals, min_value_of_subset, min_object_of_subset.
    exists 0.
    split.
    + split.
      * unfold FeasibleRemovalCount.
        exists (@nil interval).
        split.
        -- unfold IntervalSelection.
           exists (@nil interval).
           constructor.
        -- split.
           ++ unfold NonOverlappingSchedule.
              intros i j Hi Hij Hj.
              rewrite Zlength_nil in Hj.
              lia.
           ++ rewrite Zlength_nil.
              lia.
      * intros alternative_count Halternative_count.
        unfold FeasibleRemovalCount in Halternative_count.
        destruct Halternative_count as
          [alternative
            [Halternative_selection
              [_ Halternative_count]]].
        unfold IntervalSelection in Halternative_selection.
        destruct Halternative_selection as [removed Halternative_perm].
        apply Permutation_nil in Halternative_perm.
        apply app_eq_nil in Halternative_perm as [Halternative_nil _].
        subst alternative.
        rewrite Zlength_nil in Halternative_count.
        lia.
    + reflexivity.
  - rewrite Zlength_cons in Hlength.
    pose proof (Zlength_nonneg xs).
    lia.
Qed.

(** Z-indexed proof view of the standard pointwise relation. *)
Lemma forall2_znth_intervals {A B : Type} (P : A -> B -> Prop)
    (xs : list A) (ys : list B) dx dy :
  Forall2 P xs ys <->
  Zlength xs = Zlength ys /\
  forall k, 0 <= k < Zlength xs -> P (Znth k xs dx) (Znth k ys dy).
Proof.
  rewrite (Forall2_nth_iff _ _ _ xs ys dx dy), !Zlength_correct.
  unfold Znth. split.
  - intros [Hlen Hpoint]. split; [lia|]. intros k Hk. apply Hpoint. lia.
  - intros [Hlen Hpoint]. split; [lia|]. intros k Hk.
    specialize (Hpoint (Z.of_nat k) ltac:(lia)).
    now rewrite Nat2Z.id in Hpoint.
Qed.

(** Transport the explicit array premises through the record representation. *)
Lemma pair_intervals_bounds_iff : forall starts ends ps,
  PairIntervals starts ends ps ->
  (Forall (Z.le (-10000)) starts /\ Forall2 Z.lt starts ends /\
   Forall (Z.ge 10000) ends) <->
  Forall (fun p => -10000 <= interval_start p /\
    interval_start p < interval_end p /\ interval_end p <= 10000) ps.
Proof.
  intros starts ends ps Hpair.
  pose proof (pair_intervals_lengths_and_fields__partition_lomuto
    starts ends ps Hpair) as [Hse [Hps Hfields]].
  rewrite (forall_znth__greedy_prefix _ _ 0 starts).
  rewrite (forall_znth__greedy_prefix _ _ 0 ends).
  rewrite (forall_znth__greedy_prefix _ _ default_interval ps).
  rewrite (forall2_znth_intervals Z.lt starts ends 0 0).
  split.
  - intros [Hs [[_ Hproper] He]] k Hk.
    destruct (Hfields k ltac:(lia)) as [Hstart Hend].
    rewrite Hstart, Hend. repeat split.
    + apply Hs. lia.
    + apply Hproper. lia.
    + specialize (He k ltac:(lia)). lia.
  - intros Hb. split.
    + intros k Hk. specialize (Hb k ltac:(lia)).
      destruct (Hfields k Hk) as [Hstart Hend]. lia.
    + split.
      * split; [exact Hse|]. intros k Hk.
        specialize (Hb k ltac:(lia)).
        destruct (Hfields k Hk) as [Hstart Hend]. lia.
      * intros k Hk. specialize (Hb k ltac:(lia)).
        destruct (Hfields k ltac:(lia)) as [Hstart Hend]. lia.
Qed.
