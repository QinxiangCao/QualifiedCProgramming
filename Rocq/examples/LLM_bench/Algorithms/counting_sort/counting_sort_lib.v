From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Sorting.Permutation.
From AUXLib Require Import ListLib.

(** Mixed local storage has [Some 0] in every initialized histogram cell. *)
Definition CountingZeroedPrefix
    (mixed_counts : list (option Z)) (upto : Z) : Prop :=
  forall value,
    0 <= value < upto ->
    Znth value mixed_counts None = Some 0.

(** The canonical number of occurrences of [value] in a mathematical list. *)
Definition CountingFrequency (values : list Z) (value : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec values value).

(** The exact histogram of the already scanned input prefix. *)
Definition CountingHistogramPrefix
    (input counts : list Z) (processed : Z) : Prop :=
  forall value,
    0 <= value < 100 ->
    Znth value counts 0 =
      CountingFrequency (sublist 0 processed input) value.

(** The canonical inclusive end of one value bucket. *)
Definition CountingCumulativeEnd (input : list Z) (value : Z) : Z :=
  fold_right Z.add 0
    (map
      (fun index : nat =>
        CountingFrequency input (Z.of_nat index))
      (seq 0 (Z.to_nat (value + 1)))).

(** During prefix summation, lower buckets already hold cumulative ends and
    the remaining buckets still hold raw whole-input frequencies. *)
Definition CountingCumulativeState
    (input positions : list Z) (next_value : Z) : Prop :=
  forall value,
    0 <= value < 100 ->
    Znth value positions 0 =
      if value <? next_value
      then CountingCumulativeEnd input value
      else CountingFrequency input value.

(** The implementation-independent mathematical result needed by the frozen
    sort contract. *)
Definition CountingSorted (input sorted : list Z) : Prop :=
  Permutation input sorted /\
  increasing sorted.

Definition CountingBucketStart (input : list Z) (value : Z) : Z :=
  if value <=? 0
  then 0
  else CountingCumulativeEnd input (value - 1).

(** Reverse traversal fills a suffix of every value bucket.  [positions]
    marks each still-unfilled bucket prefix; [mixed_output] records the cells
    already known to agree with the mathematical sorted result. *)
Definition CountingPlacementProgress
    (input positions bucket_ends : list Z)
    (mixed_output : list (option Z)) (sorted : list Z)
    (next_index : Z) : Prop :=
  CountingSorted input sorted /\
  (forall value,
    0 <= value < 100 ->
    Znth value bucket_ends 0 =
      CountingCumulativeEnd input value) /\
  (forall value,
    0 <= value < 100 ->
    Znth value positions 0 =
      CountingBucketStart input value +
      CountingFrequency (sublist 0 (next_index + 1) input) value) /\
  (forall value index,
    0 <= value < 100 ->
    Znth value positions 0 <= index < Znth value bucket_ends 0 ->
    Znth index mixed_output None = Some (Znth index sorted 0)).

(** Sequential copy-back state: exactly the target prefix has been written,
    and the untouched suffix still comes from the original input. *)
Definition CountingCopyProgress
    (before target live : list Z) (copied : Z) : Prop :=
  live =
    app
      (sublist 0 copied target)
      (sublist copied (Zlength before) before).

From Coq Require Import Lia.
Lemma counting_zeroed_prefix_replace__initial_zeroing :
  forall mixed_counts upto,
    Zlength mixed_counts = 100 ->
    0 <= upto < 100 ->
    CountingZeroedPrefix mixed_counts upto ->
    CountingZeroedPrefix
      (replace_Znth upto (Some 0) mixed_counts) (upto + 1).
Proof.
  intros mixed_counts upto Hlength Hupto Hzeroed.
  unfold CountingZeroedPrefix in *.
  intros value Hvalue.
  destruct (Z.eq_dec value upto) as [Heq | Hneq].
  - subst value.
    rewrite Znth_replace_Znth_Same by (rewrite Hlength; lia).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by
        (try rewrite Hlength; lia).
    apply Hzeroed.
    lia.
Qed.
Lemma counting_histogram_empty__initial_zeroing :
  forall input zeros,
    (forall value,
      0 <= value < 100 ->
      Znth value zeros 0 = 0) ->
    CountingHistogramPrefix input zeros 0.
Proof.
  intros input zeros Hzeros.
  unfold CountingHistogramPrefix, CountingFrequency.
  intros value Hvalue.
  rewrite Hzeros by exact Hvalue.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma counting_all_zero_materialization__initial_zeroing :
  forall mixed_counts,
    Zlength mixed_counts = 100 ->
    (forall value,
      0 <= value < 100 ->
      Znth value mixed_counts None = Some 0) ->
    mixed_counts = map (@Some Z) (repeat 0 (Z.to_nat 100)).
Proof.
  intros mixed_counts Hlength Hzeroed.
  apply (proj2 (list_eq_ext
    mixed_counts (map (@Some Z) (repeat 0 (Z.to_nat 100))) None)).
  split.
  - rewrite Hlength.
    rewrite !Zlength_correct, length_map, repeat_length.
    reflexivity.
  - intros value Hvalue.
    rewrite Hzeroed by lia.
    rewrite (Znth_indep
      (map (@Some Z) (repeat 0 (Z.to_nat 100)))
      value None (Some 0)).
    + unfold Znth.
      rewrite map_nth, nth_repeat.
      reflexivity.
    + rewrite !Zlength_correct, length_map, repeat_length.
      lia.
Qed.
Lemma counting_frequency_prefix_snoc__histogram_cumulative :
  forall (input : list Z) i value,
    0 <= i < Zlength input ->
    CountingFrequency (sublist 0 (i + 1) input) value =
      CountingFrequency (sublist 0 i input) value +
      if Z.eq_dec (Znth i input 0) value then 1 else 0.
Proof.
  intros input i value Hi.
  assert (Hprefix :
    sublist 0 (i + 1) input =
      sublist 0 i input ++ [Znth i input 0]).
  {
    rewrite (sublist_split 0 (i + 1) i input) by lia.
    rewrite (sublist_single 0 i input) by lia.
    reflexivity.
  }
  rewrite Hprefix.
  unfold CountingFrequency.
  rewrite count_occ_app, Nat2Z.inj_add.
  destruct (Z.eq_dec (Znth i input 0) value) as [Heq | Hneq].
  - subst value.
    simpl.
    destruct (Z.eq_dec (Znth i input 0) (Znth i input 0)); lia.
  - simpl.
    destruct (Z.eq_dec (Znth i input 0) value); [contradiction | lia].
Qed.
Lemma counting_cumulative_end_step__histogram_cumulative :
  forall (input : list Z) value,
    0 <= value ->
    CountingCumulativeEnd input value =
      CountingCumulativeEnd input (value - 1) +
      CountingFrequency input value.
Proof.
  intros input value Hvalue.
  unfold CountingCumulativeEnd.
  fold sum.
  replace (value - 1 + 1) with value by lia.
  replace (Z.to_nat (value + 1)) with (S (Z.to_nat value)) by lia.
  rewrite seq_S, map_app, sum_app.
  simpl.
  replace (Z.of_nat (0 + Z.to_nat value)) with value by lia.
  unfold sum.
  rewrite Z2Nat.id by lia.
  lia.
Qed.
Lemma counting_frequency_cons__histogram_cumulative :
  forall (input : list Z) x value,
    CountingFrequency (x :: input) value =
      CountingFrequency input value +
      if Z.eq_dec x value then 1 else 0.
Proof.
  intros input x value.
  unfold CountingFrequency.
  simpl.
  destruct (Z.eq_dec x value); simpl; rewrite ?Nat2Z.inj_succ; lia.
Qed.
Lemma counting_frequency_sum_cons_notin__histogram_cumulative :
  forall (buckets input : list Z) x,
    ~ In x buckets ->
    sum (map (fun value => CountingFrequency (x :: input) value) buckets) =
      sum (map (fun value => CountingFrequency input value) buckets).
Proof.
  intros buckets.
  induction buckets as [| bucket buckets IH]; intros input x Hnotin.
  - reflexivity.
  - assert (Hx_bucket : x <> bucket).
    { intro Heq. apply Hnotin. left. symmetry. exact Heq. }
    assert (Hx_buckets : ~ In x buckets).
    { intro Hin. apply Hnotin. right. exact Hin. }
    simpl.
    rewrite (counting_frequency_cons__histogram_cumulative input x bucket).
    destruct (Z.eq_dec x bucket); [contradiction |].
    rewrite IH by exact Hx_buckets.
    lia.
Qed.
Lemma counting_frequency_sum_cons_bound__histogram_cumulative :
  forall (buckets input : list Z) x,
    NoDup buckets ->
    sum (map (fun value => CountingFrequency (x :: input) value) buckets) <=
      sum (map (fun value => CountingFrequency input value) buckets) + 1.
Proof.
  intros buckets.
  induction buckets as [| bucket buckets IH]; intros input x Hnodup.
  - simpl. lia.
  - inversion Hnodup as [| ? ? Hnotin Htail]; subst.
    simpl.
    rewrite (counting_frequency_cons__histogram_cumulative input x bucket).
    destruct (Z.eq_dec x bucket) as [Heq | Hneq].
    + subst bucket.
      rewrite (counting_frequency_sum_cons_notin__histogram_cumulative
        buckets input x) by exact Hnotin.
      destruct (Z.eq_dec x x); [lia | contradiction].
    + specialize (IH input x Htail).
      destruct (Z.eq_dec x bucket); [contradiction | lia].
Qed.
Lemma counting_frequency_range_sum_bound__histogram_cumulative :
  forall (buckets input : list Z),
    NoDup buckets ->
    sum (map (fun value => CountingFrequency input value) buckets) <=
      Zlength input.
Proof.
  intros buckets input.
  revert buckets.
  induction input as [| x input IH]; intros buckets Hnodup.
  - induction buckets as [| bucket buckets IHbuckets].
    + unfold sum, Zlength. simpl. lia.
    + inversion Hnodup; subst.
      unfold CountingFrequency, sum, Zlength. simpl.
      apply IHbuckets; assumption.
  - pose proof (IH buckets Hnodup) as Hprefix.
    pose proof (counting_frequency_sum_cons_bound__histogram_cumulative
      buckets input x Hnodup) as Hstep.
    rewrite Zlength_cons.
    lia.
Qed.
Lemma counting_nat_to_Z_map_nodup__histogram_cumulative :
  forall (indices : list nat),
    NoDup indices ->
    NoDup (map Z.of_nat indices).
Proof.
  intros indices Hnodup.
  induction Hnodup as [| index indices Hnotin Htail IH].
  - constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [other [Heq Hin]].
      apply Hnotin.
      assert (other = index) by lia.
      subst other.
      exact Hin.
    + exact IH.
Qed.
Lemma counting_cumulative_end_bound__histogram_cumulative :
  forall (input : list Z) value,
    CountingCumulativeEnd input value <= Zlength input.
Proof.
  intros input value.
  pose proof (counting_nat_to_Z_map_nodup__histogram_cumulative
    (seq 0 (Z.to_nat (value + 1)))
    (seq_NoDup (Z.to_nat (value + 1)) 0)) as Hnodup.
  pose proof (counting_frequency_range_sum_bound__histogram_cumulative
    (map Z.of_nat (seq 0 (Z.to_nat (value + 1)))) input Hnodup) as Hbound.
  rewrite map_map in Hbound.
  exact Hbound.
Qed.
Lemma counting_frequency_nonnegative__placement_boundaries :
  forall values value,
    0 <= CountingFrequency values value.
Proof.
  intros values value.
  unfold CountingFrequency.
  lia.
Qed.
Lemma counting_frequency_positive_In__placement_boundaries :
  forall values value,
    In value values ->
    1 <= CountingFrequency values value.
Proof.
  intros values value Hin.
  unfold CountingFrequency.
  apply (proj1 (count_occ_In Z.eq_dec values value)) in Hin.
  lia.
Qed.
Lemma counting_cumulative_nonnegative__placement_boundaries :
  forall values value,
    0 <= CountingCumulativeEnd values value.
Proof.
  intros values value.
  unfold CountingCumulativeEnd.
  induction (seq 0 (Z.to_nat (value + 1))) as [| index rest IH]; simpl.
  - lia.
  - pose proof
      (counting_frequency_nonnegative__placement_boundaries
         values (Z.of_nat index)).
    lia.
Qed.
Lemma fold_right_Zadd_acc__placement_boundaries :
  forall values base,
    fold_right Z.add base values =
      fold_right Z.add 0 values + base.
Proof.
  induction values as [| value values IH]; intros base; simpl.
  - lia.
  - rewrite IH.
    lia.
Qed.
Lemma counting_cumulative_bucket_identity__placement_boundaries :
  forall input value,
    0 <= value ->
    CountingCumulativeEnd input value =
      CountingBucketStart input value + CountingFrequency input value.
Proof.
  intros input value Hvalue.
  unfold CountingBucketStart.
  destruct (value <=? 0) eqn:Hvalue0.
  - apply Z.leb_le in Hvalue0.
    assert (value = 0) by lia.
    subst value.
    unfold CountingCumulativeEnd.
    simpl.
    lia.
  - apply Z.leb_gt in Hvalue0.
    unfold CountingCumulativeEnd.
    replace (Z.to_nat (value + 1)) with (S (Z.to_nat value)) by lia.
    rewrite seq_S, map_app, fold_right_app.
    simpl.
    replace (Z.of_nat (0 + Z.to_nat value)) with value by lia.
    replace (value - 1 + 1) with value by lia.
    rewrite fold_right_Zadd_acc__placement_boundaries.
    rewrite Z2Nat.id by lia.
    rewrite Z.add_0_r.
    reflexivity.
Qed.
Lemma counting_bucket_start_nonnegative__placement_boundaries :
  forall input value,
    0 <= CountingBucketStart input value.
Proof.
  intros input value.
  unfold CountingBucketStart.
  destruct (value <=? 0); [lia|].
  apply counting_cumulative_nonnegative__placement_boundaries.
Qed.
Lemma counting_index_bounds_to_In_bounds__placement_boundaries :
  forall input,
    (forall index,
      0 <= index < Zlength input ->
      0 <= Znth index input 0 < 100) ->
    forall value,
      In value input ->
      0 <= value < 100.
Proof.
  intros input Hbounds value Hin.
  destruct (In_nth input value 0 Hin) as [index [Hindex Hnth]].
  specialize (Hbounds (Z.of_nat index)).
  assert (0 <= Z.of_nat index < Zlength input).
  { rewrite Zlength_correct. lia. }
  specialize (Hbounds H).
  unfold Znth in Hbounds.
  rewrite Nat2Z.id in Hbounds.
  rewrite Hnth in Hbounds.
  exact Hbounds.
Qed.
Lemma counting_canonical_sorted_exists__placement_boundaries :
  forall input,
    (forall value, In value input -> 0 <= value < 100) ->
    exists sorted,
      Zlength sorted = Zlength input /\
      (forall index,
        0 <= index < Zlength input ->
        0 <= Znth index sorted 0 < 100) /\
      CountingSorted input sorted.
Proof.
  intros input Hbounds.
  exists (sort input).
  assert (Hperm : Permutation input (sort input)) by apply sort_list_perm.
  split.
  - pose proof (Permutation_length Hperm) as Hlength.
    rewrite !Zlength_correct.
    lia.
  - split.
    + intros index Hindex.
      assert (Hin_sorted : In (Znth index (sort input) 0) (sort input)).
      { unfold Znth.
        apply nth_In.
        pose proof (Permutation_length Hperm) as Hlength.
        rewrite <- Hlength.
        rewrite Zlength_correct in Hindex.
        lia. }
      apply Hbounds.
      eapply Permutation_in.
      * exact (Permutation_sym Hperm).
      * exact Hin_sorted.
    + unfold CountingSorted.
      split; [exact Hperm | apply sort_list_increasing].
Qed.
Lemma counting_frequency_cons_fold__placement_boundaries :
  forall indices input head,
    fold_right Z.add 0
      (map (fun index : nat =>
        CountingFrequency (head :: input) (Z.of_nat index)) indices) =
    fold_right Z.add 0
      (map (fun index : nat =>
        CountingFrequency input (Z.of_nat index)) indices) +
    Z.of_nat
      (count_occ Z.eq_dec (map Z.of_nat indices) head).
Proof.
  induction indices as [| index rest IH]; intros input head; simpl.
  - lia.
  - unfold CountingFrequency at 1.
    simpl count_occ.
    destruct (Z.eq_dec head (Z.of_nat index)) as [Heq | Hneq];
      destruct (Z.eq_dec (Z.of_nat index) head) as [Heq' | Hneq'];
      try congruence;
      rewrite IH;
      unfold CountingFrequency;
      lia.
Qed.
Lemma counting_cumulative_cons_bounded__placement_boundaries :
  forall input head value,
    0 <= head <= value ->
    CountingCumulativeEnd (head :: input) value =
      CountingCumulativeEnd input value + 1.
Proof.
  intros input head value Hhead.
  unfold CountingCumulativeEnd.
  rewrite counting_frequency_cons_fold__placement_boundaries.
  assert
    (Hmap :
      count_occ Z.eq_dec
        (map Z.of_nat (seq 0 (Z.to_nat (value + 1)))) head = 1%nat).
  { assert
      (Hin : In (Z.to_nat head) (seq 0 (Z.to_nat (value + 1)))).
    { apply (proj2 (in_seq (Z.to_nat (value + 1)) 0 (Z.to_nat head))).
      lia. }
    assert
      (Hcount_nat :
        count_occ Nat.eq_dec
          (seq 0 (Z.to_nat (value + 1))) (Z.to_nat head) = 1%nat).
    { apply
        ((proj1
          (NoDup_count_occ' Nat.eq_dec
            (seq 0 (Z.to_nat (value + 1)))))
          (seq_NoDup (Z.to_nat (value + 1)) 0)
          (Z.to_nat head)
          Hin). }
    pose proof
      (@count_occ_map nat Z Z.of_nat Nat.eq_dec Z.eq_dec
        (fun x y Heq => proj1 (Nat2Z.inj_iff x y) Heq)
        (Z.to_nat head)
        (seq 0 (Z.to_nat (value + 1)))) as Hcount_map.
    rewrite Z2Nat.id in Hcount_map by lia.
    lia. }
  rewrite Hmap.
  lia.
Qed.
Lemma counting_cumulative_99_length__placement_boundaries :
  forall input,
    (forall value, In value input -> 0 <= value < 100) ->
    CountingCumulativeEnd input 99 = Zlength input.
Proof.
  induction input as [| head input IH]; intros Hbounds.
  - reflexivity.
  - assert (Hhead : 0 <= head < 100) by (apply Hbounds; simpl; auto).
    assert (Htail : forall value, In value input -> 0 <= value < 100).
    { intros value Hin. apply Hbounds. simpl. auto. }
    rewrite counting_cumulative_cons_bounded__placement_boundaries by lia.
    rewrite IH by exact Htail.
    rewrite !Zlength_correct.
    simpl.
    lia.
Qed.
Lemma counting_cumulative_positive_at_In__placement_boundaries :
  forall input value,
    0 <= value ->
    In value input ->
    1 <= CountingCumulativeEnd input value.
Proof.
  intros input value Hvalue Hin.
  rewrite counting_cumulative_bucket_identity__placement_boundaries by lia.
  pose proof
    (counting_bucket_start_nonnegative__placement_boundaries input value).
  pose proof
    (counting_frequency_positive_In__placement_boundaries input value Hin).
  lia.
Qed.
Lemma counting_placement_initial__placement_boundaries :
  forall input positions output sorted,
    CountingSorted input sorted ->
    CountingCumulativeState input positions 100 ->
    CountingPlacementProgress
      input positions positions output sorted (Zlength input - 1).
Proof.
  intros input positions output sorted Hsorted Hstate.
  unfold CountingPlacementProgress.
  split.
  - exact Hsorted.
  - split.
    + intros value Hvalue.
      rewrite Hstate by exact Hvalue.
      assert (Hltb : (value <? 100) = true) by (apply Z.ltb_lt; lia).
      rewrite Hltb.
      reflexivity.
    + split.
      * intros value Hvalue.
        rewrite Hstate by exact Hvalue.
        assert (Hltb : (value <? 100) = true) by (apply Z.ltb_lt; lia).
        rewrite Hltb.
        replace (Zlength input - 1 + 1) with (Zlength input) by lia.
        rewrite sublist_self by reflexivity.
        apply counting_cumulative_bucket_identity__placement_boundaries.
        lia.
      * intros value index Hvalue Hindex.
        lia.
Qed.
Lemma counting_bucket_start_nat__placement_boundaries :
  forall input n,
    CountingBucketStart input (Z.of_nat n) =
      CountingCumulativeEnd input (Z.of_nat n - 1).
Proof.
  intros input n.
  destruct n as [| n].
  - reflexivity.
  - unfold CountingBucketStart.
    assert (Hleb : (Z.of_nat (S n) <=? 0) = false)
      by (apply Z.leb_gt; lia).
    rewrite Hleb.
    reflexivity.
Qed.
Lemma counting_bucket_cover_upto__placement_boundaries :
  forall input limit index,
    0 <= index <
      CountingCumulativeEnd input (Z.of_nat limit - 1) ->
    exists value,
      0 <= value < Z.of_nat limit /\
      CountingBucketStart input value <= index <
        CountingCumulativeEnd input value.
Proof.
  intros input limit.
  induction limit as [| limit IH]; intros index Hindex.
  - unfold CountingCumulativeEnd in Hindex.
    simpl in Hindex.
    lia.
  - destruct
      (Z_lt_ge_dec index
        (CountingCumulativeEnd input (Z.of_nat limit - 1)))
      as [Hprevious | Hcurrent].
    + destruct (IH index) as [value [Hvalue Hbucket]]; [lia |].
      exists value.
      split; [lia | exact Hbucket].
    + exists (Z.of_nat limit).
      split.
      * lia.
      * rewrite counting_bucket_start_nat__placement_boundaries.
        replace (Z.of_nat (S limit) - 1) with (Z.of_nat limit) in Hindex
          by lia.
        lia.
Qed.
Lemma counting_placement_complete__placement_boundaries :
  forall input positions bucket_ends output sorted,
    (forall value, In value input -> 0 <= value < 100) ->
    CountingPlacementProgress
      input positions bucket_ends output sorted (-1) ->
    forall index,
      0 <= index < Zlength input ->
      Znth index output None = Some (Znth index sorted 0).
Proof.
  intros input positions bucket_ends output sorted Hbounds Hprogress.
  destruct Hprogress as
    [Hsorted [Hbucket_ends [Hpositions Hfilled]]].
  intros index Hindex.
  assert
    (Hlimit :
      0 <= index <
        CountingCumulativeEnd input (Z.of_nat 100 - 1)).
  { replace (Z.of_nat 100 - 1) with 99 by reflexivity.
    rewrite counting_cumulative_99_length__placement_boundaries
      by exact Hbounds.
    exact Hindex. }
  destruct
    (counting_bucket_cover_upto__placement_boundaries
      input 100%nat index Hlimit)
    as [value [Hvalue Hbucket]].
  specialize (Hpositions value Hvalue).
  replace (-1 + 1) with 0 in Hpositions by lia.
  unfold sublist in Hpositions.
  simpl in Hpositions.
  unfold CountingFrequency in Hpositions.
  simpl in Hpositions.
  specialize (Hbucket_ends value Hvalue).
  apply (Hfilled value index Hvalue).
  lia.
Qed.
Lemma counting_output_prefix__placement_boundaries :
  forall output sorted n,
    0 <= n <= Zlength output ->
    Zlength sorted = n ->
    (forall index,
      0 <= index < n ->
      Znth index output None = Some (Znth index sorted 0)) ->
    sublist 0 n output = map (@Some Z) sorted.
Proof.
  intros output sorted n Hn Hsorted Hpointwise.
  apply (proj2 (list_eq_ext _ _ None)).
  split.
  - rewrite Zlength_sublist by lia.
    rewrite Zlength_correct, length_map.
    rewrite <- Zlength_correct.
    lia.
  - intros index Hindex.
    rewrite Zlength_sublist in Hindex by lia.
    rewrite Znth_sublist0 by lia.
    unfold Znth at 2.
    assert (Hindex_nat : (Z.to_nat index < length sorted)%nat).
    { rewrite Zlength_correct in Hsorted.
      lia. }
    rewrite
      (map_nth_len Z (option Z) (@Some Z) sorted
        (Z.to_nat index) None 0)
      by exact Hindex_nat.
    apply Hpointwise.
    lia.
Qed.
Lemma counting_frequency_cons__placement_transition :
  forall x xs value,
    CountingFrequency (x :: xs) value =
      CountingFrequency xs value +
      if Z.eq_dec x value then 1 else 0.
Proof.
  intros x xs value.
  unfold CountingFrequency.
  simpl.
  destruct (Z.eq_dec x value); lia.
Qed.
Lemma counting_frequency_sum_cons__placement_transition :
  forall indices x xs,
    0 <= x ->
    fold_right Z.add 0
      (map
        (fun index : nat =>
          CountingFrequency (x :: xs) (Z.of_nat index))
        indices) =
    fold_right Z.add 0
      (map
        (fun index : nat =>
          CountingFrequency xs (Z.of_nat index))
        indices) +
    Z.of_nat (count_occ Nat.eq_dec indices (Z.to_nat x)).
Proof.
  induction indices as [| index indices IH]; intros x xs Hx; simpl.
  - lia.
  - rewrite counting_frequency_cons__placement_transition.
    rewrite IH by exact Hx.
    destruct (Z.eq_dec x (Z.of_nat index)) as [Heq | Hneq];
      destruct (Nat.eq_dec index (Z.to_nat x)) as [Heq' | Hneq'];
      try lia.
Qed.
Lemma counting_cumulative_end_nil__placement_transition :
  forall value,
    CountingCumulativeEnd [] value = 0.
Proof.
  intros value.
  unfold CountingCumulativeEnd, CountingFrequency.
  set (indices := seq 0 (Z.to_nat (value + 1))).
  clearbody indices.
  induction indices as [| index indices IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.
Lemma counting_cumulative_end_cons__placement_transition :
  forall x xs value,
    0 <= x ->
    0 <= value ->
    CountingCumulativeEnd (x :: xs) value =
      CountingCumulativeEnd xs value +
      if x <=? value then 1 else 0.
Proof.
  intros x xs value Hx Hvalue.
  unfold CountingCumulativeEnd.
  rewrite counting_frequency_sum_cons__placement_transition by exact Hx.
  destruct (x <=? value) eqn:Hle.
  - apply Z.leb_le in Hle.
    assert (Hin : In (Z.to_nat x) (seq 0 (Z.to_nat (value + 1)))).
    { rewrite in_seq. lia. }
    pose proof
      (proj1 (NoDup_count_occ' Nat.eq_dec (seq 0 (Z.to_nat (value + 1))))
        (seq_NoDup (Z.to_nat (value + 1)) 0)
        (Z.to_nat x) Hin) as Hcount.
    rewrite Hcount. simpl. lia.
  - apply Z.leb_gt in Hle.
    assert (Hnotin : ~ In (Z.to_nat x) (seq 0 (Z.to_nat (value + 1)))).
    { rewrite in_seq. lia. }
    pose proof
      (proj1
        (count_occ_not_In Nat.eq_dec
          (seq 0 (Z.to_nat (value + 1))) (Z.to_nat x))
        Hnotin) as Hcount.
    rewrite Hcount. simpl. lia.
Qed.
Lemma counting_cumulative_end_as_filter__placement_transition :
  forall values value,
    Forall (fun x => 0 <= x) values ->
    0 <= value ->
    CountingCumulativeEnd values value =
      Zlength (filter (fun x => x <=? value) values).
Proof.
  induction values as [| x xs IH]; intros value Hnonneg Hvalue.
  - rewrite counting_cumulative_end_nil__placement_transition.
    reflexivity.
  - inversion Hnonneg as [| ? ? Hx Hxs]; subst.
    rewrite counting_cumulative_end_cons__placement_transition by assumption.
    simpl.
    destruct (x <=? value); simpl.
    + rewrite Zlength_cons, IH by assumption. lia.
    + rewrite IH by assumption. lia.
Qed.
Lemma counting_forall_nonnegative_from_Znth__placement_transition :
  forall values,
    (forall index,
      0 <= index < Zlength values ->
      0 <= Znth index values 0) ->
    Forall (fun x => 0 <= x) values.
Proof.
  induction values as [| x xs IH]; intros Hpoint.
  - constructor.
  - constructor.
    + specialize (Hpoint 0).
      rewrite Zlength_cons in Hpoint.
      rewrite Znth0_cons in Hpoint.
      apply Hpoint.
      pose proof (Zlength_nonneg xs). lia.
    + apply IH. intros index Hindex.
      specialize (Hpoint (index + 1)).
      rewrite Zlength_cons in Hpoint.
      rewrite Znth_cons in Hpoint by lia.
      replace (index + 1 - 1) with index in Hpoint by lia.
      apply Hpoint. lia.
Qed.
Lemma counting_increasing_filter_lower__placement_transition :
  forall values value index,
    increasing values ->
    0 <= index < Zlength values ->
    Znth index values 0 <= value ->
    index < Zlength (filter (fun x => x <=? value) values).
Proof.
  induction values as [| x xs IH]; intros value index Hinc Hindex Hle.
  - rewrite Zlength_nil in Hindex. lia.
  - destruct (Z.eq_dec index 0) as [Hindex0 | Hindex0].
    + subst index.
      rewrite Znth0_cons in Hle.
      simpl.
      destruct (x <=? value) eqn:Hxvalue.
      2: { apply Z.leb_gt in Hxvalue. lia. }
      rewrite Zlength_cons.
      pose proof
        (Zlength_nonneg (filter (fun x => x <=? value) xs)).
      lia.
    + assert (Hindexpos : 0 < index) by lia.
      simpl in Hinc.
      assert (Htail_inc : increasing xs).
      { eapply increasing_aux_tail_increasing. exact Hinc. }
      assert (Htarget_in : In (Znth (index - 1) xs 0) xs).
      { unfold Znth.
        apply nth_In.
        apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia.
        rewrite <- Zlength_correct.
        rewrite Zlength_cons in Hindex.
        lia. }
      assert (Hx_target : x <= Znth (index - 1) xs 0).
      { eapply increasing_aux_head_le_all_In; eauto. }
      rewrite Znth_cons in Hle by lia.
      simpl.
      destruct (x <=? value) eqn:Hxvalue.
      2: { apply Z.leb_gt in Hxvalue. lia. }
      rewrite Zlength_cons.
      specialize
        (IH value (index - 1) Htail_inc ltac:(rewrite Zlength_cons in Hindex; lia) Hle).
      lia.
Qed.
Lemma counting_filter_below_lower_empty__placement_transition :
  forall values lower value,
    Forall (fun x => lower <= x) values ->
    value < lower ->
    filter (fun x => x <=? value) values = [].
Proof.
  induction values as [| x xs IH]; intros lower value Hlower Hlt.
  - reflexivity.
  - inversion Hlower as [| ? ? Hx Hxs]; subst.
    simpl.
    destruct (x <=? value) eqn:Hxvalue.
    + apply Z.leb_le in Hxvalue. lia.
    + apply IH with (lower := lower); assumption.
Qed.
Lemma counting_increasing_filter_upper__placement_transition :
  forall values value index,
    increasing values ->
    0 <= index < Zlength values ->
    value < Znth index values 0 ->
    Zlength (filter (fun x => x <=? value) values) <= index.
Proof.
  induction values as [| x xs IH]; intros value index Hinc Hindex Hlt.
  - rewrite Zlength_nil in Hindex. lia.
  - destruct (Z.eq_dec index 0) as [Hindex0 | Hindex0].
    + subst index.
      rewrite Znth0_cons in Hlt.
      simpl in Hinc.
      assert (Hlower : Forall (fun y => x <= y) (x :: xs)).
      { constructor.
        - lia.
        - rewrite Forall_forall. intros y Hy.
          eapply increasing_aux_head_le_all_In; eauto. }
      rewrite
        (counting_filter_below_lower_empty__placement_transition
          (x :: xs) x value Hlower Hlt).
      reflexivity.
    + assert (Hindexpos : 0 < index) by lia.
      simpl in Hinc.
      assert (Htail_inc : increasing xs).
      { eapply increasing_aux_tail_increasing. exact Hinc. }
      rewrite Znth_cons in Hlt by lia.
      specialize
        (IH value (index - 1) Htail_inc ltac:(rewrite Zlength_cons in Hindex; lia) Hlt).
      simpl.
      destruct (x <=? value); simpl.
      * rewrite Zlength_cons. lia.
      * lia.
Qed.
Lemma counting_cumulative_end_perm__placement_transition :
  forall values1 values2 value,
    Permutation values1 values2 ->
    CountingCumulativeEnd values1 value =
      CountingCumulativeEnd values2 value.
Proof.
  intros values1 values2 value Hperm.
  assert (Hfrequency : forall x,
    CountingFrequency values1 x = CountingFrequency values2 x).
  { intros x. unfold CountingFrequency.
    f_equal.
    exact
      (proj1 (Permutation_count_occ Z.eq_dec values1 values2) Hperm x). }
  unfold CountingCumulativeEnd.
  set (indices := seq 0 (Z.to_nat (value + 1))).
  clearbody indices.
  induction indices as [| index indices IH]; simpl.
  - reflexivity.
  - rewrite Hfrequency, IH. reflexivity.
Qed.
Lemma counting_sorted_bucket_value__placement_transition :
  forall input sorted value index,
    CountingSorted input sorted ->
    Forall (fun x => 0 <= x) sorted ->
    0 <= value ->
    0 <= index < Zlength sorted ->
    CountingBucketStart input value <= index <
      CountingCumulativeEnd input value ->
    Znth index sorted 0 = value.
Proof.
  intros input sorted value index Hsorted Hnonneg Hvalue Hindex Hbucket.
  destruct Hsorted as [Hperm Hinc].
  assert (Hend : CountingCumulativeEnd input value =
      Zlength (filter (fun x => x <=? value) sorted)).
  { rewrite counting_cumulative_end_perm__placement_transition with
      (values2 := sorted) by exact Hperm.
    apply counting_cumulative_end_as_filter__placement_transition;
      assumption. }
  destruct (value <=? 0) eqn:Hvalue0.
  - apply Z.leb_le in Hvalue0.
    assert (Hnotgt : ~ value < Znth index sorted 0).
    { intro Hgt.
      pose proof
        (counting_increasing_filter_upper__placement_transition
          sorted value index Hinc Hindex Hgt) as Hupper.
      lia. }
    assert (Hindex_nonneg : 0 <= Znth index sorted 0).
    { rewrite Forall_forall in Hnonneg.
      apply Hnonneg.
      unfold Znth. apply nth_In.
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      lia. }
    lia.
  - assert (Hvaluepos : 0 < value).
    { apply Z.leb_gt in Hvalue0. lia. }
    assert (Hstart : CountingCumulativeEnd input (value - 1) <= index).
    { unfold CountingBucketStart in Hbucket.
      rewrite Hvalue0 in Hbucket.
      exact (proj1 Hbucket). }
    assert (Hend_prev : CountingCumulativeEnd input (value - 1) =
        Zlength (filter (fun x => x <=? value - 1) sorted)).
    { rewrite counting_cumulative_end_perm__placement_transition with
        (values2 := sorted) by exact Hperm.
      apply counting_cumulative_end_as_filter__placement_transition;
        try assumption; lia. }
    assert (Hnotlt : ~ Znth index sorted 0 < value).
    { intro Hlt.
      pose proof
        (counting_increasing_filter_lower__placement_transition
          sorted (value - 1) index Hinc Hindex ltac:(lia)) as Hlower.
      lia. }
    assert (Hnotgt : ~ value < Znth index sorted 0).
    { intro Hgt.
      pose proof
        (counting_increasing_filter_upper__placement_transition
          sorted value index Hinc Hindex Hgt) as Hupper.
      lia. }
    lia.
Qed.
Lemma counting_frequency_prefix_drop_last__placement_transition :
  forall input processed value,
    0 <= processed < Zlength input ->
    CountingFrequency (sublist 0 (processed + 1) input) value =
      CountingFrequency (sublist 0 processed input) value +
      if Z.eq_dec (Znth processed input 0) value then 1 else 0.
Proof.
  intros input processed value Hprocessed.
  rewrite (sublist_split 0 (processed + 1) processed input) by lia.
  rewrite (sublist_single 0 processed input) by lia.
  unfold CountingFrequency.
  rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec (Znth processed input 0) value); lia.
Qed.
Lemma counting_cumulative_end_step__placement_transition :
  forall input value,
    0 <= value ->
    CountingCumulativeEnd input value =
      CountingBucketStart input value + CountingFrequency input value.
Proof.
  intros input value Hvalue.
  unfold CountingBucketStart.
  destruct (value <=? 0) eqn:Hvalue0.
  - apply Z.leb_le in Hvalue0.
    assert (Hvalue_eq : value = 0) by lia.
    subst value.
    unfold CountingCumulativeEnd.
    simpl. lia.
  - assert (Hvaluepos : 0 < value).
    { apply Z.leb_gt in Hvalue0. lia. }
    unfold CountingCumulativeEnd.
    replace (Z.to_nat (value + 1)) with (S (Z.to_nat value)) by lia.
    replace (Z.to_nat (value - 1 + 1)) with (Z.to_nat value) by lia.
    rewrite seq_S, map_app, fold_right_app.
    simpl.
    rewrite Z2Nat.id by lia.
    set (frequencies :=
      map (fun index : nat => CountingFrequency input (Z.of_nat index))
        (seq 0 (Z.to_nat value))).
    clearbody frequencies.
    induction frequencies as [| frequency frequencies IH]; simpl; lia.
Qed.
Lemma counting_cumulative_end_nonnegative__placement_transition :
  forall input value,
    0 <= CountingCumulativeEnd input value.
Proof.
  intros input value.
  unfold CountingCumulativeEnd, CountingFrequency.
  set (indices := seq 0 (Z.to_nat (value + 1))).
  clearbody indices.
  induction indices as [| index indices IH]; simpl; lia.
Qed.
Lemma counting_bucket_start_nonnegative__placement_transition :
  forall input value,
    0 <= CountingBucketStart input value.
Proof.
  intros input value.
  unfold CountingBucketStart.
  destruct (value <=? 0).
  - lia.
  - apply counting_cumulative_end_nonnegative__placement_transition.
Qed.
Lemma counting_frequency_prefix_le__placement_transition :
  forall input processed value,
    0 <= processed <= Zlength input ->
    CountingFrequency (sublist 0 processed input) value <=
      CountingFrequency input value.
Proof.
  intros input processed value Hprocessed.
  assert (Hdecomp :
    input = sublist 0 processed input ++
      sublist processed (Zlength input) input).
  { rewrite <- (sublist_split 0 (Zlength input) processed input) by lia.
    symmetry. apply sublist_self. reflexivity. }
  rewrite Hdecomp at 2.
  unfold CountingFrequency.
  rewrite count_occ_app.
  lia.
Qed.
Lemma counting_cumulative_end_bound__placement_transition :
  forall input sorted value,
    CountingSorted input sorted ->
    Forall (fun x => 0 <= x) sorted ->
    0 <= value ->
    CountingCumulativeEnd input value <= Zlength sorted.
Proof.
  intros input sorted value [Hperm Hinc] Hnonneg Hvalue.
  rewrite counting_cumulative_end_perm__placement_transition with
    (values2 := sorted) by exact Hperm.
  rewrite counting_cumulative_end_as_filter__placement_transition by
    assumption.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_le.
  pose proof (filter_length (fun x : Z => x <=? value) sorted).
  rewrite <- H.
  apply Nat.le_add_r.
Qed.
Lemma counting_placement_step__placement_transition :
  forall n input i output bucket_ends sorted positions output_default,
    0 <= n <= 100 ->
    Zlength input = n ->
    Zlength sorted = n ->
    Zlength positions = 100 ->
    Zlength output = 100 ->
    0 <= i < n ->
    (forall index,
      0 <= index < n ->
      0 <= Znth index input 0 < 100) ->
    (forall index,
      0 <= index < n ->
      0 <= Znth index sorted 0 < 100) ->
    (forall bucket,
      0 <= bucket < 100 ->
      0 <= Znth bucket positions 0 <= n) ->
    (forall index,
      n <= index < 100 ->
      Znth index output output_default = None) ->
    1 <= Znth (Znth i input 0) positions 0 ->
    CountingPlacementProgress
      input positions bucket_ends output sorted i ->
    let value := Znth i input 0 in
    let positions' :=
      replace_Znth value (Znth value positions 0 - 1) positions in
    let write_index := Znth value positions' 0 in
    let output' := replace_Znth write_index (Some value) output in
    (forall bucket,
      0 <= bucket < 100 ->
      0 <= Znth bucket positions' 0 <= n) /\
    (i - 1 >= 0 ->
      1 <= Znth (Znth (i - 1) input 0) positions' 0) /\
    (forall index,
      n <= index < 100 ->
      Znth index output' output_default = None) /\
    CountingPlacementProgress
      input positions' bucket_ends output' sorted (i - 1).
Proof.
  intros n input i output bucket_ends sorted positions output_default
    Hn Hinput_len Hsorted_len Hpositions_len Houtput_len Hi
    Hinput_bounds Hsorted_bounds Hpositions_bounds Houtput_suffix
    Hcurrent_positive Hprogress.
  cbn zeta.
  set (value := Znth i input 0).
  set (positions' :=
    replace_Znth value (Znth value positions 0 - 1) positions).
  set (write_index := Znth value positions' 0).
  set (output' := replace_Znth write_index (Some value) output).
  change (1 <= Znth value positions 0) in Hcurrent_positive.
  assert (Hvalue : 0 <= value < 100).
  { unfold value. apply Hinput_bounds. exact Hi. }
  assert (Hposition_value :
    0 <= Znth value positions 0 <= n).
  { apply Hpositions_bounds. exact Hvalue. }
  assert (Hwrite_eq : write_index = Znth value positions 0 - 1).
  { unfold write_index, positions'.
    rewrite Znth_replace_Znth_Same.
    - reflexivity.
    - rewrite Hpositions_len. exact Hvalue. }
  assert (Hwrite_output_bounds : 0 <= write_index < Zlength output).
  { rewrite Hwrite_eq, Houtput_len. lia. }
  destruct Hprogress as
    [Hcounting_sorted [Hbucket_ends [Hposition_equation Hfilled]]].
  assert (Hsorted_nonnegative : Forall (fun x => 0 <= x) sorted).
  { apply counting_forall_nonnegative_from_Znth__placement_transition.
    intros index Hindex.
    apply Hsorted_bounds.
    rewrite Hsorted_len in Hindex. exact Hindex. }
  assert (Hnew_position_equation : forall bucket,
    0 <= bucket < 100 ->
    Znth bucket positions' 0 =
      CountingBucketStart input bucket +
      CountingFrequency (sublist 0 i input) bucket).
  { intros bucket Hbucket.
    specialize (Hposition_equation bucket Hbucket).
    pose proof
      (counting_frequency_prefix_drop_last__placement_transition
        input i bucket ltac:(rewrite Hinput_len; exact Hi)) as Hfrequency.
    destruct (Z.eq_dec value bucket) as [Hsame | Hdiff].
    - subst bucket.
      unfold positions'.
      rewrite Znth_replace_Znth_Same by
        (rewrite Hpositions_len; exact Hvalue).
      unfold value in Hposition_equation |- *.
      unfold value in Hfrequency.
      destruct (Z.eq_dec (Znth i input 0) (Znth i input 0));
        try contradiction; lia.
    - unfold positions'.
      rewrite Znth_replace_Znth_Diff by
        (rewrite ?Hpositions_len; try lia; exact Hdiff).
      unfold value in Hfrequency.
      destruct (Z.eq_dec (Znth i input 0) bucket);
        try contradiction; lia. }
  assert (Hnew_positions_bounds : forall bucket,
    0 <= bucket < 100 ->
    0 <= Znth bucket positions' 0 <= n).
  { intros bucket Hbucket.
    destruct (Z.eq_dec value bucket) as [Hsame | Hdiff].
    - subst bucket.
      unfold positions'.
      rewrite Znth_replace_Znth_Same by
        (rewrite Hpositions_len; exact Hvalue).
      lia.
    - unfold positions'.
      rewrite Znth_replace_Znth_Diff by
        (rewrite ?Hpositions_len; try lia; exact Hdiff).
      apply Hpositions_bounds. exact Hbucket. }
  assert (Hwrite_sorted_bounds : 0 <= write_index < Zlength sorted).
  { rewrite Hwrite_eq, Hsorted_len. lia. }
  assert (Hwrite_bucket :
    CountingBucketStart input value <= write_index <
      CountingCumulativeEnd input value).
  { specialize (Hposition_equation value Hvalue).
    assert (Hprefix_le :
      CountingFrequency (sublist 0 (i + 1) input) value <=
        CountingFrequency input value).
    { apply counting_frequency_prefix_le__placement_transition.
      rewrite Hinput_len. lia. }
    pose proof
      (counting_cumulative_end_step__placement_transition
        input value (proj1 Hvalue)) as Hstep.
    specialize (Hnew_position_equation value Hvalue).
    assert (Hfrequency_nonnegative :
      0 <= CountingFrequency (sublist 0 i input) value).
    { unfold CountingFrequency. lia. }
    rewrite Hwrite_eq.
    lia. }
  assert (Hwrite_value : Znth write_index sorted 0 = value).
  { eapply counting_sorted_bucket_value__placement_transition.
    - exact Hcounting_sorted.
    - exact Hsorted_nonnegative.
    - exact (proj1 Hvalue).
    - exact Hwrite_sorted_bounds.
    - exact Hwrite_bucket. }
  assert (Hnew_filled : forall bucket index,
    0 <= bucket < 100 ->
    Znth bucket positions' 0 <= index < Znth bucket bucket_ends 0 ->
    Znth index output' None = Some (Znth index sorted 0)).
  { intros bucket index Hbucket Hindex.
    assert (Hend_bound :
      CountingCumulativeEnd input bucket <= Zlength sorted).
    { eapply counting_cumulative_end_bound__placement_transition; eauto.
      lia. }
    assert (Hindex_output_bounds : 0 <= index < Zlength output).
    { specialize (Hbucket_ends bucket Hbucket).
      specialize (Hnew_positions_bounds bucket Hbucket).
      rewrite Houtput_len, Hsorted_len in *.
      lia. }
    destruct (Z.eq_dec index write_index) as [Hsame_index | Hdiff_index].
    - subst index.
      unfold output'.
      rewrite Znth_replace_Znth_Same by exact Hwrite_output_bounds.
      rewrite Hwrite_value. reflexivity.
    - unfold output'.
      rewrite Znth_replace_Znth_Diff by
        (try exact Hwrite_output_bounds; try exact Hindex_output_bounds;
          lia).
      apply Hfilled with (value := bucket); try exact Hbucket.
      split; [| exact (proj2 Hindex)].
      destruct (Z.eq_dec value bucket) as [Hsame_bucket | Hdiff_bucket].
      + subst bucket.
        unfold positions' in Hindex.
        rewrite Znth_replace_Znth_Same in Hindex by
          (rewrite Hpositions_len; exact Hvalue).
        rewrite Hwrite_eq in Hdiff_index.
        lia.
      + unfold positions' in Hindex.
        rewrite Znth_replace_Znth_Diff in Hindex by
          (rewrite ?Hpositions_len; try lia; exact Hdiff_bucket).
        exact (proj1 Hindex). }
  assert (Hnew_progress : CountingPlacementProgress
    input positions' bucket_ends output' sorted (i - 1)).
  { unfold CountingPlacementProgress.
    split.
    - exact Hcounting_sorted.
    - split.
      + exact Hbucket_ends.
      + split.
        * intros bucket Hbucket.
          replace (i - 1 + 1) with i by lia.
          apply Hnew_position_equation. exact Hbucket.
        * exact Hnew_filled. }
  assert (Hnext_positive : i - 1 >= 0 ->
    1 <= Znth (Znth (i - 1) input 0) positions' 0).
  { intros Hnext.
    set (next_value := Znth (i - 1) input 0).
    assert (Hnext_value : 0 <= next_value < 100).
    { unfold next_value. apply Hinput_bounds. lia. }
    specialize (Hnew_position_equation next_value Hnext_value).
    pose proof
      (counting_frequency_prefix_drop_last__placement_transition
        input (i - 1) next_value ltac:(rewrite Hinput_len; lia)) as Hfrequency.
    replace (i - 1 + 1) with i in Hfrequency by lia.
    unfold next_value in Hfrequency.
    destruct (Z.eq_dec (Znth (i - 1) input 0)
      (Znth (i - 1) input 0)); try contradiction.
    pose proof
      (counting_bucket_start_nonnegative__placement_transition
        input (Znth (i - 1) input 0)).
    assert (Hprevious_frequency_nonnegative :
      0 <= CountingFrequency (sublist 0 (i - 1) input)
        (Znth (i - 1) input 0)).
    { unfold CountingFrequency. lia. }
    unfold next_value in Hnew_position_equation |- *.
    lia. }
  assert (Hnew_output_suffix : forall index,
    n <= index < 100 ->
    Znth index output' output_default = None).
  { intros index Hindex.
    assert (Hindex_output_bounds : 0 <= index < Zlength output).
    { rewrite Houtput_len. lia. }
    assert (Hwrite_before_n : write_index < n).
    { rewrite Hwrite_eq. lia. }
    unfold output'.
    rewrite Znth_replace_Znth_Diff by
      (try exact Hwrite_output_bounds; try exact Hindex_output_bounds; lia).
    apply Houtput_suffix. exact Hindex. }
  split.
  - exact Hnew_positions_bounds.
  - split.
    + exact Hnext_positive.
    + split.
      * exact Hnew_output_suffix.
      * exact Hnew_progress.
Qed.
Lemma counting_copy_initial__copyback :
  forall before target,
    CountingCopyProgress before target before 0.
Proof.
  intros before target.
  unfold CountingCopyProgress.
  simpl.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.
Lemma counting_copy_step__copyback :
  forall before target live i,
    0 <= i < Zlength before ->
    Zlength target = Zlength before ->
    CountingCopyProgress before target live i ->
    CountingCopyProgress before target
      (replace_Znth i (Znth i target 0) live) (i + 1).
Proof.
  intros before target live i Hi Htarget Hcopy.
  unfold CountingCopyProgress in *.
  rewrite Hcopy.
  assert (Hprefix : Zlength (sublist 0 i target) = i).
  {
    rewrite Zlength_sublist; lia.
  }
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (i - Zlength (sublist 0 i target)) with 0 by lia.
  rewrite (sublist_split i (Zlength before) (i + 1) before) by lia.
  rewrite (sublist_single 0) by lia.
  unfold replace_Znth.
  simpl.
  rewrite (sublist_split 0 (i + 1) i target) by lia.
  rewrite (sublist_single 0) by lia.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.
Lemma counting_copy_complete__copyback :
  forall before target live,
    Zlength target = Zlength before ->
    CountingCopyProgress before target live (Zlength before) ->
    live = target.
Proof.
  intros before target live Htarget Hcopy.
  unfold CountingCopyProgress in Hcopy.
  rewrite (sublist_self target (Zlength before)) in Hcopy by lia.
  assert (Hsuffix :
    sublist (Zlength before) (Zlength before) before = []).
  {
    unfold sublist.
    apply skipn_all2.
    rewrite length_firstn.
    lia.
  }
  rewrite Hsuffix, app_nil_r in Hcopy.
  exact Hcopy.
Qed.
