From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
From Coq Require Import Sorting.Permutation.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin.
Require Import SetsClass.SetsClass.
Import SetsNotation.

(** The decimal digit selected by one LSD pass.  [exponent] is kept as an
    explicit argument because the C annotation separately owns its positivity
    and machine range. *)
Definition RadixDigit (value exponent : Z) : Z :=
  (value / exponent) mod 10.

(** Maximum of the mathematical prefix [0,hi), using the shared extremum
    semantics. Valid prefix indices are the candidate set; access safety is
    supplied separately by the C contract. *)
Definition PrefixMaximum (values : list Z) (hi maximum : Z) : Prop :=
  max_value_of_subset Z.le (fun index : Z => 0 <= index < hi)
    (fun index => Znth index values 0) maximum.

(** Decimal powers, independent of the implementation's machine bounds. *)
Definition DecimalExponent (exponent : Z) : Prop :=
  exists power : Z, 0 <= power /\ exponent = 10 ^ power.

(** Ordering by all decimal positions already processed before [exponent]. *)
Definition RadixLowerDigitsOrdered
    (values : list Z) (exponent : Z) : Prop :=
  forall left right,
    0 <= left /\ left <= right /\ right < Zlength values ->
    (Znth left values 0) mod exponent <=
    (Znth right values 0) mod exponent.

(** Stable public-facing mathematical state at the head of an LSD pass. *)
Definition RadixPassState
    (input current : list Z) (exponent : Z) : Prop :=
  Permutation input current /\
  RadixLowerDigitsOrdered current exponent.

Definition RadixBucket
    (values : list Z) (exponent digit : Z) : list Z :=
  filter
    (fun value => Z.eqb (RadixDigit value exponent) digit)
    values.

Definition RadixDigitCount
    (values : list Z) (exponent hi digit : Z) : Z :=
  Zlength (RadixBucket (sublist 0 hi values) exponent digit).

(** Exact ten-way histogram for the processed source prefix. *)
Definition DigitHistogramPrefix
    (values : list Z) (exponent hi : Z) (counts : list Z) : Prop :=
  forall digit,
    0 <= digit < 10 ->
    Znth digit counts 0 = RadixDigitCount values exponent hi digit.

(** During the prefix-sum loop, buckets below [processed] are cumulative
    exclusive endpoints; the rest still contain raw histogram counts. *)
Definition DigitPrefixTotals
    (histogram totals : list Z) (processed : Z) : Prop :=
  forall digit,
    0 <= digit < 10 ->
    (digit < processed ->
       Znth digit totals 0 = sum (sublist 0 (digit + 1) histogram)) /\
    (processed <= digit ->
       Znth digit totals 0 = Znth digit histogram 0).

Definition RadixBucketStart (histogram : list Z) (digit : Z) : Z :=
  sum (sublist 0 digit histogram).

Definition RadixBucketEnd (histogram : list Z) (digit : Z) : Z :=
  sum (sublist 0 (digit + 1) histogram).

(** Canonical stable decimal-bucket result: concatenate, in digit order, the
    source subsequences selected by each digit.  This is a mathematical stable
    partition, not an interpreter for the C loops. *)
Definition RadixStableOutput
    (source : list Z) (exponent : Z) : list Z :=
  concat
    (map
       (fun digit => RadixBucket source exponent digit)
       [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]).

Definition StableDigitPass
    (source output : list Z) (exponent : Z) : Prop :=
  output = RadixStableOutput source exponent.

(** [remaining] is the unprocessed source-prefix length during the reverse
    stable-placement loop.  Counters delimit the still-empty bucket prefixes;
    the corresponding suffixes in [mixed_output] already reveal the canonical
    stable result as [Some], and every other local-output cell is [None]. *)
Definition BucketPlacementProgress
    (source : list Z) (exponent remaining : Z)
    (histogram counters : list Z)
    (mixed_output : list (option Z)) : Prop :=
  (forall digit,
      0 <= digit < 10 ->
      Znth digit counters 0 =
        RadixBucketStart histogram digit +
        RadixDigitCount source exponent remaining digit) /\
  (forall digit,
      0 <= digit < 10 ->
      RadixBucketStart histogram digit <= Znth digit counters 0 <=
      RadixBucketEnd histogram digit) /\
  (forall digit position,
      0 <= digit < 10 ->
      Znth digit counters 0 <= position <
        RadixBucketEnd histogram digit ->
      Znth position mixed_output None =
        Some (Znth position (RadixStableOutput source exponent) 0)) /\
  (forall position,
      0 <= position < Zlength mixed_output ->
      (forall digit,
          0 <= digit < 10 ->
          position < Znth digit counters 0 \/
          RadixBucketEnd histogram digit <= position) ->
      Znth position mixed_output None = None).

(** Sequential copy-back meaning: [working] agrees with the pass result on
    the copied prefix and with the pre-pass source on the remaining suffix. *)
Definition RadixCopyPrefix
    (source pass_output working : list Z) (copied : Z) : Prop :=
  (forall index,
      0 <= index < copied ->
      Znth index working 0 = Znth index pass_output 0) /\
  (forall index,
      copied <= index < Zlength source ->
      Znth index working 0 = Znth index source 0).

From Coq Require Import Lia.
Require Import Coq.ZArith.Zquot.

(** Group-local mathematical support for the reverse stable-placement loop. *)
Require Import Coq.Sorting.Sorted Coq.micromega.Lia Coq.micromega.Psatz.
From Coq Require Import Lia Zquot.
Lemma prefix_maximum_extend_greater__maximum_pass_entry :
  forall values hi maximum,
    0 <= hi ->
    PrefixMaximum values hi maximum ->
    maximum < Znth hi values 0 ->
    PrefixMaximum values (hi + 1) (Znth hi values 0).
Proof.
  intros values hi maximum Hhi Hmaximum Hgreater.
  unfold PrefixMaximum, max_value_of_subset, max_object_of_subset in *.
  sets_unfold in Hmaximum.
  sets_unfold.
  destruct Hmaximum as [attained [[Hattained Hupper] Heq]].
  exists hi; split; [split | reflexivity]; try lia.
  intros index Hindex.
  destruct (Z.lt_ge_cases index hi) as [Hlt | Hge].
  - specialize (Hupper index ltac:(lia)); lia.
  - assert (index = hi) by lia; subst; lia.
Qed.
Lemma prefix_maximum_extend_bounded__maximum_pass_entry :
  forall values hi maximum,
    PrefixMaximum values hi maximum ->
    Znth hi values 0 <= maximum ->
    PrefixMaximum values (hi + 1) maximum.
Proof.
  intros values hi maximum Hmaximum Hbounded.
  unfold PrefixMaximum, max_value_of_subset, max_object_of_subset in *.
  sets_unfold in Hmaximum.
  sets_unfold.
  destruct Hmaximum as [index [[Hindex Hupper] Heq]].
  exists index; split; [split | exact Heq]; try lia.
  intros k Hk.
  destruct (Z.lt_ge_cases k hi) as [Hlt | Hge].
  - apply Hupper; lia.
  - assert (k = hi) by lia; subst; lia.
Qed.
Lemma decimal_exponent_active_bound__maximum_pass_entry :
  forall exponent maximum,
    DecimalExponent exponent ->
    0 <= maximum ->
    maximum <= 999999999 ->
    Z.quot maximum exponent > 0 ->
    exponent <= 100000000.
Proof.
  intros exponent maximum Hexponent Hmaximum_nonnegative
    Hmaximum_bound Hactive.
  unfold DecimalExponent in Hexponent.
  destruct Hexponent as [power [Hpower_nonnegative ->]].
  assert (Hpower_bound : power <= 8).
  {
    destruct (Z_le_gt_dec power 8); auto.
    assert (1000000000 <= 10 ^ power).
    { change (10 ^ 9 <= 10 ^ power). apply Z.pow_le_mono_r; lia. }
    assert (Z.quot maximum (10 ^ power) < 1).
    { apply Z.quot_lt_upper_bound; lia. }
    lia.
  }
  change (10 ^ power <= 10 ^ 8).
  apply Z.pow_le_mono_r; lia.
Qed.
Lemma digit_histogram_prefix_zero__count_zero_init :
  forall values exponent counts,
    (forall digit, 0 <= digit < 10 -> Znth digit counts 0 = 0) ->
    DigitHistogramPrefix values exponent 0 counts.
Proof.
  intros values exponent counts Hzero digit Hdigit.
  rewrite Hzero by exact Hdigit.
  unfold RadixDigitCount, RadixBucket.
  simpl.
  reflexivity.
Qed.
Lemma digit_histogram_prefix_step__histogram_update :
  forall values exponent hi counts,
    0 <= hi < Zlength values ->
    Zlength counts = 10 ->
    0 <= RadixDigit (Znth hi values 0) exponent < 10 ->
    DigitHistogramPrefix values exponent hi counts ->
    DigitHistogramPrefix values exponent (hi + 1)
      (replace_Znth (RadixDigit (Znth hi values 0) exponent)
        (Znth (RadixDigit (Znth hi values 0) exponent) counts 0 + 1)
        counts).
Proof.
  intros values exponent hi counts Hhi Hcounts Hdigit Hhist.
  unfold DigitHistogramPrefix in *.
  intros digit Hrange.
  specialize (Hhist digit Hrange).
  unfold RadixDigitCount, RadixBucket in *.
  rewrite (sublist_split 0 (hi + 1) hi values) by lia.
  rewrite (sublist_single 0 hi values) by lia.
  rewrite filter_app, Zlength_app.
  destruct (Z.eq_dec digit (RadixDigit (Znth hi values 0) exponent))
    as [Heq | Hneq].
  - subst digit.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Hhist.
    simpl.
    rewrite Z.eqb_refl.
    simpl.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    assert (Z.eqb (RadixDigit (Znth hi values 0) exponent) digit = false)
      as Heqb by (apply Z.eqb_neq; lia).
    rewrite Hhist.
    simpl.
    rewrite Heqb.
    simpl.
    rewrite Zlength_nil.
    lia.
Qed.
Lemma digit_prefix_totals_init__prefix_totals :
  forall histogram,
    Zlength histogram = 10 ->
    DigitPrefixTotals histogram histogram 1.
Proof.
  intros histogram Hlength digit Hdigit.
  split; intros Hprocessed.
  - assert (digit = 0) by lia.
    subst digit.
    rewrite (sublist_single 0 0 histogram) by lia.
    unfold sum.
    simpl.
    lia.
  - reflexivity.
Qed.
Lemma digit_prefix_totals_step__prefix_totals :
  forall histogram totals digit,
    Zlength histogram = 10 ->
    Zlength totals = 10 ->
    1 <= digit < 10 ->
    DigitPrefixTotals histogram totals digit ->
    DigitPrefixTotals
      histogram
      (replace_Znth digit
        (Znth digit totals 0 + Znth (digit - 1) totals 0)
        totals)
      (digit + 1).
Proof.
  intros histogram totals digit Hhist_length Htotals_length
    Hdigit Hprefix index Hindex.
  split; intros Hprocessed.
  - destruct (Z_lt_ge_dec index digit) as [Hbefore | Hat].
    + rewrite Znth_replace_Znth_Diff by lia.
      apply (proj1 (Hprefix index Hindex)).
      lia.
    + assert (index = digit) by lia.
      subst index.
      rewrite Znth_replace_Znth_Same by lia.
      pose proof (Hprefix digit Hindex) as Hcurrent.
      pose proof (Hprefix (digit - 1) ltac:(lia)) as Hprevious.
      rewrite (proj2 Hcurrent ltac:(lia)).
      rewrite (proj1 Hprevious ltac:(lia)).
      rewrite (sublist_split 0 (digit + 1) digit histogram) by lia.
      rewrite (sublist_single 0 digit histogram) by lia.
      rewrite sum_app.
      replace (digit - 1 + 1) with digit by lia.
      assert (Hsingle : sum [Znth digit histogram 0] =
                        Znth digit histogram 0).
      { unfold sum. simpl. lia. }
      rewrite Hsingle.
      lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply (proj2 (Hprefix index Hindex)).
    lia.
Qed.
Lemma digit_histogram_prefix_mass_bound__prefix_totals :
  forall values exponent hi histogram digit,
    0 <= hi <= Zlength values ->
    Zlength histogram = 10 ->
    DigitHistogramPrefix values exponent hi histogram ->
    0 <= digit < 10 ->
    0 <= sum (sublist 0 (digit + 1) histogram) <= hi.
Proof.
  intros values exponent hi histogram digit Hhi Hhist_length
    Hhistogram Hdigit.
  rewrite Zlength_correct in Hhist_length.
  destruct histogram as [|c0 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c1 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c2 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c3 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c4 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c5 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c6 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c7 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c8 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|c9 histogram]; [simpl in Hhist_length; lia|].
  destruct histogram as [|extra histogram].
  2: { simpl in Hhist_length. lia. }
  unfold DigitHistogramPrefix in Hhistogram.
  pose proof (Hhistogram 0 ltac:(lia)) as H0.
  pose proof (Hhistogram 1 ltac:(lia)) as H1.
  pose proof (Hhistogram 2 ltac:(lia)) as H2.
  pose proof (Hhistogram 3 ltac:(lia)) as H3.
  pose proof (Hhistogram 4 ltac:(lia)) as H4.
  pose proof (Hhistogram 5 ltac:(lia)) as H5.
  pose proof (Hhistogram 6 ltac:(lia)) as H6.
  pose proof (Hhistogram 7 ltac:(lia)) as H7.
  pose proof (Hhistogram 8 ltac:(lia)) as H8.
  pose proof (Hhistogram 9 ltac:(lia)) as H9.
  unfold Znth in H0, H1, H2, H3, H4, H5, H6, H7, H8, H9.
  simpl in H0, H1, H2, H3, H4, H5, H6, H7, H8, H9.
  unfold RadixDigitCount in H0, H1, H2, H3, H4, H5, H6, H7, H8, H9.
  set (source_prefix := sublist 0 hi values) in *.
  assert (Hpartition :
    Zlength (RadixBucket source_prefix exponent 0) +
    Zlength (RadixBucket source_prefix exponent 1) +
    Zlength (RadixBucket source_prefix exponent 2) +
    Zlength (RadixBucket source_prefix exponent 3) +
    Zlength (RadixBucket source_prefix exponent 4) +
    Zlength (RadixBucket source_prefix exponent 5) +
    Zlength (RadixBucket source_prefix exponent 6) +
    Zlength (RadixBucket source_prefix exponent 7) +
    Zlength (RadixBucket source_prefix exponent 8) +
    Zlength (RadixBucket source_prefix exponent 9) =
    Zlength source_prefix).
  {
    clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 Hhistogram.
    unfold RadixBucket.
    induction source_prefix as [|value source_prefix IH].
    - simpl. lia.
    - simpl.
      assert (Hradix : 0 <= RadixDigit value exponent < 10).
      { unfold RadixDigit. apply Z.mod_pos_bound. lia. }
      remember (RadixDigit value exponent) as radix eqn:Hradix_eq in *.
      destruct (Z.eq_dec radix 0) as [-> | Hradix0]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 1) as [-> | Hradix1]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 2) as [-> | Hradix2]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 3) as [-> | Hradix3]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 4) as [-> | Hradix4]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 5) as [-> | Hradix5]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 6) as [-> | Hradix6]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 7) as [-> | Hradix7]; [simpl in *; rewrite !Zlength_cons; lia|].
      destruct (Z.eq_dec radix 8) as [-> | Hradix8]; [simpl in *; rewrite !Zlength_cons; lia|].
      assert (Hradix9 : radix = 9) by lia.
      rewrite Hradix9.
      simpl.
      rewrite !Zlength_cons.
      lia.
  }
  assert (Hsource_prefix_length : Zlength source_prefix = hi).
  {
    subst source_prefix.
    rewrite Zlength_sublist by lia.
    lia.
  }
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 0)) as Hnonneg0.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 1)) as Hnonneg1.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 2)) as Hnonneg2.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 3)) as Hnonneg3.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 4)) as Hnonneg4.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 5)) as Hnonneg5.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 6)) as Hnonneg6.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 7)) as Hnonneg7.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 8)) as Hnonneg8.
  pose proof (Zlength_nonneg (RadixBucket source_prefix exponent 9)) as Hnonneg9.
  subst c0. subst c1. subst c2. subst c3. subst c4.
  subst c5. subst c6. subst c7. subst c8. subst c9.
  destruct (Z.eq_dec digit 0) as [-> | Hdigit0]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 1) as [-> | Hdigit1]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 2) as [-> | Hdigit2]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 3) as [-> | Hdigit3]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 4) as [-> | Hdigit4]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 5) as [-> | Hdigit5]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 6) as [-> | Hdigit6]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 7) as [-> | Hdigit7]; [unfold sublist, sum; simpl; lia|].
  destruct (Z.eq_dec digit 8) as [-> | Hdigit8]; [unfold sublist, sum; simpl; lia|].
  assert (digit = 9) by lia.
  subst digit.
  unfold sublist, sum.
  simpl.
  lia.
Qed.
Lemma radix_digits_length__stable_placement :
  Zlength [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] = 10.
Proof. reflexivity. Qed.
Lemma radix_digit_c_bridge__stable_placement :
  forall value exponent,
    0 <= value ->
    0 < exponent ->
    RadixDigit value exponent = Z.rem (Z.quot value exponent) 10.
Proof.
  intros value exponent Hvalue Hexponent.
  unfold RadixDigit.
  rewrite Zquot_Zdiv_pos by lia.
  rewrite Zrem_Zmod_pos by
    (try apply Z_div_nonneg_nonneg; lia).
  reflexivity.
Qed.
Lemma c_radix_digit_range__stable_placement :
  forall value exponent,
    0 <= value ->
    0 < exponent ->
    0 <= Z.rem (Z.quot value exponent) 10 < 10.
Proof.
  intros value exponent Hvalue Hexponent.
  pose proof (Z_quot_pos value exponent ltac:(lia) ltac:(lia)) as Hquot.
  apply Zrem_lt_pos_pos; lia.
Qed.
Lemma radix_digits_Znth__stable_placement :
  forall index,
    0 <= index < 10 ->
    Znth index [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] 0 = index.
Proof.
  intros index Hindex.
  assert (index = 0 \/ index = 1 \/ index = 2 \/ index = 3 \/
          index = 4 \/ index = 5 \/ index = 6 \/ index = 7 \/
          index = 8 \/ index = 9) by lia.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  end; subst; reflexivity.
Qed.
Lemma Znth_map_valid__stable_placement :
  forall {A B : Type} (f : A -> B) (values : list A)
         (default_a : A) (default_b : B) index,
    0 <= index < Zlength values ->
    Znth index (map f values) default_b = f (Znth index values default_a).
Proof.
  intros A B f values default_a default_b index Hindex.
  unfold Znth.
  assert (nth (Z.to_nat index) (map f values) default_b =
          nth (Z.to_nat index) (map f values) (f default_a)) as Hdefault.
  {
    apply nth_indep.
    rewrite Zlength_correct in Hindex.
    rewrite length_map.
    lia.
  }
  rewrite Hdefault.
  apply map_nth.
Qed.
Lemma sublist_map__stable_placement :
  forall {A B : Type} (f : A -> B) lo hi (values : list A),
    sublist lo hi (map f values) = map f (sublist lo hi values).
Proof.
  intros A B f lo hi values.
  unfold sublist.
  rewrite firstn_map, skipn_map.
  reflexivity.
Qed.
Lemma Zlength_map__stable_placement :
  forall {A B : Type} (f : A -> B) (values : list A),
    Zlength (map f values) = Zlength values.
Proof.
  intros A B f values.
  repeat rewrite Zlength_correct.
  now rewrite length_map.
Qed.
Lemma Znth_app_left__stable_placement :
  forall {A : Type} (default : A) (left right : list A) index,
    0 <= index < Zlength left ->
    Znth index (left ++ right) default = Znth index left default.
Proof.
  intros A default left right index Hindex.
  unfold Znth.
  apply app_nth1.
  rewrite Zlength_correct in Hindex. lia.
Qed.
Lemma Znth_app_right__stable_placement :
  forall {A : Type} (default : A) (left right : list A) index,
    Zlength left <= index ->
    Znth index (left ++ right) default =
      Znth (index - Zlength left) right default.
Proof.
  intros A default left right index Hindex.
  unfold Znth.
  rewrite app_nth2.
  - f_equal. rewrite Zlength_correct. lia.
  - rewrite Zlength_correct in Hindex. lia.
Qed.
Lemma sum_sublist_ext__stable_placement :
  forall (left right : list Z) hi,
    0 <= hi <= Zlength left ->
    hi <= Zlength right ->
    (forall index, 0 <= index < hi ->
       Znth index left 0 = Znth index right 0) ->
    sum (sublist 0 hi left) = sum (sublist 0 hi right).
Proof.
  intros left right hi Hleft Hright Heq.
  assert (sublist 0 hi left = sublist 0 hi right) as Hlists.
  {
    apply (proj2 (list_eq_ext (sublist 0 hi left)
                              (sublist 0 hi right) 0)).
    split.
    - repeat rewrite Zlength_sublist0 by lia. reflexivity.
    - intros index Hindex.
      assert (0 <= index < hi) as Hindex_hi.
      {
        rewrite Zlength_sublist0 in Hindex by lia.
        exact Hindex.
      }
      repeat rewrite Znth_sublist0 by lia.
      apply Heq. exact Hindex_hi.
  }
  now rewrite Hlists.
Qed.
Lemma Zlength_radix_concat__stable_placement :
  forall source exponent digits,
    Zlength
      (concat (map (fun digit => RadixBucket source exponent digit) digits)) =
    sum (map (fun digit => Zlength (RadixBucket source exponent digit))
             digits).
Proof.
  intros source exponent digits.
  induction digits as [| digit digits IH].
  - reflexivity.
  - cbn.
    rewrite Zlength_app, IH. reflexivity.
Qed.
Lemma radix_output_as_concat__stable_placement :
  forall source exponent,
    RadixStableOutput source exponent =
    concat
      (map (fun digit => RadixBucket source exponent digit)
         [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]).
Proof. reflexivity. Qed.
Lemma histogram_start_as_prefix_length__stable_placement :
  forall source exponent histogram digit,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= digit <= 10 ->
    RadixBucketStart histogram digit =
    Zlength
      (concat
         (map (fun bucket => RadixBucket source exponent bucket)
            (sublist 0 digit [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]))).
Proof.
  intros source exponent histogram digit Hhist_len Hhist Hdigit.
  unfold RadixBucketStart.
  rewrite Zlength_radix_concat__stable_placement.
  rewrite <- sublist_map__stable_placement.
  apply sum_sublist_ext__stable_placement; try lia.
  - rewrite Zlength_map__stable_placement,
      radix_digits_length__stable_placement. lia.
  - intros index Hindex.
    rewrite Znth_map_valid__stable_placement
      with (default_a := 0%Z); try (rewrite radix_digits_length__stable_placement; lia).
    rewrite radix_digits_Znth__stable_placement by lia.
    specialize (Hhist index ltac:(lia)).
    unfold RadixDigitCount in Hhist.
    rewrite sublist_self in Hhist by reflexivity.
    exact Hhist.
Qed.
Lemma radix_output_split__stable_placement :
  forall source exponent digit,
    0 <= digit < 10 ->
    RadixStableOutput source exponent =
      concat
        (map (fun bucket => RadixBucket source exponent bucket)
          (sublist 0 digit [0; 1; 2; 3; 4; 5; 6; 7; 8; 9])) ++
      RadixBucket source exponent digit ++
      concat
        (map (fun bucket => RadixBucket source exponent bucket)
          (sublist (digit + 1) 10 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9])).
Proof.
  intros source exponent digit Hdigit.
  assert (digit = 0 \/ digit = 1 \/ digit = 2 \/ digit = 3 \/
          digit = 4 \/ digit = 5 \/ digit = 6 \/ digit = 7 \/
          digit = 8 \/ digit = 9) by lia.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  end; subst; unfold RadixStableOutput; simpl;
    repeat rewrite app_nil_r; repeat rewrite app_assoc; reflexivity.
Qed.
Lemma bucket_end_start_count__stable_placement :
  forall source exponent histogram digit,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= digit < 10 ->
    RadixBucketEnd histogram digit =
      RadixBucketStart histogram digit +
      Zlength (RadixBucket source exponent digit).
Proof.
  intros source exponent histogram digit Hhist_len Hhist Hdigit.
  unfold RadixBucketEnd, RadixBucketStart.
  rewrite (sublist_split 0 (digit + 1) digit histogram) by lia.
  rewrite (sublist_single 0%Z) by lia.
  rewrite sum_app.
  simpl.
  specialize (Hhist digit ltac:(lia)).
  unfold RadixDigitCount in Hhist.
  rewrite sublist_self in Hhist by reflexivity.
  lia.
Qed.
Lemma stable_output_bucket_Znth__stable_placement :
  forall source exponent histogram digit position,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= digit < 10 ->
    RadixBucketStart histogram digit <= position <
      RadixBucketEnd histogram digit ->
    Znth position (RadixStableOutput source exponent) 0 =
      Znth (position - RadixBucketStart histogram digit)
        (RadixBucket source exponent digit) 0.
Proof.
  intros source exponent histogram digit position Hhist_len Hhist Hdigit Hposition.
  pose proof (histogram_start_as_prefix_length__stable_placement
                source exponent histogram digit Hhist_len Hhist ltac:(lia)) as Hstart.
  pose proof (bucket_end_start_count__stable_placement
                source exponent histogram digit Hhist_len Hhist Hdigit) as Hend.
  rewrite (radix_output_split__stable_placement source exponent digit Hdigit).
  rewrite Znth_app_right__stable_placement by lia.
  rewrite Znth_app_left__stable_placement by lia.
  now rewrite <- Hstart.
Qed.
Lemma sum_nonnegative_Znth__stable_placement :
  forall values : list Z,
    (forall index, 0 <= index < Zlength values ->
       0 <= Znth index values 0) ->
    0 <= sum values.
Proof.
  intros values.
  induction values as [| value values IH]; intros Hnonneg.
  - reflexivity.
  - unfold sum; fold sum.
    assert (0 <= value) as Hvalue.
    {
      specialize (Hnonneg 0 ltac:(rewrite Zlength_cons; pose proof
        (Zlength_nonneg values); lia)).
      exact Hnonneg.
    }
    assert (0 <= sum values) as Htail.
    {
      apply IH. intros index Hindex.
      specialize (Hnonneg (index + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hnonneg by lia.
      replace (index + 1 - 1) with index in Hnonneg by lia.
      exact Hnonneg.
    }
    apply Z.add_nonneg_nonneg; assumption.
Qed.
Lemma histogram_sublist_sum_nonnegative__stable_placement :
  forall source exponent histogram lo hi,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= lo <= hi -> hi <= 10 ->
    0 <= sum (sublist lo hi histogram).
Proof.
  intros source exponent histogram lo hi Hhist_len Hhist Hlohi Hhi.
  apply sum_nonnegative_Znth__stable_placement.
  intros index Hindex.
  rewrite Zlength_sublist in Hindex by lia.
  rewrite Znth_sublist by lia.
  specialize (Hhist (index + lo) ltac:(lia)).
  rewrite Hhist.
  unfold RadixDigitCount.
  apply Zlength_nonneg.
Qed.
Lemma bucket_end_le_start__stable_placement :
  forall source exponent histogram left right,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= left < 10 ->
    0 <= right <= 10 ->
    left < right ->
    RadixBucketEnd histogram left <= RadixBucketStart histogram right.
Proof.
  intros source exponent histogram left right Hhist_len Hhist
         Hleft Hright Horder.
  unfold RadixBucketEnd, RadixBucketStart.
  rewrite (sublist_split 0 right (left + 1) histogram) by lia.
  rewrite sum_app.
  pose proof (histogram_sublist_sum_nonnegative__stable_placement
                source exponent histogram (left + 1) right
                Hhist_len Hhist ltac:(lia) ltac:(lia)).
  lia.
Qed.
Lemma bucket_ranges_overlap_digit_eq__stable_placement :
  forall source exponent histogram first second first_pos second_pos,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= first < 10 ->
    0 <= second < 10 ->
    RadixBucketStart histogram first <= first_pos <
      RadixBucketEnd histogram first ->
    RadixBucketStart histogram second <= second_pos <
      RadixBucketEnd histogram second ->
    first_pos = second_pos ->
    first = second.
Proof.
  intros source exponent histogram first second first_pos second_pos
         Hhist_len Hhist Hfirst Hsecond Hfirst_pos Hsecond_pos Heq.
  subst second_pos.
  destruct (Z.lt_trichotomy first second) as [Hlt | [Hequal | Hgt]].
  - pose proof (bucket_end_le_start__stable_placement
                  source exponent histogram first second Hhist_len Hhist
                  Hfirst ltac:(lia) Hlt).
    lia.
  - exact Hequal.
  - pose proof (bucket_end_le_start__stable_placement
                  source exponent histogram second first Hhist_len Hhist
                  Hsecond ltac:(lia) Hgt).
    lia.
Qed.
Lemma radix_digit_count_step__stable_placement :
  forall source exponent index digit,
    0 <= index < Zlength source ->
    RadixDigitCount source exponent (index + 1) digit =
      RadixDigitCount source exponent index digit +
      (if Z.eqb (RadixDigit (Znth index source 0) exponent) digit
       then 1 else 0).
Proof.
  intros source exponent index digit Hindex.
  unfold RadixDigitCount, RadixBucket.
  rewrite (sublist_split 0 (index + 1) index source) by lia.
  rewrite (sublist_single 0%Z) by lia.
  rewrite filter_app, Zlength_app.
  simpl.
  destruct (Z.eqb (RadixDigit (Znth index source 0) exponent) digit);
    simpl; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.
Lemma radix_digit_count_prefix_le_full__stable_placement :
  forall source exponent remaining digit,
    0 <= remaining <= Zlength source ->
    RadixDigitCount source exponent remaining digit <=
      RadixDigitCount source exponent (Zlength source) digit.
Proof.
  intros source exponent remaining digit Hremaining.
  assert (source = sublist 0 remaining source ++
                   sublist remaining (Zlength source) source) as Hsplit.
  {
    rewrite <- sublist_split with
      (lo := 0) (hi := Zlength source) (mid := remaining) by lia.
    symmetry. apply sublist_self. reflexivity.
  }
  assert (RadixBucket source exponent digit =
          RadixBucket (sublist 0 remaining source) exponent digit ++
          RadixBucket (sublist remaining (Zlength source) source)
            exponent digit) as Hbuckets.
  {
    unfold RadixBucket.
    rewrite Hsplit at 1.
    apply filter_app.
  }
  unfold RadixDigitCount.
  rewrite (sublist_self source (Zlength source) eq_refl).
  rewrite Hbuckets, Zlength_app.
  pose proof (Zlength_nonneg
    (RadixBucket (sublist remaining (Zlength source) source)
      exponent digit)).
  lia.
Qed.
Lemma radix_digit_count_prefix_mono__stable_placement :
  forall source exponent lo hi digit,
    0 <= lo <= hi ->
    hi <= Zlength source ->
    RadixDigitCount source exponent lo digit <=
      RadixDigitCount source exponent hi digit.
Proof.
  intros source exponent lo hi digit Hlohi Hhi.
  unfold RadixDigitCount, RadixBucket.
  rewrite (sublist_split 0 hi lo source) by lia.
  rewrite filter_app, Zlength_app.
  pose proof (Zlength_nonneg
    (filter (fun value : Z => Z.eqb (RadixDigit value exponent) digit)
       (sublist lo hi source))).
  lia.
Qed.
Lemma radix_digit_count_contains_index__stable_placement :
  forall source exponent remaining index,
    0 <= index < remaining ->
    remaining <= Zlength source ->
    1 <= RadixDigitCount source exponent remaining
      (RadixDigit (Znth index source 0) exponent).
Proof.
  intros source exponent remaining index Hindex Hremaining.
  pose proof (radix_digit_count_step__stable_placement
    source exponent index (RadixDigit (Znth index source 0) exponent)
    ltac:(lia)) as Hstep.
  rewrite Z.eqb_refl in Hstep.
  assert (0 <= RadixDigitCount source exponent index
    (RadixDigit (Znth index source 0) exponent)) as Hnonneg.
  {
    unfold RadixDigitCount. apply Zlength_nonneg.
  }
  pose proof (radix_digit_count_prefix_mono__stable_placement
    source exponent (index + 1) remaining
    (RadixDigit (Znth index source 0) exponent)
    ltac:(lia) Hremaining) as Hmono.
  lia.
Qed.
Lemma bucket_progress_counter_for_index__stable_placement :
  forall source exponent remaining histogram counters mixed_output index,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    BucketPlacementProgress source exponent remaining histogram counters
      mixed_output ->
    0 <= index < remaining ->
    remaining <= Zlength source ->
    0 <= RadixDigit (Znth index source 0) exponent < 10 ->
    1 <= Znth (RadixDigit (Znth index source 0) exponent) counters 0.
Proof.
  intros source exponent remaining histogram counters mixed_output index
         Hhist_len Hhist Hprogress Hindex Hremaining Hdigit.
  unfold BucketPlacementProgress in Hprogress.
  destruct Hprogress as [Hcounter _].
  rewrite Hcounter by exact Hdigit.
  pose proof (radix_digit_count_contains_index__stable_placement
    source exponent remaining index Hindex Hremaining) as Hpositive.
  pose proof (histogram_sublist_sum_nonnegative__stable_placement
    source exponent histogram 0
    (RadixDigit (Znth index source 0) exponent)
    Hhist_len Hhist ltac:(lia) ltac:(lia)) as Hstart.
  unfold RadixBucketStart.
  lia.
Qed.
Lemma radix_bucket_current_position__stable_placement :
  forall source exponent index digit,
    0 <= index < Zlength source ->
    digit = RadixDigit (Znth index source 0) exponent ->
    Znth (RadixDigitCount source exponent index digit)
      (RadixBucket source exponent digit) 0 = Znth index source 0 /\
    RadixDigitCount source exponent index digit <
      RadixDigitCount source exponent (Zlength source) digit.
Proof.
  intros source exponent index digit Hindex Hdigit.
  assert (source =
    sublist 0 index source ++ [Znth index source 0] ++
    sublist (index + 1) (Zlength source) source) as Hsplit.
  {
    rewrite <- (sublist_single 0%Z index source) by exact Hindex.
    rewrite <- sublist_split with
      (lo := index) (hi := Zlength source) (mid := index + 1) by lia.
    rewrite <- sublist_split with
      (lo := 0) (hi := Zlength source) (mid := index) by lia.
    symmetry. apply sublist_self. reflexivity.
  }
  assert (RadixBucket source exponent digit =
          RadixBucket (sublist 0 index source) exponent digit ++
          [Znth index source 0] ++
          RadixBucket (sublist (index + 1) (Zlength source) source)
            exponent digit) as Hbuckets.
  {
    unfold RadixBucket.
    rewrite Hsplit at 1.
    rewrite !filter_app.
    simpl.
    rewrite <- Hdigit, Z.eqb_refl.
    reflexivity.
  }
  assert (RadixDigitCount source exponent index digit =
          Zlength (RadixBucket (sublist 0 index source) exponent digit))
    as Hprefix by reflexivity.
  assert (RadixDigitCount source exponent (Zlength source) digit =
          Zlength (RadixBucket source exponent digit)) as Hfull.
  {
    unfold RadixDigitCount.
    rewrite (sublist_self source (Zlength source) eq_refl).
    reflexivity.
  }
  rewrite Hprefix, Hfull, Hbuckets.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  split.
  - rewrite Znth_app_right__stable_placement by lia.
    replace (Zlength (RadixBucket (sublist 0 index source) exponent digit) -
             Zlength (RadixBucket (sublist 0 index source) exponent digit))
      with 0 by lia.
    reflexivity.
  - pose proof (Zlength_nonneg
      (RadixBucket (sublist (index + 1) (Zlength source) source)
        exponent digit)).
    lia.
Qed.
Lemma radix_current_stable_position__stable_placement :
  forall source exponent histogram index,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    0 <= index < Zlength source ->
    0 <= RadixDigit (Znth index source 0) exponent < 10 ->
    Znth
      (RadixBucketStart histogram
         (RadixDigit (Znth index source 0) exponent) +
       RadixDigitCount source exponent index
         (RadixDigit (Znth index source 0) exponent))
      (RadixStableOutput source exponent) 0 =
      Znth index source 0.
Proof.
  intros source exponent histogram index Hhist_len Hhist Hindex Hdigit.
  pose proof (radix_bucket_current_position__stable_placement
                source exponent index
                (RadixDigit (Znth index source 0) exponent)
                Hindex eq_refl) as [Hposition Hcount_lt].
  pose proof (bucket_end_start_count__stable_placement
                source exponent histogram
                (RadixDigit (Znth index source 0) exponent)
                Hhist_len Hhist Hdigit) as Hend.
  assert (RadixDigitCount source exponent (Zlength source)
            (RadixDigit (Znth index source 0) exponent) =
          Zlength (RadixBucket source exponent
            (RadixDigit (Znth index source 0) exponent))) as Hfull_count.
  {
    unfold RadixDigitCount.
    rewrite (sublist_self source (Zlength source) eq_refl).
    reflexivity.
  }
  rewrite Hfull_count in Hcount_lt.
  assert (0 <= RadixDigitCount source exponent index
            (RadixDigit (Znth index source 0) exponent)) as Hcount_nonneg.
  {
    unfold RadixDigitCount.
    apply Zlength_nonneg.
  }
  pose proof (stable_output_bucket_Znth__stable_placement
    source exponent histogram
    (RadixDigit (Znth index source 0) exponent)
    (RadixBucketStart histogram
       (RadixDigit (Znth index source 0) exponent) +
     RadixDigitCount source exponent index
       (RadixDigit (Znth index source 0) exponent))
    Hhist_len Hhist Hdigit ltac:(rewrite Hend; lia)) as Hlayout.
  rewrite Hlayout.
  replace
    (RadixBucketStart histogram
       (RadixDigit (Znth index source 0) exponent) +
     RadixDigitCount source exponent index
       (RadixDigit (Znth index source 0) exponent) -
     RadixBucketStart histogram
       (RadixDigit (Znth index source 0) exponent))
    with (RadixDigitCount source exponent index
            (RadixDigit (Znth index source 0) exponent)) by lia.
  exact Hposition.
Qed.
Lemma bucket_placement_step__stable_placement :
  forall source exponent histogram counters mixed_output index,
    Zlength histogram = 10 ->
    Zlength counters = 10 ->
    Zlength mixed_output = 1000 ->
    0 <= index < Zlength source ->
    0 <= RadixDigit (Znth index source 0) exponent < 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    BucketPlacementProgress source exponent (index + 1)
      histogram counters mixed_output ->
    let digit := RadixDigit (Znth index source 0) exponent in
    let next_counters :=
      replace_Znth digit (Znth digit counters 0 - 1) counters in
    let write_index := Znth digit next_counters 0 in
    0 <= write_index < 1000 ->
    BucketPlacementProgress source exponent index histogram next_counters
      (replace_Znth write_index (Some (Znth index source 0)) mixed_output).
Proof.
  intros source exponent histogram counters mixed_output index
         Hhist_len Hcounters_len Hmixed_len Hindex Hdigit Hhist Hprogress.
  cbn.
  set (digit := RadixDigit (Znth index source 0) exponent).
  set (next_counters :=
    replace_Znth digit (Znth digit counters 0 - 1) counters).
  set (write_index := Znth digit next_counters 0).
  intros Hwrite_valid.
  unfold BucketPlacementProgress in Hprogress |- *.
  destruct Hprogress as
    [Hcounter [Hbounds [Hplaced Hnone]]].
  assert (0 <= digit < 10) as Hdigit_range by
    (unfold digit; exact Hdigit).
  assert (Znth digit next_counters 0 = Znth digit counters 0 - 1)
    as Hnext_digit.
  {
    unfold next_counters.
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (write_index = Znth digit counters 0 - 1) as Hwrite_old.
  {
    unfold write_index. exact Hnext_digit.
  }
  assert (forall bucket,
    0 <= bucket < 10 ->
    Znth bucket next_counters 0 =
      RadixBucketStart histogram bucket +
      RadixDigitCount source exponent index bucket) as Hcounter_next.
  {
    intros bucket Hbucket.
    destruct (Z.eq_dec bucket digit) as [Heq | Hneq].
    - subst bucket.
      rewrite Hnext_digit, Hcounter by exact Hdigit_range.
      pose proof (radix_digit_count_step__stable_placement
                    source exponent index digit Hindex) as Hstep.
      assert (RadixDigit (Znth index source 0) exponent = digit)
        as Hdigit_eq by reflexivity.
      rewrite Hdigit_eq, Z.eqb_refl in Hstep.
      rewrite Hstep.
      lia.
    - unfold next_counters.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hcounter by exact Hbucket.
      pose proof (radix_digit_count_step__stable_placement
                    source exponent index bucket Hindex) as Hstep.
      assert (Z.eqb (RadixDigit (Znth index source 0) exponent) bucket = false)
        as Hdifferent.
      {
        apply Z.eqb_neq. unfold digit in Hneq. congruence.
      }
      rewrite Hdifferent in Hstep.
      lia.
  }
  assert (forall bucket,
    0 <= bucket < 10 ->
    RadixBucketStart histogram bucket <=
      Znth bucket next_counters 0 <=
    RadixBucketEnd histogram bucket) as Hbounds_next.
  {
    intros bucket Hbucket.
    rewrite Hcounter_next by exact Hbucket.
    assert (0 <= RadixDigitCount source exponent index bucket)
      as Hcount_nonneg.
    {
      unfold RadixDigitCount. apply Zlength_nonneg.
    }
    pose proof (radix_digit_count_prefix_le_full__stable_placement
                  source exponent index bucket ltac:(lia)) as Hcount_le.
    pose proof (bucket_end_start_count__stable_placement
                  source exponent histogram bucket
                  Hhist_len Hhist Hbucket) as Hend.
    assert (RadixDigitCount source exponent (Zlength source) bucket =
            Zlength (RadixBucket source exponent bucket)) as Hfull_count.
    {
      unfold RadixDigitCount.
      rewrite (sublist_self source (Zlength source) eq_refl).
      reflexivity.
    }
    rewrite Hfull_count in Hcount_le.
    lia.
  }
  pose proof (radix_bucket_current_position__stable_placement
    source exponent index digit Hindex eq_refl) as [_ Hcurrent_count_lt].
  assert (RadixDigitCount source exponent (Zlength source) digit =
          Zlength (RadixBucket source exponent digit)) as Hfull_digit.
  {
    unfold RadixDigitCount.
    rewrite (sublist_self source (Zlength source) eq_refl).
    reflexivity.
  }
  rewrite Hfull_digit in Hcurrent_count_lt.
  pose proof (bucket_end_start_count__stable_placement
                source exponent histogram digit
                Hhist_len Hhist Hdigit_range) as Hend_digit.
  assert (RadixBucketStart histogram digit <= write_index <
          RadixBucketEnd histogram digit) as Hwrite_range.
  {
    rewrite Hwrite_old, Hcounter by exact Hdigit_range.
    pose proof (radix_digit_count_step__stable_placement
                  source exponent index digit Hindex) as Hstep.
    assert (RadixDigit (Znth index source 0) exponent = digit)
      as Hdigit_eq by reflexivity.
    rewrite Hdigit_eq, Z.eqb_refl in Hstep.
    assert (0 <= RadixDigitCount source exponent index digit)
      by (unfold RadixDigitCount; apply Zlength_nonneg).
    lia.
  }
  assert (Znth write_index (RadixStableOutput source exponent) 0 =
          Znth index source 0) as Hstable_write.
  {
    pose proof (radix_current_stable_position__stable_placement
      source exponent histogram index Hhist_len Hhist Hindex Hdigit)
      as Hstable.
    assert (write_index =
      RadixBucketStart histogram digit +
      RadixDigitCount source exponent index digit) as Hwrite_counter.
    {
      unfold write_index.
      apply Hcounter_next. exact Hdigit_range.
    }
    rewrite Hwrite_counter.
    unfold digit.
    exact Hstable.
  }
  split.
    + exact Hcounter_next.
    + split.
      * exact Hbounds_next.
      * split.
        { intros bucket position Hbucket Hposition.
    destruct (Z.eq_dec bucket digit) as [Heq_bucket | Hneq_bucket].
    + subst bucket.
      rewrite Hnext_digit in Hposition.
      destruct (Z.eq_dec position write_index) as [Heq_position | Hneq_position].
      * subst position.
        rewrite Znth_replace_Znth_Same by lia.
        now rewrite Hstable_write.
      * assert (Znth digit counters 0 <= position <
                RadixBucketEnd histogram digit) as Hold_range by lia.
        pose proof (Hplaced digit position Hdigit_range Hold_range) as Hold.
        assert (0 <= position < Zlength mixed_output) as Hposition_valid.
        {
          split.
          - pose proof (histogram_sublist_sum_nonnegative__stable_placement
              source exponent histogram 0 digit Hhist_len Hhist
              ltac:(lia) ltac:(lia)).
            unfold RadixBucketStart in Hposition. lia.
          - destruct (Z_lt_ge_dec position (Zlength mixed_output))
              as [Hlt | Hge]; auto.
            unfold Znth in Hold.
            rewrite nth_overflow in Hold.
            + discriminate.
            + rewrite Zlength_correct in Hge. lia.
        }
        rewrite Znth_replace_Znth_Diff by lia.
        exact Hold.
    + assert (Znth bucket next_counters 0 = Znth bucket counters 0)
        as Hunchanged.
      {
        unfold next_counters.
        rewrite Znth_replace_Znth_Diff by lia.
        reflexivity.
      }
      rewrite Hunchanged in Hposition.
      pose proof (Hplaced bucket position Hbucket Hposition) as Hold.
      pose proof (Hbounds bucket Hbucket) as Hbucket_bounds.
      assert (RadixBucketStart histogram bucket <= position <
              RadixBucketEnd histogram bucket) as Hbucket_position by lia.
      assert (position <> write_index) as Hnot_write.
      {
        intro Heq_position.
        apply Hneq_bucket.
        eapply bucket_ranges_overlap_digit_eq__stable_placement
          with (source := source) (exponent := exponent)
               (histogram := histogram)
               (first_pos := position) (second_pos := write_index).
        - exact Hhist_len.
        - exact Hhist.
        - exact Hbucket.
        - exact Hdigit_range.
        - exact Hbucket_position.
        - exact Hwrite_range.
        - exact Heq_position.
      }
      assert (0 <= position < Zlength mixed_output) as Hposition_valid.
      {
        split.
        - pose proof (histogram_sublist_sum_nonnegative__stable_placement
            source exponent histogram 0 bucket Hhist_len Hhist
            ltac:(lia) ltac:(lia)).
          unfold RadixBucketStart in Hbucket_position. lia.
        - destruct (Z_lt_ge_dec position (Zlength mixed_output))
            as [Hlt | Hge]; auto.
          unfold Znth in Hold.
          rewrite nth_overflow in Hold.
          + discriminate.
          + rewrite Zlength_correct in Hge. lia.
      }
      rewrite Znth_replace_Znth_Diff by lia.
      exact Hold.
        }
        { intros position Hposition Hall_buckets.
    rewrite Zlength_replace_Znth in Hposition.
    assert (position <> write_index) as Hnot_write.
    {
      intro Heq_position. subst position.
      specialize (Hall_buckets digit Hdigit_range).
      lia.
    }
    assert (forall bucket,
      0 <= bucket < 10 ->
      position < Znth bucket counters 0 \/
      RadixBucketEnd histogram bucket <= position) as Hall_old.
    {
      intros bucket Hbucket.
      specialize (Hall_buckets bucket Hbucket).
      destruct (Z.eq_dec bucket digit) as [Heq | Hneq].
      - subst bucket. rewrite Hnext_digit in Hall_buckets. lia.
      - unfold next_counters in Hall_buckets.
        rewrite Znth_replace_Znth_Diff in Hall_buckets by lia.
        exact Hall_buckets.
    }
    pose proof (Hnone position Hposition Hall_old) as Hold.
    rewrite Znth_replace_Znth_Diff.
    - exact Hold.
    - rewrite Hmixed_len. exact Hwrite_valid.
    - exact Hposition.
    - congruence.
        }
Qed.
Lemma bucket_placement_initial__stable_placement :
  forall source exponent histogram endpoints,
    Zlength histogram = 10 ->
    Zlength endpoints = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    DigitPrefixTotals histogram endpoints 10 ->
    BucketPlacementProgress source exponent (Zlength source)
      histogram endpoints (repeat None (Z.to_nat 1000)).
Proof.
  intros source exponent histogram endpoints Hhist_len Hendpoints_len
         Hhist Htotals.
  unfold BucketPlacementProgress.
  split.
    + intros digit Hdigit.
      specialize (Htotals digit Hdigit).
      destruct Htotals as [Hend _].
      specialize (Hend ltac:(lia)).
      pose proof (bucket_end_start_count__stable_placement
                    source exponent histogram digit
                    Hhist_len Hhist Hdigit) as Hbucket_end.
      assert (RadixDigitCount source exponent (Zlength source) digit =
              Zlength (RadixBucket source exponent digit)) as Hfull_count.
      {
        unfold RadixDigitCount.
        rewrite (sublist_self source (Zlength source) eq_refl).
        reflexivity.
      }
      unfold RadixBucketEnd in Hbucket_end.
      lia.
    + split.
      * intros digit Hdigit.
        specialize (Htotals digit Hdigit).
        destruct Htotals as [Hend _].
        specialize (Hend ltac:(lia)).
        pose proof (bucket_end_start_count__stable_placement
                      source exponent histogram digit
                      Hhist_len Hhist Hdigit) as Hbucket_end.
        pose proof (Zlength_nonneg (RadixBucket source exponent digit)).
        unfold RadixBucketEnd in Hbucket_end |- *.
        lia.
      * split.
        { intros digit position Hdigit Hposition.
          specialize (Htotals digit Hdigit).
          destruct Htotals as [Hend _].
          specialize (Hend ltac:(lia)).
          unfold RadixBucketEnd in Hposition.
          lia.
        }
        { intros position Hposition Hall.
          apply Znth_repeat.
        }
Qed.
Lemma radix_output_cons_insertion__stable_placement :
  forall value source exponent digit,
    digit = RadixDigit value exponent ->
    0 <= digit < 10 ->
    exists before after,
      RadixStableOutput source exponent = before ++ after /\
      RadixStableOutput (value :: source) exponent =
        before ++ value :: after.
Proof.
  intros value source exponent digit Hdigit Hrange.
  exists
    (concat
      (map (fun bucket => RadixBucket source exponent bucket)
        (sublist 0 digit [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]))).
  exists
    (RadixBucket source exponent digit ++
     concat
      (map (fun bucket => RadixBucket source exponent bucket)
        (sublist (digit + 1) 10 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]))).
  split.
  - rewrite (radix_output_split__stable_placement
      source exponent digit Hrange).
    reflexivity.
  - rewrite (radix_output_split__stable_placement
      (value :: source) exponent digit Hrange).
    assert (digit = 0 \/ digit = 1 \/ digit = 2 \/ digit = 3 \/
            digit = 4 \/ digit = 5 \/ digit = 6 \/ digit = 7 \/
            digit = 8 \/ digit = 9) by lia.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    end; rewrite H in *; clear H;
      unfold RadixBucket; simpl; rewrite <- Hdigit;
      repeat rewrite Z.eqb_refl;
      repeat rewrite Z.eqb_neq by lia;
      simpl; repeat rewrite app_nil_r; repeat rewrite app_assoc;
      reflexivity.
Qed.
Lemma radix_stable_output_permutation__stable_placement :
  forall source exponent,
    (forall index,
      0 <= index < Zlength source ->
      0 <= RadixDigit (Znth index source 0) exponent < 10) ->
    Permutation source (RadixStableOutput source exponent).
Proof.
  intros source exponent Hdigits.
  induction source as [| value source IH].
  - reflexivity.
  - assert (0 <= RadixDigit value exponent < 10) as Hhead_digit.
    {
      specialize (Hdigits 0 ltac:(rewrite Zlength_cons;
        pose proof (Zlength_nonneg source); lia)).
      exact Hdigits.
    }
    assert (forall index,
      0 <= index < Zlength source ->
      0 <= RadixDigit (Znth index source 0) exponent < 10) as Htail_digits.
    {
      intros index Hindex.
      specialize (Hdigits (index + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hdigits by lia.
      replace (index + 1 - 1) with index in Hdigits by lia.
      exact Hdigits.
    }
    specialize (IH Htail_digits).
    destruct (radix_output_cons_insertion__stable_placement
      value source exponent (RadixDigit value exponent)
      eq_refl Hhead_digit) as [before [after [Hold Hnew]]].
    rewrite Hold in IH.
    rewrite Hnew.
    eapply Permutation_trans.
    + apply perm_skip. exact IH.
    + apply Permutation_middle.
Qed.
Lemma radix_stable_output_properties__stable_placement :
  forall source exponent lower upper,
    (forall index,
      0 <= index < Zlength source ->
      lower <= Znth index source 0 <= upper /\
      0 <= RadixDigit (Znth index source 0) exponent < 10) ->
    Zlength (RadixStableOutput source exponent) = Zlength source /\
    Permutation source (RadixStableOutput source exponent) /\
    (forall index,
      0 <= index < Zlength source ->
      lower <= Znth index (RadixStableOutput source exponent) 0 <= upper).
Proof.
  intros source exponent lower upper Hvalues.
  assert (forall index,
    0 <= index < Zlength source ->
    0 <= RadixDigit (Znth index source 0) exponent < 10) as Hdigits.
  {
    intros index Hindex. specialize (Hvalues index Hindex). tauto.
  }
  pose proof (radix_stable_output_permutation__stable_placement
    source exponent Hdigits) as Hperm.
  pose proof (Permutation_length Hperm) as Hlength.
  split.
  - repeat rewrite Zlength_correct. lia.
  - split.
    + exact Hperm.
    + intros index Hindex.
      assert (In (Znth index (RadixStableOutput source exponent) 0)
                 (RadixStableOutput source exponent)) as Hin_output.
      {
        unfold Znth.
        apply nth_In.
        rewrite <- Hlength.
        rewrite Zlength_correct in Hindex.
        lia.
      }
      apply Permutation_sym in Hperm.
      apply (Permutation_in
        (Znth index (RadixStableOutput source exponent) 0) Hperm)
        in Hin_output.
      apply In_nth with (d := 0%Z) in Hin_output.
      destruct Hin_output as [n [Hn Hnth]].
      specialize (Hvalues (Z.of_nat n) ltac:(rewrite Zlength_correct; lia)).
      unfold Znth in Hvalues.
      rewrite Nat2Z.id in Hvalues.
      rewrite Hnth in Hvalues.
      tauto.
Qed.
Lemma radix_position_bucket__stable_placement :
  forall source exponent histogram position,
    Zlength histogram = 10 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    (forall index,
      0 <= index < Zlength source ->
      0 <= RadixDigit (Znth index source 0) exponent < 10) ->
    0 <= position < Zlength source ->
    exists digit,
      0 <= digit < 10 /\
      RadixBucketStart histogram digit <= position <
      RadixBucketEnd histogram digit.
Proof.
  intros source exponent histogram position Hhist_len Hhist Hdigits Hposition.
  pose proof (radix_stable_output_permutation__stable_placement
                source exponent Hdigits) as Hperm.
  pose proof (Permutation_length Hperm) as Houtput_len.
  assert (RadixBucketEnd histogram 9 = Zlength source) as Hlast.
  {
    change (RadixBucketStart histogram 10 = Zlength source).
    pose proof (histogram_start_as_prefix_length__stable_placement
      source exponent histogram 10 Hhist_len Hhist ltac:(lia)) as Hstart10.
    rewrite (sublist_self [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] 10
      radix_digits_length__stable_placement) in Hstart10.
    rewrite <- radix_output_as_concat__stable_placement in Hstart10.
    assert (Zlength (RadixStableOutput source exponent) = Zlength source)
      as Houtput_Zlength.
    {
      repeat rewrite Zlength_correct.
      lia.
    }
    rewrite Houtput_Zlength in Hstart10.
    exact Hstart10.
  }
  assert (RadixBucketStart histogram 0 = 0) as Hstart0 by reflexivity.
  assert (RadixBucketStart histogram 1 = RadixBucketEnd histogram 0)
    as Hnext01 by reflexivity.
  assert (RadixBucketStart histogram 2 = RadixBucketEnd histogram 1)
    as Hnext12 by reflexivity.
  assert (RadixBucketStart histogram 3 = RadixBucketEnd histogram 2)
    as Hnext23 by reflexivity.
  assert (RadixBucketStart histogram 4 = RadixBucketEnd histogram 3)
    as Hnext34 by reflexivity.
  assert (RadixBucketStart histogram 5 = RadixBucketEnd histogram 4)
    as Hnext45 by reflexivity.
  assert (RadixBucketStart histogram 6 = RadixBucketEnd histogram 5)
    as Hnext56 by reflexivity.
  assert (RadixBucketStart histogram 7 = RadixBucketEnd histogram 6)
    as Hnext67 by reflexivity.
  assert (RadixBucketStart histogram 8 = RadixBucketEnd histogram 7)
    as Hnext78 by reflexivity.
  assert (RadixBucketStart histogram 9 = RadixBucketEnd histogram 8)
    as Hnext89 by reflexivity.
  destruct (Z_lt_dec position (RadixBucketEnd histogram 0)) as [H0 | H0].
  - exists 0. split; lia.
  - destruct (Z_lt_dec position (RadixBucketEnd histogram 1)) as [H1 | H1].
    + exists 1. split; lia.
    + destruct (Z_lt_dec position (RadixBucketEnd histogram 2)) as [H2 | H2].
      * exists 2. split; lia.
      * destruct (Z_lt_dec position (RadixBucketEnd histogram 3)) as [H3 | H3].
        -- exists 3. split; lia.
        -- destruct (Z_lt_dec position (RadixBucketEnd histogram 4)) as [H4 | H4].
          ++ exists 4. split; lia.
          ++ destruct (Z_lt_dec position (RadixBucketEnd histogram 5)) as [H5 | H5].
            ** exists 5. split; lia.
            ** destruct (Z_lt_dec position (RadixBucketEnd histogram 6)) as [H6 | H6].
              --- exists 6. split; lia.
              --- destruct (Z_lt_dec position (RadixBucketEnd histogram 7)) as [H7 | H7].
                +++ exists 7. split; lia.
                +++ destruct (Z_lt_dec position (RadixBucketEnd histogram 8)) as [H8 | H8].
                  *** exists 8. split; lia.
                  *** exists 9. split; lia.
Qed.
Lemma bucket_placement_complete__stable_placement :
  forall source exponent histogram counters mixed_output,
    Zlength histogram = 10 ->
    Zlength source <= 1000 ->
    Zlength mixed_output = 1000 ->
    DigitHistogramPrefix source exponent (Zlength source) histogram ->
    (forall index,
      0 <= index < Zlength source ->
      0 <= RadixDigit (Znth index source 0) exponent < 10) ->
    BucketPlacementProgress source exponent 0 histogram counters mixed_output ->
    (forall digit,
      0 <= digit < 10 ->
      Znth digit counters 0 = RadixBucketStart histogram digit) /\
    sublist 0 (Zlength source) mixed_output =
      map (@Some Z) (RadixStableOutput source exponent).
Proof.
  intros source exponent histogram counters mixed_output
         Hhist_len Hsource_bound Hmixed_len Hhist Hdigits Hprogress.
  pose proof (Zlength_nonneg source) as Hsource_nonneg.
  unfold BucketPlacementProgress in Hprogress.
  destruct Hprogress as
    [Hcounter [Hbounds [Hplaced Hnone]]].
  assert (forall digit,
    0 <= digit < 10 ->
    Znth digit counters 0 = RadixBucketStart histogram digit)
    as Hstarts.
  {
    intros digit Hdigit.
    rewrite Hcounter by exact Hdigit.
    unfold RadixDigitCount, RadixBucket, sublist.
    simpl. rewrite Zlength_nil. lia.
  }
  split.
  - exact Hstarts.
  - apply (proj2 (list_eq_ext
      (sublist 0 (Zlength source) mixed_output)
      (map (@Some Z) (RadixStableOutput source exponent)) None)).
    split.
    + rewrite Zlength_sublist0 by lia.
      rewrite Zlength_map__stable_placement.
      pose proof (radix_stable_output_permutation__stable_placement
        source exponent Hdigits) as Hperm.
      pose proof (Permutation_length Hperm) as Hlen.
      repeat rewrite Zlength_correct. lia.
    + intros position Hposition.
      rewrite Zlength_sublist0 in Hposition by lia.
      rewrite Znth_sublist0 by exact Hposition.
      rewrite Znth_map_valid__stable_placement
        with (default_a := 0%Z);
        try (pose proof (radix_stable_output_permutation__stable_placement
          source exponent Hdigits) as Hperm;
          pose proof (Permutation_length Hperm) as Hlen;
          repeat rewrite Zlength_correct in *; lia).
      destruct (radix_position_bucket__stable_placement
        source exponent histogram position Hhist_len Hhist Hdigits Hposition)
        as [digit [Hdigit Hrange]].
      assert (Znth digit counters 0 <= position <
              RadixBucketEnd histogram digit) as Hold_range.
      {
        rewrite Hstarts by exact Hdigit. exact Hrange.
      }
      pose proof (Hplaced digit position Hdigit Hold_range) as Hvalue.
      exact Hvalue.
Qed.
Lemma radix_copy_prefix_zero__copy_back :
  forall source pass_output,
    RadixCopyPrefix source pass_output source 0.
Proof.
  intros source pass_output.
  unfold RadixCopyPrefix.
  split.
  - intros index Hindex. lia.
  - intros index Hindex. reflexivity.
Qed.
Lemma radix_copy_prefix_step__copy_back :
  forall source pass_output working i,
    0 <= i < Zlength source ->
    Zlength working = Zlength source ->
    RadixCopyPrefix source pass_output working i ->
    RadixCopyPrefix source pass_output
      (replace_Znth i (Znth i pass_output 0) working) (i + 1).
Proof.
  intros source pass_output working i Hi Hlength [Hprefix Hsuffix].
  unfold RadixCopyPrefix.
  split.
  - intros index Hindex.
    destruct (Z.eq_dec index i) as [Heq | Hneq].
    + subst index.
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hprefix. lia.
  - intros index Hindex.
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hsuffix. lia.
Qed.
Lemma count_occ_radix_bucket__pass_transition :
  forall source exponent digit value,
    count_occ Z.eq_dec (RadixBucket source exponent digit) value =
    if Z.eqb (RadixDigit value exponent) digit
    then count_occ Z.eq_dec source value
    else 0%nat.
Proof.
  intros source exponent digit value.
  unfold RadixBucket.
  induction source as [| head tail IH].
  - simpl. destruct (Z.eqb (RadixDigit value exponent) digit); reflexivity.
  - simpl.
    destruct (Z.eq_dec head value) as [-> | Hneq].
    + destruct (Z.eqb (RadixDigit value exponent) digit) eqn:Hdigit;
        simpl; destruct (Z.eq_dec value value); try contradiction;
        rewrite IH; reflexivity.
    + destruct (Z.eqb (RadixDigit head exponent) digit) eqn:Hhead;
        simpl; destruct (Z.eq_dec head value); try contradiction;
        rewrite IH; reflexivity.
Qed.
Lemma stable_digit_pass_permutation__pass_transition :
  forall source output exponent,
    StableDigitPass source output exponent ->
    Permutation source output.
Proof.
  intros source output exponent Hpass.
  unfold StableDigitPass in Hpass. subst output.
  apply
    (proj2
       (Permutation_count_occ
          Z.eq_dec source (RadixStableOutput source exponent))).
  intro value.
  change
    (count_occ Z.eq_dec source value =
    count_occ Z.eq_dec
      (RadixBucket source exponent 0 ++
       RadixBucket source exponent 1 ++
       RadixBucket source exponent 2 ++
       RadixBucket source exponent 3 ++
       RadixBucket source exponent 4 ++
       RadixBucket source exponent 5 ++
       RadixBucket source exponent 6 ++
       RadixBucket source exponent 7 ++
       RadixBucket source exponent 8 ++
       RadixBucket source exponent 9 ++ []) value).
  rewrite !count_occ_app, !count_occ_radix_bucket__pass_transition.
  simpl count_occ.
  pose proof (Z.mod_pos_bound (value / exponent) 10 ltac:(lia)) as Hdigit.
  unfold RadixDigit in *.
  assert
    ((value / exponent) mod 10 = 0 \/
     (value / exponent) mod 10 = 1 \/
     (value / exponent) mod 10 = 2 \/
     (value / exponent) mod 10 = 3 \/
     (value / exponent) mod 10 = 4 \/
     (value / exponent) mod 10 = 5 \/
     (value / exponent) mod 10 = 6 \/
     (value / exponent) mod 10 = 7 \/
     (value / exponent) mod 10 = 8 \/
     (value / exponent) mod 10 = 9) as Hcases by lia.
  destruct Hcases as
      [Hdigit_value | [Hdigit_value | [Hdigit_value | [Hdigit_value |
      [Hdigit_value | [Hdigit_value | [Hdigit_value | [Hdigit_value |
      [Hdigit_value | Hdigit_value]]]]]]]]];
    rewrite Hdigit_value; simpl; lia.
Qed.
Lemma forall_znth__pass_transition :
  forall {A : Type} (P : A -> Prop) (default : A) values,
    Forall P values <->
    (forall index,
        0 <= index < Zlength values -> P (Znth index values default)).
Proof.
  intros A P default values.
  induction values as [| head tail IH].
  - rewrite Zlength_nil. split.
    + intros _ index Hindex. lia.
    + intros _. constructor.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg tail) as Hlength.
    split.
    + intros Hforall index Hindex.
      inversion Hforall as [| ? ? Hhead Htail]; subst.
      destruct (Z.eq_dec index 0) as [-> | Hnonzero].
      * rewrite Znth0_cons. exact Hhead.
      * rewrite Znth_cons by lia.
        apply (proj1 IH Htail). lia.
    + intros Hpoint. constructor.
      * specialize (Hpoint 0 ltac:(lia)).
        rewrite Znth0_cons in Hpoint. exact Hpoint.
      * apply (proj2 IH). intros index Hindex.
        specialize (Hpoint (index + 1) ltac:(lia)).
        rewrite Znth_cons in Hpoint by lia.
        replace (index + 1 - 1) with index in Hpoint by lia.
        exact Hpoint.
Qed.
Lemma strongly_sorted_cons_iff__pass_transition :
  forall (R : Z -> Z -> Prop) head tail,
    StronglySorted R (head :: tail) <->
    Forall (R head) tail /\ StronglySorted R tail.
Proof.
  intros R head tail. split.
  - intros Hsorted. inversion Hsorted; subst. split; assumption.
  - intros [Hhead Htail]. constructor; assumption.
Qed.
Lemma strongly_sorted_iff_index__pass_transition :
  forall (R : Z -> Z -> Prop) values,
    StronglySorted R values <->
    (forall left right,
        0 <= left -> left < right -> right < Zlength values ->
        R (Znth left values 0) (Znth right values 0)).
Proof.
  intros R values. split.
  - intros Hsorted.
    induction Hsorted as [| head tail Htail IH Hhead].
    + intros left right Hleft Horder Hright.
      rewrite Zlength_nil in Hright. lia.
    + intros left right Hleft Horder Hright.
      rewrite Zlength_cons in Hright.
      destruct (Z.eq_dec left 0) as [-> | Hleft_nonzero].
      * rewrite Znth0_cons, Znth_cons by lia.
        rewrite (forall_znth__pass_transition (R head) 0 tail) in Hhead.
        apply Hhead. lia.
      * rewrite !Znth_cons by lia.
        apply IH; lia.
  - induction values as [| head tail IH]; intros Hindex.
    + constructor.
    + constructor.
      * apply IH. intros left right Hleft Horder Hright.
        specialize
          (Hindex (left + 1) (right + 1) ltac:(lia) ltac:(lia)
             ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hindex by lia.
        replace (left + 1 - 1) with left in Hindex by lia.
        replace (right + 1 - 1) with right in Hindex by lia.
        exact Hindex.
      * apply (proj2 (forall_znth__pass_transition (R head) 0 tail)).
        intros index Hindex_bound.
        specialize
          (Hindex 0 (index + 1) ltac:(lia) ltac:(lia)
             ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth0_cons, Znth_cons in Hindex by lia.
        replace (index + 1 - 1) with index in Hindex by lia.
        exact Hindex.
Qed.
Lemma strongly_sorted_app__pass_transition :
  forall (R : Z -> Z -> Prop) left_values right_values,
    StronglySorted R (left_values ++ right_values) <->
    StronglySorted R left_values /\
    StronglySorted R right_values /\
    (forall left right,
        In left left_values -> In right right_values -> R left right).
Proof.
  intros R left_values.
  induction left_values as [| head tail IH]; intros right_values; simpl.
  - split.
    + intros Hright. split; [constructor |].
      split; [exact Hright |]. intros left right Hleft. contradiction.
    + intros [_ [Hright _]]. exact Hright.
  - rewrite !strongly_sorted_cons_iff__pass_transition.
    rewrite Forall_app, IH.
    split.
    + intros [[Hhead_tail Hhead_right]
              [Htail [Hright Hcross_tail]]].
      repeat split; try assumption.
      intros left right Hleft Hright_in.
      destruct Hleft as [-> | Hleft].
      * rewrite Forall_forall in Hhead_right.
        apply Hhead_right. exact Hright_in.
      * apply Hcross_tail; assumption.
    + intros [[Hhead_tail Htail] [Hright Hcross]].
      assert (Hhead_right : Forall (R head) right_values).
      {
        rewrite Forall_forall. intros right Hright_in.
        apply Hcross; [simpl; auto | exact Hright_in].
      }
      repeat split; try assumption.
      intros left right Hleft Hright_in.
      apply Hcross; [simpl; auto | exact Hright_in].
Qed.
Lemma strongly_sorted_filter__pass_transition :
  forall (R : Z -> Z -> Prop) (test : Z -> bool) values,
    StronglySorted R values ->
    StronglySorted R (filter test values).
Proof.
  intros R test values Hchain.
  induction Hchain as [| head tail Htail IH Hhead].
  - constructor.
  - simpl. destruct (test head) eqn:Htest.
    + constructor.
      * exact IH.
      * rewrite Forall_forall in *.
        intros value Hvalue.
        apply filter_In in Hvalue as [Hvalue _].
        apply Hhead. exact Hvalue.
    + exact IH.
Qed.
Lemma strongly_sorted_weaken__pass_transition :
  forall (R S : Z -> Z -> Prop) values,
    StronglySorted R values ->
    (forall left right,
        In left values -> In right values -> R left right -> S left right) ->
    StronglySorted S values.
Proof.
  intros R S values Hchain.
  induction Hchain as [| head tail Htail IH Hhead]; intros Hweaken.
  - constructor.
  - constructor.
    + apply IH. intros left right Hleft Hright Hrel.
      apply Hweaken; simpl; auto.
    + rewrite Forall_forall in *.
      intros right Hright.
      apply Hweaken.
      * simpl; auto.
      * simpl; auto.
      * apply Hhead. exact Hright.
Qed.
Lemma radix_mod_decompose__pass_transition :
  forall value exponent,
    0 < exponent ->
    value mod (exponent * 10) =
      RadixDigit value exponent * exponent + value mod exponent.
Proof.
  intros value exponent Hexponent.
  unfold RadixDigit.
  rewrite (Z.mod_eq value (exponent * 10)) by lia.
  rewrite (Z.mod_eq (value / exponent) 10) by lia.
  rewrite (Z.mod_eq value exponent) by lia.
  rewrite <- (Z.div_div value exponent 10) by lia.
  ring.
Qed.
Lemma radix_bucket_chain__pass_transition :
  forall source exponent digit,
    0 < exponent ->
    StronglySorted
      (fun left right => left mod exponent <= right mod exponent)
      source ->
    StronglySorted
      (fun left right =>
         left mod (exponent * 10) <= right mod (exponent * 10))
      (RadixBucket source exponent digit).
Proof.
  intros source exponent digit Hexponent Hchain.
  eapply strongly_sorted_weaken__pass_transition.
  - apply strongly_sorted_filter__pass_transition. exact Hchain.
  - intros left right Hleft Hright Hlower.
    apply filter_In in Hleft as [_ Hleft_digit].
    apply filter_In in Hright as [_ Hright_digit].
    apply Z.eqb_eq in Hleft_digit.
    apply Z.eqb_eq in Hright_digit.
    rewrite !radix_mod_decompose__pass_transition by exact Hexponent.
    rewrite Hleft_digit, Hright_digit.
    apply Z.add_le_mono_l. exact Hlower.
Qed.
Lemma radix_bucket_cross__pass_transition :
  forall source exponent left_digit right_digit left right,
    0 < exponent ->
    left_digit < right_digit ->
    In left (RadixBucket source exponent left_digit) ->
    In right (RadixBucket source exponent right_digit) ->
    left mod (exponent * 10) <= right mod (exponent * 10).
Proof.
  intros source exponent left_digit right_digit left right
    Hexponent Hdigits Hleft Hright.
  apply filter_In in Hleft as [_ Hleft_digit].
  apply filter_In in Hright as [_ Hright_digit].
  apply Z.eqb_eq in Hleft_digit.
  apply Z.eqb_eq in Hright_digit.
  pose proof (Z.mod_pos_bound left exponent ltac:(lia)) as Hleft_mod.
  pose proof (Z.mod_pos_bound right exponent ltac:(lia)) as Hright_mod.
  rewrite !radix_mod_decompose__pass_transition by exact Hexponent.
  rewrite Hleft_digit, Hright_digit.
  assert (left_digit + 1 <= right_digit) by lia.
  nia.
Qed.
Lemma radix_buckets_chain__pass_transition :
  forall digits source exponent,
    0 < exponent ->
    StronglySorted
      (fun left right => left mod exponent <= right mod exponent)
      source ->
    StronglySorted Z.lt digits ->
    StronglySorted
      (fun left right =>
         left mod (exponent * 10) <= right mod (exponent * 10))
      (concat (map (fun digit => RadixBucket source exponent digit) digits)).
Proof.
  intros digits source exponent Hexponent Hsource Hdigits.
  induction Hdigits as [| digit digits Hdigits IH Hlater].
  - constructor.
  - simpl.
    apply (proj2 (strongly_sorted_app__pass_transition _ _ _)).
    split.
    + apply radix_bucket_chain__pass_transition; assumption.
    + split.
      * exact IH.
      * intros left right Hleft Hright.
        apply in_concat in Hright as [bucket [Hbucket Hright]].
        apply in_map_iff in Hbucket as [right_digit [Hbucket Hright_digit]].
        subst bucket.
        rewrite Forall_forall in Hlater.
        eapply
          (radix_bucket_cross__pass_transition
             source exponent digit right_digit left right).
        -- exact Hexponent.
        -- apply Hlater. exact Hright_digit.
        -- exact Hleft.
        -- exact Hright.
Qed.
Lemma stable_digit_pass_next_order__pass_transition :
  forall source output exponent,
    0 < exponent ->
    RadixLowerDigitsOrdered source exponent ->
    StableDigitPass source output exponent ->
    RadixLowerDigitsOrdered output (exponent * 10).
Proof.
  intros source output exponent Hexponent Hordered Hpass.
  unfold StableDigitPass in Hpass. subst output.
  assert
    (Hsource_chain :
       StronglySorted
         (fun left right => left mod exponent <= right mod exponent)
         source).
  {
    apply (proj2 (strongly_sorted_iff_index__pass_transition _ _)).
    intros left right Hleft Horder Hright.
    apply Hordered. lia.
  }
  assert
    (Hdigits : StronglySorted Z.lt [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]).
  {
    repeat constructor; simpl; lia.
  }
  assert
    (Houtput_chain :
       StronglySorted
         (fun left right =>
            left mod (exponent * 10) <= right mod (exponent * 10))
         (RadixStableOutput source exponent)).
  {
    unfold RadixStableOutput.
    apply radix_buckets_chain__pass_transition; assumption.
  }
  intros left right [Hleft [Horder Hright]].
  destruct (Z.eq_dec left right) as [-> | Hneq].
  - lia.
  - apply
      (proj1 (strongly_sorted_iff_index__pass_transition _ _) Houtput_chain);
      lia.
Qed.
Lemma decimal_exponent_next__pass_transition :
  forall exponent,
    DecimalExponent exponent ->
    exponent <= 100000000 ->
    DecimalExponent (exponent * 10).
Proof.
  intros exponent [power [Hpower_nonneg Hexponent]] Hbound.
  exists (power + 1).
  split.
  - lia.
  - rewrite Hexponent.
    replace (power + 1) with (Z.succ power) by lia.
    rewrite Z.pow_succ_r by lia.
    ring.
Qed.
Lemma upperbound_permutation__final_result :
  forall (maximum : Z) (left right : list Z),
    Permutation left right ->
    upperbound maximum left ->
    upperbound maximum right.
Proof.
  intros maximum left right Hperm.
  induction Hperm; simpl; intros Hbound.
  - exact I.
  - destruct Hbound as [Hx Hbound].
    split; auto.
  - destruct Hbound as [Hy [Hx Hbound]].
    repeat split; auto.
  - auto.
Qed.
Lemma radix_lower_order_increasing__final_result :
  forall (values : list Z) (exponent maximum : Z),
    0 < exponent ->
    maximum < exponent ->
    lowerbound 0 values ->
    upperbound maximum values ->
    RadixLowerDigitsOrdered values exponent ->
    increasing values.
Proof.
  intros values exponent maximum Hexp Hmax.
  induction values as [| first rest IH]; intros Hlower Hupper Hordered.
  - exact I.
  - destruct rest as [| second tail].
    + exact I.
    + simpl in Hlower, Hupper.
      destruct Hlower as [Hfirst_nonneg [Hsecond_nonneg Htail_lower]].
      destruct Hupper as [Hfirst_upper [Hsecond_upper Htail_upper]].
      split.
      * specialize (Hordered 0 1).
        rewrite !Zlength_cons in Hordered.
        pose proof (Zlength_nonneg tail) as Htail_len.
        specialize (Hordered ltac:(lia)).
        rewrite Znth0_cons in Hordered.
        rewrite Znth_cons in Hordered by lia.
        rewrite Znth0_cons in Hordered.
        rewrite !Z.mod_small in Hordered by lia.
        exact Hordered.
      * apply IH.
        -- exact (conj Hsecond_nonneg Htail_lower).
        -- exact (conj Hsecond_upper Htail_upper).
        --
        intros left right Hindices.
        specialize (Hordered (left + 1) (right + 1)).
        rewrite !Zlength_cons in Hordered.
        rewrite Zlength_cons in Hindices.
        pose proof (Zlength_nonneg tail) as Htail_len.
        specialize (Hordered ltac:(lia)).
        assert (Hleft_shift :
          Znth (left + 1) (first :: second :: tail) 0 =
          Znth left (second :: tail) 0).
        {
          rewrite Znth_cons by lia.
          replace (left + 1 - 1) with left by lia.
          reflexivity.
        }
        assert (Hright_shift :
          Znth (right + 1) (first :: second :: tail) 0 =
          Znth right (second :: tail) 0).
        {
          rewrite Znth_cons by lia.
          replace (right + 1 - 1) with right by lia.
          reflexivity.
        }
        rewrite Hleft_shift, Hright_shift in Hordered.
        exact Hordered.
Qed.
Lemma radix_pass_state_final_increasing__final_result :
  forall (input current : list Z) (n exponent maximum : Z),
    Zlength input = n ->
    Zlength current = n ->
    0 < exponent ->
    0 <= maximum ->
    Z.quot maximum exponent <= 0 ->
    (forall index, 0 <= index < n -> 0 <= Znth index current 0) ->
    PrefixMaximum input n maximum ->
    RadixPassState input current exponent ->
    increasing current.
Proof.
  intros input current n exponent maximum Hinput_len Hcurrent_len
    Hexp Hmaximum Hquotient Hcurrent_nonneg Hprefix Hstate.
  assert (Hmaximum_lt : maximum < exponent).
  {
    destruct (Z_lt_ge_dec maximum exponent) as [Hlt | Hge]; auto.
    assert (1 <= Z.quot maximum exponent).
    {
      apply Zquot_le_lower_bound; lia.
    }
    lia.
  }
  destruct Hprefix as [attained [[Hattained Hinput_upper_points] Heq]].
  sets_unfold in Hinput_upper_points.
  rewrite Heq in Hinput_upper_points.
  destruct Hstate as [Hperm Hlower_order].
  assert (Hinput_upper : upperbound maximum input).
  {
    apply upperbound_intro_Znth.
    intros index Hindex.
    apply Hinput_upper_points.
    rewrite <- Hinput_len.
    exact Hindex.
  }
  assert (Hcurrent_upper : upperbound maximum current).
  {
    eapply upperbound_permutation__final_result; eauto.
  }
  assert (Hcurrent_lower : lowerbound 0 current).
  {
    apply lowerbound_intro_Znth.
    intros index Hindex.
    apply Hcurrent_nonneg.
    rewrite <- Hcurrent_len.
    exact Hindex.
  }
  eapply radix_lower_order_increasing__final_result; eauto.
Qed.
Lemma increasing_short_list__final_result :
  forall (values : list Z),
    Zlength values <= 1 ->
    increasing values.
Proof.
  intros values Hlength.
  destruct values as [| first rest].
  - exact I.
  - destruct rest as [| second tail].
    + exact I.
    + rewrite !Zlength_cons in Hlength.
      pose proof (Zlength_nonneg tail).
      lia.
Qed.
