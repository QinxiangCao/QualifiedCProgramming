Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition number_item : Type := (list Z * Z)%type.

Definition item_digits (x : number_item) : list Z :=
  sublist 0 (snd x) (fst x).

Definition paired_items (rows : list (list Z)) (lengths : list Z) :
  list number_item :=
  combine rows lengths.

Definition concatenate_items (items : list number_item) : list Z :=
  concat (map item_digits items).

Definition concatenate_rows (rows : list (list Z)) (lengths : list Z) :
  list Z :=
  concatenate_items (paired_items rows lengths).

Definition digit_lex_ge (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  (xs = ys \/
   exists k,
     0 <= k < Zlength xs /\
     (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
     Znth k ys 0 < Znth k xs 0).

Definition digit_lex_gt (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  exists k,
    0 <= k < Zlength xs /\
    (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
    Znth k ys 0 < Znth k xs 0.

Definition item_at (rows : list (list Z)) (lengths : list Z) (i : Z) :
  number_item :=
  (Znth i rows nil, Znth i lengths 0).

Definition item_before
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_gt
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).

Definition item_before_or_equal
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).

Definition ConcatLeftDigit
    (rows : list (list Z)) (lens : list Z) (i j position : Z) : Z :=
  Znth position
    (item_digits (item_at rows lens i) ++
     item_digits (item_at rows lens j)) 0.

Definition ConcatRightDigit
    (rows : list (list Z)) (lens : list Z) (i j position : Z) : Z :=
  Znth position
    (item_digits (item_at rows lens j) ++
     item_digits (item_at rows lens i)) 0.

Definition RowsWellFormed
    (rows : list (list Z)) (lengths : list Z)
    (count width : Z) : Prop :=
  Zlength rows = count /\
  Zlength lengths = count /\
  (forall i,
     0 <= i < count ->
     Zlength (Znth i rows nil) = width /\
     1 <= Znth i lengths 0 <= width /\
     1 <= Znth 0 (Znth i rows nil) 0 <= 9 /\
     (forall j,
        0 <= j < Znth i lengths 0 ->
        0 <= Znth j (Znth i rows nil) 0 <= 9)).

Definition FlatRows
    (flat : list Z) (rows : list (list Z)) (count width : Z) : Prop :=
  Zlength flat = count * width /\
  Zlength rows = count /\
  forall i,
    0 <= i < count ->
    Znth i rows nil = sublist (i * width) ((i + 1) * width) flat.

Definition PairedPermutation
    (rows lengths_rows : list (list Z))
    (lens lengths_lens : list Z) : Prop :=
  Zlength rows = Zlength lens /\
  Zlength lengths_rows = Zlength lengths_lens /\
  Permutation (paired_items rows lens)
              (paired_items lengths_rows lengths_lens).

Definition SameOutsidePairedRange
    (rows0 rows1 : list (list Z)) (lens0 lens1 : list Z)
    (left right : Z) : Prop :=
  Zlength rows0 = Zlength rows1 /\
  Zlength lens0 = Zlength lens1 /\
  forall k,
    0 <= k < Zlength rows0 ->
    (k < left \/ right < k) ->
    item_at rows1 lens1 k = item_at rows0 lens0 k.

Definition ConcatComparePrefix
    (rows : list (list Z)) (lens : list Z)
    (i j position : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  0 <= position <= Zlength lhs /\
  Zlength lhs = Zlength rhs /\
  forall k, 0 <= k < position -> Znth k lhs 0 = Znth k rhs 0.

Definition ConcatCompareOutcome
    (rows : list (list Z)) (lens : list Z)
    (i j comparison : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  (comparison = 0 /\ lhs = rhs) \/
  (exists k,
     0 <= k < Zlength lhs /\
     Zlength lhs = Zlength rhs /\
     (forall p, 0 <= p < k -> Znth p lhs 0 = Znth p rhs 0) /\
     Znth k lhs 0 <> Znth k rhs 0 /\
     comparison = Znth k lhs 0 - Znth k rhs 0).

Definition swap_Znth {A : Type} (default : A) (i j : Z) (xs : list A) :
  list A :=
  replace_Znth j (Znth i xs default)
    (replace_Znth i (Znth j xs default) xs).

Definition SwapRowsPrefix
    (before after : list (list Z)) (first second progress width : Z) : Prop :=
  let first_row := Znth first before nil in
  let second_row := Znth second before nil in
  let first_now := sublist 0 progress second_row ++
                   sublist progress width first_row in
  let second_now := sublist 0 progress first_row ++
                    sublist progress width second_row in
  after = replace_Znth second second_now
            (replace_Znth first first_now before).

Definition PartitionScanState
    (rows0 rows1 : list (list Z)) (lens0 lens1 : list Z)
    (low high boundary scan : Z) : Prop :=
  PairedPermutation rows0 rows1 lens0 lens1 /\
  SameOutsidePairedRange rows0 rows1 lens0 lens1 low high /\
  item_at rows1 lens1 high = item_at rows0 lens0 high /\
  (forall k, low <= k <= boundary -> item_before rows1 lens1 k high) /\
  (forall k, boundary < k < scan -> ~ item_before rows1 lens1 k high).

Definition GreedyPartitionedAt
    (rows : list (list Z)) (lens : list Z)
    (low high pivot : Z) : Prop :=
  low <= pivot <= high /\
  (forall k, low <= k < pivot -> item_before rows lens k pivot) /\
  (forall k, pivot < k <= high -> ~ item_before rows lens k pivot).

Definition GreedySortedRange
    (rows : list (list Z)) (lens : list Z) (left right : Z) : Prop :=
  forall i j,
    left <= i /\ i <= j /\ j <= right ->
    item_before_or_equal rows lens i j.

Definition GreedySorted
    (rows : list (list Z)) (lens : list Z) : Prop :=
  forall i j,
    0 <= i /\ i <= j /\ j < Zlength rows ->
    item_before_or_equal rows lens i j.

Definition ConcatenatedPrefix
    (rows : list (list Z)) (lens : list Z) (row_count : Z) : list Z :=
  concatenate_rows (sublist 0 row_count rows) (sublist 0 row_count lens).

Definition ConcatenatedOutputPrefix
    (rows : list (list Z)) (lens : list Z)
    (row_count digit_count : Z) : list Z :=
  ConcatenatedPrefix rows lens row_count ++
  sublist 0 digit_count (Znth row_count rows nil).

Definition LargestConcatenation
    (original_rows arranged_rows : list (list Z))
    (original_lens arranged_lens output : list Z) : Prop :=
  PairedPermutation original_rows arranged_rows
                    original_lens arranged_lens /\
  output = concatenate_rows arranged_rows arranged_lens /\
  forall alternative_rows alternative_lens,
    PairedPermutation original_rows alternative_rows
                      original_lens alternative_lens ->
    digit_lex_ge output
      (concatenate_rows alternative_rows alternative_lens).

Require Import Coq.ZArith.Zpow_facts.
Lemma concat_left_digit_bounds__safety_arithmetic :
  forall rows lens count width i j position,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    0 <= position < Znth i lens 0 + Znth j lens 0 ->
    0 <= ConcatLeftDigit rows lens i j position <= 9.
Proof.
  intros rows lens count width i j position Hwf Hi Hj Hposition.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hbounds]].
  pose proof (Hbounds i Hi) as Hirow.
  pose proof (Hbounds j Hj) as Hjrow.
  destruct Hirow as [Hiwidth [Hilength [_ Hidigits]]].
  destruct Hjrow as [Hjwidth [Hjlength [_ Hjdigits]]].
  assert (Hisub :
    Zlength (sublist 0 (Znth i lens 0) (Znth i rows nil)) =
    Znth i lens 0).
  { apply Zlength_sublist0. split; lia. }
  assert (Hjsub :
    Zlength (sublist 0 (Znth j lens 0) (Znth j rows nil)) =
    Znth j lens 0).
  { apply Zlength_sublist0. split; lia. }
  unfold ConcatLeftDigit, item_digits, item_at.
  cbn [snd fst].
  destruct (Z_lt_dec position (Znth i lens 0)) as [Hleft | Hright].
  - assert (Hleftpos :
      0 <= position <
      Zlength (sublist 0 (Znth i lens 0) (Znth i rows nil))).
    { rewrite Hisub; lia. }
    rewrite app_Znth1 by exact Hleftpos.
    assert (Hleftindex : 0 <= position < Znth i lens 0) by lia.
    rewrite Znth_sublist0 by exact Hleftindex.
    apply Hidigits; lia.
  - assert (Hrightpos :
      position >=
      Zlength (sublist 0 (Znth i lens 0) (Znth i rows nil))).
    { rewrite Hisub; lia. }
    rewrite app_Znth2 by exact Hrightpos.
    rewrite Hisub.
    assert (Hrightindex :
      0 <= position - Znth i lens 0 < Znth j lens 0) by lia.
    rewrite Znth_sublist0 by exact Hrightindex.
    apply Hjdigits; lia.
Qed.
Lemma concat_right_digit_bounds__safety_arithmetic :
  forall rows lens count width i j position,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    0 <= position < Znth i lens 0 + Znth j lens 0 ->
    0 <= ConcatRightDigit rows lens i j position <= 9.
Proof.
  intros rows lens count width i j position Hwf Hi Hj Hposition.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hbounds]].
  pose proof (Hbounds i Hi) as Hirow.
  pose proof (Hbounds j Hj) as Hjrow.
  destruct Hirow as [Hiwidth [Hilength [_ Hidigits]]].
  destruct Hjrow as [Hjwidth [Hjlength [_ Hjdigits]]].
  assert (Hisub :
    Zlength (sublist 0 (Znth i lens 0) (Znth i rows nil)) =
    Znth i lens 0).
  { apply Zlength_sublist0. split; lia. }
  assert (Hjsub :
    Zlength (sublist 0 (Znth j lens 0) (Znth j rows nil)) =
    Znth j lens 0).
  { apply Zlength_sublist0. split; lia. }
  unfold ConcatRightDigit, item_digits, item_at.
  cbn [snd fst].
  destruct (Z_lt_dec position (Znth j lens 0)) as [Hleft | Hright].
  - assert (Hleftpos :
      0 <= position <
      Zlength (sublist 0 (Znth j lens 0) (Znth j rows nil))).
    { rewrite Hjsub; lia. }
    rewrite app_Znth1 by exact Hleftpos.
    assert (Hleftindex : 0 <= position < Znth j lens 0) by lia.
    rewrite Znth_sublist0 by exact Hleftindex.
    apply Hjdigits; lia.
  - assert (Hrightpos :
      position >=
      Zlength (sublist 0 (Znth j lens 0) (Znth j rows nil))).
    { rewrite Hjsub; lia. }
    rewrite app_Znth2 by exact Hrightpos.
    rewrite Hjsub.
    assert (Hrightindex :
      0 <= position - Znth j lens 0 < Znth i lens 0) by lia.
    rewrite Znth_sublist0 by exact Hrightindex.
    apply Hidigits; lia.
Qed.
Lemma PartitionScanState_identity__partition_and_compare_init :
  forall rows lens low high,
    Zlength rows = Zlength lens ->
    PartitionScanState rows rows lens lens low high (low - 1) low.
Proof.
  intros rows lens low high Hlength.
  unfold PartitionScanState, PairedPermutation, SameOutsidePairedRange.
  repeat split; try assumption; try reflexivity; try apply Permutation_refl; intros; lia.
Qed.
Lemma ConcatComparePrefix_zero__partition_and_compare_init :
  forall rows lens i j,
    ConcatComparePrefix rows lens i j 0.
Proof.
  intros rows lens i j.
  unfold ConcatComparePrefix.
  repeat split.
  - lia.
  - apply Zlength_nonneg.
  - rewrite !Zlength_app.
    lia.
  - intros k Hk.
    lia.
Qed.
Lemma FlatRows_Znth__compare_left_digit :
  forall flat rows count width i j,
    FlatRows flat rows count width ->
    0 <= i < count ->
    0 <= j < width ->
    Znth (i * width + j) flat 0 = Znth j (Znth i rows nil) 0.
Proof.
  intros flat rows count width i j Hflat Hi Hj.
  destruct Hflat as [Hflat_length [Hrows_length Hrow]].
  rewrite Hrow by exact Hi.
  rewrite Znth_sublist by nia.
  f_equal.
  lia.
Qed.
Lemma ConcatLeftDigit_first__compare_left_digit :
  forall rows lens count width i j position,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= position < Znth i lens 0 ->
    ConcatLeftDigit rows lens i j position =
      Znth position (Znth i rows nil) 0.
Proof.
  intros rows lens count width i j position Hwf Hi Hposition.
  destruct Hwf as [Hrows_length [Hlens_length Hall]].
  specialize (Hall i Hi).
  destruct Hall as [Hrow_length [Hitem_length Hdigits]].
  unfold ConcatLeftDigit, item_digits, item_at.
  simpl.
  rewrite app_Znth1.
  - rewrite Znth_sublist0 by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.
Lemma ConcatLeftDigit_second__compare_left_digit :
  forall rows lens count width i j position,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    Znth i lens 0 <= position < Znth i lens 0 + Znth j lens 0 ->
    ConcatLeftDigit rows lens i j position =
      Znth (position - Znth i lens 0) (Znth j rows nil) 0.
Proof.
  intros rows lens count width i j position Hwf Hi Hj Hposition.
  destruct Hwf as [Hrows_length [Hlens_length Hall]].
  pose proof (Hall i Hi) as Hrow_i.
  pose proof (Hall j Hj) as Hrow_j.
  destruct Hrow_i as [Hrow_i_length [Hitem_i_length Hdigits_i]].
  destruct Hrow_j as [Hrow_j_length [Hitem_j_length Hdigits_j]].
  unfold ConcatLeftDigit, item_digits, item_at.
  simpl.
  rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  rewrite Znth_sublist0 by lia.
  f_equal.
  lia.
Qed.
Lemma ConcatRightDigit_first_flat__compare_right_digit :
  forall flat rows lens count width scan high position,
    FlatRows flat rows count width ->
    RowsWellFormed rows lens count width ->
    0 <= high < count ->
    0 <= position < Znth high lens 0 ->
    Znth (high * width + position) flat 0 =
      ConcatRightDigit rows lens scan high position.
Proof.
  intros flat rows lens count width scan high position
    Hflat Hwell Hhigh Hposition.
  unfold FlatRows in Hflat.
  destruct Hflat as [_ [_ Hrow]].
  unfold RowsWellFormed in Hwell.
  destruct Hwell as [_ [_ Hwell]].
  pose proof (Hwell high Hhigh) as Hhigh_well.
  destruct Hhigh_well as [Hhigh_length [Hhigh_digits _]].
  assert (Hhigh_sub_length :
    Zlength (sublist 0 (Znth high lens 0) (Znth high rows nil)) =
      Znth high lens 0).
  { apply Zlength_sublist0; lia. }
  unfold ConcatRightDigit, item_digits, item_at.
  cbn [fst snd].
  rewrite (@app_Znth1 Z 0
    (sublist 0 (Znth high lens 0) (Znth high rows nil))
    (sublist 0 (Znth scan lens 0) (Znth scan rows nil))
    position) by (rewrite Hhigh_sub_length; exact Hposition).
  rewrite (@Znth_sublist0 Z 0 position (Znth high lens 0)
    (Znth high rows nil)) by exact Hposition.
  rewrite (Hrow high) by lia.
  cbn [fst].
  rewrite (@Znth_sublist Z 0 (high * width) position
    ((high + 1) * width) flat) by nia.
  f_equal; lia.
Qed.
Lemma ConcatRightDigit_second_flat__compare_right_digit :
  forall flat rows lens count width scan high position,
    FlatRows flat rows count width ->
    RowsWellFormed rows lens count width ->
    0 <= scan < count ->
    0 <= high < count ->
    Znth high lens 0 <= position ->
    position < Znth high lens 0 + Znth scan lens 0 ->
    Znth (scan * width + (position - Znth high lens 0)) flat 0 =
      ConcatRightDigit rows lens scan high position.
Proof.
  intros flat rows lens count width scan high position
    Hflat Hwell Hscan Hhigh Hposition Hposition_end.
  unfold FlatRows in Hflat.
  destruct Hflat as [_ [_ Hrow]].
  unfold RowsWellFormed in Hwell.
  destruct Hwell as [_ [_ Hwell]].
  pose proof (Hwell high Hhigh) as Hhigh_well.
  pose proof (Hwell scan Hscan) as Hscan_well.
  destruct Hhigh_well as [Hhigh_length [Hhigh_digits _]].
  destruct Hscan_well as [Hscan_length [Hscan_digits _]].
  assert (Hhigh_sub_length :
    Zlength (sublist 0 (Znth high lens 0) (Znth high rows nil)) =
      Znth high lens 0).
  { apply Zlength_sublist0; lia. }
  assert (Htail_position :
    0 <= position - Znth high lens 0 < Znth scan lens 0) by lia.
  unfold ConcatRightDigit, item_digits, item_at.
  cbn [fst snd].
  rewrite (@app_Znth2 Z 0
    (sublist 0 (Znth high lens 0) (Znth high rows nil))
    (sublist 0 (Znth scan lens 0) (Znth scan rows nil))
    position) by (rewrite Hhigh_sub_length; lia).
  rewrite Hhigh_sub_length.
  rewrite (@Znth_sublist0 Z 0 (position - Znth high lens 0)
    (Znth scan lens 0) (Znth scan rows nil)) by exact Htail_position.
  rewrite (Hrow scan) by lia.
  cbn [fst].
  rewrite (@Znth_sublist Z 0 (scan * width)
    (position - Znth high lens 0) ((scan + 1) * width) flat) by nia.
  f_equal; lia.
Qed.
Lemma concat_item_digits_Zlength__compare_outcome :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    Zlength
      (item_digits (item_at rows lens i) ++
       item_digits (item_at rows lens j)) =
    Znth i lens 0 + Znth j lens 0.
Proof.
  intros rows lens count width i j Hwf Hi Hj.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hwf]].
  pose proof (Hwf i Hi) as Hwi.
  pose proof (Hwf j Hj) as Hwj.
  destruct Hwi as [Hrowi [Hleni _]].
  destruct Hwj as [Hrowj [Hlenj _]].
  unfold item_digits, item_at.
  change
    (Zlength
       (sublist 0 (Znth i lens 0) (Znth i rows nil) ++
        sublist 0 (Znth j lens 0) (Znth j rows nil)) =
     Znth i lens 0 + Znth j lens 0).
  rewrite Zlength_app.
  rewrite !Zlength_sublist by lia.
  lia.
Qed.
Lemma ConcatComparePrefix_step__compare_outcome :
  forall rows lens i j position,
    ConcatComparePrefix rows lens i j position ->
    ConcatLeftDigit rows lens i j position =
      ConcatRightDigit rows lens i j position ->
    position <
      Zlength
        (item_digits (item_at rows lens i) ++
         item_digits (item_at rows lens j)) ->
    ConcatComparePrefix rows lens i j (position + 1).
Proof.
  intros rows lens i j position Hprefix Heq Hbound.
  unfold ConcatComparePrefix in Hprefix |- *.
  cbv beta zeta in Hprefix |- *.
  unfold ConcatLeftDigit, ConcatRightDigit in Heq.
  destruct Hprefix as [Hposition [Hlength Hprefix]].
  split.
  - lia.
  - split.
    + exact Hlength.
    + intros k Hk.
      destruct (Z.lt_ge_cases k position) as [Hlt | Hge].
      * apply Hprefix; lia.
      * assert (k = position) by lia.
        subst k.
        exact Heq.
Qed.
Lemma ConcatCompareOutcome_difference__compare_outcome :
  forall rows lens i j position,
    ConcatComparePrefix rows lens i j position ->
    position <
      Zlength
        (item_digits (item_at rows lens i) ++
         item_digits (item_at rows lens j)) ->
    ConcatLeftDigit rows lens i j position <>
      ConcatRightDigit rows lens i j position ->
    ConcatCompareOutcome rows lens i j
      (ConcatLeftDigit rows lens i j position -
       ConcatRightDigit rows lens i j position).
Proof.
  intros rows lens i j position Hprefix Hbound Hneq.
  unfold ConcatComparePrefix in Hprefix.
  cbv beta zeta in Hprefix.
  destruct Hprefix as [Hposition [Hlength Hprefix]].
  unfold ConcatCompareOutcome.
  cbv beta zeta.
  right.
  exists position.
  unfold ConcatLeftDigit, ConcatRightDigit in Hneq |- *.
  repeat split; try assumption; try lia.
Qed.
Lemma ConcatCompareOutcome_zero__compare_outcome :
  forall rows lens i j position,
    ConcatComparePrefix rows lens i j position ->
    Zlength
      (item_digits (item_at rows lens i) ++
       item_digits (item_at rows lens j)) <= position ->
    ConcatCompareOutcome rows lens i j 0.
Proof.
  intros rows lens i j position Hprefix Hfull.
  unfold ConcatComparePrefix in Hprefix.
  cbv beta zeta in Hprefix.
  destruct Hprefix as [Hposition [Hlength Hprefix]].
  unfold ConcatCompareOutcome.
  cbv beta zeta.
  left.
  split.
  - reflexivity.
  - apply (proj2 (list_eq_ext _ _ 0)).
    split.
    + exact Hlength.
    + intros k Hk.
      apply Hprefix.
      lia.
Qed.
Lemma SwapRowsPrefix_zero__scan_row_swap :
  forall before lens count width first second,
    RowsWellFormed before lens count width ->
    0 <= first < count ->
    0 <= second < count ->
    SwapRowsPrefix before before first second 0 width.
Proof.
  intros before lens count width first second Hwf Hfirst Hsecond.
  destruct Hwf as [Hrows [Hlens Hwf]].
  pose proof (Hwf first Hfirst) as [Hfirst_len _].
  pose proof (Hwf second Hsecond) as [Hsecond_len _].
  unfold SwapRowsPrefix.
  rewrite !Zsublist_nil by lia.
  simpl.
  rewrite (sublist_self (Znth first before nil) width)
    by (symmetry; exact Hfirst_len).
  rewrite (sublist_self (Znth second before nil) width)
    by (symmetry; exact Hsecond_len).
  rewrite !replace_Znth_Znth.
  reflexivity.
Qed.
Lemma advance_prefix_row__scan_row_swap :
  forall (first_row second_row : list Z) progress width,
    Zlength first_row = width ->
    Zlength second_row = width ->
    0 <= progress < width ->
    replace_Znth progress (Znth progress second_row 0)
      (sublist 0 progress second_row ++
       sublist progress width first_row) =
    sublist 0 (progress + 1) second_row ++
    sublist (progress + 1) width first_row.
Proof.
  intros first_row second_row progress width Hfirst Hsecond Hprogress.
  rewrite replace_Znth_app_r.
  2:{ rewrite Zlength_sublist; lia. }
  rewrite Zlength_sublist by lia.
  replace (progress - (progress - 0)) with 0 by lia.
  rewrite (sublist_split progress width (progress + 1) first_row)
    by lia.
  rewrite (sublist_single 0 progress first_row) by lia.
  rewrite replace_Znth_nothing by (rewrite Zlength_sublist; lia).
  unfold replace_Znth.
  simpl.
  rewrite (sublist_split 0 (progress + 1) progress second_row)
    by lia.
  rewrite (sublist_single 0 progress second_row) by lia.
  change
    (sublist 0 progress second_row ++
       ([Znth progress second_row 0] ++
        sublist (progress + 1) width first_row) =
     (sublist 0 progress second_row ++ [Znth progress second_row 0]) ++
       sublist (progress + 1) width first_row).
  apply app_assoc.
Qed.
Lemma sublist_replace_flat_cell__scan_row_swap :
  forall (flat : list Z) count width row column i value,
    Zlength flat = count * width ->
    0 < width ->
    0 <= row < count ->
    0 <= column < width ->
    0 <= i < count ->
    sublist (i * width) ((i + 1) * width)
      (replace_Znth (row * width + column) value flat) =
    if Z.eq_dec i row then
      replace_Znth column value
        (sublist (i * width) ((i + 1) * width) flat)
    else
      sublist (i * width) ((i + 1) * width) flat.
Proof.
  intros flat count width row column i value Hflat Hwidth Hrow Hcolumn Hi.
  assert (Hreplace : 0 <= row * width + column < Zlength flat).
  {
    rewrite Hflat.
    split.
    - nia.
    - assert ((row + 1) * width <= count * width).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      nia.
  }
  destruct (Z.eq_dec i row) as [Heq | Hneq].
  - subst i.
    apply (proj2 (list_eq_ext _ _ 0)).
    split.
    + rewrite Zlength_sublist
        by (rewrite Zlength_replace_Znth, Hflat; nia).
      rewrite Zlength_replace_Znth.
      rewrite Zlength_sublist by (rewrite Hflat; nia).
      reflexivity.
    + intros k Hk.
      rewrite Zlength_sublist in Hk
        by (rewrite Zlength_replace_Znth, Hflat; nia).
      assert (Hquery : 0 <= row * width + k < Zlength flat).
      {
        rewrite Hflat.
        split.
        - nia.
        - assert ((row + 1) * width <= count * width).
          { apply Z.mul_le_mono_nonneg_r; lia. }
          nia.
      }
      rewrite Znth_sublist by nia.
      destruct (Z.eq_dec k column) as [Hkc | Hkc].
      * subst k.
        replace (column + row * width) with (row * width + column) by lia.
        rewrite !Znth_replace_Znth_Same by
            (first [exact Hreplace | rewrite Zlength_sublist; nia]).
        reflexivity.
      * replace (k + row * width) with (row * width + k) by lia.
        rewrite !Znth_replace_Znth_Diff by
            (first [exact Hreplace | exact Hquery |
                    rewrite Zlength_sublist; nia | nia]).
        rewrite Znth_sublist by nia.
        f_equal; nia.
  - apply (proj2 (list_eq_ext _ _ 0)).
    split.
    + rewrite Zlength_sublist
        by (rewrite Zlength_replace_Znth, Hflat; nia).
      rewrite Zlength_sublist by (rewrite Hflat; nia).
      reflexivity.
    + intros k Hk.
      rewrite Zlength_sublist in Hk
        by (rewrite Zlength_replace_Znth, Hflat; nia).
      assert (Hquery : 0 <= i * width + k < Zlength flat).
      {
        rewrite Hflat.
        split.
        - nia.
        - assert ((i + 1) * width <= count * width).
          { apply Z.mul_le_mono_nonneg_r; lia. }
          nia.
      }
      rewrite Znth_sublist by nia.
      replace (k + i * width) with (i * width + k) by lia.
      rewrite Znth_replace_Znth_Diff by
          (try rewrite ?Zlength_replace_Znth;
           try exact Hreplace; try exact Hquery; nia).
      rewrite Znth_sublist by nia.
      f_equal; nia.
Qed.
Lemma FlatRows_replace_cell__scan_row_swap :
  forall flat rows count width row column value,
    FlatRows flat rows count width ->
    0 < width ->
    0 <= row < count ->
    0 <= column < width ->
    FlatRows
      (replace_Znth (row * width + column) value flat)
      (replace_Znth row
        (replace_Znth column value (Znth row rows nil)) rows)
      count width.
Proof.
  intros flat rows count width row column value Hflat Hwidth Hrow Hcolumn.
  destruct Hflat as [Hflat_len [Hrows_len Hrows]].
  unfold FlatRows.
  split.
  - rewrite Zlength_replace_Znth; exact Hflat_len.
  - split.
    + rewrite Zlength_replace_Znth; exact Hrows_len.
    + intros i Hi.
      rewrite (sublist_replace_flat_cell__scan_row_swap
        flat count width row column i value); try assumption.
      destruct (Z.eq_dec i row) as [Heq | Hneq].
      * subst i.
        rewrite Znth_replace_Znth_Same by (rewrite Hrows_len; lia).
        rewrite Hrows by assumption.
        reflexivity.
      * rewrite Znth_replace_Znth_Diff by
            (try rewrite Hrows_len; try lia).
        apply Hrows; assumption.
Qed.
Lemma FlatRows_Znth_cell__scan_row_swap :
  forall flat rows count width row column,
    FlatRows flat rows count width ->
    0 <= row < count ->
    0 <= column < width ->
    Znth (row * width + column) flat 0 =
    Znth column (Znth row rows nil) 0.
Proof.
  intros flat rows count width row column Hflat Hrow Hcolumn.
  destruct Hflat as [Hflat_len [Hrows_len Hrows]].
  rewrite Hrows by assumption.
  rewrite Znth_sublist by nia.
  f_equal; nia.
Qed.
Lemma prefix_row_at_progress__scan_row_swap :
  forall (first_row second_row : list Z) progress width,
    Zlength first_row = width ->
    Zlength second_row = width ->
    0 <= progress < width ->
    Znth progress
      (sublist 0 progress second_row ++
       sublist progress width first_row) 0 =
    Znth progress first_row 0.
Proof.
  intros first_row second_row progress width Hfirst Hsecond Hprogress.
  rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia.
  replace (progress - (progress - 0)) with 0 by lia.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.
Lemma replace_Znth_comm__scan_row_swap :
  forall {A : Type} (xs : list A) i j (a b : A),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a xs) =
    replace_Znth i a (replace_Znth j b xs).
Proof.
  intros A xs i j a b Hi Hj Hneq.
  unfold replace_Znth.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat j).
  assert (Hnat : ni <> nj).
  {
    intro Heq.
    apply Hneq.
    subst ni nj.
    apply Z2Nat.inj; lia.
  }
  clearbody ni nj; clear i j Hi Hj Hneq.
  revert ni nj Hnat.
  induction xs as [|x xs IH]; intros [|ni] [|nj] Hnat;
    simpl in *; try congruence; try reflexivity.
  f_equal; eapply IH; congruence.
Qed.
Lemma replace_Znth_overwrite__scan_row_swap :
  forall {A : Type} (xs : list A) i (a b : A),
    replace_Znth i b (replace_Znth i a xs) =
    replace_Znth i b xs.
Proof.
  intros A xs i a b.
  unfold replace_Znth.
  set (n := Z.to_nat i).
  clearbody n; clear i.
  revert n.
  induction xs as [|x xs IH]; intros [|n]; simpl; auto.
  f_equal; apply IH.
Qed.
Lemma SwapRowsPrefix_step__scan_row_swap :
  forall before now first second progress width count,
    Zlength before = count ->
    0 <= first < count ->
    0 <= second < count ->
    first <> second ->
    Zlength (Znth first before nil) = width ->
    Zlength (Znth second before nil) = width ->
    0 <= progress < width ->
    SwapRowsPrefix before now first second progress width ->
    SwapRowsPrefix before
      (replace_Znth second
        (replace_Znth progress (Znth progress (Znth first now nil) 0)
          (Znth second now nil))
        (replace_Znth first
          (replace_Znth progress (Znth progress (Znth second now nil) 0)
            (Znth first now nil))
          now))
      first second (progress + 1) width.
Proof.
  intros before now first second progress width count Hlen Hfirst Hsecond
    Hneq Hfirst_len Hsecond_len Hprogress Hswap.
  unfold SwapRowsPrefix in Hswap |- *.
  cbn in Hswap |- *.
  subst now.
  assert (Hfirst_now :
    Znth first
      (replace_Znth second
        (sublist 0 progress (Znth first before nil) ++
         sublist progress width (Znth second before nil))
        (replace_Znth first
          (sublist 0 progress (Znth second before nil) ++
           sublist progress width (Znth first before nil)) before)) nil =
    sublist 0 progress (Znth second before nil) ++
    sublist progress width (Znth first before nil)).
  {
    rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth, Hlen; lia).
    rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    reflexivity.
  }
  assert (Hsecond_now :
    Znth second
      (replace_Znth second
        (sublist 0 progress (Znth first before nil) ++
         sublist progress width (Znth second before nil))
        (replace_Znth first
          (sublist 0 progress (Znth second before nil) ++
           sublist progress width (Znth first before nil)) before)) nil =
    sublist 0 progress (Znth first before nil) ++
    sublist progress width (Znth second before nil)).
  {
    rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_replace_Znth, Hlen; lia).
    reflexivity.
  }
  cbn in Hfirst_now, Hsecond_now.
  rewrite Hfirst_now, Hsecond_now.
  assert (Hfirst_cell :
    Znth progress
      (firstn (Z.to_nat progress) (Znth second before nil) ++
       sublist progress width (Znth first before nil)) 0 =
    Znth progress (Znth first before nil) 0).
  {
    change (Znth progress
      (sublist 0 progress (Znth second before nil) ++
       sublist progress width (Znth first before nil)) 0 =
      Znth progress (Znth first before nil) 0).
    apply prefix_row_at_progress__scan_row_swap; assumption.
  }
  assert (Hsecond_cell :
    Znth progress
      (firstn (Z.to_nat progress) (Znth first before nil) ++
       sublist progress width (Znth second before nil)) 0 =
    Znth progress (Znth second before nil) 0).
  {
    change (Znth progress
      (sublist 0 progress (Znth first before nil) ++
       sublist progress width (Znth second before nil)) 0 =
      Znth progress (Znth second before nil) 0).
    apply prefix_row_at_progress__scan_row_swap; assumption.
  }
  rewrite Hfirst_cell, Hsecond_cell.
  assert (Hadvance_second :
    replace_Znth progress (Znth progress (Znth first before nil) 0)
      (firstn (Z.to_nat progress) (Znth first before nil) ++
       sublist progress width (Znth second before nil)) =
    sublist 0 (progress + 1) (Znth first before nil) ++
    sublist (progress + 1) width (Znth second before nil)).
  {
    change (replace_Znth progress (Znth progress (Znth first before nil) 0)
      (sublist 0 progress (Znth first before nil) ++
       sublist progress width (Znth second before nil)) =
      sublist 0 (progress + 1) (Znth first before nil) ++
      sublist (progress + 1) width (Znth second before nil)).
    apply advance_prefix_row__scan_row_swap; assumption.
  }
  assert (Hadvance_first :
    replace_Znth progress (Znth progress (Znth second before nil) 0)
      (firstn (Z.to_nat progress) (Znth second before nil) ++
       sublist progress width (Znth first before nil)) =
    sublist 0 (progress + 1) (Znth second before nil) ++
    sublist (progress + 1) width (Znth first before nil)).
  {
    change (replace_Znth progress (Znth progress (Znth second before nil) 0)
      (sublist 0 progress (Znth second before nil) ++
       sublist progress width (Znth first before nil)) =
      sublist 0 (progress + 1) (Znth second before nil) ++
      sublist (progress + 1) width (Znth first before nil)).
    apply advance_prefix_row__scan_row_swap; assumption.
  }
  rewrite Hadvance_second, Hadvance_first.
  assert (Hcomm :
    replace_Znth first
      (sublist 0 (progress + 1) (Znth second before nil) ++
       sublist (progress + 1) width (Znth first before nil))
      (replace_Znth second
        (firstn (Z.to_nat progress) (Znth first before nil) ++
         sublist progress width (Znth second before nil))
        (replace_Znth first
          (firstn (Z.to_nat progress) (Znth second before nil) ++
           sublist progress width (Znth first before nil)) before)) =
    replace_Znth second
      (firstn (Z.to_nat progress) (Znth first before nil) ++
       sublist progress width (Znth second before nil))
      (replace_Znth first
        (sublist 0 (progress + 1) (Znth second before nil) ++
         sublist (progress + 1) width (Znth first before nil))
        (replace_Znth first
          (firstn (Z.to_nat progress) (Znth second before nil) ++
           sublist progress width (Znth first before nil)) before))).
  {
    apply replace_Znth_comm__scan_row_swap; lia.
  }
  rewrite Hcomm.
  rewrite replace_Znth_overwrite__scan_row_swap.
  rewrite replace_Znth_overwrite__scan_row_swap.
  reflexivity.
Qed.
Lemma SwapRowsPrefix_same__scan_row_swap :
  forall before index progress width,
    Zlength (Znth index before nil) = width ->
    0 <= progress <= width ->
    SwapRowsPrefix before before index index progress width.
Proof.
  intros before index progress width Hrow Hprogress.
  unfold SwapRowsPrefix; cbn.
  assert (Hwhole :
    firstn (Z.to_nat progress) (Znth index before nil) ++
    sublist progress width (Znth index before nil) =
    Znth index before nil).
  {
    change (sublist 0 progress (Znth index before nil) ++
      sublist progress width (Znth index before nil) =
      Znth index before nil).
    rewrite <- (sublist_split 0 width progress (Znth index before nil))
      by lia.
    apply sublist_self; symmetry; assumption.
  }
  rewrite Hwhole.
  rewrite !replace_Znth_Znth.
  reflexivity.
Qed.
Lemma FlatRows_swap_progress_step__scan_row_swap :
  forall flat before now count width first second progress,
    FlatRows flat now count width ->
    Zlength before = count ->
    0 <= first < count ->
    0 <= second < count ->
    Zlength (Znth first before nil) = width ->
    Zlength (Znth second before nil) = width ->
    0 <= progress < width ->
    SwapRowsPrefix before now first second progress width ->
    exists next,
      FlatRows
        (replace_Znth (second * width + progress)
          (Znth (first * width + progress) flat 0)
          (replace_Znth (first * width + progress)
            (Znth (second * width + progress) flat 0) flat))
        next count width /\
      SwapRowsPrefix before next first second (progress + 1) width.
Proof.
  intros flat before now count width first second progress Hflat Hbefore
    Hfirst Hsecond Hfirst_len Hsecond_len Hprogress Hswap.
  destruct (Z.eq_dec first second) as [Heq | Hneq].
  - subst second.
    rewrite !replace_Znth_Znth.
    exists now; split; [exact Hflat |].
    pose proof (SwapRowsPrefix_same__scan_row_swap
      before first progress width Hfirst_len) as Hsame.
    specialize (Hsame ltac:(lia)).
    unfold SwapRowsPrefix in Hswap, Hsame.
    cbn in Hswap, Hsame.
    assert (Hnow : now = before) by congruence.
    rewrite Hnow.
    apply SwapRowsPrefix_same__scan_row_swap; [assumption | lia].
  - set (flat_mid :=
      replace_Znth (first * width + progress)
        (Znth (second * width + progress) flat 0) flat).
    set (rows_mid :=
      replace_Znth first
        (replace_Znth progress
          (Znth (second * width + progress) flat 0)
          (Znth first now nil)) now).
    assert (Hflat_mid : FlatRows flat_mid rows_mid count width).
    {
      subst flat_mid rows_mid.
      eapply FlatRows_replace_cell__scan_row_swap; eauto; lia.
    }
    set (flat_next :=
      replace_Znth (second * width + progress)
        (Znth (first * width + progress) flat 0) flat_mid).
    set (rows_next :=
      replace_Znth second
        (replace_Znth progress
          (Znth (first * width + progress) flat 0)
          (Znth second rows_mid nil)) rows_mid).
    assert (Hflat_next : FlatRows flat_next rows_next count width).
    {
      subst flat_next rows_next.
      eapply FlatRows_replace_cell__scan_row_swap; eauto; lia.
    }
    exists rows_next; split.
    + change (FlatRows flat_next rows_next count width).
      exact Hflat_next.
    + subst rows_next rows_mid.
      pose proof (FlatRows_Znth_cell__scan_row_swap
        flat now count width first progress Hflat Hfirst Hprogress)
        as Hfirst_cell.
      pose proof (FlatRows_Znth_cell__scan_row_swap
        flat now count width second progress Hflat Hsecond Hprogress)
        as Hsecond_cell.
      rewrite Hfirst_cell, Hsecond_cell.
      rewrite Znth_replace_Znth_Diff by
          (destruct Hflat as [_ [Hnow _]];
           try rewrite Hnow; lia).
      eapply SwapRowsPrefix_step__scan_row_swap; eauto.
Qed.
Lemma ConcatCompareOutcome_nonpositive_not_item_before__scan_advance :
  forall rows lens i j comparison,
    ConcatCompareOutcome rows lens i j comparison ->
    comparison <= 0 ->
    ~ item_before rows lens i j.
Proof.
  intros rows lens i j comparison Hout Hle Hbefore.
  unfold ConcatCompareOutcome, item_before, digit_lex_gt in *.
  destruct Hout as [[Hcomp Heq] |
                    [k [Hkrange [Hlen [Hprefix [Hneq Hcomp]]]]]].
  - destruct Hbefore as [_ [q [Hqrange [Hqprefix Hqstrict]]]].
    rewrite Heq in Hqstrict.
    lia.
  - destruct Hbefore as [_ [q [Hqrange [Hqprefix Hqstrict]]]].
    destruct (Z_lt_ge_dec q k) as [Hqk | Hkq].
    + specialize (Hprefix q).
      specialize (Hqprefix q).
      lia.
    + destruct (Z_lt_ge_dec k q) as [Hkq' | Hqk'].
      * specialize (Hqprefix k).
        apply Hneq.
        apply Hqprefix.
        lia.
      * assert (q = k) by lia.
        subst q.
        lia.
Qed.
Lemma PartitionScanState_advance_nonbefore__scan_advance :
  forall rows0 rows1 lens0 lens1 low high boundary scan,
    PartitionScanState rows0 rows1 lens0 lens1 low high boundary scan ->
    ~ item_before rows1 lens1 scan high ->
    PartitionScanState rows0 rows1 lens0 lens1 low high boundary (scan + 1).
Proof.
  intros rows0 rows1 lens0 lens1 low high boundary scan Hstate Hscan.
  unfold PartitionScanState in *.
  destruct Hstate as [Hperm [Houtside [Hpivot [Hbefore Hnotbefore]]]].
  split; [exact Hperm |].
  split; [exact Houtside |].
  split; [exact Hpivot |].
  split; [exact Hbefore |].
  intros k Hrange Hitem.
  destruct (Z_lt_ge_dec k scan) as [Hkscan | Hscank].
  - eapply Hnotbefore; eauto; lia.
  - assert (k = scan) by lia.
    subst k.
    exact (Hscan Hitem).
Qed.
Lemma ConcatCompareOutcome_positive_item_before__scan_advance :
  forall rows lens i j comparison,
    ConcatCompareOutcome rows lens i j comparison ->
    comparison > 0 ->
    item_before rows lens i j.
Proof.
  intros rows lens i j comparison Hout Hpositive.
  unfold ConcatCompareOutcome, item_before, digit_lex_gt in *.
  destruct Hout as [[Hzero Heq] |
                    [k [Hkrange [Hlen [Hprefix [Hneq Hcomp]]]]]].
  - lia.
  - split; [exact Hlen |].
    exists k.
    repeat split; try assumption; lia.
Qed.
Lemma Zlength_swap_Znth__scan_advance :
  forall (A : Type) (d : A) i j (xs : list A),
    Zlength (swap_Znth d i j xs) = Zlength xs.
Proof.
  intros.
  unfold swap_Znth.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.
Lemma Znth_swap_Znth_left__scan_advance :
  forall (A : Type) (d : A) i j (xs : list A),
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Znth i (swap_Znth d i j xs) d = Znth j xs d.
Proof.
  intros A d i j xs Hi Hj.
  unfold swap_Znth.
  destruct (Z.eq_dec i j) as [Heq | Hneq].
  - subst j.
    rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by
        (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
Qed.
Lemma Znth_swap_Znth_right__scan_advance :
  forall (A : Type) (d : A) i j (xs : list A),
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Znth j (swap_Znth d i j xs) d = Znth i xs d.
Proof.
  intros A d i j xs Hi Hj.
  unfold swap_Znth.
  rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
  reflexivity.
Qed.
Lemma Znth_swap_Znth_diff__scan_advance :
  forall (A : Type) (d : A) i j k (xs : list A),
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    0 <= k < Zlength xs ->
    k <> i ->
    k <> j ->
    Znth k (swap_Znth d i j xs) d = Znth k xs d.
Proof.
  intros A d i j k xs Hi Hj Hk Hki Hkj.
  unfold swap_Znth.
  rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff by lia.
  reflexivity.
Qed.
Lemma item_at_swap_left__scan_advance :
  forall rows lens i j,
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    Zlength rows = Zlength lens ->
    item_at (swap_Znth nil i j rows) (swap_Znth 0 i j lens) i =
    item_at rows lens j.
Proof.
  intros rows lens i j Hi Hj Hlen.
  unfold item_at.
  rewrite Znth_swap_Znth_left__scan_advance by lia.
  rewrite Znth_swap_Znth_left__scan_advance by lia.
  reflexivity.
Qed.
Lemma item_at_swap_right__scan_advance :
  forall rows lens i j,
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    Zlength rows = Zlength lens ->
    item_at (swap_Znth nil i j rows) (swap_Znth 0 i j lens) j =
    item_at rows lens i.
Proof.
  intros rows lens i j Hi Hj Hlen.
  unfold item_at.
  rewrite Znth_swap_Znth_right__scan_advance by lia.
  rewrite Znth_swap_Znth_right__scan_advance by lia.
  reflexivity.
Qed.
Lemma item_at_swap_diff__scan_advance :
  forall rows lens i j k,
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    0 <= k < Zlength rows ->
    Zlength rows = Zlength lens ->
    k <> i ->
    k <> j ->
    item_at (swap_Znth nil i j rows) (swap_Znth 0 i j lens) k =
    item_at rows lens k.
Proof.
  intros rows lens i j k Hi Hj Hk Hlen Hki Hkj.
  unfold item_at.
  rewrite Znth_swap_Znth_diff__scan_advance by lia.
  rewrite Znth_swap_Znth_diff__scan_advance by lia.
  reflexivity.
Qed.
Lemma RowsWellFormed_swap_Znth__scan_advance :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    RowsWellFormed
      (swap_Znth nil i j rows) (swap_Znth 0 i j lens) count width.
Proof.
  intros rows lens count width i j Hwf Hi Hj.
  unfold RowsWellFormed in *.
  destruct Hwf as [Hrowslen [Hlenslen Hall]].
  split.
  - rewrite Zlength_swap_Znth__scan_advance.
    exact Hrowslen.
  - split.
    + rewrite Zlength_swap_Znth__scan_advance.
      exact Hlenslen.
    + intros k Hk.
      destruct (Z.eq_dec k i) as [Hki | Hki].
      * subst k.
        rewrite Znth_swap_Znth_left__scan_advance by lia.
        rewrite Znth_swap_Znth_left__scan_advance by lia.
        apply Hall.
        exact Hj.
      * destruct (Z.eq_dec k j) as [Hkj | Hkj].
        -- subst k.
           rewrite Znth_swap_Znth_right__scan_advance by lia.
           rewrite Znth_swap_Znth_right__scan_advance by lia.
           apply Hall.
           exact Hi.
        -- rewrite Znth_swap_Znth_diff__scan_advance by lia.
           rewrite Znth_swap_Znth_diff__scan_advance by lia.
           apply Hall.
           exact Hk.
Qed.
Lemma SwapRowsPrefix_complete__scan_advance :
  forall before after lens count width first second progress,
    RowsWellFormed before lens count width ->
    0 <= first < count ->
    0 <= second < count ->
    progress = width ->
    SwapRowsPrefix before after first second progress width ->
    after = swap_Znth nil first second before.
Proof.
  intros before after lens count width first second progress
         Hwf Hfirst Hsecond Hprogress Hswap.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hrowslen [Hlenslen Hall]].
  pose proof (Hall first Hfirst) as [Hfirstlen Hfirstprops].
  pose proof (Hall second Hsecond) as [Hsecondlen Hsecondprops].
  subst progress.
  unfold SwapRowsPrefix, swap_Znth in *.
  rewrite (sublist_self (Znth first before nil) width) in Hswap by lia.
  rewrite (sublist_self (Znth second before nil) width) in Hswap by lia.
  rewrite !Zsublist_nil in Hswap by lia.
  repeat rewrite app_nil_r in Hswap.
  exact Hswap.
Qed.
Lemma sum_permutation__scan_advance :
  forall xs ys, Permutation xs ys -> sum xs = sum ys.
Proof.
  intros xs ys Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma replace_Znth_swap_form__scan_advance :
  forall (A : Type) (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
      (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  change (replace_Znth 0 xj (xi :: l2 ++ xj :: l3))
    with (xj :: l2 ++ xj :: l3).
  rewrite replace_Znth_app_r with
      (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A)
      (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  change (replace_Znth 0 xi (xj :: l3)) with (xi :: l3).
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__scan_advance :
  forall (A : Type) (l : list A) i j (d : A),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l (swap_Znth d i j l).
Proof.
  intros A l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  unfold swap_Znth.
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
  assert (Hj_lr : (nj < List.length lr)%nat).
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
      rewrite Nat.add_comm, Hnat.
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
    rewrite !Zlength_correct, !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form__scan_advance.
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
Lemma replace_nth_comm__scan_advance :
  forall (A : Type) ni nj (l : list A) a b,
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
Lemma replace_Znth_comm__scan_advance :
  forall (A : Type) (l : list A) i j a b,
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm__scan_advance.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma permutation_swap_Znth__scan_advance :
  forall (A : Type) (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l (swap_Znth d i j l).
Proof.
  intros A l i j d Hi Hj.
  unfold swap_Znth.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - fold (swap_Znth d i j l).
    apply permutation_swap_Znth_lt__scan_advance.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm__scan_advance by lia.
      fold (swap_Znth d j i l).
      apply permutation_swap_Znth_lt__scan_advance.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.
Lemma map_replace_Znth__scan_advance :
  forall (A B : Type) (f : A -> B) n x (xs : list A),
    map f (replace_Znth n x xs) =
    replace_Znth n (f x) (map f xs).
Proof.
  intros A B f n x xs.
  unfold replace_Znth.
  generalize (Z.to_nat n) as k.
  induction xs as [|a xs IH]; intros k; destruct k; simpl; auto.
  rewrite IH.
  reflexivity.
Qed.
Lemma map_swap_Znth__scan_advance :
  forall (A B : Type) (f : A -> B) d i j (xs : list A),
    map f (swap_Znth d i j xs) =
    swap_Znth (f d) i j (map f xs).
Proof.
  intros A B f d i j xs.
  unfold swap_Znth.
  repeat rewrite map_replace_Znth__scan_advance.
  unfold Znth.
  rewrite !map_nth.
  reflexivity.
Qed.
Lemma map_fst_combine__scan_advance :
  forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys ->
    map fst (combine xs ys) = xs.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys Hlen; destruct ys; simpl in *;
    try discriminate; auto.
  f_equal.
  apply IH.
  lia.
Qed.
Lemma map_snd_combine__scan_advance :
  forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys ->
    map snd (combine xs ys) = ys.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys Hlen; destruct ys; simpl in *;
    try discriminate; auto.
  f_equal.
  apply IH.
  lia.
Qed.
Lemma combine_map_fst_snd__scan_advance :
  forall (A B : Type) (ps : list (A * B)),
    combine (map fst ps) (map snd ps) = ps.
Proof.
  intros A B ps.
  induction ps as [|[a b] ps IH]; simpl; f_equal; auto.
Qed.
Lemma paired_items_swap_eq__scan_advance :
  forall rows lens i j,
    Zlength rows = Zlength lens ->
    paired_items (swap_Znth nil i j rows) (swap_Znth 0 i j lens) =
    swap_Znth (nil, 0) i j (paired_items rows lens).
Proof.
  intros rows lens i j Hlen.
  unfold paired_items.
  assert (Hnatlen : length rows = length lens).
  { rewrite !Zlength_correct in Hlen. lia. }
  symmetry.
  rewrite <- (combine_map_fst_snd__scan_advance
    (list Z) Z (swap_Znth (nil, 0) i j (combine rows lens))).
  rewrite !map_swap_Znth__scan_advance.
  rewrite map_fst_combine__scan_advance by exact Hnatlen.
  rewrite map_snd_combine__scan_advance by exact Hnatlen.
  reflexivity.
Qed.
Lemma paired_items_swap_permutation__scan_advance :
  forall rows lens i j,
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    Permutation (paired_items rows lens)
      (paired_items (swap_Znth nil i j rows) (swap_Znth 0 i j lens)).
Proof.
  intros rows lens i j Hlen Hi Hj.
  rewrite paired_items_swap_eq__scan_advance by exact Hlen.
  apply permutation_swap_Znth__scan_advance.
  - unfold paired_items.
    rewrite Zlength_correct, length_combine.
    assert (Hnatlen : length rows = length lens).
    { rewrite !Zlength_correct in Hlen. lia. }
    rewrite Hnatlen, Nat.min_id.
    rewrite <- Zlength_correct.
    lia.
  - unfold paired_items.
    rewrite Zlength_correct, length_combine.
    assert (Hnatlen : length rows = length lens).
    { rewrite !Zlength_correct in Hlen. lia. }
    rewrite Hnatlen, Nat.min_id.
    rewrite <- Zlength_correct.
    lia.
Qed.
Lemma PartitionScanState_swap_advance__scan_advance :
  forall original_rows before original_lens lens
         count width low high boundary scan comparison,
    RowsWellFormed before lens count width ->
    PartitionScanState original_rows before original_lens lens
      low high (boundary - 1) scan ->
    ConcatCompareOutcome before lens scan high comparison ->
    comparison > 0 ->
    0 <= low ->
    low <= boundary ->
    boundary <= scan ->
    scan < high ->
    high < count ->
    PartitionScanState original_rows
      (swap_Znth nil boundary scan before)
      original_lens (swap_Znth 0 boundary scan lens)
      low high boundary (scan + 1).
Proof.
  intros original_rows before original_lens lens
         count width low high boundary scan comparison
         Hwf Hstate Hout Hpositive Hlow Hboundary Hbs Hsh Hhighcount.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hbeforelen [Hlenslen Hall]].
  assert (Hboundaryrange : 0 <= boundary < Zlength before) by lia.
  assert (Hscanrange : 0 <= scan < Zlength before) by lia.
  assert (Hcurlen : Zlength before = Zlength lens) by lia.
  destruct Hstate as [Hpaired [Houtside [Hpivot [Hbefore Hnotbefore]]]].
  assert (Hhighsame :
    item_at (swap_Znth nil boundary scan before)
            (swap_Znth 0 boundary scan lens) high =
    item_at before lens high).
  {
    apply item_at_swap_diff__scan_advance; try lia.
  }
  assert (Hscanbefore : item_before before lens scan high).
  {
    eapply ConcatCompareOutcome_positive_item_before__scan_advance; eauto.
  }
  split.
  - unfold PairedPermutation in *.
    destruct Hpaired as [Horiginallen [Hcurrentlen Hperm]].
    split; [exact Horiginallen |].
    split.
    + rewrite !Zlength_swap_Znth__scan_advance.
      exact Hcurrentlen.
    + eapply Permutation_trans; [exact Hperm |].
      apply paired_items_swap_permutation__scan_advance; try assumption.
  - split.
    + unfold SameOutsidePairedRange in *.
      destruct Houtside as [Hrowsoutside [Hlensoutside Halloutside]].
      split.
      * rewrite Zlength_swap_Znth__scan_advance.
        exact Hrowsoutside.
      * split.
        -- rewrite Zlength_swap_Znth__scan_advance.
           exact Hlensoutside.
        -- intros k Hkrange Hkoutside.
           rewrite item_at_swap_diff__scan_advance; try lia.
           apply Halloutside; assumption.
    + split.
      * rewrite Hhighsame.
        exact Hpivot.
      * split.
        -- intros k Hkrange.
           destruct (Z.eq_dec k boundary) as [Hkb | Hkb].
           ++ subst k.
              unfold item_before in *.
              rewrite item_at_swap_left__scan_advance by lia.
              rewrite Hhighsame.
              exact Hscanbefore.
           ++ assert (Hkscan : k <> scan) by lia.
              unfold item_before in *.
              rewrite item_at_swap_diff__scan_advance by lia.
              rewrite Hhighsame.
              apply Hbefore.
              lia.
        -- intros k Hkrange Hitem.
           destruct (Z.eq_dec k scan) as [Hks | Hks].
           ++ subst k.
              assert (Hboundaryscan : boundary < scan) by lia.
              unfold item_before in Hitem.
              rewrite item_at_swap_right__scan_advance in Hitem by lia.
              rewrite Hhighsame in Hitem.
              eapply Hnotbefore; [| exact Hitem].
              lia.
           ++ assert (Hkboundary : k <> boundary) by lia.
              unfold item_before in Hitem.
              rewrite item_at_swap_diff__scan_advance in Hitem by lia.
              rewrite Hhighsame in Hitem.
              eapply Hnotbefore; [| exact Hitem].
              lia.
Qed.
Lemma SwapRowsPrefix_zero__scan_advance :
  forall rows lens count width first second,
    RowsWellFormed rows lens count width ->
    0 <= first < count ->
    0 <= second < count ->
    SwapRowsPrefix rows rows first second 0 width.
Proof.
  intros rows lens count width first second Hwf Hfirst Hsecond.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hrowslen [Hlenslen Hall]].
  pose proof (Hall first Hfirst) as [Hfirstlen Hfirstprops].
  pose proof (Hall second Hsecond) as [Hsecondlen Hsecondprops].
  unfold SwapRowsPrefix.
  rewrite !Zsublist_nil by lia.
  rewrite (sublist_self (Znth first rows nil) width) by lia.
  rewrite (sublist_self (Znth second rows nil) width) by lia.
  simpl.
  rewrite !replace_Znth_Znth.
  reflexivity.
Qed.
Lemma FlatRows_replace_cell__pivot_finalization :
  forall flat rows count width row column value,
    FlatRows flat rows count width ->
    0 <= row < count ->
    0 <= column < width ->
    FlatRows
      (replace_Znth (row * width + column) value flat)
      (replace_Znth row
        (replace_Znth column value (Znth row rows nil)) rows)
      count width.
Proof.
  intros flat rows count width row column value
    (Hflat_len & Hrows_len & Hrows) Hrow Hcolumn.
  repeat split.
  - rewrite Zlength_replace_Znth. exact Hflat_len.
  - rewrite Zlength_replace_Znth. exact Hrows_len.
  - intros k Hk.
    destruct (Z.eq_dec k row) as [-> | Hkrow].
    + rewrite Znth_replace_Znth_Same by (rewrite Hrows_len; lia).
      rewrite Hrows by exact Hrow.
      apply (proj2 (list_eq_ext _ _ 0)).
      split.
      * rewrite Zlength_replace_Znth.
        rewrite !Zlength_sublist by
          (rewrite ?Zlength_replace_Znth, ?Hflat_len; nia).
        lia.
      * intros q Hq.
        rewrite Zlength_replace_Znth in Hq.
        rewrite Zlength_sublist in Hq by (rewrite Hflat_len; nia).
        destruct (Z.eq_dec q column) as [-> | Hqcolumn].
        -- rewrite Znth_replace_Znth_Same by
             (rewrite Zlength_sublist; [lia | rewrite Hflat_len; nia]).
           rewrite Znth_sublist by nia.
           replace (column + row * width) with
             (row * width + column) by lia.
           rewrite Znth_replace_Znth_Same by (rewrite Hflat_len; nia).
           reflexivity.
        -- rewrite Znth_replace_Znth_Diff by
             (try rewrite Zlength_sublist; try rewrite Hflat_len; nia).
           rewrite !Znth_sublist by nia.
           rewrite Znth_replace_Znth_Diff by
             (try rewrite Hflat_len; nia).
           reflexivity.
    + rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrows_len; lia).
      rewrite Hrows by exact Hk.
      apply (proj2 (list_eq_ext _ _ 0)).
      split.
      * rewrite !Zlength_sublist by
          (rewrite ?Zlength_replace_Znth, ?Hflat_len; nia).
        reflexivity.
      * intros q Hq.
        rewrite Zlength_sublist in Hq by (rewrite Hflat_len; nia).
        rewrite !Znth_sublist by nia.
        rewrite Znth_replace_Znth_Diff by
          (try rewrite Hflat_len; nia).
        reflexivity.
Qed.
Lemma FlatRows_Znth_cell__pivot_finalization :
  forall flat rows count width row column,
    FlatRows flat rows count width ->
    0 <= row < count ->
    0 <= column < width ->
    Znth (row * width + column) flat 0 =
    Znth column (Znth row rows nil) 0.
Proof.
  intros flat rows count width row column
    (Hflat_len & Hrows_len & Hrows) Hrow Hcolumn.
  rewrite Hrows by exact Hrow.
  rewrite Znth_sublist by nia.
  replace (column + row * width) with
    (row * width + column) by lia.
  reflexivity.
Qed.
Lemma row_prefix_replace_advance__pivot_finalization :
  forall first_row second_row progress width,
    Zlength first_row = width ->
    Zlength second_row = width ->
    0 <= progress < width ->
    replace_Znth progress (Znth progress second_row 0)
      (sublist 0 progress second_row ++
       sublist progress width first_row) =
    sublist 0 (progress + 1) second_row ++
    sublist (progress + 1) width first_row.
Proof.
  intros first_row second_row progress width
    Hfirst_len Hsecond_len Hprogress.
  rewrite replace_Znth_app_r by
    (rewrite Zlength_sublist0; lia).
  rewrite replace_Znth_nothing by
    (rewrite Zlength_sublist0; lia).
  rewrite Zlength_sublist0 by lia.
  replace (progress - progress) with 0 by lia.
  assert (Hfirst_tail :
    sublist progress width first_row =
      [Znth progress first_row 0] ++
      sublist (progress + 1) width first_row).
  {
    rewrite (sublist_split progress width (progress + 1) first_row)
      by lia.
    rewrite (@sublist_single Z 0 progress first_row) by lia.
    reflexivity.
  }
  assert (Hsecond_prefix :
    sublist 0 (progress + 1) second_row =
      sublist 0 progress second_row ++
      [Znth progress second_row 0]).
  {
    rewrite (sublist_split 0 (progress + 1) progress second_row)
      by lia.
    rewrite (@sublist_single Z 0 progress second_row) by lia.
    reflexivity.
  }
  rewrite Hfirst_tail, Hsecond_prefix.
  unfold replace_Znth.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma Znth_prefix_mix_boundary__pivot_finalization :
  forall first_row second_row progress width,
    Zlength first_row = width ->
    Zlength second_row = width ->
    0 <= progress < width ->
    Znth progress
      (sublist 0 progress second_row ++
       sublist progress width first_row) 0 =
    Znth progress first_row 0.
Proof.
  intros first_row second_row progress width
    Hfirst_len Hsecond_len Hprogress.
  rewrite app_Znth2 by (rewrite Zlength_sublist0; lia).
  rewrite Zlength_sublist0 by lia.
  replace (progress - progress) with 0 by lia.
  rewrite Znth_sublist by lia.
  replace (0 + progress) with progress by lia.
  reflexivity.
Qed.
Lemma replace_nth_comm__pivot_finalization :
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
    + f_equal. apply IHni. lia.
Qed.
Lemma replace_Znth_comm__pivot_finalization :
  forall {A : Type} (l : list A) i j a b,
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hij.
  unfold replace_Znth.
  apply replace_nth_comm__pivot_finalization.
  intro Heq.
  apply Hij.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma replace_nth_twice__pivot_finalization :
  forall {A : Type} n (l : list A) a b,
    replace_nth n (replace_nth n l a) b =
    replace_nth n l b.
Proof.
  intros A n.
  induction n; intros l a b; destruct l as [|x xs]; simpl; auto.
  f_equal. apply IHn.
Qed.
Lemma replace_Znth_twice__pivot_finalization :
  forall {A : Type} (l : list A) i a b,
    replace_Znth i b (replace_Znth i a l) =
    replace_Znth i b l.
Proof.
  intros A l i a b.
  unfold replace_Znth.
  apply replace_nth_twice__pivot_finalization.
Qed.
Lemma SwapRowsPrefix_advance_distinct__pivot_finalization :
  forall before current first second progress width,
    0 <= first < second ->
    second < Zlength before ->
    Zlength (Znth first before nil) = width ->
    Zlength (Znth second before nil) = width ->
    0 <= progress < width ->
    SwapRowsPrefix before current first second progress width ->
    SwapRowsPrefix before
      (replace_Znth second
        (replace_Znth progress
          (Znth progress (Znth first current nil) 0)
          (Znth second current nil))
        (replace_Znth first
          (replace_Znth progress
            (Znth progress (Znth second current nil) 0)
            (Znth first current nil))
          current))
      first second (progress + 1) width.
Proof.
  intros before current first second progress width
    Hfirst Hsecond_bound Hfirst_len Hsecond_len Hprogress Hswap.
  assert (Hcurrent_first :
    Znth first current nil =
      sublist 0 progress (Znth second before nil) ++
      sublist progress width (Znth first before nil)).
  {
    unfold SwapRowsPrefix in Hswap.
    rewrite Hswap.
    rewrite Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Hcurrent_second :
    Znth second current nil =
      sublist 0 progress (Znth first before nil) ++
      sublist progress width (Znth second before nil)).
  {
    unfold SwapRowsPrefix in Hswap.
    rewrite Hswap.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hfirst_boundary :
    Znth progress (Znth first current nil) 0 =
    Znth progress (Znth first before nil) 0).
  {
    rewrite Hcurrent_first.
    apply Znth_prefix_mix_boundary__pivot_finalization;
      assumption.
  }
  assert (Hsecond_boundary :
    Znth progress (Znth second current nil) 0 =
    Znth progress (Znth second before nil) 0).
  {
    rewrite Hcurrent_second.
    apply Znth_prefix_mix_boundary__pivot_finalization;
      assumption.
  }
  unfold SwapRowsPrefix.
  rewrite Hfirst_boundary, Hsecond_boundary.
  rewrite Hcurrent_first, Hcurrent_second.
  rewrite (row_prefix_replace_advance__pivot_finalization
    (Znth first before nil) (Znth second before nil)
    progress width Hfirst_len Hsecond_len Hprogress).
  rewrite (row_prefix_replace_advance__pivot_finalization
    (Znth second before nil) (Znth first before nil)
    progress width Hsecond_len Hfirst_len Hprogress).
  unfold SwapRowsPrefix in Hswap.
  rewrite Hswap.
  rewrite (replace_Znth_comm__pivot_finalization
    (replace_Znth first
      (sublist 0 progress (Znth second before nil) ++
       sublist progress width (Znth first before nil)) before)
    second first
    (sublist 0 progress (Znth first before nil) ++
     sublist progress width (Znth second before nil))
    (sublist 0 (progress + 1) (Znth second before nil) ++
     sublist (progress + 1) width (Znth first before nil))) by lia.
  rewrite !replace_Znth_twice__pivot_finalization.
  reflexivity.
Qed.
Lemma SwapRowsPrefix_same_current__pivot_finalization :
  forall before current index progress width,
    Zlength (Znth index before nil) = width ->
    0 <= progress <= width ->
    SwapRowsPrefix before current index index progress width ->
    current = before.
Proof.
  intros before current index progress width Hrow_len Hprogress Hswap.
  assert (Hmix :
    sublist 0 progress (Znth index before nil) ++
    sublist progress width (Znth index before nil) =
    Znth index before nil).
  {
    rewrite <- (sublist_split 0 width progress
      (Znth index before nil)) by lia.
    apply sublist_self.
    symmetry. exact Hrow_len.
  }
  unfold SwapRowsPrefix in Hswap.
  rewrite Hmix in Hswap.
  rewrite replace_Znth_twice__pivot_finalization in Hswap.
  rewrite replace_Znth_Znth in Hswap.
  exact Hswap.
Qed.
Lemma SwapRowsPrefix_same_refl__pivot_finalization :
  forall before index progress width,
    Zlength (Znth index before nil) = width ->
    0 <= progress <= width ->
    SwapRowsPrefix before before index index progress width.
Proof.
  intros before index progress width Hrow_len Hprogress.
  assert (Hmix :
    sublist 0 progress (Znth index before nil) ++
    sublist progress width (Znth index before nil) =
    Znth index before nil).
  {
    rewrite <- (sublist_split 0 width progress
      (Znth index before nil)) by lia.
    apply sublist_self.
    symmetry. exact Hrow_len.
  }
  unfold SwapRowsPrefix.
  rewrite Hmix.
  rewrite replace_Znth_twice__pivot_finalization.
  rewrite replace_Znth_Znth.
  reflexivity.
Qed.
Lemma swap_Znth_length__pivot_finalization :
  forall {A : Type} (d : A) i j xs,
    Zlength (swap_Znth d i j xs) = Zlength xs.
Proof.
  intros. unfold swap_Znth. rewrite !Zlength_replace_Znth. reflexivity.
Qed.
Lemma swap_Znth_left__pivot_finalization :
  forall {A : Type} (d : A) i j xs,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Znth i (swap_Znth d i j xs) d = Znth j xs d.
Proof.
  intros A d i j xs Hi Hj.
  unfold swap_Znth.
  destruct (Z.eq_dec i j) as [-> | Hij].
  - rewrite !replace_Znth_Znth. reflexivity.
  - rewrite Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by exact Hi.
    reflexivity.
Qed.
Lemma swap_Znth_right__pivot_finalization :
  forall {A : Type} (d : A) i j xs,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Znth j (swap_Znth d i j xs) d = Znth i xs d.
Proof.
  intros A d i j xs Hi Hj.
  unfold swap_Znth.
  rewrite Znth_replace_Znth_Same by
    (rewrite Zlength_replace_Znth; exact Hj).
  reflexivity.
Qed.
Lemma swap_Znth_other__pivot_finalization :
  forall {A : Type} (d : A) i j k xs,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    0 <= k < Zlength xs ->
    k <> i -> k <> j ->
    Znth k (swap_Znth d i j xs) d = Znth k xs d.
Proof.
  intros A d i j k xs Hi Hj Hk Hki Hkj.
  unfold swap_Znth.
  rewrite Znth_replace_Znth_Diff by
    (try rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff by lia.
  reflexivity.
Qed.
Lemma swap_Znth_reverse__pivot_finalization :
  forall {A : Type} (d : A) i j xs,
    0 <= i -> 0 <= j ->
    replace_Znth i (Znth j xs d)
      (replace_Znth j (Znth i xs d) xs) =
    swap_Znth d i j xs.
Proof.
  intros A d i j xs Hi Hj.
  unfold swap_Znth.
  destruct (Z.eq_dec i j) as [-> | Hij].
  - rewrite !replace_Znth_twice__pivot_finalization. reflexivity.
  - apply replace_Znth_comm__pivot_finalization; lia.
Qed.
Lemma SwapRowsPrefix_complete__pivot_finalization :
  forall before after first second width,
    Zlength (Znth first before nil) = width ->
    Zlength (Znth second before nil) = width ->
    SwapRowsPrefix before after first second width width ->
    after = swap_Znth nil first second before.
Proof.
  intros before after first second width Hfirst Hsecond Hswap.
  unfold SwapRowsPrefix in Hswap.
  rewrite (sublist_self (Znth first before nil) width
    (eq_sym Hfirst)) in Hswap.
  rewrite (sublist_self (Znth second before nil) width
    (eq_sym Hsecond)) in Hswap.
  assert (Hfirst_tail :
    sublist width width (Znth first before nil) = nil).
  {
    unfold sublist.
    replace (Z.to_nat width) with
      (length (Znth first before nil)).
    2:{
      apply Nat2Z.inj.
      rewrite Z2Nat.id.
      - rewrite <- Zlength_correct. exact Hfirst.
      - rewrite <- Hfirst. apply Zlength_nonneg.
    }
    rewrite firstn_all, skipn_all. reflexivity.
  }
  assert (Hsecond_tail :
    sublist width width (Znth second before nil) = nil).
  {
    unfold sublist.
    replace (Z.to_nat width) with
      (length (Znth second before nil)).
    2:{
      apply Nat2Z.inj.
      rewrite Z2Nat.id.
      - rewrite <- Zlength_correct. exact Hsecond.
      - rewrite <- Hsecond. apply Zlength_nonneg.
    }
    rewrite firstn_all, skipn_all. reflexivity.
  }
  rewrite Hfirst_tail, Hsecond_tail in Hswap.
  rewrite !app_nil_r in Hswap.
  exact Hswap.
Qed.
Lemma paired_items_length__pivot_finalization :
  forall rows lens,
    Zlength rows = Zlength lens ->
    Zlength (paired_items rows lens) = Zlength rows.
Proof.
  intros rows.
  induction rows as [|row rows IH]; intros lens Hlen.
  - destruct lens; reflexivity.
  - destruct lens as [|len lens].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg rows). lia.
    + change
        (Zlength ((row, len) :: paired_items rows lens) =
         Zlength (row :: rows)).
      rewrite !Zlength_cons.
      f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_paired_items__pivot_finalization :
  forall rows lens i,
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    Znth i (paired_items rows lens) (nil, 0) = item_at rows lens i.
Proof.
  intros rows.
  induction rows as [|row rows IH]; intros lens i Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct lens as [|len lens].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg rows). lia.
    + unfold paired_items, item_at in *; simpl in *.
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * reflexivity.
      * rewrite !Znth_cons by lia.
        apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma paired_items_swap__pivot_finalization :
  forall rows lens i j,
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    paired_items (swap_Znth nil i j rows) (swap_Znth 0 i j lens) =
    swap_Znth (nil, 0) i j (paired_items rows lens).
Proof.
  intros rows lens i j Hlen Hi Hj.
  assert (Hilens : 0 <= i < Zlength lens) by
    (rewrite <- Hlen; exact Hi).
  assert (Hjlens : 0 <= j < Zlength lens) by
    (rewrite <- Hlen; exact Hj).
  assert (Hipairs : 0 <= i < Zlength (paired_items rows lens)) by
    (rewrite paired_items_length__pivot_finalization by exact Hlen; exact Hi).
  assert (Hjpairs : 0 <= j < Zlength (paired_items rows lens)) by
    (rewrite paired_items_length__pivot_finalization by exact Hlen; exact Hj).
  apply (proj2 (list_eq_ext _ _ (nil, 0))).
  split.
  - rewrite paired_items_length__pivot_finalization.
    + rewrite swap_Znth_length__pivot_finalization.
      rewrite swap_Znth_length__pivot_finalization.
      symmetry. apply paired_items_length__pivot_finalization. exact Hlen.
    + rewrite !swap_Znth_length__pivot_finalization. exact Hlen.
  - intros k Hk.
    rewrite paired_items_length__pivot_finalization in Hk.
    2:{ rewrite !swap_Znth_length__pivot_finalization. exact Hlen. }
    rewrite swap_Znth_length__pivot_finalization in Hk.
    rewrite Znth_paired_items__pivot_finalization.
    2:{ rewrite !swap_Znth_length__pivot_finalization. exact Hlen. }
    2:{ rewrite swap_Znth_length__pivot_finalization. exact Hk. }
    unfold item_at.
    destruct (Z.eq_dec k i) as [-> | Hki].
    + rewrite (swap_Znth_left__pivot_finalization nil i j rows Hi Hj).
      rewrite (swap_Znth_left__pivot_finalization 0 i j lens Hilens Hjlens).
      rewrite (swap_Znth_left__pivot_finalization
        (nil, 0) i j (paired_items rows lens) Hipairs Hjpairs).
      rewrite Znth_paired_items__pivot_finalization; auto.
    + destruct (Z.eq_dec k j) as [-> | Hkj].
      * rewrite (swap_Znth_right__pivot_finalization nil i j rows Hi Hj).
        rewrite (swap_Znth_right__pivot_finalization 0 i j lens Hilens Hjlens).
        rewrite (swap_Znth_right__pivot_finalization
          (nil, 0) i j (paired_items rows lens) Hipairs Hjpairs).
        rewrite Znth_paired_items__pivot_finalization; auto.
      * assert (Hkpairs :
          0 <= k < Zlength (paired_items rows lens)) by
          (rewrite paired_items_length__pivot_finalization by exact Hlen;
           exact Hk).
        assert (Hklens : 0 <= k < Zlength lens) by
          (rewrite <- Hlen; exact Hk).
        rewrite (swap_Znth_other__pivot_finalization
          nil i j k rows Hi Hj Hk Hki Hkj).
        rewrite (swap_Znth_other__pivot_finalization
          0 i j k lens Hilens Hjlens Hklens Hki Hkj).
        rewrite (swap_Znth_other__pivot_finalization
          (nil, 0) i j k (paired_items rows lens)
          Hipairs Hjpairs Hkpairs Hki Hkj).
        rewrite Znth_paired_items__pivot_finalization; auto.
Qed.
Lemma replace_Znth_swap_form__pivot_finalization :
  forall {A : Type} (l1 l2 l3 : list A) xi xj,
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by
    (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by
    (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (Hzero :
    replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
    xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite Hzero.
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by
    (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with
    (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with
    (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__pivot_finalization :
  forall {A : Type} (xs : list A) i j d,
    0 <= i < j ->
    j < Zlength xs ->
    Permutation xs (swap_Znth d i j xs).
Proof.
  intros A xs i j d Hij Hj.
  unfold swap_Znth.
  remember (Znth i xs d) as xi.
  remember (Znth j xs d) as xj.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni xs).
  set (rest := skipn (S ni) xs).
  set (l2 := firstn nj rest).
  set (l3 := skipn (S nj) rest).
  assert (Hsplit_i : xs = l1 ++ xi :: rest).
  {
    subst l1 rest ni.
    rewrite (list_split_nth _ (Z.to_nat i) xs d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi. reflexivity.
  }
  assert (Hj_rest : (nj < length rest)%nat).
  {
    subst nj rest ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  assert (Hsplit_j : rest = l2 ++ xj :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj rest d) at 1 by exact Hj_rest.
    replace xj with (nth nj rest d).
    2:{
      subst nj rest ni. rewrite Heqxj. unfold Znth. rewrite nth_skipn.
      assert (Hnat :
        (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia. lia.
      }
      rewrite Nat.add_comm, Hnat. reflexivity.
    }
    reflexivity.
  }
  assert (Hxs : xs = l1 ++ xi :: l2 ++ xj :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace xs with (l1 ++ xi :: l2 ++ xj :: l3) by
    (symmetry; exact Hxs).
  replace i with (Zlength l1).
  2:{
    subst l1 ni. rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 rest ni nj. rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  rewrite replace_Znth_swap_form__pivot_finalization.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma permutation_swap_Znth__pivot_finalization :
  forall {A : Type} (xs : list A) i j d,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    Permutation xs (swap_Znth d i j xs).
Proof.
  intros A xs i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hij].
  - apply permutation_swap_Znth_lt__pivot_finalization; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + unfold swap_Znth.
      rewrite replace_Znth_comm__pivot_finalization by lia.
      fold (swap_Znth d j i xs).
      apply permutation_swap_Znth_lt__pivot_finalization; lia.
    + assert (i = j) by lia. subst j.
      unfold swap_Znth. rewrite !replace_Znth_Znth.
      apply Permutation_refl.
Qed.
Lemma RowsWellFormed_swap__pivot_finalization :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    RowsWellFormed (swap_Znth nil i j rows) (swap_Znth 0 i j lens)
      count width.
Proof.
  intros rows lens count width i j
    (Hrows_len & Hlens_len & Hrows) Hi Hj.
  unfold RowsWellFormed.
  split.
  - rewrite swap_Znth_length__pivot_finalization. exact Hrows_len.
  - split.
    + rewrite swap_Znth_length__pivot_finalization. exact Hlens_len.
    + intros k Hk.
    destruct (Z.eq_dec k i) as [-> | Hki].
    * rewrite (swap_Znth_left__pivot_finalization nil i j rows)
        by (rewrite ?Hrows_len; lia).
      rewrite (swap_Znth_left__pivot_finalization 0 i j lens)
        by (rewrite ?Hlens_len; lia).
      apply Hrows. exact Hj.
    * destruct (Z.eq_dec k j) as [-> | Hkj].
      -- rewrite (swap_Znth_right__pivot_finalization nil i j rows)
          by (rewrite ?Hrows_len; lia).
        rewrite (swap_Znth_right__pivot_finalization 0 i j lens)
          by (rewrite ?Hlens_len; lia).
        apply Hrows. exact Hi.
      -- rewrite (swap_Znth_other__pivot_finalization nil i j k rows)
          by (rewrite ?Hrows_len; lia).
        rewrite (swap_Znth_other__pivot_finalization 0 i j k lens)
          by (rewrite ?Hlens_len; lia).
        apply Hrows. exact Hk.
Qed.
Lemma PairedPermutation_swap__pivot_finalization :
  forall original_rows rows original_lens lens i j,
    PairedPermutation original_rows rows original_lens lens ->
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    PairedPermutation original_rows (swap_Znth nil i j rows)
      original_lens (swap_Znth 0 i j lens).
Proof.
  intros original_rows rows original_lens lens i j
    (Horiginal_len & Hcurrent_len & Hperm) Hlen Hi Hj.
  repeat split.
  - exact Horiginal_len.
  - rewrite swap_Znth_length__pivot_finalization.
    rewrite swap_Znth_length__pivot_finalization.
    exact Hcurrent_len.
  - eapply Permutation_trans; [exact Hperm |].
    rewrite paired_items_swap__pivot_finalization by assumption.
    apply permutation_swap_Znth__pivot_finalization.
    + rewrite paired_items_length__pivot_finalization by exact Hlen. exact Hi.
    + rewrite paired_items_length__pivot_finalization by exact Hlen. exact Hj.
Qed.
Lemma SameOutsidePairedRange_swap_inside__pivot_finalization :
  forall original_rows rows original_lens lens low high i j,
    SameOutsidePairedRange original_rows rows original_lens lens low high ->
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    0 <= j < Zlength rows ->
    low <= i <= high ->
    low <= j <= high ->
    SameOutsidePairedRange original_rows (swap_Znth nil i j rows)
      original_lens (swap_Znth 0 i j lens) low high.
Proof.
  intros original_rows rows original_lens lens low high i j
    (Hrows_len & Hlens_len & Houtside) Hlen Hi Hj Hirange Hjrange.
  repeat split.
  - rewrite swap_Znth_length__pivot_finalization. exact Hrows_len.
  - rewrite swap_Znth_length__pivot_finalization. exact Hlens_len.
  - intros k Hk Hkoutside.
    assert (Hki : k <> i) by lia.
    assert (Hkj : k <> j) by lia.
    assert (Hkrows : 0 <= k < Zlength rows) by
      (rewrite <- Hrows_len; exact Hk).
    assert (Hilens : 0 <= i < Zlength lens) by
      (rewrite <- Hlen; exact Hi).
    assert (Hjlens : 0 <= j < Zlength lens) by
      (rewrite <- Hlen; exact Hj).
    assert (Hklens : 0 <= k < Zlength lens) by
      (rewrite <- Hlen; exact Hkrows).
    unfold item_at.
    rewrite (swap_Znth_other__pivot_finalization
      nil i j k rows Hi Hj Hkrows Hki Hkj).
    rewrite (swap_Znth_other__pivot_finalization
      0 i j k lens Hilens Hjlens Hklens Hki Hkj).
    apply Houtside; assumption.
Qed.
Lemma PartitionScanState_finalize__pivot_finalization :
  forall original_rows rows original_lens lens count width low high pivot,
    RowsWellFormed rows lens count width ->
    PartitionScanState original_rows rows original_lens lens
      low high (pivot - 1) high ->
    0 <= low -> low < high -> high < count ->
    low <= pivot <= high ->
    GreedyPartitionedAt
      (swap_Znth nil pivot high rows)
      (swap_Znth 0 pivot high lens) low high pivot.
Proof.
  intros original_rows rows original_lens lens count width low high pivot
    (Hrows_len & Hlens_len & Hrow_wf) Hstate
    Hlow Hlow_high Hhigh_count Hpivot.
  destruct Hstate as
    (Hperm & Houtside & Hhigh_same & Hbefore & Hafter).
  assert (Hpivot_bound : 0 <= pivot < Zlength rows) by
    (rewrite Hrows_len; lia).
  assert (Hhigh_bound : 0 <= high < Zlength rows) by
    (rewrite Hrows_len; lia).
  assert (Hpivot_lens : 0 <= pivot < Zlength lens) by
    (rewrite Hlens_len; lia).
  assert (Hhigh_lens : 0 <= high < Zlength lens) by
    (rewrite Hlens_len; lia).
  unfold GreedyPartitionedAt.
  split; [exact Hpivot |].
  split.
  - intros k Hk.
    assert (Hk_bound : 0 <= k < Zlength rows) by
      (rewrite Hrows_len; lia).
    assert (Hk_lens : 0 <= k < Zlength lens) by
      (rewrite Hlens_len; lia).
    assert (Hki : k <> pivot) by lia.
    assert (Hkh : k <> high) by lia.
    assert (Hitem_k :
      item_at (swap_Znth nil pivot high rows)
        (swap_Znth 0 pivot high lens) k = item_at rows lens k).
    {
      unfold item_at.
      rewrite (swap_Znth_other__pivot_finalization
        nil pivot high k rows Hpivot_bound Hhigh_bound Hk_bound Hki Hkh).
      rewrite (swap_Znth_other__pivot_finalization
        0 pivot high k lens Hpivot_lens Hhigh_lens Hk_lens Hki Hkh).
      reflexivity.
    }
    assert (Hitem_pivot :
      item_at (swap_Znth nil pivot high rows)
        (swap_Znth 0 pivot high lens) pivot = item_at rows lens high).
    {
      unfold item_at.
      rewrite (swap_Znth_left__pivot_finalization
        nil pivot high rows Hpivot_bound Hhigh_bound).
      rewrite (swap_Znth_left__pivot_finalization
        0 pivot high lens Hpivot_lens Hhigh_lens).
      reflexivity.
    }
    unfold item_before. rewrite Hitem_k, Hitem_pivot.
    apply Hbefore. lia.
  - intros k Hk.
    assert (Hk_bound : 0 <= k < Zlength rows) by
      (rewrite Hrows_len; lia).
    assert (Hk_lens : 0 <= k < Zlength lens) by
      (rewrite Hlens_len; lia).
    assert (Hki : k <> pivot) by lia.
    assert (Hitem_pivot :
      item_at (swap_Znth nil pivot high rows)
        (swap_Znth 0 pivot high lens) pivot = item_at rows lens high).
    {
      unfold item_at.
      rewrite (swap_Znth_left__pivot_finalization
        nil pivot high rows Hpivot_bound Hhigh_bound).
      rewrite (swap_Znth_left__pivot_finalization
        0 pivot high lens Hpivot_lens Hhigh_lens).
      reflexivity.
    }
    destruct (Z.eq_dec k high) as [-> | Hkh].
    + assert (Hitem_high :
        item_at (swap_Znth nil pivot high rows)
          (swap_Znth 0 pivot high lens) high = item_at rows lens pivot).
      {
        unfold item_at.
        rewrite (swap_Znth_right__pivot_finalization
          nil pivot high rows Hpivot_bound Hhigh_bound).
        rewrite (swap_Znth_right__pivot_finalization
          0 pivot high lens Hpivot_lens Hhigh_lens).
        reflexivity.
      }
      unfold item_before. rewrite Hitem_high, Hitem_pivot.
      apply Hafter. lia.
    + assert (Hitem_k :
        item_at (swap_Znth nil pivot high rows)
          (swap_Znth 0 pivot high lens) k = item_at rows lens k).
      {
        unfold item_at.
        rewrite (swap_Znth_other__pivot_finalization
          nil pivot high k rows Hpivot_bound Hhigh_bound Hk_bound Hki Hkh).
        rewrite (swap_Znth_other__pivot_finalization
          0 pivot high k lens Hpivot_lens Hhigh_lens Hk_lens Hki Hkh).
        reflexivity.
      }
      unfold item_before. rewrite Hitem_k, Hitem_pivot.
      apply Hafter. lia.
Qed.
Lemma sum_swap_Znth__pivot_finalization :
  forall xs i j,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs ->
    sum (swap_Znth 0 i j xs) = sum xs.
Proof.
  intros xs i j Hi Hj.
  pose proof (permutation_swap_Znth__pivot_finalization
    xs i j 0 Hi Hj) as Hperm.
  assert (Hsum_perm : forall l1 l2 : list Z,
    Permutation l1 l2 -> sum l2 = sum l1).
  {
    intros l1 l2 H.
    induction H as
      [|x a b Htail IHtail|x y l|a b c Hab IHab Hbc IHbc];
      unfold sum in *; simpl in *.
    - reflexivity.
    - f_equal. exact IHtail.
    - lia.
    - rewrite IHbc, IHab. reflexivity.
  }
  apply Hsum_perm. exact Hperm.
Qed.
Lemma paired_permutation_refl__quicksort_range_composition :
  forall rows lens,
    Zlength rows = Zlength lens ->
    PairedPermutation rows rows lens lens.
Proof.
  intros rows lens Hlen.
  unfold PairedPermutation.
  repeat split; auto using Permutation_refl.
Qed.
Lemma paired_permutation_trans__quicksort_range_composition :
  forall rows0 rows1 rows2 lens0 lens1 lens2,
    PairedPermutation rows0 rows1 lens0 lens1 ->
    PairedPermutation rows1 rows2 lens1 lens2 ->
    PairedPermutation rows0 rows2 lens0 lens2.
Proof.
  intros rows0 rows1 rows2 lens0 lens1 lens2
    [Hlen0 [Hlen1 Hperm01]] [Hlen1' [Hlen2 Hperm12]].
  unfold PairedPermutation.
  split; [exact Hlen0 |].
  split; [exact Hlen2 |].
  eapply Permutation_trans; eauto.
Qed.
Lemma same_outside_paired_range_refl__quicksort_range_composition :
  forall rows lens left right,
    SameOutsidePairedRange rows rows lens lens left right.
Proof.
  intros rows lens left right.
  unfold SameOutsidePairedRange.
  repeat split; auto.
Qed.
Lemma same_outside_paired_range_trans__quicksort_range_composition :
  forall rows0 rows1 rows2 lens0 lens1 lens2 left right,
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left right ->
    SameOutsidePairedRange rows1 rows2 lens1 lens2 left right ->
    SameOutsidePairedRange rows0 rows2 lens0 lens2 left right.
Proof.
  intros rows0 rows1 rows2 lens0 lens1 lens2 left right
    [Hrows01 [Hlens01 Heq01]] [Hrows12 [Hlens12 Heq12]].
  unfold SameOutsidePairedRange.
  split; [lia |].
  split; [lia |].
  intros k Hk Hout.
  assert (Hk1 : 0 <= k < Zlength rows1).
  { rewrite <- Hrows01; exact Hk. }
  rewrite (Heq12 k Hk1 Hout).
  apply Heq01; assumption.
Qed.
Lemma same_outside_paired_range_weaken__quicksort_range_composition :
  forall rows0 rows1 lens0 lens1 left1 right1 left2 right2,
    left2 <= left1 ->
    right1 <= right2 ->
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left1 right1 ->
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left2 right2.
Proof.
  intros rows0 rows1 lens0 lens1 left1 right1 left2 right2
    Hleft Hright [Hrows [Hlens Heq]].
  unfold SameOutsidePairedRange.
  split; [exact Hrows |].
  split; [exact Hlens |].
  intros k Hk Hout.
  apply Heq; [exact Hk |].
  destruct Hout as [Hout | Hout]; [left | right]; lia.
Qed.
Lemma digit_lex_ge_refl__quicksort_range_composition :
  forall xs, digit_lex_ge xs xs.
Proof.
  intros xs.
  unfold digit_lex_ge.
  split; [reflexivity |].
  left; reflexivity.
Qed.
Lemma item_before_or_equal_refl__quicksort_range_composition :
  forall rows lens i,
    item_before_or_equal rows lens i i.
Proof.
  intros rows lens i.
  unfold item_before_or_equal.
  apply digit_lex_ge_refl__quicksort_range_composition.
Qed.
Lemma greedy_sorted_range_base__quicksort_range_composition :
  forall rows lens left right,
    left >= right ->
    GreedySortedRange rows lens left right.
Proof.
  intros rows lens left right Hrange i j [Hi [Hij Hj]].
  assert (i = j) by lia.
  subst j.
  apply item_before_or_equal_refl__quicksort_range_composition.
Qed.
Lemma decimal_fold_acc__quicksort_range_composition :
  forall xs acc,
    fold_left (fun value digit => 10 * value + digit) xs acc =
    acc * 10 ^ Zlength xs +
    fold_left (fun value digit => 10 * value + digit) xs 0.
Proof.
  induction xs as [|x xs IH]; intros acc.
  - simpl. ring.
  - change
      (fold_left (fun value digit => 10 * value + digit) xs
         (10 * acc + x) =
       acc * 10 ^ Zlength (x :: xs) +
       fold_left (fun value digit => 10 * value + digit) xs x).
    rewrite (IH (10 * acc + x)), (IH x), Zlength_cons.
    rewrite Z.pow_succ_r by apply Zlength_nonneg.
    ring.
Qed.
Lemma decimal_fold_app__quicksort_range_composition :
  forall xs ys,
    fold_left (fun value digit => 10 * value + digit) (xs ++ ys) 0 =
    fold_left (fun value digit => 10 * value + digit) xs 0 *
      10 ^ Zlength ys +
    fold_left (fun value digit => 10 * value + digit) ys 0.
Proof.
  intros xs ys.
  rewrite fold_left_app.
  apply decimal_fold_acc__quicksort_range_composition.
Qed.
Lemma decimal_fold_bounds__quicksort_range_composition :
  forall xs,
    Forall (fun digit => 0 <= digit < 10) xs ->
    0 <= fold_left (fun value digit => 10 * value + digit) xs 0 <
         10 ^ Zlength xs.
Proof.
  induction xs as [|x xs IH]; intros Hdigits.
  - simpl. lia.
  - inversion Hdigits as [|? ? Hx Hxs]; subst.
    specialize (IH Hxs).
    simpl fold_left.
    rewrite decimal_fold_acc__quicksort_range_composition.
    rewrite Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg.
    nia.
Qed.
Lemma digit_lex_ge_cons_iff__quicksort_range_composition :
  forall x y xs ys,
    Zlength xs = Zlength ys ->
    (digit_lex_ge (x :: xs) (y :: ys) <->
     y < x \/ (x = y /\ digit_lex_ge xs ys)).
Proof.
  intros x y xs ys Hlen.
  split.
  - intros [_ [Heq | [k [Hk [Hprefix Hdiff]]]]].
    + inversion Heq; subst.
      right; split; [reflexivity |].
      apply digit_lex_ge_refl__quicksort_range_composition.
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * left.
        rewrite !Znth0_cons in Hdiff.
        exact Hdiff.
      * right.
        assert (Hxy : x = y).
        {
          specialize (Hprefix 0 ltac:(lia)).
          rewrite !Znth0_cons in Hprefix.
          exact Hprefix.
        }
        split; [exact Hxy |].
        unfold digit_lex_ge.
        split; [exact Hlen |].
        right.
        exists (k - 1).
        split.
        { rewrite Zlength_cons in Hk. lia. }
        split.
        { intros j Hj.
          specialize (Hprefix (j + 1) ltac:(lia)).
          rewrite !Znth_cons in Hprefix by lia.
          replace (j + 1 - 1) with j in Hprefix by lia.
          exact Hprefix. }
        rewrite !Znth_cons in Hdiff by lia.
        replace (k - 1) with (k - 1) by lia.
        exact Hdiff.
  - intros [Hyx | [Hxy Htail]].
    + unfold digit_lex_ge.
      split; [rewrite !Zlength_cons; lia |].
      right.
      exists 0.
      split.
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      split.
      { intros j Hj. lia. }
      rewrite !Znth0_cons. exact Hyx.
    + subst y.
      destruct Htail as [_ [Heq | [k [Hk [Hprefix Hdiff]]]]].
      * subst ys. apply digit_lex_ge_refl__quicksort_range_composition.
      * unfold digit_lex_ge.
        split; [rewrite !Zlength_cons; lia |].
        right.
        exists (k + 1).
        split.
        { rewrite Zlength_cons. lia. }
        split.
        { intros j Hj.
          destruct (Z.eq_dec j 0) as [-> | Hj0].
          - rewrite !Znth0_cons. reflexivity.
          - rewrite !Znth_cons by lia.
            apply Hprefix. lia. }
        rewrite !Znth_cons by lia.
        replace (k + 1 - 1) with k by lia.
        exact Hdiff.
Qed.
Lemma digit_lex_ge_decimal_iff__quicksort_range_composition :
  forall xs ys,
    Zlength xs = Zlength ys ->
    Forall (fun digit => 0 <= digit < 10) xs ->
    Forall (fun digit => 0 <= digit < 10) ys ->
    (digit_lex_ge xs ys <->
     fold_left (fun value digit => 10 * value + digit) xs 0 >=
     fold_left (fun value digit => 10 * value + digit) ys 0).
Proof.
  induction xs as [|x xs IH]; intros ys Hlen Hxs Hys;
    destruct ys as [|y ys].
  - simpl. split; intros; [lia |].
    apply digit_lex_ge_refl__quicksort_range_composition.
  - rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ys). lia.
  - rewrite Zlength_cons, Zlength_nil in Hlen.
    pose proof (Zlength_nonneg xs). lia.
  - inversion Hxs as [|? ? Hx Hxs']; subst.
    inversion Hys as [|? ? Hy Hys']; subst.
    assert (Htail_len : Zlength xs = Zlength ys).
    { rewrite !Zlength_cons in Hlen. lia. }
    specialize (IH ys Htail_len Hxs' Hys').
    rewrite digit_lex_ge_cons_iff__quicksort_range_composition by
      exact Htail_len.
    change
      (y < x \/ (x = y /\ digit_lex_ge xs ys) <->
       fold_left (fun value digit => 10 * value + digit) xs x >=
       fold_left (fun value digit => 10 * value + digit) ys y).
    rewrite (decimal_fold_acc__quicksort_range_composition xs x),
      (decimal_fold_acc__quicksort_range_composition ys y).
    pose proof (decimal_fold_bounds__quicksort_range_composition xs Hxs')
      as Hbound_xs.
    pose proof (decimal_fold_bounds__quicksort_range_composition ys Hys')
      as Hbound_ys.
    rewrite <- Htail_len.
    rewrite <- Htail_len in Hbound_ys.
    split.
    + intros [Hyx | [Hxy Htail]].
      * nia.
      * subst y. apply IH in Htail. nia.
    + intros Hvalue.
      destruct (Z.lt_trichotomy x y) as [Hxy | [Hxy | Hyx]].
      * exfalso; nia.
      * right. split; [exact Hxy |].
        apply IH. subst y. nia.
      * left. exact Hyx.
Qed.
Lemma concat_digit_order_cross_iff__quicksort_range_composition :
  forall xs ys,
    Forall (fun digit => 0 <= digit < 10) xs ->
    Forall (fun digit => 0 <= digit < 10) ys ->
    (digit_lex_ge (xs ++ ys) (ys ++ xs) <->
     fold_left (fun value digit => 10 * value + digit) xs 0 *
       (10 ^ Zlength ys - 1) >=
     fold_left (fun value digit => 10 * value + digit) ys 0 *
       (10 ^ Zlength xs - 1)).
Proof.
  intros xs ys Hxs Hys.
  rewrite digit_lex_ge_decimal_iff__quicksort_range_composition.
  - rewrite !decimal_fold_app__quicksort_range_composition.
    nia.
  - rewrite !Zlength_app. lia.
  - apply Forall_app. split; assumption.
  - apply Forall_app. split; assumption.
Qed.
Lemma concat_digit_order_trans__quicksort_range_composition :
  forall xs ys zs,
    Forall (fun digit => 0 <= digit < 10) xs ->
    Forall (fun digit => 0 <= digit < 10) ys ->
    Forall (fun digit => 0 <= digit < 10) zs ->
    0 < Zlength xs ->
    0 < Zlength ys ->
    0 < Zlength zs ->
    digit_lex_ge (xs ++ ys) (ys ++ xs) ->
    digit_lex_ge (ys ++ zs) (zs ++ ys) ->
    digit_lex_ge (xs ++ zs) (zs ++ xs).
Proof.
  intros xs ys zs Hxs Hys Hzs Hlenx Hleny Hlenz Hxy Hyz.
  apply (proj2
    (concat_digit_order_cross_iff__quicksort_range_composition xs zs
      Hxs Hzs)).
  apply (proj1
    (concat_digit_order_cross_iff__quicksort_range_composition xs ys
      Hxs Hys)) in Hxy.
  apply (proj1
    (concat_digit_order_cross_iff__quicksort_range_composition ys zs
      Hys Hzs)) in Hyz.
  pose proof (Zpower_gt_1 10 (Zlength xs) ltac:(lia) Hlenx) as Hpowx.
  pose proof (Zpower_gt_1 10 (Zlength ys) ltac:(lia) Hleny) as Hpowy.
  pose proof (Zpower_gt_1 10 (Zlength zs) ltac:(lia) Hlenz) as Hpowz.
  nia.
Qed.
Lemma digit_lex_not_gt_flip__quicksort_range_composition :
  forall xs ys,
    Zlength xs = Zlength ys ->
    Forall (fun digit => 0 <= digit < 10) xs ->
    Forall (fun digit => 0 <= digit < 10) ys ->
    ~ digit_lex_gt xs ys ->
    digit_lex_ge ys xs.
Proof.
  intros xs ys Hlen Hxs Hys Hnot.
  apply (proj2
    (digit_lex_ge_decimal_iff__quicksort_range_composition ys xs
      ltac:(lia) Hys Hxs)).
  destruct (Z_le_gt_dec
    (fold_left (fun value digit => 10 * value + digit) xs 0)
    (fold_left (fun value digit => 10 * value + digit) ys 0))
    as [Hle | Hgt]; [lia |].
  pose proof (proj2
    (digit_lex_ge_decimal_iff__quicksort_range_composition xs ys
      Hlen Hxs Hys) ltac:(lia)) as Hge.
  destruct Hge as [_ [Heq | Hstrict]].
  - subst ys. lia.
  - exfalso. apply Hnot. unfold digit_lex_gt. split; assumption.
Qed.
Lemma Forall_sublist_by_Znth__quicksort_range_composition :
  forall (P : Z -> Prop) (l : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l 0)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhilen Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhilen Hpoint Hn.
  induction n; intros lo hi Hlohi Hhilen Hpoint Hn.
  - assert (hi = lo) by lia. subst hi.
    rewrite Zsublist_nil by lia. constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
    2: { split; [lia | exact Hhilen]. }
    rewrite (@sublist_single Z 0 lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.
Lemma item_digits_properties__quicksort_range_composition :
  forall rows lens count width i,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 < Zlength (item_digits (item_at rows lens i)) /\
    Forall (fun digit => 0 <= digit < 10)
      (item_digits (item_at rows lens i)).
Proof.
  intros rows lens count width i
    [Hrows [Hlens Hitems]] Hi.
  specialize (Hitems i Hi) as
    [Hrowlen [Hitemlen [_ Hdigits]]].
  unfold item_digits, item_at; simpl.
  split.
  - rewrite Zlength_sublist by (rewrite Hrowlen; lia).
    lia.
  - apply Forall_sublist_by_Znth__quicksort_range_composition.
    + lia.
    + rewrite Hrowlen. lia.
    + intros k Hk. specialize (Hdigits k ltac:(lia)). lia.
Qed.
Lemma item_before_or_equal_trans__quicksort_range_composition :
  forall rows lens count width i j k,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    0 <= k < count ->
    item_before_or_equal rows lens i j ->
    item_before_or_equal rows lens j k ->
    item_before_or_equal rows lens i k.
Proof.
  intros rows lens count width i j k Hwf Hi Hj Hk Hij Hjk.
  pose proof (item_digits_properties__quicksort_range_composition
    rows lens count width i Hwf Hi) as [Hleni Hdi].
  pose proof (item_digits_properties__quicksort_range_composition
    rows lens count width j Hwf Hj) as [Hlenj Hdj].
  pose proof (item_digits_properties__quicksort_range_composition
    rows lens count width k Hwf Hk) as [Hlenk Hdk].
  unfold item_before_or_equal in *.
  eapply (concat_digit_order_trans__quicksort_range_composition
    (item_digits (item_at rows lens i))
    (item_digits (item_at rows lens j))
    (item_digits (item_at rows lens k))); eauto.
Qed.
Lemma item_before_implies_or_equal__quicksort_range_composition :
  forall rows lens i j,
    item_before rows lens i j ->
    item_before_or_equal rows lens i j.
Proof.
  intros rows lens i j [Hlen Hstrict].
  unfold item_before_or_equal, digit_lex_ge.
  split; [exact Hlen |]. right; exact Hstrict.
Qed.
Lemma item_not_before_flip__quicksort_range_composition :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < count ->
    ~ item_before rows lens i j ->
    item_before_or_equal rows lens j i.
Proof.
  intros rows lens count width i j Hwf Hi Hj Hnot.
  pose proof (item_digits_properties__quicksort_range_composition
    rows lens count width i Hwf Hi) as [_ Hdi].
  pose proof (item_digits_properties__quicksort_range_composition
    rows lens count width j Hwf Hj) as [_ Hdj].
  unfold item_before in Hnot.
  unfold item_before_or_equal.
  apply digit_lex_not_gt_flip__quicksort_range_composition.
  - rewrite !Zlength_app. lia.
  - apply Forall_app. split; assumption.
  - apply Forall_app. split; assumption.
  - exact Hnot.
Qed.
Lemma Znth_combine__quicksort_range_composition :
  forall {A B : Type} i (xs : list A) (ys : list B) dx dy,
    0 <= i < Zlength xs ->
    Zlength xs = Zlength ys ->
    Znth i (combine xs ys) (dx, dy) = (Znth i xs dx, Znth i ys dy).
Proof.
  intros A B i xs.
  revert i.
  induction xs as [|x xs IH]; intros i ys dx dy Hi Hlen.
  - rewrite Zlength_correct in Hi. simpl in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl.
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * rewrite !Znth0_cons. reflexivity.
      * rewrite !Znth_cons by lia.
        apply IH.
        -- rewrite Zlength_cons in Hi. lia.
        -- rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Zlength_paired_items_eq__quicksort_range_composition :
  forall rows lens,
    Zlength rows = Zlength lens ->
    Zlength (paired_items rows lens) = Zlength rows.
Proof.
  intros rows lens Hlen.
  unfold paired_items.
  revert lens Hlen.
  induction rows as [|row rows IH]; intros lens Hlen;
    destruct lens as [|len lens].
  - reflexivity.
  - rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg lens). lia.
  - rewrite Zlength_cons, Zlength_nil in Hlen.
    pose proof (Zlength_nonneg rows). lia.
  - simpl combine. rewrite !Zlength_cons.
    f_equal. apply IH.
    rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma paired_items_Znth__quicksort_range_composition :
  forall rows lens i,
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    Znth i (paired_items rows lens) (nil, 0) = item_at rows lens i.
Proof.
  intros rows lens i Hlen Hi.
  unfold paired_items, item_at.
  apply Znth_combine__quicksort_range_composition; assumption.
Qed.
Lemma sublist_eq_from_Znth__quicksort_range_composition :
  forall {A : Type} (d : A) (xs ys : list A) lo hi,
    Zlength xs = Zlength ys ->
    0 <= lo <= hi ->
    hi <= Zlength xs ->
    (forall k, lo <= k < hi -> Znth k xs d = Znth k ys d) ->
    sublist lo hi xs = sublist lo hi ys.
Proof.
  intros A d xs ys lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi xs) (sublist lo hi ys) d)).
  split.
  - repeat rewrite Zlength_correct.
    repeat rewrite sublist_length by
      (try exact Hlohi; try rewrite <- Hlen; exact Hhilen).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    { rewrite Zlength_sublist in Hi by lia. exact Hi. }
    rewrite (@Znth_sublist_lt A d lo hi xs i).
    2: exact Hlohi.
    2: exact Hhilen.
    2: exact Hi'.
    rewrite (@Znth_sublist_lt A d lo hi ys i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint. lia.
Qed.
Lemma list_decompose_sublist__quicksort_range_composition :
  forall {A : Type} (xs : list A) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength xs ->
    xs = sublist 0 lo xs ++ sublist lo hi xs ++
         sublist hi (Zlength xs) xs.
Proof.
  intros A xs lo hi Hlohi Hhilen.
  rewrite <- (sublist_self xs (Zlength xs)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength xs) lo xs).
  2: lia.
  2: { split; [transitivity hi; lia | lia]. }
  rewrite (sublist_split lo (Zlength xs) hi xs).
  2: lia.
  2: { split; [exact Hhilen | lia]. }
  reflexivity.
Qed.
Lemma paired_items_outside_sublist_eq__quicksort_range_composition :
  forall rows0 rows1 lens0 lens1 lo hi left right,
    Zlength rows0 = Zlength lens0 ->
    Zlength rows1 = Zlength lens1 ->
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left right ->
    0 <= lo <= hi ->
    hi <= Zlength rows0 ->
    (forall k, lo <= k < hi -> k < left \/ right < k) ->
    sublist lo hi (paired_items rows1 lens1) =
    sublist lo hi (paired_items rows0 lens0).
Proof.
  intros rows0 rows1 lens0 lens1 lo hi left right
    Hlen0 Hlen1 [Hrows [Hlens Heq]] Hlohi Hhi Houtside.
  apply sublist_eq_from_Znth__quicksort_range_composition
    with (d := (nil, 0)).
  - rewrite !Zlength_paired_items_eq__quicksort_range_composition
      by assumption.
    lia.
  - exact Hlohi.
  - rewrite Zlength_paired_items_eq__quicksort_range_composition
      by assumption.
    lia.
  - intros k Hk.
    rewrite paired_items_Znth__quicksort_range_composition
      by (try assumption; rewrite <- Hrows; lia).
    rewrite paired_items_Znth__quicksort_range_composition
      by (try assumption; lia).
    apply Heq; [lia | apply Houtside; exact Hk].
Qed.
Lemma paired_middle_permutation__quicksort_range_composition :
  forall rows0 rows1 lens0 lens1 left right,
    PairedPermutation rows0 rows1 lens0 lens1 ->
    SameOutsidePairedRange rows0 rows1 lens0 lens1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength rows0 ->
    Permutation
      (sublist left (right + 1) (paired_items rows0 lens0))
      (sublist left (right + 1) (paired_items rows1 lens1)).
Proof.
  intros rows0 rows1 lens0 lens1 left right
    [Hlen0 [Hlen1 Hperm]] Hsame Hbounds Hright.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hrows [Hlens Heq]].
  assert (Hplen0 : Zlength (paired_items rows0 lens0) = Zlength rows0).
  { apply Zlength_paired_items_eq__quicksort_range_composition; exact Hlen0. }
  assert (Hplen1 : Zlength (paired_items rows1 lens1) = Zlength rows1).
  { apply Zlength_paired_items_eq__quicksort_range_composition; exact Hlen1. }
  assert (Hprefix :
    sublist 0 left (paired_items rows1 lens1) =
    sublist 0 left (paired_items rows0 lens0)).
  {
    eapply paired_items_outside_sublist_eq__quicksort_range_composition.
    - exact Hlen0.
    - exact Hlen1.
    - exact Hsame0.
    - lia.
    - lia.
    - intros k Hk. left. lia.
  }
  assert (Hsuffix :
    sublist (right + 1) (Zlength rows0) (paired_items rows1 lens1) =
    sublist (right + 1) (Zlength rows0) (paired_items rows0 lens0)).
  {
    eapply paired_items_outside_sublist_eq__quicksort_range_composition.
    - exact Hlen0.
    - exact Hlen1.
    - exact Hsame0.
    - lia.
    - lia.
    - intros k Hk. right. lia.
  }
  rewrite (list_decompose_sublist__quicksort_range_composition
    (paired_items rows0 lens0) left (right + 1)
    Hbounds ltac:(rewrite Hplen0; lia)) in Hperm.
  rewrite (list_decompose_sublist__quicksort_range_composition
    (paired_items rows1 lens1) left (right + 1)
    Hbounds ltac:(rewrite Hplen1, <- Hrows; lia)) in Hperm.
  rewrite Hplen0, Hplen1, <- Hrows in Hperm.
  rewrite Hprefix, Hsuffix in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma Forall_sublist_by_Znth_pair__quicksort_range_composition :
  forall (P : number_item -> Prop) xs lo hi,
    0 <= lo <= hi ->
    hi <= Zlength xs ->
    (forall k, lo <= k < hi -> P (Znth k xs (nil, 0))) ->
    Forall P (sublist lo hi xs).
Proof.
  intros P xs lo hi Hlohi Hhilen Hpoint.
  apply (proj2 (@Forall_nth number_item P (sublist lo hi xs))).
  intros n d Hn.
  rewrite (@nth_indep number_item (sublist lo hi xs) n d (nil, 0) Hn).
  assert (Hindex : 0 <= Z.of_nat n < Zlength (sublist lo hi xs)).
  {
    rewrite Zlength_correct.
    split; [lia |]. apply Nat2Z.inj_lt. exact Hn.
  }
  rewrite <- (Nat2Z.id n).
  change (P (Znth (Z.of_nat n) (sublist lo hi xs) (nil, 0))).
  assert (Hsubindex : 0 <= Z.of_nat n < hi - lo).
  { rewrite Zlength_sublist in Hindex by lia. exact Hindex. }
  pose proof (@Znth_sublist_lt number_item (nil, 0) lo hi xs
    (Z.of_nat n) Hlohi Hhilen Hsubindex) as Hnth.
  pose proof (Hpoint (lo + Z.of_nat n) ltac:(lia)) as HP.
  exact (eq_rect _ P HP _ (eq_sym Hnth)).
Qed.
Lemma Forall_permutation_pair__quicksort_range_composition :
  forall (P : number_item -> Prop) xs ys,
    Permutation xs ys ->
    Forall P xs ->
    Forall P ys.
Proof.
  intros P xs ys Hperm.
  induction Hperm; intros HForall.
  - exact HForall.
  - inversion HForall; subst. constructor; auto.
  - repeat match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end.
    constructor; auto.
  - apply IHHperm2, IHHperm1. exact HForall.
Qed.
Lemma Forall_sublist_Znth_pair__quicksort_range_composition :
  forall (P : number_item -> Prop) xs lo hi k,
    0 <= lo <= hi ->
    hi <= Zlength xs ->
    Forall P (sublist lo hi xs) ->
    lo <= k < hi ->
    P (Znth k xs (nil, 0)).
Proof.
  intros P xs lo hi k Hlohi Hhilen HForall Hk.
  assert (Hidx : 0 <= k - lo < Zlength (sublist lo hi xs)).
  { rewrite Zlength_sublist by lia. lia. }
  apply Forall_forall with
    (x := Znth (k - lo) (sublist lo hi xs) (nil, 0)) in HForall.
  2: {
    unfold Znth. apply nth_In.
    rewrite Zlength_correct in Hidx. lia.
  }
  assert (Hsubidx : 0 <= k - lo < hi - lo).
  { rewrite Zlength_sublist in Hidx by lia. exact Hidx. }
  pose proof (@Znth_sublist_lt number_item (nil, 0) lo hi xs
    (k - lo) Hlohi Hhilen Hsubidx) as Hnth.
  replace (lo + (k - lo)) with k in Hnth by lia.
  exact (eq_rect _ P HForall _ Hnth).
Qed.
Lemma greedy_partitioned_preserved_left__quicksort_range_composition :
  forall rows0 rows1 lens0 lens1 count width low high pivot,
    RowsWellFormed rows1 lens1 count width ->
    PairedPermutation rows0 rows1 lens0 lens1 ->
    SameOutsidePairedRange rows0 rows1 lens0 lens1 low (pivot - 1) ->
    0 <= low ->
    high < count ->
    GreedyPartitionedAt rows0 lens0 low high pivot ->
    GreedyPartitionedAt rows1 lens1 low high pivot.
Proof.
  intros rows0 rows1 lens0 lens1 count width low high pivot
    Hwf Hperm Hsame Hlow Hhigh Hpart.
  pose proof Hperm as Hperm0.
  pose proof Hsame as Hsame0.
  destruct Hwf as [Hrows1 [Hlens1 Hitems1]].
  destruct Hperm as [Hlen0 [Hlen1 Hpairperm]].
  destruct Hsame as [Hrows [Hlens Heq]].
  destruct Hpart as [Hp_range [Hleft Hright]].
  assert (Hrows0 : Zlength rows0 = count) by lia.
  assert (Hpivot : item_at rows1 lens1 pivot = item_at rows0 lens0 pivot).
  {
    apply Heq; [lia |]. right. lia.
  }
  split; [exact Hp_range |].
  split.
  - assert (Hmid : Permutation
      (sublist low pivot (paired_items rows0 lens0))
      (sublist low pivot (paired_items rows1 lens1))).
    {
      replace pivot with (pivot - 1 + 1) by lia.
      eapply paired_middle_permutation__quicksort_range_composition;
        eauto; lia.
    }
    assert (Hsrc : Forall
      (fun item =>
        digit_lex_gt
          (item_digits item ++ item_digits (item_at rows0 lens0 pivot))
          (item_digits (item_at rows0 lens0 pivot) ++ item_digits item))
      (sublist low pivot (paired_items rows0 lens0))).
    {
      apply Forall_sublist_by_Znth_pair__quicksort_range_composition.
      + lia.
      + rewrite Zlength_paired_items_eq__quicksort_range_composition
          by exact Hlen0. lia.
      + intros k Hk.
        rewrite paired_items_Znth__quicksort_range_composition
          by (try exact Hlen0; lia).
        unfold item_before in Hleft.
        apply Hleft. lia.
    }
    pose proof (Forall_permutation_pair__quicksort_range_composition
      _ _ _ Hmid Hsrc) as Hdst.
    intros k Hk.
    unfold item_before.
    assert (HP := Forall_sublist_Znth_pair__quicksort_range_composition
      (fun item =>
        digit_lex_gt
          (item_digits item ++ item_digits (item_at rows0 lens0 pivot))
          (item_digits (item_at rows0 lens0 pivot) ++ item_digits item))
      (paired_items rows1 lens1) low pivot k).
    specialize (HP ltac:(lia)).
    specialize (HP ltac:(rewrite Zlength_paired_items_eq__quicksort_range_composition
      by exact Hlen1; lia)).
    specialize (HP Hdst ltac:(lia)).
    rewrite paired_items_Znth__quicksort_range_composition in HP
      by (try exact Hlen1; lia).
    rewrite Hpivot. exact HP.
  - intros k Hk.
    assert (Hitem : item_at rows1 lens1 k = item_at rows0 lens0 k).
    { apply Heq; [lia |]. right. lia. }
    specialize (Hright k Hk).
    unfold item_before in *.
    rewrite Hitem, Hpivot. exact Hright.
Qed.
Lemma greedy_partitioned_preserved_right__quicksort_range_composition :
  forall rows0 rows1 lens0 lens1 count width low high pivot,
    RowsWellFormed rows1 lens1 count width ->
    PairedPermutation rows0 rows1 lens0 lens1 ->
    SameOutsidePairedRange rows0 rows1 lens0 lens1 (pivot + 1) high ->
    0 <= low ->
    high < count ->
    GreedyPartitionedAt rows0 lens0 low high pivot ->
    GreedyPartitionedAt rows1 lens1 low high pivot.
Proof.
  intros rows0 rows1 lens0 lens1 count width low high pivot
    Hwf Hperm Hsame Hlow Hhigh Hpart.
  pose proof Hperm as Hperm0.
  pose proof Hsame as Hsame0.
  destruct Hwf as [Hrows1 [Hlens1 Hitems1]].
  destruct Hperm as [Hlen0 [Hlen1 Hpairperm]].
  destruct Hsame as [Hrows [Hlens Heq]].
  destruct Hpart as [Hp_range [Hleft Hright]].
  assert (Hrows0 : Zlength rows0 = count) by lia.
  assert (Hpivot : item_at rows1 lens1 pivot = item_at rows0 lens0 pivot).
  {
    apply Heq; [lia |]. left. lia.
  }
  split; [exact Hp_range |].
  split.
  - intros k Hk.
    assert (Hitem : item_at rows1 lens1 k = item_at rows0 lens0 k).
    { apply Heq; [lia |]. left. lia. }
    specialize (Hleft k Hk).
    unfold item_before in *.
    rewrite Hitem, Hpivot. exact Hleft.
  - assert (Hmid : Permutation
      (sublist (pivot + 1) (high + 1) (paired_items rows0 lens0))
      (sublist (pivot + 1) (high + 1) (paired_items rows1 lens1))).
    {
      eapply paired_middle_permutation__quicksort_range_composition;
        eauto; lia.
    }
    assert (Hsrc : Forall
      (fun item =>
        ~ digit_lex_gt
          (item_digits item ++ item_digits (item_at rows0 lens0 pivot))
          (item_digits (item_at rows0 lens0 pivot) ++ item_digits item))
      (sublist (pivot + 1) (high + 1) (paired_items rows0 lens0))).
    {
      apply Forall_sublist_by_Znth_pair__quicksort_range_composition.
      + lia.
      + rewrite Zlength_paired_items_eq__quicksort_range_composition
          by exact Hlen0. lia.
      + intros k Hk.
        rewrite paired_items_Znth__quicksort_range_composition
          by (try exact Hlen0; lia).
        unfold item_before in Hright.
        apply Hright. lia.
    }
    pose proof (Forall_permutation_pair__quicksort_range_composition
      _ _ _ Hmid Hsrc) as Hdst.
    intros k Hk.
    unfold item_before.
    assert (HP := Forall_sublist_Znth_pair__quicksort_range_composition
      (fun item =>
        ~ digit_lex_gt
          (item_digits item ++ item_digits (item_at rows0 lens0 pivot))
          (item_digits (item_at rows0 lens0 pivot) ++ item_digits item))
      (paired_items rows1 lens1) (pivot + 1) (high + 1) k).
    specialize (HP ltac:(lia)).
    specialize (HP ltac:(rewrite Zlength_paired_items_eq__quicksort_range_composition
      by exact Hlen1; lia)).
    specialize (HP Hdst ltac:(lia)).
    rewrite paired_items_Znth__quicksort_range_composition in HP
      by (try exact Hlen1; lia).
    rewrite Hpivot. exact HP.
Qed.
Lemma greedy_sorted_range_preserved_outside__quicksort_range_composition :
  forall rows0 rows1 lens0 lens1 change_left change_right left right,
    SameOutsidePairedRange
      rows0 rows1 lens0 lens1 change_left change_right ->
    0 <= left ->
    right < Zlength rows0 ->
    (forall k, left <= k <= right ->
       k < change_left \/ change_right < k) ->
    GreedySortedRange rows0 lens0 left right ->
    GreedySortedRange rows1 lens1 left right.
Proof.
  intros rows0 rows1 lens0 lens1 change_left change_right left right
    [Hrows [Hlens Heq]] Hleft Hright Houtside Hsorted.
  intros i j [Hi [Hij Hj]].
  assert (Hibounds : 0 <= i < Zlength rows0) by lia.
  assert (Hjbounds : 0 <= j < Zlength rows0) by lia.
  assert (Hieq : item_at rows1 lens1 i = item_at rows0 lens0 i).
  { apply Heq; [exact Hibounds |]. apply Houtside. lia. }
  assert (Hjeq : item_at rows1 lens1 j = item_at rows0 lens0 j).
  { apply Heq; [exact Hjbounds |]. apply Houtside. lia. }
  specialize (Hsorted i j ltac:(lia)).
  unfold item_before_or_equal in *.
  rewrite Hieq, Hjeq.
  exact Hsorted.
Qed.
Lemma greedy_sorted_range_combine__quicksort_range_composition :
  forall rows lens count width low high pivot,
    RowsWellFormed rows lens count width ->
    0 <= low ->
    high < count ->
    GreedyPartitionedAt rows lens low high pivot ->
    GreedySortedRange rows lens low (pivot - 1) ->
    GreedySortedRange rows lens (pivot + 1) high ->
    GreedySortedRange rows lens low high.
Proof.
  intros rows lens count width low high pivot Hwf Hlow Hhigh
    [Hpivot [Hpart_left Hpart_right]] Hsorted_left Hsorted_right.
  intros i j [Hi [Hij Hj]].
  assert (Hip : i <= pivot \/ pivot < i) by lia.
  assert (Hjp : j < pivot \/ pivot <= j) by lia.
  destruct Hip as [Hip | Hip]; destruct Hjp as [Hjp | Hjp].
  - apply Hsorted_left. lia.
  - assert (Hi_cases : i < pivot \/ i = pivot) by lia.
    assert (Hj_cases : j = pivot \/ pivot < j) by lia.
    destruct Hi_cases as [Hi_lt | ->]; destruct Hj_cases as [-> | Hj_gt].
    + apply item_before_implies_or_equal__quicksort_range_composition.
      apply Hpart_left. lia.
    + eapply item_before_or_equal_trans__quicksort_range_composition
        with (j := pivot); try exact Hwf; try lia.
      * apply item_before_implies_or_equal__quicksort_range_composition.
        apply Hpart_left. lia.
      * apply item_not_before_flip__quicksort_range_composition
          with (count := count) (width := width); try exact Hwf; try lia.
        apply Hpart_right. lia.
    + apply item_before_or_equal_refl__quicksort_range_composition.
    + apply item_not_before_flip__quicksort_range_composition
        with (count := count) (width := width); try exact Hwf; try lia.
      apply Hpart_right. lia.
  - lia.
  - apply Hsorted_right. lia.
Qed.
Lemma ConcatenatedPrefix_zero__output_setup :
  forall rows lens, ConcatenatedPrefix rows lens 0 = nil.
Proof.
  intros rows lens.
  unfold ConcatenatedPrefix, concatenate_rows, concatenate_items, paired_items.
  rewrite !Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma ConcatenatedOutputPrefix_zero__output_setup :
  forall rows lens row_count,
    ConcatenatedOutputPrefix rows lens row_count 0 =
    ConcatenatedPrefix rows lens row_count.
Proof.
  intros rows lens row_count.
  unfold ConcatenatedOutputPrefix.
  rewrite Zsublist_nil by lia.
  apply app_nil_r.
Qed.
Lemma sublist_snoc__output_inner_loop :
  forall {A : Type} (d : A) (xs : list A) i,
    0 <= i < Zlength xs ->
    sublist 0 (i + 1) xs = sublist 0 i xs ++ Znth i xs d :: nil.
Proof.
  intros A d xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single d i xs) by lia.
  reflexivity.
Qed.
Lemma FlatRows_Znth__output_inner_loop :
  forall flat rows count width i j,
    FlatRows flat rows count width ->
    0 <= i < count ->
    0 <= j < width ->
    Znth (i * width + j) flat 0 = Znth j (Znth i rows nil) 0.
Proof.
  intros flat rows count width i j Hflat Hi Hj.
  destruct Hflat as [Hflat_len [Hrows_len Hrow]].
  specialize (Hrow i Hi).
  rewrite Hrow.
  rewrite Znth_sublist by nia.
  replace (j + i * width) with (i * width + j) by lia.
  reflexivity.
Qed.
Lemma Zlength_concatenate_rows_pointwise__output_inner_loop :
  forall rows lens,
    Zlength rows = Zlength lens ->
    (forall k,
       0 <= k < Zlength rows ->
       0 <= Znth k lens 0 <= Zlength (Znth k rows nil)) ->
    Zlength (concatenate_rows rows lens) = sum lens.
Proof.
  induction rows as [| row rows IH]; intros lens Hlen Hbounds.
  - destruct lens as [| len lens].
    + reflexivity.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct lens as [| len lens].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + assert (Hhead : 0 <= len <= Zlength row).
      {
        assert (Hzero : 0 <= 0 < Zlength (row :: rows)).
        { rewrite Zlength_correct. simpl. lia. }
        specialize (Hbounds 0 Hzero).
        unfold Znth in Hbounds. simpl in Hbounds.
        exact Hbounds.
      }
      assert (Htail_len : Zlength rows = Zlength lens) by
        (rewrite !Zlength_correct in Hlen; simpl in Hlen;
         rewrite !Zlength_correct; lia).
      assert (Htail_bounds :
        forall k,
          0 <= k < Zlength rows ->
          0 <= Znth k lens 0 <= Zlength (Znth k rows nil)).
      {
        intros k Hk.
        assert (Hnext : 0 <= k + 1 < Zlength (row :: rows)).
        {
          rewrite Zlength_correct in *.
          simpl in *.
          lia.
        }
        specialize (Hbounds (k + 1) Hnext).
        rewrite (Znth_cons 0 (k + 1) len lens) in Hbounds by lia.
        rewrite (Znth_cons nil (k + 1) row rows) in Hbounds by lia.
        replace (k + 1 - 1) with k in Hbounds by lia.
        exact Hbounds.
      }
      change
        (Zlength (item_digits (row, len) ++ concatenate_rows rows lens) =
         len + sum lens).
      rewrite Zlength_app.
      unfold item_digits at 1. simpl.
      rewrite Zlength_sublist by lia.
      rewrite (IH lens Htail_len Htail_bounds).
      lia.
Qed.
Lemma Zlength_ConcatenatedPrefix__output_inner_loop :
  forall rows lens count width i,
    RowsWellFormed rows lens count width ->
    0 <= i <= count ->
    Zlength (ConcatenatedPrefix rows lens i) = sum (sublist 0 i lens).
Proof.
  intros rows lens count width i Hwf Hi.
  destruct Hwf as [Hrows_len [Hlens_len Hrows]].
  unfold ConcatenatedPrefix.
  apply Zlength_concatenate_rows_pointwise__output_inner_loop.
  - rewrite !Zlength_sublist0 by lia.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist0 in Hk by lia.
    rewrite !Znth_sublist0 by lia.
    specialize (Hrows k ltac:(lia)).
    destruct Hrows as [Hrow_len [Hlen_bounds Hdigits]].
    lia.
Qed.
Lemma sum_nonnegative_pointwise__output_inner_loop :
  forall xs,
    (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0) ->
    0 <= sum xs.
Proof.
  induction xs as [| x xs IH]; intros Hnonneg; simpl.
  - lia.
  - assert (Hx : 0 <= x).
    {
      assert (Hzero : 0 <= 0 < Zlength (x :: xs)).
      { rewrite Zlength_correct. simpl. lia. }
      specialize (Hnonneg 0 Hzero).
      unfold Znth in Hnonneg. simpl in Hnonneg.
      exact Hnonneg.
    }
    assert (Htail : forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0).
    {
      intros k Hk.
      assert (Hnext : 0 <= k + 1 < Zlength (x :: xs)).
      {
        rewrite Zlength_correct in *.
        simpl in *.
        lia.
      }
      specialize (Hnonneg (k + 1) Hnext).
      rewrite (Znth_cons 0 (k + 1) x xs) in Hnonneg by lia.
      replace (k + 1 - 1) with k in Hnonneg by lia.
      exact Hnonneg.
    }
    specialize (IH Htail).
    lia.
Qed.
Lemma sum_prefix_plus_digit_lt_total__output_inner_loop :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < Znth i lens 0 ->
    sum (sublist 0 i lens) + j < sum lens.
Proof.
  intros rows lens count width i j Hwf Hi Hj.
  destruct Hwf as [Hrows_len [Hlens_len Hrows]].
  assert (Hlens_split :
    lens = sublist 0 i lens ++
           Znth i lens 0 :: sublist (i + 1) count lens).
  {
    symmetry.
    transitivity (sublist 0 count lens).
    - rewrite (sublist_split 0 count i lens) by lia.
      rewrite (sublist_split i count (i + 1) lens) by lia.
      rewrite (sublist_single 0 i lens) by lia.
      reflexivity.
    - apply sublist_self. symmetry. exact Hlens_len.
  }
  assert (Hsuffix : 0 <= sum (sublist (i + 1) count lens)).
  {
    apply sum_nonnegative_pointwise__output_inner_loop.
    intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    specialize (Hrows (k + (i + 1)) ltac:(lia)).
    destruct Hrows as [Hrow_len [Hlen_bounds Hdigits]].
    lia.
  }
  pose proof (f_equal sum Hlens_split) as Hsum.
  rewrite sum_app in Hsum.
  simpl in Hsum.
  lia.
Qed.
Lemma Zlength_ConcatenatedOutputPrefix__output_inner_loop :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j <= Znth i lens 0 ->
    Zlength (ConcatenatedOutputPrefix rows lens i j) =
      sum (sublist 0 i lens) + j.
Proof.
  intros rows lens count width i j Hwf Hi Hj.
  unfold ConcatenatedOutputPrefix.
  rewrite Zlength_app.
  rewrite (Zlength_ConcatenatedPrefix__output_inner_loop
             rows lens count width i Hwf) by lia.
  destruct Hwf as [Hrows_len [Hlens_len Hrows]].
  specialize (Hrows i Hi).
  destruct Hrows as [Hrow_len [Hlen_bounds Hdigits]].
  rewrite Zlength_sublist0 by lia.
  lia.
Qed.
Lemma ConcatenatedOutputPrefix_lt_sum__output_inner_loop :
  forall rows lens count width i j,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < Znth i lens 0 ->
    Zlength (ConcatenatedOutputPrefix rows lens i j) < sum lens.
Proof.
  intros rows lens count width i j Hwf Hi Hj.
  rewrite (Zlength_ConcatenatedOutputPrefix__output_inner_loop
             rows lens count width i j Hwf Hi) by lia.
  eapply sum_prefix_plus_digit_lt_total__output_inner_loop; eauto.
Qed.
Lemma ConcatenatedPrefix_succ__output_inner_loop :
  forall rows lens count width i,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    ConcatenatedPrefix rows lens (i + 1) =
      ConcatenatedPrefix rows lens i ++ item_digits (item_at rows lens i).
Proof.
  intros rows lens count width i Hwf Hi.
  destruct Hwf as [Hrows_len [Hlens_len Hrows]].
  unfold ConcatenatedPrefix, concatenate_rows, concatenate_items,
    paired_items, item_at.
  rewrite (sublist_snoc__output_inner_loop nil rows i) by lia.
  rewrite (sublist_snoc__output_inner_loop 0 lens i) by lia.
  rewrite combine_app.
  2: {
    rewrite !sublist_length by lia.
    reflexivity.
  }
  rewrite map_app, concat_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma ConcatenatedOutputPrefix_append__output_inner_loop :
  forall flat rows lens count width i j,
    FlatRows flat rows count width ->
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    0 <= j < Znth i lens 0 ->
    ConcatenatedOutputPrefix rows lens i j ++
      Znth (i * width + j) flat 0 :: nil =
    ConcatenatedOutputPrefix rows lens i (j + 1).
Proof.
  intros flat rows lens count width i j Hflat Hwf Hi Hj.
  assert (Hdigit :
    Znth (i * width + j) flat 0 = Znth j (Znth i rows nil) 0).
  {
    eapply FlatRows_Znth__output_inner_loop; eauto.
    destruct Hwf as [Hrows_len [Hlens_len Hrows]].
    specialize (Hrows i Hi).
    lia.
  }
  rewrite Hdigit.
  unfold ConcatenatedOutputPrefix.
  rewrite <- app_assoc.
  f_equal.
  symmetry.
  apply sublist_snoc__output_inner_loop.
  destruct Hwf as [Hrows_len [Hlens_len Hrows]].
  specialize (Hrows i Hi).
  lia.
Qed.
Lemma ConcatenatedOutputPrefix_full_row__output_inner_loop :
  forall rows lens count width i,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    ConcatenatedOutputPrefix rows lens i (Znth i lens 0) =
      ConcatenatedPrefix rows lens (i + 1).
Proof.
  intros rows lens count width i Hwf Hi.
  unfold ConcatenatedOutputPrefix.
  rewrite (ConcatenatedPrefix_succ__output_inner_loop
             rows lens count width i Hwf Hi).
  unfold item_digits, item_at.
  reflexivity.
Qed.
Lemma digit_lex_ge_refl__largest_concatenation_final :
  forall xs, digit_lex_ge xs xs.
Proof.
  intros xs.
  unfold digit_lex_ge.
  split; [reflexivity | left; reflexivity].
Qed.
Lemma digit_lex_ge_cons_strict__largest_concatenation_final :
  forall x y xs ys,
    Zlength xs = Zlength ys ->
    y < x ->
    digit_lex_ge (x :: xs) (y :: ys).
Proof.
  intros x y xs ys Hlen Hlt.
  unfold digit_lex_ge.
  split.
  - rewrite !Zlength_cons. lia.
  - right. exists 0.
    split.
    + pose proof (Zlength_nonneg xs).
      rewrite Zlength_cons. lia.
    + split.
      * intros j Hj. lia.
      * rewrite !Znth0_cons. exact Hlt.
Qed.
Lemma digit_lex_ge_cons_same__largest_concatenation_final :
  forall x xs ys,
    digit_lex_ge xs ys ->
    digit_lex_ge (x :: xs) (x :: ys).
Proof.
  intros x xs ys Hge.
  unfold digit_lex_ge in *.
  destruct Hge as [Hlen [Heq | [k [Hk [Hprefix Hlt]]]]].
  - split.
    + rewrite !Zlength_cons. lia.
    + left. now subst ys.
  - split.
    + rewrite !Zlength_cons. lia.
    + right. exists (k + 1).
      split.
      * rewrite Zlength_cons. lia.
      * split.
        -- intros j Hj.
           destruct (Z.eq_dec j 0) as [-> | Hj0].
           ++ rewrite !Znth0_cons. reflexivity.
           ++ rewrite !Znth_cons by lia.
              apply Hprefix. lia.
        -- rewrite !Znth_cons by lia.
           replace (k + 1 - 1) with k by lia.
           exact Hlt.
Qed.
Lemma digit_lex_ge_cons_inv__largest_concatenation_final :
  forall x y xs ys,
    digit_lex_ge (x :: xs) (y :: ys) ->
    Zlength xs = Zlength ys /\
    (y < x \/ (x = y /\ digit_lex_ge xs ys)).
Proof.
  intros x y xs ys Hge.
  unfold digit_lex_ge in Hge.
  destruct Hge as [Hlen [Heq | [k [Hk [Hprefix Hlt]]]]].
  - inversion Heq; subst.
    split; [reflexivity |].
    right. split; [reflexivity |].
    apply digit_lex_ge_refl__largest_concatenation_final.
  - split.
    + rewrite !Zlength_cons in Hlen. lia.
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * left. rewrite !Znth0_cons in Hlt. exact Hlt.
      * right.
        assert (Hxy : x = y).
        { specialize (Hprefix 0 ltac:(lia)).
          rewrite !Znth0_cons in Hprefix.
          exact Hprefix. }
        split; [exact Hxy |].
        unfold digit_lex_ge.
        split.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- right. exists (k - 1).
           split.
           ++ rewrite Zlength_cons in Hk. lia.
           ++ split.
              ** intros j Hj.
                 specialize (Hprefix (j + 1) ltac:(lia)).
                 rewrite !Znth_cons in Hprefix by lia.
                 replace (j + 1 - 1) with j in Hprefix by lia.
                 exact Hprefix.
              ** rewrite !Znth_cons in Hlt by lia.
                 replace (k - 1) with (k - 1) by lia.
                 exact Hlt.
Qed.
Lemma digit_lex_ge_trans__largest_concatenation_final :
  forall xs ys zs,
    digit_lex_ge xs ys ->
    digit_lex_ge ys zs ->
    digit_lex_ge xs zs.
Proof.
  induction xs as [|x xs IH]; intros ys zs Hxy Hyz.
  - unfold digit_lex_ge in Hxy.
    destruct Hxy as [Hlen _].
    destruct ys as [|y ys].
    2: { rewrite Zlength_nil, Zlength_cons in Hlen.
         pose proof (Zlength_nonneg ys). lia. }
    unfold digit_lex_ge in Hyz.
    destruct Hyz as [Hlenz _].
    destruct zs as [|z zs]; [apply digit_lex_ge_refl__largest_concatenation_final|].
    rewrite Zlength_nil, Zlength_cons in Hlenz.
    pose proof (Zlength_nonneg zs). lia.
  - unfold digit_lex_ge in Hxy.
    destruct Hxy as [Hlenxy Hbodyxy].
    destruct ys as [|y ys].
    { rewrite Zlength_cons, Zlength_nil in Hlenxy.
      pose proof (Zlength_nonneg xs). lia. }
    unfold digit_lex_ge in Hyz.
    destruct Hyz as [Hlenyz Hbodyyz].
    destruct zs as [|z zs].
    { rewrite Zlength_cons, Zlength_nil in Hlenyz.
      pose proof (Zlength_nonneg ys). lia. }
    assert (Hxy' : digit_lex_ge (x :: xs) (y :: ys)).
    { unfold digit_lex_ge. split; assumption. }
    assert (Hyz' : digit_lex_ge (y :: ys) (z :: zs)).
    { unfold digit_lex_ge. split; assumption. }
    destruct (digit_lex_ge_cons_inv__largest_concatenation_final
                _ _ _ _ Hxy') as [Hlxy Hcase_xy].
    destruct Hcase_xy as [Hyx | [Hxeqy Htailxy]].
    + destruct (digit_lex_ge_cons_inv__largest_concatenation_final
                  _ _ _ _ Hyz') as [Hlyz Hcase_yz].
      destruct Hcase_yz as [Hzy | [Hyeqz Htailyz]].
      * apply digit_lex_ge_cons_strict__largest_concatenation_final.
        -- rewrite !Zlength_cons in Hlenxy, Hlenyz. lia.
        -- lia.
      * apply digit_lex_ge_cons_strict__largest_concatenation_final.
        -- rewrite !Zlength_cons in Hlenxy, Hlenyz. lia.
        -- rewrite <- Hyeqz. exact Hyx.
    + destruct (digit_lex_ge_cons_inv__largest_concatenation_final
                  _ _ _ _ Hyz') as [Hlyz Hcase_yz].
      destruct Hcase_yz as [Hzy | [Hyeqz Htailyz]].
      * apply digit_lex_ge_cons_strict__largest_concatenation_final.
        -- rewrite !Zlength_cons in Hlenxy, Hlenyz. lia.
        -- rewrite Hxeqy. exact Hzy.
      * subst y z.
        apply digit_lex_ge_cons_same__largest_concatenation_final.
        eapply IH; eauto.
Qed.
Lemma digit_lex_ge_prefix__largest_concatenation_final :
  forall prefix xs ys,
    digit_lex_ge xs ys ->
    digit_lex_ge (prefix ++ xs) (prefix ++ ys).
Proof.
  induction prefix as [|x prefix IH]; intros xs ys Hge; simpl.
  - exact Hge.
  - apply digit_lex_ge_cons_same__largest_concatenation_final.
    apply IH. exact Hge.
Qed.
Lemma digit_lex_ge_suffix__largest_concatenation_final :
  forall xs ys suffix,
    digit_lex_ge xs ys ->
    digit_lex_ge (xs ++ suffix) (ys ++ suffix).
Proof.
  induction xs as [|x xs IH]; intros ys suffix Hge.
  - unfold digit_lex_ge in Hge.
    destruct Hge as [Hlen _].
    destruct ys as [|y ys]; [simpl; apply digit_lex_ge_refl__largest_concatenation_final|].
    rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ys). lia.
  - destruct ys as [|y ys].
    { unfold digit_lex_ge in Hge. destruct Hge as [Hlen _].
      rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg xs). lia. }
    destruct (digit_lex_ge_cons_inv__largest_concatenation_final
                _ _ _ _ Hge) as [Hlen [Hyx | [Hxy Htail]]].
    + simpl. apply digit_lex_ge_cons_strict__largest_concatenation_final.
      * rewrite !Zlength_app. lia.
      * exact Hyx.
    + subst y. simpl.
      apply digit_lex_ge_cons_same__largest_concatenation_final.
      apply IH. exact Htail.
Qed.
Lemma concatenate_items_nil__largest_concatenation_final :
  concatenate_items nil = nil.
Proof. reflexivity. Qed.
Lemma concatenate_items_cons__largest_concatenation_final :
  forall x xs,
    concatenate_items (x :: xs) =
    item_digits x ++ concatenate_items xs.
Proof. reflexivity. Qed.
Lemma concatenate_items_app__largest_concatenation_final :
  forall xs ys,
    concatenate_items (xs ++ ys) =
    concatenate_items xs ++ concatenate_items ys.
Proof.
  intros xs ys.
  unfold concatenate_items.
  rewrite map_app, concat_app.
  reflexivity.
Qed.
Lemma item_moves_after_list__largest_concatenation_final :
  forall x items,
    (forall y,
       In y items ->
       digit_lex_ge
         (item_digits x ++ item_digits y)
         (item_digits y ++ item_digits x)) ->
    digit_lex_ge
      (item_digits x ++ concatenate_items items)
      (concatenate_items items ++ item_digits x).
Proof.
  intros x items.
  induction items as [|y ys IH]; intros Hbefore.
  - simpl. rewrite app_nil_r.
    apply digit_lex_ge_refl__largest_concatenation_final.
  - rewrite concatenate_items_cons__largest_concatenation_final.
    pose proof (Hbefore y (or_introl eq_refl)) as Hxy.
    pose proof
      (digit_lex_ge_suffix__largest_concatenation_final
         _ _ (concatenate_items ys) Hxy) as Hswap.
    assert (Htail :
      digit_lex_ge
        (item_digits x ++ concatenate_items ys)
        (concatenate_items ys ++ item_digits x)).
    { apply IH. intros z Hz. apply Hbefore. now right. }
    pose proof
      (digit_lex_ge_prefix__largest_concatenation_final
         (item_digits y) _ _ Htail) as Hmove.
    rewrite !app_assoc in Hmove.
    rewrite !app_assoc.
    eapply digit_lex_ge_trans__largest_concatenation_final.
    + exact Hswap.
    + exact Hmove.
Qed.
Lemma ordered_items_maximize_concatenation__largest_concatenation_final :
  forall items alternative,
    (forall prefix x middle y suffix,
       items = prefix ++ x :: middle ++ y :: suffix ->
       digit_lex_ge
         (item_digits x ++ item_digits y)
         (item_digits y ++ item_digits x)) ->
    Permutation items alternative ->
    digit_lex_ge
      (concatenate_items items)
      (concatenate_items alternative).
Proof.
  induction items as [|x xs IH]; intros alternative Hordered Hperm.
  - apply Permutation_nil in Hperm. subst alternative.
    apply digit_lex_ge_refl__largest_concatenation_final.
  - assert (Hin : In x alternative).
    { eapply Permutation_in; [exact Hperm | left; reflexivity]. }
    destruct (in_split x alternative Hin) as [prefix [suffix Halternative]].
    subst alternative.
    assert (Hperm_tail : Permutation xs (prefix ++ suffix)).
    { eapply Permutation_cons_app_inv. exact Hperm. }
    assert (Hordered_tail :
      forall before a middle b after,
        xs = before ++ a :: middle ++ b :: after ->
        digit_lex_ge
          (item_digits a ++ item_digits b)
          (item_digits b ++ item_digits a)).
    { intros before a middle b after Hxs.
      apply (Hordered (x :: before) a middle b after).
      simpl. f_equal. exact Hxs. }
    pose proof (IH (prefix ++ suffix) Hordered_tail Hperm_tail) as Htail.
    pose proof
      (digit_lex_ge_prefix__largest_concatenation_final
         (item_digits x) _ _ Htail) as Hwith_head.
    assert (Hcross :
      forall y,
        In y prefix ->
        digit_lex_ge
          (item_digits x ++ item_digits y)
          (item_digits y ++ item_digits x)).
    { intros y Hy.
      assert (Hyrest : In y (prefix ++ suffix)).
      { apply in_or_app. left. exact Hy. }
      assert (Hyxs : In y xs).
      { eapply Permutation_in.
        - apply Permutation_sym. exact Hperm_tail.
        - exact Hyrest. }
      destruct (in_split y xs Hyxs) as [before [after Hxs]].
      apply (Hordered nil x before y after).
      simpl. f_equal. exact Hxs. }
    pose proof
      (item_moves_after_list__largest_concatenation_final
         x prefix Hcross) as Hbubble.
    pose proof
      (digit_lex_ge_suffix__largest_concatenation_final
         _ _ (concatenate_items suffix) Hbubble) as Hbubble_suffix.
    rewrite concatenate_items_cons__largest_concatenation_final.
    rewrite !concatenate_items_app__largest_concatenation_final in Hwith_head.
    rewrite concatenate_items_app__largest_concatenation_final.
    rewrite concatenate_items_cons__largest_concatenation_final.
    rewrite !app_assoc in Hwith_head.
    rewrite !app_assoc.
    eapply digit_lex_ge_trans__largest_concatenation_final.
    + exact Hwith_head.
    + exact Hbubble_suffix.
Qed.
Lemma Zlength_paired_items__largest_concatenation_final :
  forall rows lens,
    Zlength rows = Zlength lens ->
    Zlength (paired_items rows lens) = Zlength rows.
Proof.
  induction rows as [|row rows IH]; intros lens Hlen.
  - destruct lens as [|len lens].
    + reflexivity.
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg lens). lia.
  - destruct lens as [|len lens].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg rows). lia.
    + unfold paired_items in *.
      simpl combine.
      rewrite !Zlength_cons in Hlen |- *.
      f_equal.
      apply IH. lia.
Qed.
Lemma Znth_paired_items__largest_concatenation_final :
  forall rows lens i,
    Zlength rows = Zlength lens ->
    0 <= i < Zlength rows ->
    Znth i (paired_items rows lens) (nil, 0) =
    item_at rows lens i.
Proof.
  induction rows as [|row rows IH]; intros lens i Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct lens as [|len lens].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg rows). lia.
    + change
        (Znth i ((row, len) :: paired_items rows lens) (nil, 0) =
         (Znth i (row :: rows) nil, Znth i (len :: lens) 0)).
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * rewrite !Znth0_cons. reflexivity.
      * rewrite !Znth_cons by lia.
        change
          (Znth (i - 1) (paired_items rows lens) (nil, 0) =
           item_at rows lens (i - 1)).
        apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_at_app_cons__largest_concatenation_final :
  forall (A : Type) (default x : A) prefix suffix,
    Znth (Zlength prefix) (prefix ++ x :: suffix) default = x.
Proof.
  intros A default x prefix.
  induction prefix as [|a prefix IH]; intros suffix.
  - simpl. rewrite Znth0_cons. reflexivity.
  - simpl app.
    pose proof (Zlength_nonneg prefix).
    rewrite Znth_cons by (rewrite Zlength_cons; lia).
    replace (Zlength (a :: prefix) - 1) with (Zlength prefix)
      by (rewrite Zlength_cons; lia).
    apply IH.
Qed.
Lemma greedy_sorted_orders_paired_items__largest_concatenation_final :
  forall rows lens,
    Zlength rows = Zlength lens ->
    GreedySorted rows lens ->
    forall prefix x middle y suffix,
      paired_items rows lens = prefix ++ x :: middle ++ y :: suffix ->
      digit_lex_ge
        (item_digits x ++ item_digits y)
        (item_digits y ++ item_digits x).
Proof.
  intros rows lens Hlen Hsorted prefix x middle y suffix Hitems.
  set (ix := Zlength prefix).
  set (iy := Zlength (prefix ++ x :: middle)).
  assert (Hitems_len : Zlength (paired_items rows lens) = Zlength rows).
  { apply Zlength_paired_items__largest_concatenation_final. exact Hlen. }
  assert (Hbounds : 0 <= ix /\ ix <= iy /\ iy < Zlength rows).
  { subst ix iy.
    rewrite Hitems in Hitems_len.
    rewrite (Zlength_app prefix (x :: middle ++ y :: suffix)) in Hitems_len.
    rewrite (Zlength_cons x (middle ++ y :: suffix)) in Hitems_len.
    rewrite (Zlength_app middle (y :: suffix)) in Hitems_len.
    rewrite (Zlength_cons y suffix) in Hitems_len.
    rewrite (Zlength_app prefix (x :: middle)).
    rewrite (Zlength_cons x middle).
    pose proof (Zlength_nonneg prefix).
    pose proof (Zlength_nonneg middle).
    pose proof (Zlength_nonneg suffix).
    lia. }
  assert (Hix : item_at rows lens ix = x).
  { pose proof
      (Znth_at_app_cons__largest_concatenation_final
         number_item (nil, 0) x prefix (middle ++ y :: suffix)) as Hat.
    rewrite <- Hitems in Hat.
    rewrite Znth_paired_items__largest_concatenation_final in Hat
      by (exact Hlen || lia).
    exact Hat. }
  assert (Hiy : item_at rows lens iy = y).
  { pose proof
      (Znth_at_app_cons__largest_concatenation_final
         number_item (nil, 0) y (prefix ++ x :: middle) suffix) as Hat.
    assert (Hregroup :
      paired_items rows lens = (prefix ++ x :: middle) ++ y :: suffix).
    { rewrite Hitems.
      change
        (prefix ++ ((x :: middle) ++ (y :: suffix)) =
         (prefix ++ (x :: middle)) ++ (y :: suffix)).
      apply app_assoc. }
    rewrite <- Hregroup in Hat.
    rewrite Znth_paired_items__largest_concatenation_final in Hat
      by (exact Hlen || lia).
    exact Hat. }
  specialize (Hsorted ix iy Hbounds).
  unfold item_before_or_equal in Hsorted.
  rewrite Hix, Hiy in Hsorted.
  exact Hsorted.
Qed.
Lemma greedy_sorted_maximizes_concatenate_rows__largest_concatenation_final :
  forall rows lens alternative_rows alternative_lens,
    Zlength rows = Zlength lens ->
    GreedySorted rows lens ->
    Permutation (paired_items rows lens)
                (paired_items alternative_rows alternative_lens) ->
    digit_lex_ge
      (concatenate_rows rows lens)
      (concatenate_rows alternative_rows alternative_lens).
Proof.
  intros rows lens alternative_rows alternative_lens Hlen Hsorted Hperm.
  unfold concatenate_rows.
  eapply ordered_items_maximize_concatenation__largest_concatenation_final.
  - eapply greedy_sorted_orders_paired_items__largest_concatenation_final;
      eauto.
  - exact Hperm.
Qed.
Lemma RowsWellFormed_item_digits_length__largest_concatenation_final :
  forall rows lens count width i,
    RowsWellFormed rows lens count width ->
    0 <= i < count ->
    Zlength (item_digits (item_at rows lens i)) = Znth i lens 0.
Proof.
  intros rows lens count width i Hwf Hi.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hrows [Hlens Hall]].
  specialize (Hall i Hi).
  destruct Hall as [Hrow [Hlen _]].
  unfold item_digits, item_at. simpl.
  apply Zlength_sublist0.
  lia.
Qed.
Lemma concatenate_rows_length_from_items__largest_concatenation_final :
  forall rows lens,
    Zlength rows = Zlength lens ->
    (forall i,
       0 <= i < Zlength rows ->
       Zlength (item_digits (item_at rows lens i)) = Znth i lens 0) ->
    Zlength (concatenate_rows rows lens) = sum lens.
Proof.
  induction rows as [|row rows IH]; intros lens Hlen Hdigits.
  - destruct lens as [|len lens].
    + reflexivity.
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg lens). lia.
  - destruct lens as [|len lens].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg rows). lia.
    + assert (Hhead : Zlength (item_digits (row, len)) = len).
      { specialize (Hdigits 0).
        assert (0 <= 0 < Zlength (row :: rows)).
        { pose proof (Zlength_nonneg rows).
          rewrite Zlength_cons. lia. }
        specialize (Hdigits H).
        unfold item_at in Hdigits.
        rewrite !Znth0_cons in Hdigits.
        exact Hdigits. }
      change
        (Zlength
           (item_digits (row, len) ++
            concatenate_items (paired_items rows lens)) =
         len + sum lens).
      rewrite Zlength_app, Hhead.
      f_equal.
      change (Zlength (concatenate_rows rows lens) = sum lens).
      apply IH.
      * rewrite !Zlength_cons in Hlen. lia.
      * intros i Hi.
        specialize (Hdigits (i + 1)).
        assert (0 <= i + 1 < Zlength (row :: rows))
          by (rewrite Zlength_cons; lia).
        specialize (Hdigits H).
        unfold item_at in Hdigits |- *.
        rewrite !Znth_cons in Hdigits by lia.
        replace (i + 1 - 1) with i in Hdigits by lia.
        exact Hdigits.
Qed.
Lemma RowsWellFormed_concatenate_rows_length__largest_concatenation_final :
  forall rows lens count width,
    RowsWellFormed rows lens count width ->
    Zlength (concatenate_rows rows lens) = sum lens.
Proof.
  intros rows lens count width Hwf.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hrows [Hlens Hall]].
  apply concatenate_rows_length_from_items__largest_concatenation_final.
  - lia.
  - intros i Hi.
    apply RowsWellFormed_item_digits_length__largest_concatenation_final
      with (count := count) (width := width).
    + unfold RowsWellFormed. exact (conj Hrows (conj Hlens Hall)).
    + lia.
Qed.
Lemma ConcatenatedPrefix_full__largest_concatenation_final :
  forall rows lens count width,
    RowsWellFormed rows lens count width ->
    ConcatenatedPrefix rows lens count = concatenate_rows rows lens.
Proof.
  intros rows lens count width Hwf.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [Hrows [Hlens Hall]].
  unfold ConcatenatedPrefix.
  rewrite (sublist_self rows count (eq_sym Hrows)).
  rewrite (sublist_self lens count (eq_sym Hlens)).
  reflexivity.
Qed.
Lemma GreedySorted_LargestConcatenation__largest_concatenation_final :
  forall original_rows arranged_rows original_lens arranged_lens count width,
    RowsWellFormed arranged_rows arranged_lens count width ->
    PairedPermutation original_rows arranged_rows
                      original_lens arranged_lens ->
    GreedySorted arranged_rows arranged_lens ->
    LargestConcatenation
      original_rows arranged_rows original_lens arranged_lens
      (concatenate_rows arranged_rows arranged_lens).
Proof.
  intros original_rows arranged_rows original_lens arranged_lens
         count width Hwf Hpaired Hsorted.
  unfold LargestConcatenation.
  split; [exact Hpaired |].
  split; [reflexivity |].
  intros alternative_rows alternative_lens Halternative.
  unfold PairedPermutation in Hpaired, Halternative.
  destruct Hpaired as [Horiginal [Harranged Hperm_arranged]].
  destruct Halternative as [Horiginal_alt [Halternative_len Hperm_alt]].
  eapply greedy_sorted_maximizes_concatenate_rows__largest_concatenation_final.
  - unfold RowsWellFormed in Hwf. lia.
  - exact Hsorted.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm_arranged.
    + exact Hperm_alt.
Qed.
