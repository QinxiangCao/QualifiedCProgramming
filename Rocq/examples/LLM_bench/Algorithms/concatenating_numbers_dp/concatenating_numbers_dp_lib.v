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

Definition item_at
    (rows : list (list Z)) (lengths : list Z) (i : Z) : number_item :=
  (Znth i rows nil, Znth i lengths 0).

Definition concatenate_indices
    (rows : list (list Z)) (lengths indices : list Z) : list Z :=
  concat (map (fun i => item_digits (item_at rows lengths i)) indices).

Definition all_indices (count : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat count)).

Definition digit_lex_ge (xs ys : list Z) : Prop :=
  Zlength xs = Zlength ys /\
  (xs = ys \/
   exists k,
     0 <= k < Zlength xs /\
     (forall j, 0 <= j < k -> Znth j xs 0 = Znth j ys 0) /\
     Znth k ys 0 < Znth k xs 0).

Definition item_before_or_equal
    (rows : list (list Z)) (lengths : list Z) (i j : Z) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i)).

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

(* Stable semantic state for the comparator scan.  The C locals holding the
   two row lengths are observations of [lens], while [position] records the
   common prefix already compared.  Arithmetic bounds and memory ownership
   remain explicit in the C invariant. *)
Definition ConcatCompareLoopState
    (rows : list (list Z)) (lens : list Z)
    (left right left_length right_length position : Z) : Prop :=
  left_length = Znth left lens 0 /\
  right_length = Znth right lens 0 /\
  ConcatComparePrefix rows lens left right position.

Definition ConcatCompareSignOutcome
    (rows : list (list Z)) (lens : list Z)
    (i j comparison : Z) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j) in
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i) in
  (comparison = 0 /\ lhs = rhs) \/
  (comparison = 1 /\
   exists k,
     0 <= k < Zlength lhs /\
     Zlength lhs = Zlength rhs /\
     (forall p, 0 <= p < k -> Znth p lhs 0 = Znth p rhs 0) /\
     Znth k rhs 0 < Znth k lhs 0) \/
  (comparison = -1 /\
   exists k,
     0 <= k < Zlength lhs /\
     Zlength lhs = Zlength rhs /\
     (forall p, 0 <= p < k -> Znth p lhs 0 = Znth p rhs 0) /\
     Znth k lhs 0 < Znth k rhs 0).

Definition BestIndexForMask
    (rows : list (list Z)) (lens : list Z)
    (count mask index : Z) : Prop :=
  0 <= index < count /\
  Z.testbit mask index = true /\
  forall other,
    0 <= other < count ->
    Z.testbit mask other = true ->
    item_before_or_equal rows lens index other.

(* A semantic table invariant: every materialized nonzero mask stores a
   mathematically greatest first row for that selected subset. *)
Definition DPTablePrefix
    (rows : list (list Z)) (lens : list Z) (count computed : Z)
    (choices : list Z) : Prop :=
  1 <= computed <= Z.shiftl 1 count /\
  Zlength choices = computed /\
  Znth 0 choices 0 = -1 /\
  forall mask,
    1 <= mask < computed ->
    BestIndexForMask rows lens count mask (Znth mask choices 0).

Definition BitScanState
    (mask count bit bit_value : Z) : Prop :=
  1 <= mask < Z.shiftl 1 count /\
  0 <= bit <= count /\
  bit_value = Z.shiftl 1 bit /\
  (forall lower,
     0 <= lower < bit -> Z.testbit mask lower = false).

Definition SelectedBitState
    (mask count bit bit_value rest : Z) : Prop :=
  BitScanState mask count bit bit_value /\
  Z.land mask bit_value <> 0 /\
  0 <= bit < count /\
  Z.testbit mask bit = true /\
  rest = Z.lxor mask bit_value /\
  0 <= rest < mask.

Definition MaskIndexes (count mask : Z) (indices : list Z) : Prop :=
  forall index,
    In index indices <->
    0 <= index < count /\ Z.testbit mask index = true.

(* The output loop has consumed [done] and still owns exactly the rows whose
   bits occur in [mask].  The concatenation of [done ++ todo] is a global
   optimum, so this describes a mathematical optimal-prefix state rather
   than an execution trace of the C loop. *)
Definition LargestConcatenation
    (rows : list (list Z)) (lens output : list Z) : Prop :=
  exists order,
    Permutation (all_indices (Zlength rows)) order /\
    output = concatenate_indices rows lens order /\
    forall alternative,
      Permutation (all_indices (Zlength rows)) alternative ->
      digit_lex_ge output (concatenate_indices rows lens alternative).

Definition GreedyOutputPrefix
    (rows : list (list Z)) (lens : list Z)
    (count mask : Z) (output : list Z) : Prop :=
  exists done todo,
    Permutation (all_indices count) (done ++ todo) /\
    MaskIndexes count mask todo /\
    output = concatenate_indices rows lens done /\
    LargestConcatenation rows lens
      (concatenate_indices rows lens (done ++ todo)).

Definition AppendRowPrefix
    (rows : list (list Z)) (lens : list Z)
    (prior : list Z) (index position : Z) (current : list Z) : Prop :=
  current = prior ++
    sublist 0 position (item_digits (item_at rows lens index)).

Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.ZArith.Zbitwise.
Require Import Coq.Logic.ClassicalDescription.
Lemma ConcatComparePrefix_zero__compare_bounds :
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
Lemma flat_rows_cell_lookup__compare_digits :
  forall flat rows count width row offset,
    FlatRows flat rows count width ->
    0 <= row < count ->
    0 <= offset < width ->
    Znth (row * width + offset) flat 0 =
      Znth offset (Znth row rows nil) 0.
Proof.
  intros flat rows count width row offset Hflat Hrow Hoff.
  unfold FlatRows in Hflat.
  destruct Hflat as (_ & _ & Hrows).
  specialize (Hrows row Hrow).
  assert (Hwidth : 0 <= width) by lia.
  assert (Hstart : 0 <= row * width).
  { apply Z.mul_nonneg_nonneg; lia. }
  rewrite Hrows, Znth_sublist.
  2: exact Hstart.
  2: { replace ((row + 1) * width - row * width) with width by ring.
       lia. }
  f_equal; lia.
Qed.
Lemma concat_digit_lookup__compare_digits :
  forall flat rows lens count width left right left_length right_length position,
    RowsWellFormed rows lens count width ->
    FlatRows flat rows count width ->
    0 <= left < count ->
    0 <= right < count ->
    left_length = Znth left lens 0 ->
    right_length = Znth right lens 0 ->
    (0 <= position < left_length ->
       Znth (left * width + position) flat 0 =
       ConcatLeftDigit rows lens left right position) /\
    (left_length <= position < left_length + right_length ->
       Znth (right * width + position - left_length) flat 0 =
       ConcatLeftDigit rows lens left right position) /\
    (0 <= position < right_length ->
       Znth (right * width + position) flat 0 =
       ConcatRightDigit rows lens left right position) /\
    (right_length <= position < right_length + left_length ->
       Znth (left * width + position - right_length) flat 0 =
       ConcatRightDigit rows lens left right position).
Proof.
  intros flat rows lens count width left right left_length right_length
    position Hwf Hflat Hleft Hright Hleft_length Hright_length.
  destruct Hwf as (_ & _ & Hwf).
  pose proof (Hwf left Hleft) as
    (Hleft_row_length & Hleft_length_bounds & _ & _).
  pose proof (Hwf right Hright) as
    (Hright_row_length & Hright_length_bounds & _ & _).
  assert (Hleft_digits_length :
    Zlength (sublist 0 (Znth left lens 0) (Znth left rows nil)) =
      left_length).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hright_digits_length :
    Zlength (sublist 0 (Znth right lens 0) (Znth right rows nil)) =
      right_length).
  { rewrite Zlength_sublist by lia. lia. }
  repeat split; intro Hposition.
  - rewrite flat_rows_cell_lookup__compare_digits with
      (rows := rows) (count := count) (row := left) by auto with zarith.
    unfold ConcatLeftDigit, item_digits, item_at.
    assert (Hposition_left :
      0 <= position <
        Zlength (sublist 0 (Znth left lens 0) (Znth left rows nil))).
    { rewrite Hleft_digits_length; lia. }
    rewrite app_Znth1 by exact Hposition_left.
    rewrite Znth_sublist0.
    2: { rewrite <- Hleft_length. exact Hposition. }
    reflexivity.
  - replace (right * width + position - left_length) with
      (right * width + (position - left_length)) by ring.
    rewrite flat_rows_cell_lookup__compare_digits with
      (rows := rows) (count := count) (row := right) by auto with zarith.
    unfold ConcatLeftDigit, item_digits, item_at.
    assert (Hposition_left :
      position >=
        Zlength (sublist 0 (Znth left lens 0) (Znth left rows nil))).
    { rewrite Hleft_digits_length; lia. }
    rewrite app_Znth2 by exact Hposition_left.
    rewrite Znth_sublist0.
    2: { rewrite Zlength_sublist by (cbn; lia). cbn. lia. }
    change
      (Znth (position - left_length) (Znth right rows nil) 0 =
       Znth
         (position -
          Zlength (sublist 0 (Znth left lens 0) (Znth left rows nil)))
         (Znth right rows nil) 0).
    rewrite Hleft_digits_length.
    reflexivity.
  - rewrite flat_rows_cell_lookup__compare_digits with
      (rows := rows) (count := count) (row := right) by auto with zarith.
    unfold ConcatRightDigit, item_digits, item_at.
    assert (Hposition_right :
      0 <= position <
        Zlength (sublist 0 (Znth right lens 0) (Znth right rows nil))).
    { rewrite Hright_digits_length; lia. }
    rewrite app_Znth1 by exact Hposition_right.
    rewrite Znth_sublist0.
    2: { rewrite <- Hright_length. exact Hposition. }
    reflexivity.
  - replace (left * width + position - right_length) with
      (left * width + (position - right_length)) by ring.
    rewrite flat_rows_cell_lookup__compare_digits with
      (rows := rows) (count := count) (row := left) by auto with zarith.
    unfold ConcatRightDigit, item_digits, item_at.
    assert (Hposition_right :
      position >=
        Zlength (sublist 0 (Znth right lens 0) (Znth right rows nil))).
    { rewrite Hright_digits_length; lia. }
    rewrite app_Znth2 by exact Hposition_right.
    rewrite Znth_sublist0.
    2: { rewrite Zlength_sublist by (cbn; lia). cbn. lia. }
    change
      (Znth (position - right_length) (Znth left rows nil) 0 =
       Znth
         (position -
          Zlength (sublist 0 (Znth right lens 0) (Znth right rows nil)))
         (Znth left rows nil) 0).
    rewrite Hright_digits_length.
    reflexivity.
Qed.
Lemma item_digits_Zlength__compare_semantics :
  forall rows lens count width index,
    RowsWellFormed rows lens count width ->
    0 <= index < count ->
    Zlength (item_digits (item_at rows lens index)) = Znth index lens 0.
Proof.
  intros rows lens count width index Hwf Hindex.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as (_ & _ & Hrow).
  specialize (Hrow index Hindex).
  destruct Hrow as (Hrow_length & Hitem_length & _).
  unfold item_digits, item_at.
  simpl.
  rewrite Zlength_sublist by lia.
  lia.
Qed.
Lemma concat_pair_Zlength__compare_semantics :
  forall rows lens count width left right,
    RowsWellFormed rows lens count width ->
    0 <= left < count ->
    0 <= right < count ->
    Zlength
      (item_digits (item_at rows lens left) ++
       item_digits (item_at rows lens right)) =
      Znth left lens 0 + Znth right lens 0.
Proof.
  intros rows lens count width left right Hwf Hleft Hright.
  rewrite Zlength_app.
  rewrite (item_digits_Zlength__compare_semantics
    rows lens count width left Hwf Hleft).
  rewrite (item_digits_Zlength__compare_semantics
    rows lens count width right Hwf Hright).
  reflexivity.
Qed.
Lemma concat_compare_prefix_step__compare_semantics :
  forall rows lens count width left right left_length right_length position,
    RowsWellFormed rows lens count width ->
    0 <= left < count ->
    0 <= right < count ->
    ConcatCompareLoopState
      rows lens left right left_length right_length position ->
    position < left_length + right_length ->
    ConcatLeftDigit rows lens left right position =
      ConcatRightDigit rows lens left right position ->
    ConcatCompareLoopState
      rows lens left right left_length right_length (position + 1).
Proof.
  intros rows lens count width left right left_length right_length position
    Hwf Hleft Hright Hstate Hposition Hequal.
  unfold ConcatCompareLoopState in *.
  destruct Hstate as (Hleft_length & Hright_length & Hprefix).
  split; [exact Hleft_length |].
  split; [exact Hright_length |].
  unfold ConcatComparePrefix in *.
  destruct Hprefix as (Hposition_bounds & Hsame_length & Hbefore).
  split.
  - pose proof (concat_pair_Zlength__compare_semantics
      rows lens count width left right Hwf Hleft Hright) as Hlength.
    rewrite <- Hleft_length, <- Hright_length in Hlength.
    lia.
  - split; [exact Hsame_length |].
    intros k Hk.
    destruct (Z_lt_ge_dec k position) as [Hbefore_position | Hat_position].
    + apply Hbefore; lia.
    + assert (k = position) by lia.
      subst k.
      unfold ConcatLeftDigit, ConcatRightDigit in Hequal.
      exact Hequal.
Qed.
Lemma concat_compare_outcome_at_difference__compare_semantics :
  forall rows lens count width left right left_length right_length
    position comparison,
    RowsWellFormed rows lens count width ->
    0 <= left < count ->
    0 <= right < count ->
    ConcatCompareLoopState
      rows lens left right left_length right_length position ->
    position < left_length + right_length ->
    ((comparison = -1 /\
      ConcatLeftDigit rows lens left right position <
        ConcatRightDigit rows lens left right position) \/
     (comparison = 1 /\
      ConcatRightDigit rows lens left right position <
        ConcatLeftDigit rows lens left right position)) ->
    ConcatCompareSignOutcome rows lens left right comparison.
Proof.
  intros rows lens count width left right left_length right_length
    position comparison Hwf Hleft Hright Hstate Hposition Hcomparison.
  unfold ConcatCompareLoopState in Hstate.
  destruct Hstate as (Hleft_length & Hright_length & Hprefix).
  unfold ConcatComparePrefix in Hprefix.
  destruct Hprefix as (Hposition_bounds & Hsame_length & Hbefore).
  pose proof (concat_pair_Zlength__compare_semantics
    rows lens count width left right Hwf Hleft Hright) as Hlength.
  rewrite <- Hleft_length, <- Hright_length in Hlength.
  unfold ConcatCompareSignOutcome.
  destruct Hcomparison as [[Hcomparison Hdigit] | [Hcomparison Hdigit]];
    subst comparison.
  - right; right.
    split; [reflexivity |].
    exists position.
    repeat split.
    + lia.
    + lia.
    + exact Hsame_length.
    + exact Hbefore.
    + unfold ConcatLeftDigit, ConcatRightDigit in Hdigit.
      exact Hdigit.
  - right; left.
    split; [reflexivity |].
    exists position.
    repeat split.
    + lia.
    + lia.
    + exact Hsame_length.
    + exact Hbefore.
    + unfold ConcatLeftDigit, ConcatRightDigit in Hdigit.
      exact Hdigit.
Qed.
Lemma concat_compare_outcome_at_end__compare_semantics :
  forall rows lens count width left right left_length right_length position,
    RowsWellFormed rows lens count width ->
    0 <= left < count ->
    0 <= right < count ->
    ConcatCompareLoopState
      rows lens left right left_length right_length position ->
    position >= left_length + right_length ->
    position <= left_length + right_length ->
    ConcatCompareSignOutcome rows lens left right 0.
Proof.
  intros rows lens count width left right left_length right_length position
    Hwf Hleft Hright Hstate Hposition_lower Hposition_upper.
  unfold ConcatCompareLoopState in Hstate.
  destruct Hstate as (Hleft_length & Hright_length & Hprefix).
  unfold ConcatComparePrefix in Hprefix.
  destruct Hprefix as (Hposition_bounds & Hsame_length & Hbefore).
  pose proof (concat_pair_Zlength__compare_semantics
    rows lens count width left right Hwf Hleft Hright) as Hlength.
  rewrite <- Hleft_length, <- Hright_length in Hlength.
  assert (Hposition :
    position =
      Zlength
        (item_digits (item_at rows lens left) ++
         item_digits (item_at rows lens right))) by lia.
  unfold ConcatCompareSignOutcome.
  left.
  split; [reflexivity |].
  apply (list_eq_nth Z
    (item_digits (item_at rows lens left) ++
     item_digits (item_at rows lens right))
    (item_digits (item_at rows lens right) ++
     item_digits (item_at rows lens left)) 0).
  - rewrite !Zlength_correct in Hsame_length.
    lia.
  - intros n Hn.
    rewrite <- (Nat2Z.id n).
    apply Hbefore.
    split; [lia |].
    rewrite Hposition, Zlength_correct.
    lia.
Qed.
Lemma dp_table_prefix_singleton__dp_initialization :
  forall rows lens count,
    1 <= Z.shiftl 1 count ->
    DPTablePrefix rows lens count 1 (-1 :: nil).
Proof.
  intros rows lens count Hshift.
  unfold DPTablePrefix.
  repeat split; cbn; try lia.
Qed.
Lemma signed_last_nbits_double_power__bit_scan :
  forall bit_value state_count count,
    1 <= bit_value ->
    bit_value <= state_count ->
    state_count = Z.shiftl 1 count ->
    count <= 20 ->
    - 2 ^ (32 - 1) <= bit_value * 2 ^ 1 < 2 ^ (32 - 1).
Proof.
  intros bit_value state_count count Hpositive Hbounded Hstate Hcount.
  change (-2147483648 <= bit_value * 2 < 2147483648).
  rewrite Z.shiftl_1_l in Hstate.
  assert (Hpow : 2 ^ count <= 2 ^ 20).
  { apply Z.pow_le_mono_r; lia. }
  rewrite <- Hstate in Hpow.
  change (state_count <= 1048576) in Hpow.
  clear Hstate Hcount count.
  split.
  - assert (0 <= bit_value * 2).
    { apply Z.mul_nonneg_nonneg; lia. }
    lia.
  - assert (bit_value * 2 <= 1048576 * 2).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia.
Qed.
Lemma bit_scan_advance__bit_scan :
  forall mask count bit bit_value,
    BitScanState mask count bit bit_value ->
    Z.land mask bit_value = 0 ->
    bit < count /\
    Z.testbit mask bit = false /\
    bit_value * 2 = Z.shiftl 1 (bit + 1) /\
    1 <= bit_value * 2 /\
    bit_value * 2 <= Z.shiftl 1 count /\
    (forall lower,
       0 <= lower < bit + 1 -> Z.testbit mask lower = false).
Proof.
  intros mask count bit bit_value Hscan Hland.
  unfold BitScanState in Hscan.
  destruct Hscan as (Hmask & Hbit & Hvalue & Hlower).
  assert (Hlog : Z.log2 mask < count).
  { apply (proj1 (Z.log2_lt_pow2 mask count ltac:(lia))).
    rewrite <- Z.shiftl_1_l.
    lia. }
  assert (Hbitlt : bit < count).
  { assert (Hlog_nonneg : 0 <= Z.log2 mask) by apply Z.log2_nonneg.
    assert (Hneq : bit <> count).
    { intro Heq; subst bit.
      pose proof (Z.bit_log2 mask ltac:(lia)) as Hset.
      pose proof (Hlower (Z.log2 mask) ltac:(lia)) as Hclear.
      congruence. }
    lia. }
  assert (Hmaskbit : Z.testbit mask bit = false).
  { assert (Hlandbit : Z.testbit (Z.land mask bit_value) bit = false).
    { rewrite Hland, Z.testbit_0_l; reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hvaluebit : Z.testbit bit_value bit = true).
    { rewrite Hvalue, Z.shiftl_spec by lia.
      replace (bit - bit) with 0 by lia.
      reflexivity. }
    rewrite Hvaluebit in Hlandbit.
    rewrite Bool.andb_true_r in Hlandbit.
    exact Hlandbit. }
  assert (Hdouble : bit_value * 2 = Z.shiftl 1 (bit + 1)).
  { rewrite Hvalue, !Z.shiftl_1_l.
    replace (bit + 1) with (Z.succ bit) by lia.
    rewrite Z.pow_succ_r by lia.
    ring. }
  assert (Hpositive : 1 <= bit_value * 2).
  { destruct Hbit as [Hbit_nonneg _].
    rewrite Hvalue, Z.shiftl_1_l.
    pose proof (Z.pow_pos_nonneg 2 bit ltac:(lia) Hbit_nonneg).
    nia. }
  assert (Hupper : bit_value * 2 <= Z.shiftl 1 count).
  { rewrite Hdouble, !Z.shiftl_1_l.
    apply Z.pow_le_mono_r; lia. }
  repeat split; try assumption.
  intros lower Hlower_next.
  destruct (Z.lt_ge_cases lower bit) as [Hlt | Hge].
  - apply Hlower; lia.
  - replace lower with bit by lia.
    exact Hmaskbit.
Qed.
Lemma testbit_shiftl_one__bit_scan :
  forall bit n,
    0 <= bit ->
    0 <= n ->
    Z.testbit (Z.shiftl 1 bit) n = Z.eqb n bit.
Proof.
  intros bit n Hbit Hn.
  rewrite Z.shiftl_spec by lia.
  destruct (Z.eq_dec n bit) as [Heq | Hneq].
  - subst n.
    replace (bit - bit) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  - assert (Hnb : Z.eqb n bit = false).
    { apply Z.eqb_neq; exact Hneq. }
    rewrite Hnb.
    destruct (Z_lt_ge_dec (n - bit) 0) as [Hneg | Hnonneg].
    + rewrite Z.testbit_neg_r by lia.
      reflexivity.
    + apply Z.bits_above_log2; [lia |].
      change (0 < n - bit).
      lia.
Qed.
Lemma selected_bit_state_from_scan__bit_scan :
  forall mask count bit bit_value,
    BitScanState mask count bit bit_value ->
    Z.land mask bit_value <> 0 ->
    bit < count /\
    Z.testbit mask bit = true /\
    Z.land mask bit_value = bit_value /\
    0 <= Z.lxor mask bit_value < mask /\
    bit_value < Z.shiftl 1 count.
Proof.
  intros mask count bit bit_value Hscan Hland_nonzero.
  unfold BitScanState in Hscan.
  destruct Hscan as (Hmask & Hbit & Hvalue & Hlower).
  assert (Honehot :
    Z.testbit mask bit = true /\
    Z.land mask bit_value = bit_value).
  { destruct (Z.testbit mask bit) eqn:Hmaskbit.
    - split; [reflexivity |].
      apply Z.bits_inj'; intros n Hn.
      rewrite Z.land_spec, Hvalue,
        !testbit_shiftl_one__bit_scan by lia.
      destruct (Z.eqb n bit) eqn:Hnb; simpl.
      + apply Z.eqb_eq in Hnb; subst n.
        rewrite Hmaskbit; reflexivity.
      + rewrite Bool.andb_false_r; reflexivity.
    - exfalso; apply Hland_nonzero.
      apply Z.bits_inj'; intros n Hn.
      rewrite Z.land_spec, Z.testbit_0_l, Hvalue,
        testbit_shiftl_one__bit_scan by lia.
      destruct (Z.eqb n bit) eqn:Hnb; simpl.
      + apply Z.eqb_eq in Hnb; subst n.
        rewrite Hmaskbit; reflexivity.
      + rewrite Bool.andb_false_r; reflexivity. }
  destruct Honehot as [Hmaskbit Hland].
  assert (Hlog : Z.log2 mask < count).
  { apply (proj1 (Z.log2_lt_pow2 mask count ltac:(lia))).
    rewrite <- Z.shiftl_1_l.
    lia. }
  assert (Hbitlt : bit < count).
  { destruct (Z_lt_ge_dec (Z.log2 mask) bit) as [Habove | Hnot_above].
    - pose proof (Z.bits_above_log2 mask bit ltac:(lia) Habove) as Hclear.
      congruence.
    - lia. }
  assert (Hvalue_positive : 0 < bit_value).
  { rewrite Hvalue, Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia. }
  assert (Hxor_nonnegative : 0 <= Z.lxor mask bit_value).
  { apply (proj2 (Z.lxor_nonneg mask bit_value)).
    split; intros; lia. }
  assert (Hxor_small : Z.lxor mask bit_value < mask).
  { pose proof (Z.add_lxor_2land mask bit_value) as Hxor.
    rewrite Hland in Hxor.
    lia. }
  assert (Hvalue_small : bit_value < Z.shiftl 1 count).
  { rewrite Hvalue, !Z.shiftl_1_l.
    apply Z.pow_lt_mono_r; lia. }
  repeat split; assumption.
Qed.
Lemma digit_lex_ge_refl__dp_table_transition :
  forall xs, digit_lex_ge xs xs.
Proof.
  intros xs.
  unfold digit_lex_ge.
  split; [reflexivity |].
  left; reflexivity.
Qed.
Lemma decimal_fold_acc__dp_table_transition :
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
Lemma decimal_fold_app__dp_table_transition :
  forall xs ys,
    fold_left (fun value digit => 10 * value + digit) (xs ++ ys) 0 =
    fold_left (fun value digit => 10 * value + digit) xs 0 *
      10 ^ Zlength ys +
    fold_left (fun value digit => 10 * value + digit) ys 0.
Proof.
  intros xs ys.
  rewrite fold_left_app.
  apply decimal_fold_acc__dp_table_transition.
Qed.
Lemma decimal_fold_bounds__dp_table_transition :
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
    rewrite decimal_fold_acc__dp_table_transition.
    rewrite Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg.
    nia.
Qed.
Lemma digit_lex_ge_cons_iff__dp_table_transition :
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
      apply digit_lex_ge_refl__dp_table_transition.
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
      * subst ys. apply digit_lex_ge_refl__dp_table_transition.
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
Lemma digit_lex_ge_decimal_iff__dp_table_transition :
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
    apply digit_lex_ge_refl__dp_table_transition.
  - rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ys). lia.
  - rewrite Zlength_cons, Zlength_nil in Hlen.
    pose proof (Zlength_nonneg xs). lia.
  - inversion Hxs as [|? ? Hx Hxs']; subst.
    inversion Hys as [|? ? Hy Hys']; subst.
    assert (Htail_len : Zlength xs = Zlength ys).
    { rewrite !Zlength_cons in Hlen. lia. }
    specialize (IH ys Htail_len Hxs' Hys').
    rewrite digit_lex_ge_cons_iff__dp_table_transition by
      exact Htail_len.
    change
      (y < x \/ (x = y /\ digit_lex_ge xs ys) <->
       fold_left (fun value digit => 10 * value + digit) xs x >=
       fold_left (fun value digit => 10 * value + digit) ys y).
    rewrite (decimal_fold_acc__dp_table_transition xs x),
      (decimal_fold_acc__dp_table_transition ys y).
    pose proof (decimal_fold_bounds__dp_table_transition xs Hxs')
      as Hbound_xs.
    pose proof (decimal_fold_bounds__dp_table_transition ys Hys')
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
Lemma concat_digit_order_cross_iff__dp_table_transition :
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
  rewrite digit_lex_ge_decimal_iff__dp_table_transition.
  - rewrite !decimal_fold_app__dp_table_transition.
    nia.
  - rewrite !Zlength_app. lia.
  - apply Forall_app. split; assumption.
  - apply Forall_app. split; assumption.
Qed.
Lemma concat_digit_order_trans__dp_table_transition :
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
    (concat_digit_order_cross_iff__dp_table_transition xs zs
      Hxs Hzs)).
  apply (proj1
    (concat_digit_order_cross_iff__dp_table_transition xs ys
      Hxs Hys)) in Hxy.
  apply (proj1
    (concat_digit_order_cross_iff__dp_table_transition ys zs
      Hys Hzs)) in Hyz.
  pose proof (Zpower_gt_1 10 (Zlength xs) ltac:(lia) Hlenx) as Hpowx.
  pose proof (Zpower_gt_1 10 (Zlength ys) ltac:(lia) Hleny) as Hpowy.
  pose proof (Zpower_gt_1 10 (Zlength zs) ltac:(lia) Hlenz) as Hpowz.
  nia.
Qed.
Lemma Forall_sublist_by_Znth__dp_table_transition :
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
Lemma item_digits_properties__dp_table_transition :
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
  - apply Forall_sublist_by_Znth__dp_table_transition.
    + lia.
    + rewrite Hrowlen. lia.
    + intros k Hk. specialize (Hdigits k ltac:(lia)). lia.
Qed.
Lemma item_before_or_equal_transitive__dp_table_transition :
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
  pose proof (item_digits_properties__dp_table_transition
    rows lens count width i Hwf Hi) as [Hleni Hdi].
  pose proof (item_digits_properties__dp_table_transition
    rows lens count width j Hwf Hj) as [Hlenj Hdj].
  pose proof (item_digits_properties__dp_table_transition
    rows lens count width k Hwf Hk) as [Hlenk Hdk].
  unfold item_before_or_equal in *.
  eapply (concat_digit_order_trans__dp_table_transition
    (item_digits (item_at rows lens i))
    (item_digits (item_at rows lens j))
    (item_digits (item_at rows lens k))); eauto.
Qed.
Lemma item_before_or_equal_refl__dp_table_transition :
  forall rows lens i,
    item_before_or_equal rows lens i i.
Proof.
  intros rows lens i.
  unfold item_before_or_equal.
  apply digit_lex_ge_refl__dp_table_transition.
Qed.
Lemma testbit_shiftl_one__dp_table_transition :
  forall bit index,
    0 <= bit ->
    0 <= index ->
    (Z.testbit (Z.shiftl 1 bit) index = true <-> index = bit).
Proof.
  intros bit index Hbit Hindex.
  rewrite Z.shiftl_spec by lia.
  destruct (Z.lt_trichotomy index bit) as [Hlt | [Heq | Hgt]].
  - rewrite Z.testbit_neg_r by lia.
    split; [discriminate | lia].
  - subst index. replace (bit - bit) with 0 by lia.
    simpl. tauto.
  - replace (index - bit) with (Z.succ (index - bit - 1)) by lia.
    change
      (Z.testbit (2 * 0 + 1) (Z.succ (index - bit - 1)) = true <->
       index = bit).
    rewrite Z.testbit_odd_succ by lia.
    rewrite Z.testbit_0_l.
    split; [discriminate | lia].
Qed.
Lemma selected_mask_partition__dp_table_transition :
  forall mask count bit bit_value rest index,
    SelectedBitState mask count bit bit_value rest ->
    0 <= index < count ->
    (Z.testbit mask index = true <->
     index = bit \/ Z.testbit rest index = true).
Proof.
  intros mask count bit bit_value rest index Hselected Hindex.
  unfold SelectedBitState in Hselected.
  destruct Hselected as
    [Hscan [Hland [Hbit_bounds [Hmask_bit [Hrest Hrest_bounds]]]]].
  unfold BitScanState in Hscan.
  destruct Hscan as [Hmask_bounds [Hscan_bit [Hbit_value Hlower]]].
  subst bit_value rest.
  destruct (Z.eq_dec index bit) as [Heq | Hneq].
  - subst index. split; intros _.
    + left; reflexivity.
    + exact Hmask_bit.
  - assert (Hshift : Z.testbit (Z.shiftl 1 bit) index = false).
    {
      destruct (Z.testbit (Z.shiftl 1 bit) index) eqn:Htest;
        [|reflexivity].
      apply (proj1 (testbit_shiftl_one__dp_table_transition
        bit index ltac:(lia) ltac:(lia))) in Htest.
      contradiction.
    }
    rewrite Z.lxor_spec, Hshift.
    destruct (Z.testbit mask index); simpl; tauto.
Qed.
Lemma dp_table_prefix_extend__dp_table_transition :
  forall rows lens count mask choices index,
    DPTablePrefix rows lens count mask choices ->
    mask < Z.shiftl 1 count ->
    BestIndexForMask rows lens count mask index ->
    DPTablePrefix rows lens count (mask + 1) (choices ++ [index]).
Proof.
  intros rows lens count mask choices index
    [Hcomputed [Hlength [Hzero Hall]]] Hmask Hbest.
  unfold DPTablePrefix.
  split.
  - lia.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + split.
      * rewrite app_Znth1.
        -- exact Hzero.
        -- rewrite Hlength. lia.
      * intros current Hcurrent.
        destruct (Z.lt_trichotomy current mask) as [Hlt | [Heq | Hgt]].
        -- rewrite app_Znth1.
           ++ apply Hall. lia.
           ++ rewrite Hlength. lia.
        -- subst current.
           rewrite app_Znth2.
           ++ rewrite Hlength. replace (mask - mask) with 0 by lia.
              rewrite Znth0_cons. exact Hbest.
           ++ rewrite Hlength. lia.
        -- lia.
Qed.
Lemma compare_outcome_nonpositive__dp_table_transition :
  forall rows lens bit previous comparison,
    comparison <= 0 ->
    ConcatCompareSignOutcome rows lens bit previous comparison ->
    item_before_or_equal rows lens previous bit.
Proof.
  intros rows lens bit previous comparison Hcomparison Houtcome.
  unfold ConcatCompareSignOutcome in Houtcome.
  unfold item_before_or_equal.
  destruct Houtcome as [[Hzero Heq] |
    [[Hpositive [k [Hk [Hlength [Hprefix Hdigit]]]]] |
     [Hnegative [k [Hk [Hlength [Hprefix Hdigit]]]]]]].
  - subst comparison.
    rewrite Heq.
    apply digit_lex_ge_refl__dp_table_transition.
  - lia.
  - subst comparison.
    unfold digit_lex_ge.
    split; [lia |].
    right. exists k.
    split; [rewrite <- Hlength; exact Hk |].
    split.
    + intros p Hp. symmetry. apply Hprefix. exact Hp.
    + exact Hdigit.
Qed.
Lemma compare_outcome_positive__dp_table_transition :
  forall rows lens bit previous comparison,
    comparison > 0 ->
    ConcatCompareSignOutcome rows lens bit previous comparison ->
    item_before_or_equal rows lens bit previous.
Proof.
  intros rows lens bit previous comparison Hcomparison Houtcome.
  unfold ConcatCompareSignOutcome in Houtcome.
  unfold item_before_or_equal.
  destruct Houtcome as [[Hzero Heq] |
    [[Hpositive [k [Hk [Hlength [Hprefix Hdigit]]]]] |
     [Hnegative [k [Hk [Hlength [Hprefix Hdigit]]]]]]].
  - lia.
  - subst comparison.
    unfold digit_lex_ge.
    split; [exact Hlength |].
    right. exists k.
    split; [exact Hk |].
    split; assumption.
  - lia.
Qed.
Lemma best_index_keep_previous__dp_table_transition :
  forall rows lens count mask bit bit_value rest previous comparison,
    SelectedBitState mask count bit bit_value rest ->
    BestIndexForMask rows lens count rest previous ->
    comparison <= 0 ->
    ConcatCompareSignOutcome rows lens bit previous comparison ->
    BestIndexForMask rows lens count mask previous.
Proof.
  intros rows lens count mask bit bit_value rest previous comparison
    Hselected Hbest Hcomparison Houtcome.
  unfold BestIndexForMask in *.
  destruct Hbest as [Hprevious_bounds [Hprevious_rest Hprevious_best]].
  split.
  - exact Hprevious_bounds.
  - split.
    + apply (proj2 (selected_mask_partition__dp_table_transition
        mask count bit bit_value rest previous Hselected Hprevious_bounds)).
      right; exact Hprevious_rest.
    + intros other Hother_bounds Hother_mask.
      apply (proj1 (selected_mask_partition__dp_table_transition
        mask count bit bit_value rest other Hselected Hother_bounds))
        in Hother_mask.
      destruct Hother_mask as [-> | Hother_rest].
      * eapply compare_outcome_nonpositive__dp_table_transition; eauto.
      * eapply Hprevious_best; eauto.
Qed.
Lemma best_index_choose_bit__dp_table_transition :
  forall rows lens count width mask bit bit_value rest previous comparison,
    RowsWellFormed rows lens count width ->
    SelectedBitState mask count bit bit_value rest ->
    BestIndexForMask rows lens count rest previous ->
    comparison > 0 ->
    ConcatCompareSignOutcome rows lens bit previous comparison ->
    BestIndexForMask rows lens count mask bit.
Proof.
  intros rows lens count width mask bit bit_value rest previous comparison
    Hrows Hselected Hbest Hcomparison Houtcome.
  unfold SelectedBitState in Hselected at 1.
  destruct Hselected as
    [Hscan [Hland [Hbit_bounds [Hmask_bit [Hrest Hrest_bounds]]]]].
  assert (Hselected_full :
    SelectedBitState mask count bit bit_value rest).
  {
    unfold SelectedBitState.
    exact (conj Hscan
      (conj Hland
        (conj Hbit_bounds
          (conj Hmask_bit (conj Hrest Hrest_bounds))))).
  }
  unfold BestIndexForMask in *.
  destruct Hbest as [Hprevious_bounds [Hprevious_rest Hprevious_best]].
  split.
  - exact Hbit_bounds.
  - split.
    + exact Hmask_bit.
    + intros other Hother_bounds Hother_mask.
      apply (proj1 (selected_mask_partition__dp_table_transition
        mask count bit bit_value rest other Hselected_full Hother_bounds))
        in Hother_mask.
      destruct Hother_mask as [-> | Hother_rest].
      * apply item_before_or_equal_refl__dp_table_transition.
      * eapply item_before_or_equal_transitive__dp_table_transition
          with (j := previous) (count := count) (width := width); eauto.
        eapply compare_outcome_positive__dp_table_transition; eauto.
Qed.
Lemma best_index_singleton__dp_table_transition :
  forall rows lens count mask bit bit_value rest,
    SelectedBitState mask count bit bit_value rest ->
    rest = 0 ->
    BestIndexForMask rows lens count mask bit.
Proof.
  intros rows lens count mask bit bit_value rest Hselected Hrest_zero.
  unfold SelectedBitState in Hselected at 1.
  destruct Hselected as
    [Hscan [Hland [Hbit_bounds [Hmask_bit [Hrest Hrest_bounds]]]]].
  assert (Hselected_full :
    SelectedBitState mask count bit bit_value rest).
  {
    unfold SelectedBitState.
    exact (conj Hscan
      (conj Hland
        (conj Hbit_bounds
          (conj Hmask_bit (conj Hrest Hrest_bounds))))).
  }
  unfold BestIndexForMask.
  split.
  - exact Hbit_bounds.
  - split.
    + exact Hmask_bit.
    + intros other Hother_bounds Hother_mask.
      apply (proj1 (selected_mask_partition__dp_table_transition
        mask count bit bit_value rest other Hselected_full Hother_bounds))
        in Hother_mask.
      destruct Hother_mask as [-> | Hother_rest].
      * apply item_before_or_equal_refl__dp_table_transition.
      * rewrite Hrest_zero, Z.testbit_0_l in Hother_rest. discriminate.
Qed.
Lemma digit_lex_ge_refl__output_initialization :
  forall xs, digit_lex_ge xs xs.
Proof.
  intros xs.
  unfold digit_lex_ge.
  split; [reflexivity | left; reflexivity].
Qed.
Lemma digit_lex_ge_cons_strict__output_initialization :
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
    + pose proof (Zlength_nonneg xs). rewrite Zlength_cons. lia.
    + split.
      * intros j Hj. lia.
      * rewrite !Znth0_cons. exact Hlt.
Qed.
Lemma digit_lex_ge_cons_same__output_initialization :
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
Lemma digit_lex_ge_cons_inv__output_initialization :
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
    apply digit_lex_ge_refl__output_initialization.
  - split.
    + rewrite !Zlength_cons in Hlen. lia.
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * left. rewrite !Znth0_cons in Hlt. exact Hlt.
      * right.
        assert (Hxy : x = y).
        { specialize (Hprefix 0 ltac:(lia)).
          rewrite !Znth0_cons in Hprefix. exact Hprefix. }
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
                 exact Hlt.
Qed.
Lemma digit_lex_ge_trans__output_initialization :
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
    destruct zs as [|z zs].
    + apply digit_lex_ge_refl__output_initialization.
    + rewrite Zlength_nil, Zlength_cons in Hlenz.
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
    destruct (digit_lex_ge_cons_inv__output_initialization
                _ _ _ _ Hxy') as [Hlxy Hcase_xy].
    destruct Hcase_xy as [Hyx | [Hxeqy Htailxy]].
    + destruct (digit_lex_ge_cons_inv__output_initialization
                  _ _ _ _ Hyz') as [Hlyz Hcase_yz].
      destruct Hcase_yz as [Hzy | [Hyeqz Htailyz]].
      * apply digit_lex_ge_cons_strict__output_initialization; lia.
      * apply digit_lex_ge_cons_strict__output_initialization.
        -- rewrite !Zlength_cons in Hlenxy, Hlenyz. lia.
        -- rewrite <- Hyeqz. exact Hyx.
    + destruct (digit_lex_ge_cons_inv__output_initialization
                  _ _ _ _ Hyz') as [Hlyz Hcase_yz].
      destruct Hcase_yz as [Hzy | [Hyeqz Htailyz]].
      * apply digit_lex_ge_cons_strict__output_initialization.
        -- rewrite !Zlength_cons in Hlenxy, Hlenyz. lia.
        -- rewrite Hxeqy. exact Hzy.
      * subst y z.
        apply digit_lex_ge_cons_same__output_initialization.
        eapply IH; eauto.
Qed.
Lemma digit_lex_ge_total__output_initialization :
  forall xs ys,
    Zlength xs = Zlength ys ->
    digit_lex_ge xs ys \/ digit_lex_ge ys xs.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys as [|y ys].
    + left. apply digit_lex_ge_refl__output_initialization.
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg ys). lia.
  - destruct ys as [|y ys].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg xs). lia.
    + assert (Htails : Zlength xs = Zlength ys).
      { rewrite !Zlength_cons in Hlen. lia. }
      destruct (Z_lt_dec x y) as [Hxy | Hnxy].
      * right. apply digit_lex_ge_cons_strict__output_initialization; lia.
      * destruct (Z.eq_dec x y) as [Hxy | Hneq].
        -- subst y. destruct (IH ys Htails) as [Hge | Hge].
           ++ left. apply digit_lex_ge_cons_same__output_initialization. exact Hge.
           ++ right. apply digit_lex_ge_cons_same__output_initialization. exact Hge.
        -- left. apply digit_lex_ge_cons_strict__output_initialization; lia.
Qed.
Lemma finite_list_maximum_on__output_initialization :
  forall (A : Type) (R : A -> A -> Prop) candidates,
    candidates <> nil ->
    (forall x y,
       In x candidates -> In y candidates -> R x y \/ R y x) ->
    (forall x y z,
       In x candidates -> In y candidates -> In z candidates ->
       R x y -> R y z -> R x z) ->
    exists best,
      In best candidates /\
      forall candidate, In candidate candidates -> R best candidate.
Proof.
  intros A R candidates.
  induction candidates as [|a tail IH]; intros Hne Htotal Htrans.
  - contradiction.
  - destruct tail as [|b tail].
    + exists a. split; [left; reflexivity |].
      intros candidate Hin.
      assert (Haa : R a a).
      { destruct (Htotal a a (or_introl eq_refl) (or_introl eq_refl))
          as [Haa | Haa]; exact Haa. }
      destruct Hin as [Hin | []]. subst candidate. exact Haa.
    + assert (Htailne : b :: tail <> nil) by discriminate.
      assert (Htailtotal :
        forall x y, In x (b :: tail) -> In y (b :: tail) -> R x y \/ R y x).
      { intros x y Hx Hy. apply Htotal; right; assumption. }
      assert (Htailtrans :
        forall x y z,
          In x (b :: tail) -> In y (b :: tail) -> In z (b :: tail) ->
          R x y -> R y z -> R x z).
      { intros x y z Hx Hy Hz Hxy Hyz.
        eapply Htrans; eauto; right; eauto. }
      destruct (IH Htailne Htailtotal Htailtrans)
        as [best [Hbest Hbestmax]].
      destruct (Htotal a best (or_introl eq_refl) (or_intror Hbest))
        as [Hab | Hba].
      * exists a. split; [left; reflexivity |].
        assert (Haa : R a a).
        { destruct (Htotal a a (or_introl eq_refl) (or_introl eq_refl))
            as [Haa | Haa]; exact Haa. }
        intros candidate Hcandidate.
        destruct Hcandidate as [Hcandidate | Hcandidate].
        -- subst candidate. exact Haa.
        -- eapply Htrans.
           ++ left; reflexivity.
           ++ right; exact Hbest.
           ++ right; exact Hcandidate.
           ++ exact Hab.
           ++ apply Hbestmax. exact Hcandidate.
      * exists best. split; [right; exact Hbest |].
        intros candidate Hcandidate.
        destruct Hcandidate as [-> | Hcandidate].
        -- exact Hba.
        -- apply Hbestmax. exact Hcandidate.
Qed.
Lemma list_power_snd_complete__output_initialization :
  forall (A B : Type) (positions : list A) (values output : list B),
    length positions = length output ->
    (forall x, In x output -> In x values) ->
    In output
      (map (fun assignment => map snd assignment)
        (list_power positions values)).
Proof.
  intros A B positions.
  induction positions as [|position positions IH];
    intros values output Hlen Hin.
  - destruct output as [|x output]; [simpl; auto | simpl in Hlen; lia].
  - destruct output as [|x output]; [simpl in Hlen; lia |].
    simpl in Hlen.
    assert (Htail :
      In output
        (map (fun assignment => map snd assignment)
          (list_power positions values))).
    { apply IH; [lia |].
      intros y Hy. apply Hin. right. exact Hy. }
    apply in_map_iff in Htail.
    destruct Htail as [assignment [Houtput Hassignment]].
    apply in_map_iff.
    exists ((position, x) :: assignment).
    split.
    + simpl. now rewrite Houtput.
    + simpl. apply in_flat_map.
      exists assignment. split; [exact Hassignment |].
      apply in_map_iff.
      exists x. split; [reflexivity |].
      apply Hin. left. reflexivity.
Qed.
Lemma permutation_candidate_in__output_initialization :
  forall (base order : list Z),
    Permutation base order ->
    In order
      (filter
        (fun candidate =>
           if excluded_middle_informative (Permutation base candidate)
           then true else false)
        (map (fun assignment => map snd assignment)
          (list_power (seq 0 (length base)) base))).
Proof.
  intros base order Hperm.
  apply filter_In. split.
  - apply list_power_snd_complete__output_initialization.
    + rewrite length_seq. apply Permutation_length. exact Hperm.
    + intros x Hx. eapply Permutation_in; [symmetry; exact Hperm | exact Hx].
  - destruct (excluded_middle_informative (Permutation base order))
      as [H | H]; [reflexivity | contradiction].
Qed.
Lemma permutation_candidate_sound__output_initialization :
  forall (base order : list Z),
    In order
      (filter
        (fun candidate =>
           if excluded_middle_informative (Permutation base candidate)
           then true else false)
        (map (fun assignment => map snd assignment)
          (list_power (seq 0 (length base)) base))) ->
    Permutation base order.
Proof.
  intros base order Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Htest].
  destruct (excluded_middle_informative (Permutation base order))
    as [H | H]; [exact H | discriminate].
Qed.
Lemma concatenate_indices_length_permutation__output_initialization :
  forall rows lens first second,
    Permutation first second ->
    Zlength (concatenate_indices rows lens first) =
    Zlength (concatenate_indices rows lens second).
Proof.
  intros rows lens first second Hperm.
  induction Hperm.
  - reflexivity.
  - unfold concatenate_indices in *. simpl.
    rewrite !Zlength_app. lia.
  - unfold concatenate_indices. simpl.
    rewrite !Zlength_app. lia.
  - etransitivity; eauto.
Qed.
Lemma largest_concatenation_exists__output_initialization :
  forall rows lens,
    exists order,
      Permutation (all_indices (Zlength rows)) order /\
      forall alternative,
        Permutation (all_indices (Zlength rows)) alternative ->
        digit_lex_ge
          (concatenate_indices rows lens order)
          (concatenate_indices rows lens alternative).
Proof.
  intros rows lens.
  set (base := all_indices (Zlength rows)).
  set (candidates :=
    filter
      (fun candidate =>
         if excluded_middle_informative (Permutation base candidate)
         then true else false)
      (map (fun assignment => map snd assignment)
        (list_power (seq 0 (length base)) base))).
  assert (Hbase : In base candidates).
  { subst candidates.
    apply permutation_candidate_in__output_initialization.
    reflexivity. }
  assert (Hnonempty : candidates <> nil).
  { intro Heq. rewrite Heq in Hbase. exact Hbase. }
  assert (Hsound : forall order, In order candidates -> Permutation base order).
  { intros order Horder. subst candidates.
    apply permutation_candidate_sound__output_initialization. exact Horder. }
  destruct (finite_list_maximum_on__output_initialization
    (list Z)
    (fun first second =>
       digit_lex_ge
         (concatenate_indices rows lens first)
         (concatenate_indices rows lens second))
    candidates Hnonempty) as [best [Hbest Hmax]].
  - intros first second Hfirst Hsecond.
    apply digit_lex_ge_total__output_initialization.
    eapply concatenate_indices_length_permutation__output_initialization.
    eapply Permutation_trans.
    + apply Permutation_sym. apply Hsound. exact Hfirst.
    + apply Hsound. exact Hsecond.
  - intros first second third Hfirst Hsecond Hthird H12 H23.
    eapply digit_lex_ge_trans__output_initialization; eauto.
  - exists best. split.
    + subst base. apply Hsound. exact Hbest.
    + intros alternative Halternative.
      apply Hmax.
      subst candidates.
      apply permutation_candidate_in__output_initialization.
      subst base. exact Halternative.
Qed.
Lemma all_indices_spec__output_initialization :
  forall count index,
    0 <= count ->
    (In index (all_indices count) <-> 0 <= index < count).
Proof.
  intros count index Hcount.
  unfold all_indices.
  split.
  - intros Hin. apply in_map_iff in Hin.
    destruct Hin as [n [Hindex Hn]].
    apply in_seq in Hn.
    subst index.
    destruct Hn as [_ Hn].
    split; [apply Nat2Z.is_nonneg |].
    replace count with (Z.of_nat (Z.to_nat count)).
    2: { apply Z2Nat.id. exact Hcount. }
    apply Nat2Z.inj_lt. exact Hn.
  - intros Hindex. apply in_map_iff.
    exists (Z.to_nat index). split.
    + rewrite Z2Nat.id by lia. reflexivity.
    + apply in_seq.
      split; [lia |].
      apply Z2Nat.inj_lt; lia.
Qed.
Lemma full_mask_indexes__output_initialization :
  forall count,
    0 <= count ->
    MaskIndexes count (Z.shiftl 1 count - 1) (all_indices count).
Proof.
  intros count Hcount index.
  rewrite all_indices_spec__output_initialization by exact Hcount.
  split.
  - intros Hindex. split; [exact Hindex |].
    replace (Z.shiftl 1 count - 1) with (Z.ones count).
    2: { unfold Z.ones. lia. }
    rewrite Z.testbit_ones_nonneg by lia.
    apply Z.ltb_lt. lia.
  - intros [Hindex _]. exact Hindex.
Qed.
Lemma greedy_output_full_mask__output_initialization :
  forall rows lens count,
    Zlength rows = count ->
    0 <= count ->
    GreedyOutputPrefix rows lens count (Z.shiftl 1 count - 1) nil.
Proof.
  intros rows lens count Hrows Hcount.
  destruct (largest_concatenation_exists__output_initialization rows lens)
    as [order [Hperm Hmax]].
  pose proof Hperm as HpermRows.
  rewrite Hrows in Hperm.
  unfold GreedyOutputPrefix.
  exists nil, order. simpl.
  split; [exact Hperm |].
  split.
  - unfold MaskIndexes. intros index.
    pose proof (full_mask_indexes__output_initialization count Hcount index)
      as Hfull.
    split.
    + intros Hin. apply Hfull.
      eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
    + intros Hbit. eapply Permutation_in; [exact Hperm |].
      apply Hfull. exact Hbit.
  - split; [reflexivity |].
    unfold LargestConcatenation.
    exists order. split; [exact HpermRows |].
    split; [reflexivity |].
    intros alternative Halternative. apply Hmax. exact Halternative.
Qed.
Lemma item_digits_length__output_initialization :
  forall rows lens count width index,
    RowsWellFormed rows lens count width ->
    0 <= index < count ->
    Zlength (item_digits (item_at rows lens index)) = Znth index lens 0.
Proof.
  intros rows lens count width index Hwf Hindex.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hrows]].
  specialize (Hrows index Hindex).
  destruct Hrows as [Hrowlen [Hlen _]].
  unfold item_digits, item_at. simpl.
  rewrite Zlength_sublist by lia. lia.
Qed.
Lemma concatenate_indices_length__output_initialization :
  forall rows lens count width indices,
    RowsWellFormed rows lens count width ->
    (forall index, In index indices -> 0 <= index < count) ->
    Zlength (concatenate_indices rows lens indices) =
    sum (map (fun index => Znth index lens 0) indices).
Proof.
  intros rows lens count width indices Hwf Hindices.
  induction indices as [|index indices IH].
  - reflexivity.
  - unfold concatenate_indices in *. simpl.
    rewrite Zlength_app.
    rewrite item_digits_length__output_initialization with
      (count := count) (width := width).
    + rewrite IH; [reflexivity |].
      intros i Hi. apply Hindices. right. exact Hi.
    + exact Hwf.
    + apply Hindices. left. reflexivity.
Qed.
Lemma map_lens_all_indices__output_initialization :
  forall lens,
    map (fun index => Znth index lens 0) (all_indices (Zlength lens)) = lens.
Proof.
  intros lens.
  apply (list_eq_nth Z _ _ 0).
  - unfold all_indices.
    rewrite !length_map, length_seq.
    rewrite Zlength_correct, Nat2Z.id. reflexivity.
  - intros n Hn.
    assert (HnLens : (n < length lens)%nat).
    { unfold all_indices in Hn.
      rewrite !length_map, length_seq, Zlength_correct, Nat2Z.id in Hn.
      exact Hn. }
    unfold all_indices.
    rewrite (map_nth_len Z Z (fun index => Znth index lens 0)
      (map Z.of_nat (seq 0 (Z.to_nat (Zlength lens)))) n 0 0).
    2: { rewrite length_map, length_seq, Zlength_correct, Nat2Z.id.
         exact HnLens. }
    rewrite (map_nth_len nat Z Z.of_nat
      (seq 0 (Z.to_nat (Zlength lens))) n 0 (0%nat)).
    2: { rewrite length_seq, Zlength_correct, Nat2Z.id. exact HnLens. }
    rewrite seq_nth by
      (rewrite Zlength_correct, Nat2Z.id; exact HnLens).
    simpl.
    unfold Znth.
    rewrite Nat2Z.id.
    reflexivity.
Qed.
Lemma sum_permutation__output_initialization :
  forall first second,
    Permutation first second ->
    sum first = sum second.
Proof.
  intros first second Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma sum_nonnegative__output_initialization :
  forall values,
    (forall value, In value values -> 0 <= value) ->
    0 <= sum values.
Proof.
  intros values Hnonneg.
  induction values as [|value values IH]; simpl; [lia |].
  assert (Hvalue : 0 <= value) by (apply Hnonneg; left; reflexivity).
  assert (Htail : forall x, In x values -> 0 <= x).
  { intros x Hx. apply Hnonneg. right. exact Hx. }
  specialize (IH Htail). lia.
Qed.
Lemma sum_member_le__output_initialization :
  forall values value,
    In value values ->
    (forall x, In x values -> 0 <= x) ->
    value <= sum values.
Proof.
  intros values value Hin Hnonneg.
  apply in_split in Hin.
  destruct Hin as [before [after Hvalues]].
  subst values. rewrite sum_app. simpl.
  assert (0 <= sum before).
  { apply sum_nonnegative__output_initialization.
    intros x Hx. apply Hnonneg. apply in_or_app. left. exact Hx. }
  assert (0 <= sum after).
  { apply sum_nonnegative__output_initialization.
    intros x Hx. apply Hnonneg. apply in_or_app. right. right. exact Hx. }
  lia.
Qed.
Lemma greedy_output_remaining_length__output_initialization :
  forall rows lens count width mask output index,
    RowsWellFormed rows lens count width ->
    GreedyOutputPrefix rows lens count mask output ->
    0 <= index < count ->
    Z.testbit mask index = true ->
    Zlength output + Znth index lens 0 <= sum lens.
Proof.
  intros rows lens count width mask output index
    Hwf Hgreedy Hindex Hbit.
  unfold GreedyOutputPrefix in Hgreedy.
  destruct Hgreedy as
    [done [todo [Hperm [Hmask [Houtput Hlargest]]]]].
  assert (Hcount : 0 <= count).
  { unfold RowsWellFormed in Hwf.
    destruct Hwf as [Hrowslen _].
    pose proof (Zlength_nonneg rows). lia. }
  assert (HinTodo : In index todo).
  { apply Hmask. split; assumption. }
  assert (Hvalid :
    forall i, In i (done ++ todo) -> 0 <= i < count).
  { intros i Hi.
    apply all_indices_spec__output_initialization; [exact Hcount |].
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hi]. }
  assert (HdoneLength :
    Zlength output = sum (map (fun i => Znth i lens 0) done)).
  { rewrite Houtput.
    apply concatenate_indices_length__output_initialization
      with (count := count) (width := width); [exact Hwf |].
    intros i Hi. apply Hvalid. apply in_or_app. left. exact Hi. }
  assert (HsumParts :
    sum lens =
      sum (map (fun i => Znth i lens 0) done) +
      sum (map (fun i => Znth i lens 0) todo)).
  { assert (Hlenslen : Zlength lens = count).
    { unfold RowsWellFormed in Hwf. tauto. }
    assert (Hmapped :
      map (fun i => Znth i lens 0) (all_indices count) = lens).
    { rewrite <- Hlenslen.
      apply map_lens_all_indices__output_initialization. }
    pose proof (Permutation_map (fun i => Znth i lens 0) Hperm)
      as Hmappedperm.
    pose proof (sum_permutation__output_initialization _ _ Hmappedperm)
      as Hsums.
    rewrite Hmapped, map_app, sum_app in Hsums. lia. }
  assert (HselectedLe :
    Znth index lens 0 <= sum (map (fun i => Znth i lens 0) todo)).
  { apply sum_member_le__output_initialization.
    - apply in_map_iff. exists index. split; [reflexivity | exact HinTodo].
    - intros x Hx. apply in_map_iff in Hx.
      destruct Hx as [i [Hx Hi]]. subst x.
      unfold RowsWellFormed in Hwf.
      destruct Hwf as [_ [_ Hrows]].
      specialize (Hrows i).
      assert (0 <= i < count).
      { apply Hvalid. apply in_or_app. right. exact Hi. }
      specialize (Hrows H). lia. }
  lia.
Qed.
Lemma append_row_prefix_step__output_row_copy :
  forall flat rows lens count width prior output index position,
    RowsWellFormed rows lens count width ->
    FlatRows flat rows count width ->
    0 <= index < count ->
    0 <= position < Znth index lens 0 ->
    AppendRowPrefix rows lens prior index position output ->
    AppendRowPrefix rows lens prior index (position + 1)
      (output ++ [Znth (index * width + position) flat 0]).
Proof.
  intros flat rows lens count width prior output index position
    Hwf Hflat Hindex Hposition Hprefix.
  destruct Hwf as (_ & _ & Hrows).
  specialize (Hrows index Hindex).
  destruct Hrows as (Hrow_length & Hlens & _ & _).
  assert (Hcell :
    Znth (index * width + position) flat 0 =
    Znth position (Znth index rows nil) 0).
  { eapply flat_rows_cell_lookup__compare_digits; eauto; lia. }
  assert (Hdigits_length :
    Zlength (item_digits (item_at rows lens index)) =
    Znth index lens 0).
  { unfold item_digits, item_at; simpl.
    rewrite Zlength_sublist; lia. }
  assert (Hdigit_cell :
    Znth position (item_digits (item_at rows lens index)) 0 =
    Znth position (Znth index rows nil) 0).
  { unfold item_digits, item_at; simpl.
    rewrite Znth_sublist by lia.
    f_equal; lia. }
  unfold AppendRowPrefix in *.
  subst output.
  rewrite (sublist_split 0 (position + 1) position
    (item_digits (item_at rows lens index))) by lia.
  rewrite (sublist_single 0 position
    (item_digits (item_at rows lens index))) by lia.
  rewrite Hcell.
  rewrite Hdigit_cell.
  rewrite app_assoc.
  reflexivity.
Qed.
Lemma row_output_capacity__output_row_copy :
  forall result_length lens first position,
    0 <= position ->
    position < Znth first lens 0 ->
    result_length + (Znth first lens 0 - position) <= sum lens ->
    result_length < sum lens.
Proof.
  intros; lia.
Qed.
Lemma log2_lt_pow2__output_finalization :
  forall x n,
    0 <= x < 2 ^ n ->
    0 < n ->
    Z.log2 x < n.
Proof.
  intros x n Hx Hn.
  destruct (Z.eq_dec x 0) as [-> | Hx0].
  - simpl; lia.
  - pose proof (Z.log2_spec x ltac:(lia)) as [Hpow _].
    destruct (Z_lt_ge_dec (Z.log2 x) n); [assumption |].
    pose proof (Z.pow_le_mono_r 2 n (Z.log2 x) ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma item_digits_length_for_output__output_finalization :
  forall rows lens count width index,
    RowsWellFormed rows lens count width ->
    0 <= index < count ->
    Zlength (item_digits (item_at rows lens index)) = Znth index lens 0.
Proof.
  intros rows lens count width index Hwf Hindex.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hrows]].
  specialize (Hrows index Hindex).
  destruct Hrows as [Hrowlen [Hitemlen _]].
  unfold item_digits, item_at; simpl.
  rewrite Zlength_sublist; lia.
Qed.
Lemma sum_permutation__output_finalization :
  forall left right,
    Permutation left right ->
    sum left = sum right.
Proof.
  intros left right Hpermutation.
  unfold sum.
  induction Hpermutation; simpl; lia.
Qed.
Lemma all_indices_bounds__output_finalization :
  forall count index,
    0 <= count ->
    In index (all_indices count) ->
    0 <= index < count.
Proof.
  intros count index Hcount Hin.
  unfold all_indices in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [n [<- Hin]].
  apply in_seq in Hin.
  simpl in Hin.
  split; [lia |].
  rewrite <- (Z2Nat.id count) by lia.
  apply Nat2Z.inj_lt.
  lia.
Qed.
Lemma all_indices_lookup_lens__output_finalization :
  forall lens,
    map (fun index => Znth index lens 0) (all_indices (Zlength lens)) =
    lens.
Proof.
  intros lens.
  unfold all_indices.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite map_map.
  apply (list_eq_nth Z _ _ 0).
  - rewrite length_map, length_seq; reflexivity.
  - intros n Hn.
    rewrite length_map, length_seq in Hn.
    rewrite
      (map_nth_len nat Z
         (fun index : nat => Znth (Z.of_nat index) lens 0)
         (seq 0 (length lens)) n 0 0%nat)
      by (rewrite length_seq; exact Hn).
    rewrite seq_nth by exact Hn.
    unfold Znth.
    rewrite Nat2Z.id.
    reflexivity.
Qed.
Lemma concatenate_indices_length__output_finalization :
  forall rows lens indices,
    Zlength (concatenate_indices rows lens indices) =
    sum
      (map
         (fun index => Zlength (item_digits (item_at rows lens index)))
         indices).
Proof.
  intros rows lens indices.
  unfold concatenate_indices.
  induction indices as [|index rest IH].
  - reflexivity.
  - simpl. rewrite Zlength_app, IH.
    reflexivity.
Qed.
Lemma concatenate_indices_permutation_length__output_finalization :
  forall rows lens count width order,
    RowsWellFormed rows lens count width ->
    Permutation (all_indices count) order ->
    Zlength (concatenate_indices rows lens order) = sum lens.
Proof.
  intros rows lens count width order Hwf Hpermutation.
  pose proof Hwf as Hwf_copy.
  unfold RowsWellFormed in Hwf_copy.
  destruct Hwf_copy as [Hrows_length [Hlens_length Hrows]].
  assert (Hcount : 0 <= count).
  { pose proof (Zlength_nonneg rows); lia. }
  assert (Hvalid : forall index, In index order -> 0 <= index < count).
  { intros index Hin.
    apply all_indices_bounds__output_finalization; [exact Hcount |].
    eapply Permutation_in.
    - apply Permutation_sym; exact Hpermutation.
    - exact Hin. }
  assert (Hitem_lengths :
      map
        (fun index => Zlength (item_digits (item_at rows lens index)))
        order =
      map (fun index => Znth index lens 0) order).
  { apply map_ext_in.
    intros index Hin.
    apply item_digits_length_for_output__output_finalization with
      (count := count) (width := width); auto. }
  assert (Hlookup :
      map (fun index => Znth index lens 0) (all_indices count) = lens).
  { rewrite <- Hlens_length.
    apply all_indices_lookup_lens__output_finalization. }
  pose proof
    (Permutation_map (fun index => Znth index lens 0) Hpermutation)
    as Hmapped.
  pose proof (sum_permutation__output_finalization _ _ Hmapped) as Hsum.
  rewrite concatenate_indices_length__output_finalization.
  rewrite Hitem_lengths.
  rewrite <- Hsum, Hlookup.
  reflexivity.
Qed.
Lemma largest_concatenation_length__output_finalization :
  forall rows lens count width output,
    RowsWellFormed rows lens count width ->
    LargestConcatenation rows lens output ->
    Zlength output = sum lens.
Proof.
  intros rows lens count width output Hwf Hlargest.
  unfold LargestConcatenation in Hlargest.
  destruct Hlargest as
    [order [Hpermutation [Houtput Hgreatest]]].
  rewrite Houtput.
  apply concatenate_indices_permutation_length__output_finalization
    with (count := count) (width := width); [exact Hwf |].
  rewrite <- (proj1 Hwf).
  exact Hpermutation.
Qed.
Lemma greedy_output_empty_mask__output_finalization :
  forall rows lens count width output,
    RowsWellFormed rows lens count width ->
    GreedyOutputPrefix rows lens count 0 output ->
    LargestConcatenation rows lens output /\
    Zlength output = sum lens.
Proof.
  intros rows lens count width output Hwf Hgreedy.
  unfold GreedyOutputPrefix in Hgreedy.
  destruct Hgreedy as
    [done [todo [Hpermutation [Hmask [Houtput Hlargest]]]]].
  assert (Htodo : todo = []).
  { destruct todo as [|index rest]; [reflexivity |].
    exfalso.
    pose proof (proj1 (Hmask index) (or_introl eq_refl)) as [_ Hbit].
    rewrite Z.testbit_0_l in Hbit.
    discriminate. }
  subst todo.
  rewrite app_nil_r in Hpermutation, Hlargest.
  split.
  - rewrite Houtput.
    exact Hlargest.
  - rewrite Houtput.
    apply concatenate_indices_permutation_length__output_finalization
      with (count := count) (width := width); assumption.
Qed.
Lemma lxor_lt_pow2__output_finalization :
  forall x y n,
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ n ->
    0 < n ->
    0 <= Z.lxor x y < 2 ^ n.
Proof.
  intros x y n Hx Hy Hn.
  split.
  - rewrite Z.lxor_nonneg.
    tauto.
  - apply Z.log2_lt_cancel.
    rewrite Z.log2_pow2 by lia.
    eapply Z.le_lt_trans.
    + apply Z.log2_lxor; lia.
    + apply Z.max_lub_lt;
        eapply log2_lt_pow2__output_finalization; eauto.
Qed.
Lemma testbit_one_positive__output_finalization :
  forall k,
    0 < k ->
    Z.testbit 1 k = false.
Proof.
  intros k Hk.
  destruct k; try lia.
  destruct p; reflexivity.
Qed.
Lemma shifted_one_testbit__output_finalization :
  forall first index,
    0 <= first ->
    0 <= index ->
    Z.testbit (Z.shiftl 1 first) index = Z.eqb index first.
Proof.
  intros first index Hfirst Hindex.
  rewrite Z.shiftl_spec by lia.
  destruct (Z.eq_dec index first) as [-> | Hneq].
  - rewrite Z.sub_diag, Z.eqb_refl; reflexivity.
  - assert (Heqb : Z.eqb index first = false) by
        (apply Z.eqb_neq; exact Hneq).
    rewrite Heqb.
    destruct (Z_lt_ge_dec index first).
    + rewrite Z.testbit_neg_r by lia; reflexivity.
    + apply testbit_one_positive__output_finalization; lia.
Qed.
Lemma lxor_shifted_one_true__output_finalization :
  forall mask first index,
    0 <= first ->
    Z.testbit mask first = true ->
    (Z.testbit (Z.lxor mask (Z.shiftl 1 first)) index = true <->
     Z.testbit mask index = true /\ index <> first).
Proof.
  intros mask first index Hfirst Hselected.
  destruct (Z_lt_ge_dec index 0) as [Hnegative | Hindex].
  - rewrite !Z.testbit_neg_r by lia.
    split.
    + discriminate.
    + intros [Hfalse _]; discriminate.
  - rewrite Z.lxor_spec.
    rewrite shifted_one_testbit__output_finalization by lia.
    destruct (Z.eq_dec index first) as [-> | Hneq].
    + rewrite Z.eqb_refl, Hselected.
      simpl.
      split.
      * discriminate.
      * intros [_ Hneq]; contradiction.
    + assert (Heqb : Z.eqb index first = false) by
        (apply Z.eqb_neq; exact Hneq).
      rewrite Heqb.
      destruct (Z.testbit mask index); simpl; tauto.
Qed.
Lemma all_indices_nodup__output_finalization :
  forall count,
    NoDup (all_indices count).
Proof.
  intros count.
  unfold all_indices.
  apply NoDup_map_NoDup_ForallPairs.
  - intros x y _ _ Heq.
    apply Nat2Z.inj; exact Heq.
  - apply seq_NoDup.
Qed.
Lemma concatenate_indices_app__output_finalization :
  forall rows lens left right,
    concatenate_indices rows lens (left ++ right) =
    concatenate_indices rows lens left ++
    concatenate_indices rows lens right.
Proof.
  intros rows lens left right.
  unfold concatenate_indices.
  rewrite map_app, concat_app.
  reflexivity.
Qed.
Lemma digit_lex_ge_refl__output_finalization :
  forall xs,
    digit_lex_ge xs xs.
Proof.
  intros xs.
  unfold digit_lex_ge.
  split; [reflexivity | left; reflexivity].
Qed.
Lemma digit_lex_ge_antisym__output_finalization :
  forall xs ys,
    digit_lex_ge xs ys ->
    digit_lex_ge ys xs ->
    xs = ys.
Proof.
  intros xs ys Hxy Hyx.
  unfold digit_lex_ge in *.
  destruct Hxy as [_ [Heq | [k [Hk [Hpre Hgt]]]]]; [assumption |].
  destruct Hyx as [_ [Heq | [j [Hj [Hpre' Hgt']]]]]; [symmetry; assumption |].
  destruct (Z.lt_trichotomy k j) as [Hlt | [Heq | Hgtidx]].
  - specialize (Hpre' k ltac:(lia)).
    lia.
  - subst j; lia.
  - specialize (Hpre j ltac:(lia)).
    lia.
Qed.
Lemma digit_lex_ge_trans__output_finalization :
  forall xs ys zs,
    digit_lex_ge xs ys ->
    digit_lex_ge ys zs ->
    digit_lex_ge xs zs.
Proof.
  intros xs ys zs Hxy Hyz.
  unfold digit_lex_ge in *.
  destruct Hxy as [Hlenxy [Heqxy | [k [Hk [Hprexy Hgtxy]]]]].
  - subst ys; assumption.
  - destruct Hyz as [Hlenyz [Heqyz | [j [Hj [Hpreyz Hgtyz]]]]].
    + subst zs.
      split; [assumption |].
      right; exists k.
      split; [exact Hk |].
      split; assumption.
    + split; [lia |].
      right.
      destruct (Z.lt_trichotomy k j) as [Hlt | [Heq | Hgtidx]].
      * exists k.
        repeat split; try lia.
        -- intros p Hp.
           rewrite (Hprexy p) by lia.
           apply Hpreyz; lia.
        -- rewrite <- (Hpreyz k) by lia.
           exact Hgtxy.
      * subst j.
        exists k.
        repeat split; try lia.
        -- intros p Hp.
           rewrite (Hprexy p) by lia.
           apply Hpreyz; lia.
      * exists j.
        repeat split; try lia.
        -- intros p Hp.
           rewrite (Hprexy p) by lia.
           apply Hpreyz; lia.
        -- rewrite (Hprexy j) by lia.
           exact Hgtyz.
Qed.
Lemma digit_lex_ge_append_right__output_finalization :
  forall xs ys suffix,
    digit_lex_ge xs ys ->
    digit_lex_ge (xs ++ suffix) (ys ++ suffix).
Proof.
  intros xs ys suffix Hge.
  unfold digit_lex_ge in *.
  destruct Hge as [Hlen [Heq | [k [Hk [Hpre Hgt]]]]].
  - subst ys.
    split; [reflexivity | left; reflexivity].
  - split.
    + rewrite !Zlength_app; lia.
    + right; exists k.
      split.
      { rewrite Zlength_app.
        pose proof (Zlength_nonneg suffix).
        lia. }
      split.
      * intros j Hj.
        rewrite !app_Znth1 by lia.
        apply Hpre; lia.
      * rewrite !app_Znth1 by lia.
        exact Hgt.
Qed.
Lemma digit_lex_ge_append_left__output_finalization :
  forall prefix xs ys,
    digit_lex_ge xs ys ->
    digit_lex_ge (prefix ++ xs) (prefix ++ ys).
Proof.
  intros prefix xs ys Hge.
  unfold digit_lex_ge in *.
  destruct Hge as [Hlen [Heq | [k [Hk [Hpre Hgt]]]]].
  - subst ys.
    split; [reflexivity | left; reflexivity].
  - split.
    + rewrite !Zlength_app; lia.
    + right; exists (Zlength prefix + k).
      split.
      { rewrite Zlength_app.
        pose proof (Zlength_nonneg prefix).
        lia. }
      split.
      * intros j Hj.
        destruct (Z_lt_ge_dec j (Zlength prefix)).
        -- rewrite !app_Znth1 by lia; reflexivity.
        -- rewrite !app_Znth2 by lia.
           apply Hpre; lia.
      * rewrite !app_Znth2 by lia.
        replace (Zlength prefix + k - Zlength prefix) with k by lia.
        exact Hgt.
Qed.
Lemma item_digits_length__output_finalization :
  forall rows lens count width index,
    RowsWellFormed rows lens count width ->
    0 <= index < count ->
    Zlength (item_digits (item_at rows lens index)) = Znth index lens 0.
Proof.
  intros rows lens count width index Hwf Hindex.
  unfold RowsWellFormed in Hwf.
  destruct Hwf as [_ [_ Hrows]].
  specialize (Hrows index Hindex).
  destruct Hrows as [Hrowlen [Hitemlen _]].
  unfold item_digits, item_at; simpl.
  rewrite Zlength_sublist; lia.
Qed.
Lemma concatenate_indices_cons__output_finalization :
  forall rows lens index rest,
    concatenate_indices rows lens (index :: rest) =
    item_digits (item_at rows lens index) ++
    concatenate_indices rows lens rest.
Proof.
  reflexivity.
Qed.
Lemma concatenate_indices_singleton__output_finalization :
  forall rows lens index,
    concatenate_indices rows lens [index] =
    item_digits (item_at rows lens index).
Proof.
  intros; unfold concatenate_indices; simpl.
  apply app_nil_r.
Qed.
Lemma concatenate_move_best_front_ge__output_finalization :
  forall rows lens first before after,
    (forall index,
       In index before ->
       item_before_or_equal rows lens first index) ->
    digit_lex_ge
      (concatenate_indices rows lens (first :: before ++ after))
      (concatenate_indices rows lens (before ++ first :: after)).
Proof.
  intros rows lens first before.
  induction before as [|index before IH]; intros after Hbest.
  - simpl.
    apply digit_lex_ge_refl__output_finalization.
  - change (digit_lex_ge
      (concatenate_indices rows lens
         (first :: index :: before ++ after))
      (concatenate_indices rows lens
         (index :: before ++ first :: after))).
    rewrite !concatenate_indices_cons__output_finalization.
    eapply digit_lex_ge_trans__output_finalization with
      (ys :=
        item_digits (item_at rows lens index) ++
        item_digits (item_at rows lens first) ++
        concatenate_indices rows lens (before ++ after)).
    + rewrite !app_assoc.
      apply digit_lex_ge_append_right__output_finalization.
      apply Hbest; simpl; auto.
    + apply digit_lex_ge_append_left__output_finalization.
      apply IH.
      intros other Hother.
      apply Hbest; simpl; auto.
Qed.
Lemma greedy_output_consume_best__output_finalization :
  forall rows lens count width mask first prior current position,
    RowsWellFormed rows lens count width ->
    BestIndexForMask rows lens count mask first ->
    GreedyOutputPrefix rows lens count mask prior ->
    AppendRowPrefix rows lens prior first position current ->
    position >= Znth first lens 0 ->
    position <= Znth first lens 0 ->
    GreedyOutputPrefix rows lens count
      (Z.lxor mask (Z.shiftl 1 first)) current.
Proof.
  intros rows lens count width mask first prior current position
    Hwf Hbest Hgreedy Happend Hpositionlo Hpositionhi.
  unfold BestIndexForMask in Hbest.
  destruct Hbest as [Hfirst [Hselected Hbest]].
  unfold GreedyOutputPrefix in Hgreedy.
  destruct Hgreedy as
    [done [todo [Hpermutation [Hmask [Hprior Hlargest]]]]].
  assert (Hinfirst : In first todo).
  { apply (proj2 (Hmask first)); auto. }
  apply in_split in Hinfirst.
  destruct Hinfirst as [before [after Htodo]].
  subst todo.
  pose proof (all_indices_nodup__output_finalization count) as Hall_nodup.
  pose proof (Permutation_NoDup Hpermutation Hall_nodup) as Hcombined_nodup.
  pose proof
    (NoDup_app_remove_l done (before ++ first :: after) Hcombined_nodup)
    as Htodo_nodup.
  pose proof (NoDup_remove_2 before after first Htodo_nodup) as Hfirst_removed.
  pose proof
    (item_digits_length__output_finalization
       rows lens count width first Hwf Hfirst) as Hitem_length.
  assert (Hposition : position = Znth first lens 0) by lia.
  unfold AppendRowPrefix in Happend.
  rewrite sublist_self in Happend by lia.
  unfold GreedyOutputPrefix.
  exists (done ++ [first]), (before ++ after).
  split.
  - rewrite <- app_assoc; simpl.
    change (Permutation (all_indices count)
        (done ++ (first :: before ++ after))).
    eapply Permutation_trans; [exact Hpermutation |].
    change (Permutation (done ++ (before ++ first :: after))
        (done ++ (first :: before ++ after))).
    apply Permutation_app_head.
    apply Permutation_sym.
    apply Permutation_middle.
  - split.
    + unfold MaskIndexes in *.
      intros index.
      rewrite lxor_shifted_one_true__output_finalization by
        (try lia; assumption).
      split.
      * intros Hin.
      assert (Hinold : In index (before ++ first :: after)).
      { apply in_app_iff in Hin.
        apply in_app_iff.
        destruct Hin as [Hin | Hin]; [left | right; right]; assumption. }
      pose proof (proj1 (Hmask index) Hinold) as [Hbounds Hbit].
      split; [exact Hbounds |].
      split; [exact Hbit |].
      intros ->; apply Hfirst_removed.
      exact Hin.
      * intros [Hbounds [Hbit Hneq]].
      pose proof (proj2 (Hmask index) (conj Hbounds Hbit)) as Hinold.
      apply in_app_iff in Hinold.
      apply in_app_iff.
      destruct Hinold as [Hin | [Heq | Hin]].
      -- left; exact Hin.
      -- exfalso; apply Hneq; symmetry; exact Heq.
      -- right; exact Hin.
    + split.
      * rewrite Happend, Hprior.
      rewrite concatenate_indices_app__output_finalization.
      rewrite concatenate_indices_singleton__output_finalization.
      reflexivity.
      * assert (Hmove :
          digit_lex_ge
            (concatenate_indices rows lens (first :: before ++ after))
            (concatenate_indices rows lens (before ++ first :: after))).
      { apply concatenate_move_best_front_ge__output_finalization.
        intros index Hindex.
        assert (Hinold : In index (before ++ first :: after)).
        { apply in_app_iff; left; exact Hindex. }
        pose proof (proj1 (Hmask index) Hinold) as [Hbounds Hbit].
        exact (Hbest index Hbounds Hbit). }
      assert (Hnew_old :
          digit_lex_ge
            (concatenate_indices rows lens
               (done ++ (first :: before ++ after)))
            (concatenate_indices rows lens
               (done ++ (before ++ first :: after)))).
      { rewrite !concatenate_indices_app__output_finalization.
        apply digit_lex_ge_append_left__output_finalization.
        rewrite <- concatenate_indices_app__output_finalization.
        exact Hmove. }
      assert (Hnew_permutation :
          Permutation (all_indices count)
            (done ++ (first :: before ++ after))).
      { eapply Permutation_trans; [exact Hpermutation |].
        apply Permutation_app_head.
        apply Permutation_sym.
        apply Permutation_middle. }
      pose proof Hlargest as Hlargest_copy.
      destruct Hlargest as
        [optimal_order [Hoptimal_permutation [Hoptimal_output Hoptimal]]].
      assert (Hnew_permutation_rows :
          Permutation (all_indices (Zlength rows))
            (done ++ (first :: before ++ after))).
      { rewrite (proj1 Hwf).
        exact Hnew_permutation. }
      pose proof (Hoptimal _ Hnew_permutation_rows) as Hold_new.
      assert (Hequal :
          concatenate_indices rows lens (done ++ (first :: before ++ after)) =
          concatenate_indices rows lens (done ++ (before ++ first :: after))).
      { apply digit_lex_ge_antisym__output_finalization; assumption. }
      rewrite <- app_assoc; simpl.
      rewrite Hequal.
      exact Hlargest_copy.
Qed.
