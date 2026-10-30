Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition zquad_1 (q : Z * Z * Z * Z) : Z :=
  fst (fst (fst q)).

Definition zquad_2 (q : Z * Z * Z * Z) : Z :=
  snd (fst (fst q)).

Definition zquad_3 (q : Z * Z * Z * Z) : Z :=
  snd (fst q).

Definition zquad_4 (q : Z * Z * Z * Z) : Z :=
  snd q.

Definition MatrixCell (matrix : list Z) (n i j : Z) : Z :=
  Znth (i * n + j) matrix 0.

Definition MatrixValuesBounded (matrix : list Z) (n : Z) : Prop :=
  forall k, 0 <= k < n * n -> 1 <= Znth k matrix 0 <= 1000000.

Definition QueriesBounded
    (queries : list (Z * Z * Z * Z)) (n : Z) : Prop :=
  Forall (fun query =>
    let '(x1, y1, x2, y2) := query in
    0 <= x1 <= x2 /\ x2 < n /\ 0 <= y1 <= y2 /\ y2 < n) queries.

Definition RawQueriesEncode
    (queries : list (Z * Z * Z * Z)) (raw : list Z) : Prop :=
  Zlength raw = 4 * Zlength queries /\
  forall i,
    0 <= i < Zlength queries ->
    let '(x1, y1, x2, y2) := Znth i queries (0, 0, 0, 0) in
    Znth (4 * i) raw 0 = x1 + 1 /\
    Znth (4 * i + 1) raw 0 = y1 + 1 /\
    Znth (4 * i + 2) raw 0 = x2 + 1 /\
    Znth (4 * i + 3) raw 0 = y2 + 1.

Definition PrefixSumValue (matrix : list Z) (n r c : Z) : Z :=
  fold_right Z.add 0
    (flat_map (fun i =>
      map (fun j => MatrixCell matrix n i j) (Zrange 0 c))
      (Zrange 0 r)).

Definition PrefixRowValue (matrix : list Z) (n r c : Z) : Z :=
  fold_right Z.add 0
    (flat_map (fun i =>
      map (fun j => MatrixCell matrix n i j * (i + 1)) (Zrange 0 c))
      (Zrange 0 r)).

Definition PrefixColValue (matrix : list Z) (n r c : Z) : Z :=
  fold_right Z.add 0
    (flat_map (fun i =>
      map (fun j => MatrixCell matrix n i j * (j + 1)) (Zrange 0 c))
      (Zrange 0 r)).

Definition PrefixTables
    (matrix sums rows cols : list Z) (n stride upto : Z) : Prop :=
  Zlength sums = stride * stride /\
  Zlength rows = stride * stride /\
  Zlength cols = stride * stride /\
  (forall r,
    0 <= r < stride ->
    Znth (r * stride) sums 0 = 0 /\
    Znth (r * stride) rows 0 = 0 /\
    Znth (r * stride) cols 0 = 0) /\
  forall r c,
    0 <= r < stride ->
    0 <= c < stride ->
    r * stride + c < upto ->
    Znth (r * stride + c) sums 0 = PrefixSumValue matrix n r c /\
    Znth (r * stride + c) rows 0 = PrefixRowValue matrix n r c /\
    Znth (r * stride + c) cols 0 = PrefixColValue matrix n r c.

Definition RectLookup
    (values : list Z) (stride x1 y1 x2 y2 : Z) : Z :=
  Znth (x2 * stride + y2) values 0 -
  Znth ((x1 - 1) * stride + y2) values 0 -
  Znth (x2 * stride + y1 - 1) values 0 +
  Znth ((x1 - 1) * stride + y1 - 1) values 0.

Definition RectanglesBounded
    (values : list Z) (stride bound : Z) : Prop :=
  forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    0 <= RectLookup values stride x1 y1 x2 y2 <= bound.

Definition RectIntermediatesSafe (values : list Z) (stride : Z) : Prop :=
  forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    let upper_right := Znth (x2 * stride + y2) values 0 in
    let upper_left := Znth ((x1 - 1) * stride + y2) values 0 in
    let lower_right := Znth (x2 * stride + y1 - 1) values 0 in
    -9223372036854775808 <= upper_right - upper_left <= 9223372036854775807 /\
    -9223372036854775808 <=
      upper_right - upper_left - lower_right <= 9223372036854775807.

Definition QueryArithmeticSafe
    (sums rows cols : list Z) (stride x1 y1 x2 y2 : Z) : Prop :=
  let sm := RectLookup sums stride x1 y1 x2 y2 in
  let rs := RectLookup rows stride x1 y1 x2 y2 in
  let cs := RectLookup cols stride x1 y1 x2 y2 in
  0 <= rs - x1 * sm <= 4000000000000000 /\
  0 <= cs - (y1 - 1) * sm <= 4002000000000000 /\
  0 <= (y2 - y1 + 1) * (rs - x1 * sm) +
       cs - (y1 - 1) * sm <= 8000002000000000000.

Definition TablesReady
    (matrix sums rows cols : list Z) (n stride : Z) : Prop :=
  PrefixTables matrix sums rows cols n stride (stride * stride) /\
  RectanglesBounded sums stride 4000000000000 /\
  RectanglesBounded rows stride 4002000000000000 /\
  RectanglesBounded cols stride 4002000000000000 /\
  RectIntermediatesSafe sums stride /\
  RectIntermediatesSafe rows stride /\
  RectIntermediatesSafe cols stride /\
  forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    QueryArithmeticSafe sums rows cols stride x1 y1 x2 y2.

Definition FlattenedWeightedSum
    (matrix : list Z) (n : Z) (query : Z * Z * Z * Z) (value : Z) : Prop :=
  let '(x1, y1, x2, y2) := query in
  value = fold_right Z.add 0
    (map (fun p =>
      let '(i, j) := p in
      MatrixCell matrix n i j *
        ((i - x1) * (y2 - y1 + 1) + (j - y1) + 1))
      (flat_map (fun i => map (fun j => (i, j)) (Zrange y1 (y2 + 1)))
                (Zrange x1 (x2 + 1)))).

Definition OutputPrefix
    (matrix : list Z) (n : Z) (queries : list (Z * Z * Z * Z))
    (out : list Z) (done : Z) : Prop :=
  Zlength out = done /\
  Forall2 (FlattenedWeightedSum matrix n) (sublist 0 done queries) out.

Definition Spec (matrix : list Z) (n : Z)
    (queries : list (Z * Z * Z * Z)) (out : list Z) : Prop :=
  Forall2 (FlattenedWeightedSum matrix n) queries out.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.micromega.Lia Coq.micromega.Psatz Coq.setoid_ring.Ring.
Lemma prefix_tables_repeat_zero_initial__prefix_init_boundary :
  forall matrix n,
    1 <= n ->
    PrefixTables matrix
      (repeat 0 (Z.to_nat ((n + 1) * (n + 1))))
      (repeat 0 (Z.to_nat ((n + 1) * (n + 1))))
      (repeat 0 (Z.to_nat ((n + 1) * (n + 1))))
      n (n + 1) (n + 1).
Proof.
  intros matrix n Hn.
  unfold PrefixTables.
  split.
  - rewrite Zlength_correct, repeat_length. lia.
  - split.
    + rewrite Zlength_correct, repeat_length. lia.
    + split.
      * rewrite Zlength_correct, repeat_length. lia.
      * split.
        -- intros r Hr.
           repeat split; apply Znth_repeat.
        -- intros r c Hr Hc Hidx.
           assert (Hr0 : r = 0) by nia.
           subst r.
           repeat split.
           ++ rewrite Znth_repeat.
              unfold PrefixSumValue. reflexivity.
           ++ rewrite Znth_repeat.
              unfold PrefixRowValue. reflexivity.
           ++ rewrite Znth_repeat.
              unfold PrefixColValue. reflexivity.
Qed.
Lemma prefix_tables_extend_zero_column__prefix_init_boundary :
  forall matrix sums rows cols n S i,
    1 <= n ->
    S = n + 1 ->
    0 <= i < S ->
    PrefixTables matrix sums rows cols n S (i * S) ->
    PrefixTables matrix sums rows cols n S (i * S + 1).
Proof.
  intros matrix sums rows cols n S i Hn HS Hi Htables.
  unfold PrefixTables in Htables |- *.
  destruct Htables as [Hsums [Hrows [Hcols [Hzero Hprefix]]]].
  split; [exact Hsums |].
  split; [exact Hrows |].
  split; [exact Hcols |].
  split; [exact Hzero |].
  intros r c Hr Hc Hidx.
  destruct (Z_lt_ge_dec (r * S + c) (i * S)) as [Hlt | Hge].
  - exact (Hprefix r c Hr Hc Hlt).
  - assert (Heq : r * S + c = i * S) by lia.
    assert (Hri : r = i) by nia.
    assert (Hc0 : c = 0) by nia.
    subst r; subst c.
    specialize (Hzero i Hi).
    destruct Hzero as [Hzs [Hzr Hzc]].
    rewrite Z.add_0_r.
    repeat split.
    + rewrite Hzs. unfold PrefixSumValue. simpl.
      induction (Zrange 0 i); simpl; auto.
    + rewrite Hzr. unfold PrefixRowValue. simpl.
      induction (Zrange 0 i); simpl; auto.
    + rewrite Hzc. unfold PrefixColValue. simpl.
      induction (Zrange 0 i); simpl; auto.
Qed.
Lemma Zlength_Zrange_aux__prefix_sum_safety : forall low count,
  Zlength (Zrange_aux low count) = Z.of_nat count.
Proof.
  intros low count. revert low.
  induction count; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IHcount. lia.
Qed.
Lemma Zlength_Zrange__prefix_sum_safety : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle.
  unfold Zrange.
  rewrite Zlength_Zrange_aux__prefix_sum_safety, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma Zrange_snoc__prefix_sum_safety : forall high,
  1 <= high ->
  Zrange 0 high = Zrange 0 (high - 1) ++ [high - 1].
Proof.
  intros high Hhigh.
  unfold Zrange.
  replace (Z.to_nat (high - 0))
    with (Z.to_nat (high - 1 - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  simpl.
  rewrite Z2Nat.id by lia.
  replace (0 + (high - 1)) with (high - 1) by lia.
  replace (high - 1 - 0) with (high - 1) by lia.
  reflexivity.
Qed.
Lemma fold_right_Zadd_app__prefix_sum_safety : forall left right,
  fold_right Z.add 0 (left ++ right) =
  fold_right Z.add 0 left + fold_right Z.add 0 right.
Proof.
  intros left right.
  induction left; simpl; lia.
Qed.
Lemma sum_map_Zrange_snoc__prefix_sum_safety : forall f high,
  1 <= high ->
  fold_right Z.add 0 (map f (Zrange 0 high)) =
  fold_right Z.add 0 (map f (Zrange 0 (high - 1))) + f (high - 1).
Proof.
  intros f high Hhigh.
  rewrite Zrange_snoc__prefix_sum_safety by exact Hhigh.
  rewrite map_app.
  rewrite fold_right_Zadd_app__prefix_sum_safety. simpl. lia.
Qed.
Lemma sum_flat_map_col_snoc__prefix_sum_safety :
  forall rows high (f : Z -> Z -> Z),
    1 <= high ->
    fold_right Z.add 0
      (flat_map (fun i => map (f i) (Zrange 0 high)) rows) =
    fold_right Z.add 0
      (flat_map (fun i => map (f i) (Zrange 0 (high - 1))) rows) +
    fold_right Z.add 0 (map (fun i => f i (high - 1)) rows).
Proof.
  intros rows high f Hhigh.
  induction rows as [|a rows IH]; simpl.
  - lia.
  - rewrite !fold_right_Zadd_app__prefix_sum_safety.
    rewrite sum_map_Zrange_snoc__prefix_sum_safety by exact Hhigh.
    lia.
Qed.
Lemma prefix_sum_value_cell_recurrence__prefix_sum_safety : forall matrix n r c,
  1 <= r -> 1 <= c ->
  PrefixSumValue matrix n r c =
    MatrixCell matrix n (r - 1) (c - 1) +
    PrefixSumValue matrix n (r - 1) c +
    PrefixSumValue matrix n r (c - 1) -
    PrefixSumValue matrix n (r - 1) (c - 1).
Proof.
  intros matrix n r c Hr Hc.
  unfold PrefixSumValue.
  rewrite (Zrange_snoc__prefix_sum_safety r Hr).
  rewrite !flat_map_app. simpl.
  rewrite !fold_right_Zadd_app__prefix_sum_safety.
  rewrite !(sum_flat_map_col_snoc__prefix_sum_safety
    (Zrange 0 (r - 1)) c (fun i j => MatrixCell matrix n i j) Hc).
  rewrite (sum_map_Zrange_snoc__prefix_sum_safety
    (fun j => MatrixCell matrix n (r - 1) j) c Hc).
  lia.
Qed.
Lemma prefix_predecessor_indices__prefix_sum_safety : forall S i j,
  1 <= S ->
  i * S + j - S = (i - 1) * S + j /\
  i * S + j - 1 = i * S + (j - 1) /\
  i * S + j - S - 1 = (i - 1) * S + (j - 1) /\
  (i - 1) * S + j < i * S + j /\
  i * S + (j - 1) < i * S + j /\
  (i - 1) * S + (j - 1) < i * S + j.
Proof.
  intros S i j HS.
  repeat split; nia.
Qed.
Lemma matrix_cell_index__prefix_sum_safety : forall matrix n i j,
  Znth (((i - 1) * n + j) - 1) matrix 0 =
  MatrixCell matrix n (i - 1) (j - 1).
Proof.
  intros matrix n i j.
  unfold MatrixCell.
  f_equal. ring.
Qed.
Lemma fold_right_add_Forall_bounds__prefix_sum_safety : forall values bound,
  0 <= bound ->
  Forall (fun value => 0 <= value <= bound) values ->
  0 <= fold_right Z.add 0 values <= Zlength values * bound.
Proof.
  intros values bound Hbound Hvalues.
  induction Hvalues; simpl.
  - lia.
  - rewrite Zlength_cons. lia.
Qed.
Lemma Zlength_map__prefix_sum_safety : forall (A B : Type) (f : A -> B) values,
  Zlength (map f values) = Zlength values.
Proof.
  intros A B f values.
  induction values; simpl.
  - reflexivity.
  - rewrite !Zlength_cons, IHvalues. reflexivity.
Qed.
Lemma Zlength_flat_map_rect__prefix_sum_safety :
  forall (A B : Type) (rows : list A) (f : A -> list B) width,
    (forall row, In row rows -> Zlength (f row) = width) ->
    Zlength (flat_map f rows) = Zlength rows * width.
Proof.
  intros A B rows f width Hwidth.
  induction rows as [|a rows IH]; simpl.
  - reflexivity.
  - rewrite Zlength_app, Zlength_cons.
    rewrite Hwidth by (left; reflexivity).
    rewrite IH.
    + ring.
    + intros row Hrow. apply Hwidth. right. exact Hrow.
Qed.
Lemma prefix_sum_value_bounds__prefix_sum_safety : forall matrix n r c,
  MatrixValuesBounded matrix n ->
  0 <= n <= 2000 ->
  0 <= r <= n ->
  0 <= c <= n ->
  0 <= PrefixSumValue matrix n r c <= 4000000000000.
Proof.
  intros matrix n r c Hmatrix Hn Hr Hc.
  unfold PrefixSumValue.
  assert (Hvalues :
    Forall (fun value => 0 <= value <= 1000000)
      (flat_map
        (fun i => map (fun j => MatrixCell matrix n i j) (Zrange 0 c))
        (Zrange 0 r))).
  {
    apply Forall_forall.
    intros value Hvalue.
    apply in_flat_map in Hvalue.
    destruct Hvalue as [ri [Hri Hvalue]].
    apply in_map_iff in Hvalue.
    destruct Hvalue as [cj [Hvalue Hcj]].
    subst value.
    apply (proj2 (In_Zrange 0 r ri)) in Hri.
    apply (proj2 (In_Zrange 0 c cj)) in Hcj.
    unfold MatrixCell.
    specialize (Hmatrix (ri * n + cj)).
    assert (0 <= ri * n + cj < n * n) by nia.
    specialize (Hmatrix H).
    lia.
  }
  pose proof
    (fold_right_add_Forall_bounds__prefix_sum_safety _ 1000000 (ltac:(lia)) Hvalues)
    as Hsum.
  assert (Hlen :
    Zlength
      (flat_map
        (fun i => map (fun j => MatrixCell matrix n i j) (Zrange 0 c))
        (Zrange 0 r)) = r * c).
  {
    rewrite Zlength_flat_map_rect__prefix_sum_safety with (width := c).
    - rewrite Zlength_Zrange__prefix_sum_safety by lia. ring.
    - intros row Hrow.
      rewrite Zlength_map__prefix_sum_safety.
      rewrite Zlength_Zrange__prefix_sum_safety by lia. lia.
  }
  rewrite Hlen in Hsum.
  nia.
Qed.
Lemma zrange_zero_snoc__prefix_row_safety : forall k,
  1 <= k ->
  Zrange 0 k = Zrange 0 (k - 1) ++ [k - 1].
Proof.
  intros k Hk.
  unfold Zrange.
  replace (k - 0) with k by lia.
  replace (k - 1 - 0) with (k - 1) by lia.
  replace (Z.to_nat k) with
      (Z.to_nat (k - 1) + 1)%nat by
    (apply Nat2Z.inj; rewrite Nat2Z.inj_add;
     repeat rewrite Z2Nat.id by lia; simpl; lia).
  rewrite Zrange_aux_app.
  rewrite Z2Nat.id by lia.
  simpl.
  replace (0 + (k - 1)) with (k - 1) by lia.
  reflexivity.
Qed.
Lemma fold_right_add_app__prefix_row_safety : forall xs ys,
  fold_right Z.add 0 (xs ++ ys) =
  fold_right Z.add 0 xs + fold_right Z.add 0 ys.
Proof.
  intros xs ys. induction xs as [|x xs IH]; simpl; lia.
Qed.
Lemma prefix_row_slice_snoc__prefix_row_safety :
  forall matrix n row c,
    1 <= c ->
    fold_right Z.add 0
      (map (fun j => MatrixCell matrix n row j * (row + 1))
           (Zrange 0 c)) =
    fold_right Z.add 0
      (map (fun j => MatrixCell matrix n row j * (row + 1))
           (Zrange 0 (c - 1))) +
    MatrixCell matrix n row (c - 1) * (row + 1).
Proof.
  intros matrix n row c Hc.
  rewrite zrange_zero_snoc__prefix_row_safety by lia.
  rewrite map_app, fold_right_add_app__prefix_row_safety.
  simpl. lia.
Qed.
Lemma prefix_row_value_snoc__prefix_row_safety :
  forall matrix n r c,
    1 <= r ->
    PrefixRowValue matrix n r c =
    PrefixRowValue matrix n (r - 1) c +
    fold_right Z.add 0
      (map (fun j => MatrixCell matrix n (r - 1) j * r)
           (Zrange 0 c)).
Proof.
  intros matrix n r c Hr.
  unfold PrefixRowValue.
  rewrite (zrange_zero_snoc__prefix_row_safety r Hr).
  rewrite flat_map_app, fold_right_add_app__prefix_row_safety.
  simpl.
  replace (r - 1 + 1) with r by lia.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma prefix_row_slice_bounds__prefix_row_safety :
  forall matrix n row c,
    MatrixValuesBounded matrix n ->
    0 <= row < n ->
    0 <= c <= n ->
    0 <= fold_right Z.add 0
      (map (fun j => MatrixCell matrix n row j * (row + 1))
           (Zrange 0 c)) <= c * 1000000 * (row + 1).
Proof.
  intros matrix n row c Hmatrix Hrow Hc.
  unfold MatrixValuesBounded in Hmatrix.
  assert (Hnat : forall m : nat,
    Z.of_nat m <= n ->
    0 <= fold_right Z.add 0
      (map (fun j => MatrixCell matrix n row j * (row + 1))
           (Zrange 0 (Z.of_nat m))) <=
      Z.of_nat m * 1000000 * (row + 1)).
  {
    intros m. induction m as [|m IH].
    - simpl. lia.
    - rewrite Nat2Z.inj_succ. unfold Z.succ. intros Hmn.
      rewrite (prefix_row_slice_snoc__prefix_row_safety
        matrix n row (Z.of_nat m + 1) ltac:(lia)).
      replace (Z.of_nat m + 1 - 1) with (Z.of_nat m) by lia.
      specialize (IH ltac:(lia)).
      pose proof
        (Hmatrix (row * n + Z.of_nat m) ltac:(nia))
        as Hcell.
      change (1 <= MatrixCell matrix n row (Z.of_nat m) <= 1000000)
        in Hcell.
      assert (Hweighted :
        0 <= MatrixCell matrix n row (Z.of_nat m) * (row + 1) <=
          1000000 * (row + 1)).
      { nia. }
      replace ((Z.of_nat m + 1) * 1000000 * (row + 1)) with
        (Z.of_nat m * 1000000 * (row + 1) + 1000000 * (row + 1))
        by ring.
      lia.
  }
  specialize (Hnat (Z.to_nat c)).
  rewrite Z2Nat.id in Hnat by lia.
  apply Hnat. lia.
Qed.
Lemma prefix_row_value_bounds__prefix_row_safety :
  forall matrix n r c,
    MatrixValuesBounded matrix n ->
    1 <= n <= 2000 ->
    0 <= r <= n ->
    0 <= c <= n ->
    0 <= PrefixRowValue matrix n r c <= 4002000000000000.
Proof.
  intros matrix n r c Hmatrix Hn Hr Hc.
  assert (Hprecise :
    0 <= PrefixRowValue matrix n r c /\
    2 * PrefixRowValue matrix n r c <=
      c * 1000000 * r * (r + 1)).
  {
    assert (Hnat : forall m : nat,
      Z.of_nat m <= n ->
      0 <= PrefixRowValue matrix n (Z.of_nat m) c /\
      2 * PrefixRowValue matrix n (Z.of_nat m) c <=
      c * 1000000 * Z.of_nat m * (Z.of_nat m + 1)).
    {
      intros m. induction m as [|m IH].
      - unfold PrefixRowValue, Zrange. simpl. lia.
      - rewrite Nat2Z.inj_succ. unfold Z.succ. intros Hmn.
        rewrite (prefix_row_value_snoc__prefix_row_safety
          matrix n (Z.of_nat m + 1) c ltac:(lia)).
        replace (Z.of_nat m + 1 - 1) with (Z.of_nat m) by lia.
        specialize (IH ltac:(lia)).
        pose proof
          (prefix_row_slice_bounds__prefix_row_safety
             matrix n (Z.of_nat m) c Hmatrix ltac:(lia) Hc)
          as Hslice.
        replace
          (c * 1000000 * (Z.of_nat m + 1) * (Z.of_nat m + 1 + 1))
          with
          (c * 1000000 * Z.of_nat m * (Z.of_nat m + 1) +
           2 * (c * 1000000 * (Z.of_nat m + 1)))
          by ring.
        lia.
    }
    specialize (Hnat (Z.to_nat r)).
    rewrite Z2Nat.id in Hnat by lia.
    apply Hnat. lia.
  }
  destruct Hprecise as [Hlo Htwice].
  split; [exact Hlo|].
  nia.
Qed.
Lemma prefix_row_value_cell_recurrence__prefix_row_safety :
  forall matrix n r c,
    1 <= r -> 1 <= c ->
    MatrixCell matrix n (r - 1) (c - 1) * r +
      PrefixRowValue matrix n (r - 1) c +
      PrefixRowValue matrix n r (c - 1) -
      PrefixRowValue matrix n (r - 1) (c - 1) =
    PrefixRowValue matrix n r c.
Proof.
  intros matrix n r c Hr Hc.
  rewrite (prefix_row_value_snoc__prefix_row_safety matrix n r c Hr).
  rewrite (prefix_row_value_snoc__prefix_row_safety matrix n r (c - 1) Hr).
  pose proof
    (prefix_row_slice_snoc__prefix_row_safety matrix n (r - 1) c Hc)
    as Hslice.
  replace (r - 1 + 1) with r in Hslice by lia.
  rewrite Hslice.
  ring.
Qed.
Lemma fold_add_map__prefix_col_safety :
  forall (A : Type) (xs : list A) (f : A -> Z),
    fold_right Z.add 0 (map f xs) =
    fold_right (fun x acc => f x + acc) 0 xs.
Proof.
  intros A xs f.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma fold_add_flat_map_map__prefix_col_safety :
  forall (A B : Type) (xs : list A) (ys : list B) (f : A -> B -> Z),
    fold_right Z.add 0 (flat_map (fun x => map (f x) ys) xs) =
    fold_right
      (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
      0 xs.
Proof.
  intros A B xs ys f.
  induction xs as [|x xs IH].
  - reflexivity.
  - change
      (ListLib.sum (map (f x) ys ++ flat_map (fun x => map (f x) ys) xs) =
       fold_right (fun y acc => f x y + acc) 0 ys +
       fold_right
         (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
         0 xs).
    rewrite ListLib.sum_app.
    rewrite fold_add_map__prefix_col_safety.
    change
      (fold_right (fun y acc => f x y + acc) 0 ys +
       fold_right Z.add 0 (flat_map (fun x => map (f x) ys) xs) =
       fold_right (fun y acc => f x y + acc) 0 ys +
       fold_right
         (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
         0 xs).
    rewrite IH. reflexivity.
Qed.
Lemma prefix_col_value_as_nested_sum__prefix_col_safety :
  forall matrix n r c,
    PrefixColValue matrix n r c =
      SumLib.Sum.sum (fun i => 0 <= i < r) (fun i =>
        SumLib.Sum.sum (fun j => 0 <= j < c) (fun j =>
          MatrixCell matrix n i j * (j + 1))).
Proof.
  intros matrix n r c.
  unfold PrefixColValue.
  rewrite fold_add_flat_map_map__prefix_col_safety.
  rewrite SumLib.ZRange.sum_range_unfold.
  generalize (Zrange 0 r) as xs. intro xs.
  induction xs as [|i xs IH]; simpl; [reflexivity|].
  rewrite IH, SumLib.ZRange.sum_range_unfold. reflexivity.
Qed.
Lemma twice_fold_zrange_aux_succ__prefix_col_safety :
  forall m low,
    2 * fold_right (fun j acc => (j + 1) + acc) 0
          (SumLib.ZRange.Zrange_aux low m) =
    Z.of_nat m * (2 * low + Z.of_nat m + 1).
Proof.
  induction m as [|m IH]; intros low;
    cbn [SumLib.ZRange.Zrange_aux fold_right].
  - ring.
  - specialize (IH (low + 1)).
    rewrite Nat2Z.inj_succ.
    rewrite Z.mul_add_distr_l.
    rewrite IH.
    ring.
Qed.
Lemma twice_sum_index_succ__prefix_col_safety :
  forall c,
    0 <= c ->
    2 * SumLib.Sum.sum (fun j => 0 <= j < c) (fun j => j + 1) =
    c * (c + 1).
Proof.
  intros c Hc.
  rewrite SumLib.ZRange.sum_range_unfold.
  unfold Zrange.
  rewrite twice_fold_zrange_aux_succ__prefix_col_safety.
  rewrite Z2Nat.id by lia.
  nia.
Qed.
Lemma nested_prefix_recurrence__prefix_col_safety :
  forall (f : Z -> Z -> Z) i j,
    1 <= i -> 1 <= j ->
    SumLib.Sum.sum (fun x => 0 <= x < i) (fun x =>
      SumLib.Sum.sum (fun y => 0 <= y < j) (fun y => f x y)) =
    f (i - 1) (j - 1) +
    SumLib.Sum.sum (fun x => 0 <= x < i - 1) (fun x =>
      SumLib.Sum.sum (fun y => 0 <= y < j) (fun y => f x y)) +
    SumLib.Sum.sum (fun x => 0 <= x < i) (fun x =>
      SumLib.Sum.sum (fun y => 0 <= y < j - 1) (fun y => f x y)) -
    SumLib.Sum.sum (fun x => 0 <= x < i - 1) (fun x =>
      SumLib.Sum.sum (fun y => 0 <= y < j - 1) (fun y => f x y)).
Proof.
  intros f i j Hi Hj.
  pose proof
    (SumLib.ZRange.sum_Z_range_extend_right 0 (i - 1)
      (fun x => SumLib.Sum.sum (fun y => 0 <= y < j) (fun y => f x y))
      ltac:(lia)) as Houter_j.
  pose proof
    (SumLib.ZRange.sum_Z_range_extend_right 0 (i - 1)
      (fun x => SumLib.Sum.sum (fun y => 0 <= y < j - 1) (fun y => f x y))
      ltac:(lia)) as Houter_prev.
  pose proof
    (SumLib.ZRange.sum_Z_range_extend_right 0 (j - 1)
      (fun y => f (i - 1) y) ltac:(lia)) as Hinner.
  replace (i - 1 + 1) with i in Houter_j, Houter_prev by lia.
  replace (j - 1 + 1) with j in Hinner by lia.
  nia.
Qed.
Lemma prefix_col_value_cell_recurrence__prefix_col_safety :
  forall matrix n i j,
    1 <= i -> 1 <= j ->
    PrefixColValue matrix n i j =
      MatrixCell matrix n (i - 1) (j - 1) * j +
      PrefixColValue matrix n (i - 1) j +
      PrefixColValue matrix n i (j - 1) -
      PrefixColValue matrix n (i - 1) (j - 1).
Proof.
  intros matrix n i j Hi Hj.
  rewrite !prefix_col_value_as_nested_sum__prefix_col_safety.
  pose proof
    (nested_prefix_recurrence__prefix_col_safety
      (fun x y => MatrixCell matrix n x y * (y + 1)) i j Hi Hj) as H.
  cbv beta in H.
  replace (j - 1 + 1) with j in H by lia.
  exact H.
Qed.
Lemma prefix_col_value_bounds__prefix_col_safety :
  forall matrix n r c,
    MatrixValuesBounded matrix n ->
    1 <= n <= 2000 ->
    0 <= r <= n ->
    0 <= c <= n ->
    0 <= PrefixColValue matrix n r c <= 4002000000000000.
Proof.
  intros matrix n r c Hmatrix Hn Hr Hc.
  rewrite prefix_col_value_as_nested_sum__prefix_col_safety.
  set (inner := fun i =>
    SumLib.Sum.sum (fun j => 0 <= j < c) (fun j =>
      MatrixCell matrix n i j * (j + 1))).
  assert (Hinner : forall i, 0 <= i < r ->
      0 <= 2 * inner i <= 1000000 * c * (c + 1)).
  {
    intros i Hi.
    assert (Hcell : forall j, 0 <= j < c ->
        1 <= MatrixCell matrix n i j <= 1000000).
    {
      intros j Hj.
      unfold MatrixCell.
      apply Hmatrix.
      nia.
    }
    assert (Hnonneg : 0 <= inner i).
    {
      unfold inner.
      pose proof
        (SumLib.ZRange.sum_Z_range_lower_bound 0 c
          (fun j => MatrixCell matrix n i j * (j + 1)) 0
          ltac:(lia)) as H.
      specialize (H ltac:(intros j Hj; pose proof (Hcell j Hj); nia)).
      simpl in H. nia.
    }
    assert (Hupper : inner i <=
        SumLib.Sum.sum (fun j => 0 <= j < c)
          (fun j => 1000000 * (j + 1))).
    {
      unfold inner.
      apply SumLib.ZRange.sum_Z_range_le.
      intros j Hj. pose proof (Hcell j Hj). nia.
    }
    rewrite SumLib.ZRange.sum_Z_range_factor_l in Hupper.
    pose proof (twice_sum_index_succ__prefix_col_safety c ltac:(lia))
      as Hweights.
    nia.
  }
  assert (Hdoubled :
      0 <= 2 * SumLib.Sum.sum (fun i => 0 <= i < r) inner <=
      r * (1000000 * c * (c + 1))).
  {
    rewrite <- SumLib.ZRange.sum_Z_range_factor_l.
    pose proof
      (SumLib.ZRange.sum_Z_range_bounds 0 r
        (fun i => 2 * inner i) 0 (1000000 * c * (c + 1))
        ltac:(lia) Hinner) as H.
    nia.
  }
  assert (Hcprod : c * (c + 1) <= 2000 * 2001) by nia.
  assert (Hrprod : r * (c * (c + 1)) <= 2000 * (2000 * 2001)) by nia.
  nia.
Qed.
Lemma weighted_cell_bounds__prefix_col_safety :
  forall x j,
    1 <= x <= 1000000 ->
    1 <= j <= 2000 ->
    0 <= x * j <= 2000000000.
Proof.
  intros x j Hx Hj. nia.
Qed.
Lemma Zrange_zero_snoc__prefix_update : forall k,
  0 <= k -> Zrange 0 (k + 1) = Zrange 0 k ++ [k].
Proof.
  intros k Hk. unfold Zrange.
  replace (Z.to_nat (k + 1 - 0)) with (Z.to_nat (k - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app. simpl.
  replace (k - 0) with k by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma row_sum_snoc__prefix_update :
  forall (f : Z -> Z -> Z) r c,
    0 <= c ->
    fold_right Z.add 0 (map (fun y => f r y) (Zrange 0 (c + 1))) =
    fold_right Z.add 0 (map (fun y => f r y) (Zrange 0 c)) + f r c.
Proof.
  intros f r c Hc.
  change (ListLib.sum (map (fun y => f r y) (Zrange 0 (c + 1))) =
    ListLib.sum (map (fun y => f r y) (Zrange 0 c)) + f r c).
  rewrite (Zrange_zero_snoc__prefix_update c Hc), map_app, sum_app.
  unfold ListLib.sum. simpl. lia.
Qed.
Lemma rectangle_sum_row_snoc__prefix_update :
  forall (f : Z -> Z -> Z) r c,
    0 <= r ->
    fold_right Z.add 0
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 c))
        (Zrange 0 (r + 1))) =
    fold_right Z.add 0
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 c))
        (Zrange 0 r)) +
    fold_right Z.add 0 (map (fun y => f r y) (Zrange 0 c)).
Proof.
  intros f r c Hr.
  change (ListLib.sum
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 c))
        (Zrange 0 (r + 1))) =
    ListLib.sum
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 c))
        (Zrange 0 r)) +
    ListLib.sum (map (fun y => f r y) (Zrange 0 c))).
  rewrite (Zrange_zero_snoc__prefix_update r Hr), flat_map_app, sum_app.
  simpl. rewrite ?app_nil_r. reflexivity.
Qed.
Lemma rectangle_sum_step__prefix_update :
  forall (f : Z -> Z -> Z) r c,
    0 <= r -> 0 <= c ->
    fold_right Z.add 0
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 (c + 1)))
        (Zrange 0 (r + 1))) =
    f r c +
    fold_right Z.add 0
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 (c + 1)))
        (Zrange 0 r)) +
    fold_right Z.add 0
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 c))
        (Zrange 0 (r + 1))) -
    fold_right Z.add 0
      (flat_map (fun x => map (fun y => f x y) (Zrange 0 c))
        (Zrange 0 r)).
Proof.
  intros f r c Hr Hc.
  pose proof (rectangle_sum_row_snoc__prefix_update
    f r (c + 1) Hr) as Hwide.
  pose proof (rectangle_sum_row_snoc__prefix_update
    f r c Hr) as Hnarrow.
  pose proof (row_sum_snoc__prefix_update f r c Hc) as Hrow.
  lia.
Qed.
Lemma prefix_sum_value_step__prefix_update : forall matrix n r c,
  0 <= r -> 0 <= c ->
  PrefixSumValue matrix n (r + 1) (c + 1) =
    MatrixCell matrix n r c +
    PrefixSumValue matrix n r (c + 1) +
    PrefixSumValue matrix n (r + 1) c -
    PrefixSumValue matrix n r c.
Proof.
  intros matrix n r c Hr Hc.
  unfold PrefixSumValue.
  exact (rectangle_sum_step__prefix_update
    (fun x y => MatrixCell matrix n x y) r c Hr Hc).
Qed.
Lemma prefix_row_value_step__prefix_update : forall matrix n r c,
  0 <= r -> 0 <= c ->
  PrefixRowValue matrix n (r + 1) (c + 1) =
    MatrixCell matrix n r c * (r + 1) +
    PrefixRowValue matrix n r (c + 1) +
    PrefixRowValue matrix n (r + 1) c -
    PrefixRowValue matrix n r c.
Proof.
  intros matrix n r c Hr Hc.
  unfold PrefixRowValue.
  exact (rectangle_sum_step__prefix_update
    (fun x y => MatrixCell matrix n x y * (x + 1)) r c Hr Hc).
Qed.
Lemma prefix_col_value_step__prefix_update : forall matrix n r c,
  0 <= r -> 0 <= c ->
  PrefixColValue matrix n (r + 1) (c + 1) =
    MatrixCell matrix n r c * (c + 1) +
    PrefixColValue matrix n r (c + 1) +
    PrefixColValue matrix n (r + 1) c -
    PrefixColValue matrix n r c.
Proof.
  intros matrix n r c Hr Hc.
  unfold PrefixColValue.
  exact (rectangle_sum_step__prefix_update
    (fun x y => MatrixCell matrix n x y * (y + 1)) r c Hr Hc).
Qed.
Lemma flat_index_injective__prefix_update : forall stride r c i j,
  0 < stride ->
  0 <= r < stride -> 0 <= c < stride ->
  0 <= i < stride -> 0 <= j < stride ->
  r * stride + c = i * stride + j ->
  r = i /\ c = j.
Proof.
  intros stride r c i j Hstride Hr Hc Hi Hj Heq.
  destruct (Z.lt_trichotomy r i) as [Hlt | [Heqi | Hgt]].
  - exfalso. nia.
  - subst r. split; [reflexivity | lia].
  - exfalso. nia.
Qed.
Lemma prefix_tables_replace_step__prefix_transition :
  forall matrix sums rows cols n i j,
    1 <= n ->
    1 <= i <= n ->
    1 <= j <= n ->
    PrefixTables matrix sums rows cols n (n + 1) (i * (n + 1) + j) ->
    PrefixTables matrix
      (replace_Znth (i * (n + 1) + j)
        (Znth (((i - 1) * n + j) - 1) matrix 0 +
         Znth ((i * (n + 1) + j) - (n + 1)) sums 0 +
         Znth ((i * (n + 1) + j) - 1) sums 0 -
         Znth (((i * (n + 1) + j) - (n + 1)) - 1) sums 0) sums)
      (replace_Znth (i * (n + 1) + j)
        (Znth (((i - 1) * n + j) - 1) matrix 0 * i +
         Znth ((i * (n + 1) + j) - (n + 1)) rows 0 +
         Znth ((i * (n + 1) + j) - 1) rows 0 -
         Znth (((i * (n + 1) + j) - (n + 1)) - 1) rows 0) rows)
      (replace_Znth (i * (n + 1) + j)
        (Znth (((i - 1) * n + j) - 1) matrix 0 * j +
         Znth ((i * (n + 1) + j) - (n + 1)) cols 0 +
         Znth ((i * (n + 1) + j) - 1) cols 0 -
         Znth (((i * (n + 1) + j) - (n + 1)) - 1) cols 0) cols)
      n (n + 1) (i * (n + 1) + (j + 1)).
Proof.
  intros matrix sums rows cols n i j Hn Hi Hj Htables.
  unfold PrefixTables in Htables |- *.
  destruct Htables as [Hsums [Hrows [Hcols [Hzero Hprefix]]]].
  split.
  - rewrite Zlength_replace_Znth, Hsums. reflexivity.
  - split.
    + rewrite Zlength_replace_Znth, Hrows. reflexivity.
    + split.
      * rewrite Zlength_replace_Znth, Hcols. reflexivity.
      * split.
        -- intros r Hr.
           assert (Hneq : r * (n + 1) <> i * (n + 1) + j).
           { intro Heq.
             assert (Hflat : r * (n + 1) + 0 = i * (n + 1) + j) by lia.
             pose proof (flat_index_injective__prefix_update
               (n + 1) r 0 i j ltac:(lia) Hr ltac:(lia)
               ltac:(lia) ltac:(lia) Hflat) as Hbad. lia. }
           destruct (Hzero r Hr) as [Hsum [Hrow Hcol]].
           rewrite !Znth_replace_Znth_Diff by
             (rewrite ?Hsums, ?Hrows, ?Hcols; nia).
           auto.
        -- { intros r c Hr Hc Hidx.
    assert (Hstride : 0 < n + 1) by lia.
    assert (Hcurrent : 0 <= i * (n + 1) + j < (n + 1) * (n + 1)) by nia.
    assert (Hquery : 0 <= r * (n + 1) + c < (n + 1) * (n + 1)) by nia.
    destruct (Z.eq_dec (r * (n + 1) + c) (i * (n + 1) + j))
      as [Heq | Hneq].
    + destruct (flat_index_injective__prefix_update
        (n + 1) r c i j Hstride Hr Hc ltac:(lia) ltac:(lia) Heq) as [-> ->].
      assert (Hup := Hprefix (i - 1) j).
      assert (Hleft := Hprefix i (j - 1)).
      assert (Hdiag := Hprefix (i - 1) (j - 1)).
      specialize (Hup ltac:(lia) ltac:(lia) ltac:(nia)).
      specialize (Hleft ltac:(lia) ltac:(lia) ltac:(nia)).
      specialize (Hdiag ltac:(lia) ltac:(lia) ltac:(nia)).
      destruct Hup as [Hup_sum [Hup_row Hup_col]].
      destruct Hleft as [Hleft_sum [Hleft_row Hleft_col]].
      destruct Hdiag as [Hdiag_sum [Hdiag_row Hdiag_col]].
      rewrite !Znth_replace_Znth_Same by
        (rewrite ?Hsums, ?Hrows, ?Hcols; exact Hcurrent).
      replace ((i * (n + 1) + j) - (n + 1))
        with ((i - 1) * (n + 1) + j) by ring.
      replace ((i * (n + 1) + j) - 1)
        with (i * (n + 1) + (j - 1)) by ring.
      replace (((i * (n + 1) + j) - (n + 1)) - 1)
        with ((i - 1) * (n + 1) + (j - 1)) by ring.
      replace (((i - 1) * (n + 1) + j) - 1)
        with ((i - 1) * (n + 1) + (j - 1)) by ring.
      split.
      * rewrite Hup_sum, Hleft_sum, Hdiag_sum.
        pose proof (prefix_sum_value_step__prefix_update matrix n
          (i - 1) (j - 1) ltac:(lia) ltac:(lia)) as Hstep.
        unfold MatrixCell in Hstep.
        replace (((i - 1) * n + j) - 1) with ((i - 1) * n + (j - 1)) by ring.
        replace (i - 1 + 1) with i in Hstep by ring.
        replace (j - 1 + 1) with j in Hstep by ring.
        symmetry. exact Hstep.
      * split.
        -- rewrite Hup_row, Hleft_row, Hdiag_row.
           pose proof (prefix_row_value_step__prefix_update matrix n
             (i - 1) (j - 1) ltac:(lia) ltac:(lia)) as Hstep.
           unfold MatrixCell in Hstep.
           replace (((i - 1) * n + j) - 1) with ((i - 1) * n + (j - 1)) by ring.
           replace (i - 1 + 1) with i in Hstep by ring.
           replace (j - 1 + 1) with j in Hstep by ring.
           symmetry. exact Hstep.
        -- rewrite Hup_col, Hleft_col, Hdiag_col.
           pose proof (prefix_col_value_step__prefix_update matrix n
             (i - 1) (j - 1) ltac:(lia) ltac:(lia)) as Hstep.
           unfold MatrixCell in Hstep.
           replace (((i - 1) * n + j) - 1) with ((i - 1) * n + (j - 1)) by ring.
           replace (i - 1 + 1) with i in Hstep by ring.
           replace (j - 1 + 1) with j in Hstep by ring.
           symmetry. exact Hstep.
    + assert (Hold : r * (n + 1) + c < i * (n + 1) + j) by lia.
      specialize (Hprefix r c Hr Hc Hold).
      destruct Hprefix as [Hsum [Hrow Hcol]].
      split.
      * rewrite Znth_replace_Znth_Diff by
          (rewrite ?Hsums; lia).
        exact Hsum.
      * split.
        -- rewrite Znth_replace_Znth_Diff by
             (rewrite ?Hrows; lia).
           exact Hrow.
        -- rewrite Znth_replace_Znth_Diff by
             (rewrite ?Hcols; lia).
           exact Hcol.
           }
Qed.
Lemma fold_add_app__tables_ready : forall l1 l2 : list Z,
  fold_right Z.add 0 (l1 ++ l2) =
  fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2; simpl; [ring|].
  rewrite IH. ring.
Qed.
Lemma fold_add_map__tables_ready :
  forall (f : Z -> Z) xs,
  fold_right Z.add 0 (map f xs) =
  fold_right (fun x acc => f x + acc) 0 xs.
Proof.
  intros f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma fold_flat_map_as_nested_sum__tables_ready :
  forall (f : Z -> Z -> Z) r c,
  fold_right Z.add 0
    (flat_map (fun i => map (fun j => f i j) (Zrange 0 c))
      (Zrange 0 r)) =
  SumLib.Sum.sum (fun i : Z => 0 <= i < r)
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < c) (fun j => f i j)).
Proof.
  intros f r c.
  rewrite sum_range_unfold.
  induction (Zrange 0 r) as [|i is IH]; simpl.
  - reflexivity.
  - rewrite fold_add_app__tables_ready, IH.
    rewrite sum_range_unfold.
    rewrite fold_add_map__tables_ready.
    reflexivity.
Qed.
Lemma prefix_rect_formula_generic__tables_ready :
  forall (f : Z -> Z -> Z) xl xh yl yh,
  0 <= xl <= xh -> 0 <= yl <= yh ->
  SumLib.Sum.sum (fun i : Z => 0 <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yh) (fun j => f i j)) -
  SumLib.Sum.sum (fun i : Z => 0 <= i < xl)
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yh) (fun j => f i j)) -
  SumLib.Sum.sum (fun i : Z => 0 <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yl) (fun j => f i j)) +
  SumLib.Sum.sum (fun i : Z => 0 <= i < xl)
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yl) (fun j => f i j)) =
  SumLib.Sum.sum (fun i : Z => xl <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => f i j)).
Proof.
  intros f xl xh yl yh Hx Hy.
  rewrite (sum_Z_range_split 0 xl xh
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yh) (fun j => f i j)))
    by lia.
  rewrite (sum_Z_range_split 0 xl xh
    (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yl) (fun j => f i j)))
    by lia.
  assert (HA :
    SumLib.Sum.sum (fun i : Z => 0 <= i < xl)
      (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yh) (fun j => f i j)) =
    SumLib.Sum.sum (fun i : Z => 0 <= i < xl)
      (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yl) (fun j => f i j)) +
    SumLib.Sum.sum (fun i : Z => 0 <= i < xl)
      (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => f i j))).
  {
    rewrite <- sum_Z_range_add.
    apply sum_Z_range_ext. intros i Hi.
    apply sum_Z_range_split. lia.
  }
  assert (HB :
    SumLib.Sum.sum (fun i : Z => xl <= i < xh)
      (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yh) (fun j => f i j)) =
    SumLib.Sum.sum (fun i : Z => xl <= i < xh)
      (fun i => SumLib.Sum.sum (fun j : Z => 0 <= j < yl) (fun j => f i j)) +
    SumLib.Sum.sum (fun i : Z => xl <= i < xh)
      (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => f i j))).
  {
    rewrite <- sum_Z_range_add.
    apply sum_Z_range_ext. intros i Hi.
    apply sum_Z_range_split. lia.
  }
  rewrite HA, HB. ring.
Qed.
Lemma consecutive_sum_formula__tables_ready :
  forall n : Z, 0 <= n ->
    2 * SumLib.Sum.sum (fun x : Z => 1 <= x < n + 1) (fun x => x) =
    n * (n + 1).
Proof.
  intros n Hn.
  assert (Hnat : forall k : nat,
    2 * SumLib.Sum.sum (fun x : Z => 1 <= x < Z.of_nat k + 1) (fun x => x) =
    Z.of_nat k * (Z.of_nat k + 1)).
  {
    induction k as [|k IH].
    - rewrite sum_Z_range_empty by lia. ring.
    - rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat k) + 1)
        with ((Z.of_nat k + 1) + 1) by lia.
      rewrite sum_Z_range_extend_right by lia.
      replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia.
      nia.
  }
  specialize (Hnat (Z.to_nat n)).
  rewrite Z2Nat.id in Hnat by lia. exact Hnat.
Qed.
Lemma shifted_offset_sums__tables_ready :
  forall lo hi,
  0 <= lo <= hi ->
  2 * SumLib.Sum.sum (fun x : Z => lo <= x < hi) (fun x => x - lo) =
    (hi - lo) * (hi - lo - 1) /\
  2 * SumLib.Sum.sum (fun x : Z => lo <= x < hi) (fun x => x - lo + 1) =
    (hi - lo) * (hi - lo + 1).
Proof.
  intros lo hi Hrange.
  assert (Hzero :
    SumLib.Sum.sum (fun x : Z => lo <= x < hi) (fun x => x - lo) =
    SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun x => x)).
  {
    pose proof (sum_Z_range_shift 0 (hi - lo) lo (fun x => x - lo)) as H.
    replace (0 + lo) with lo in H by lia.
    replace (hi - lo + lo) with hi in H by ring.
    rewrite H.
    apply sum_Z_range_ext. intros x Hx. ring.
  }
  assert (Hone :
    (SumLib.Sum.sum (fun x : Z => lo <= x < hi) (fun x => x - lo + 1) =
     SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun x => x + 1)) /\
    (SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun x => x + 1) =
     SumLib.Sum.sum (fun x : Z => 1 <= x < (hi - lo) + 1) (fun x => x))).
  {
    split.
    - pose proof (sum_Z_range_shift 0 (hi - lo) lo
        (fun x => x - lo + 1)) as H.
      replace (0 + lo) with lo in H by lia.
      replace (hi - lo + lo) with hi in H by ring.
      rewrite H.
      apply sum_Z_range_ext. intros x Hx. ring.
    - symmetry.
      pose proof (sum_Z_range_shift 0 (hi - lo) 1 (fun x => x)) as H.
      replace (0 + 1) with 1 in H by lia. exact H.
  }
  destruct Hone as [Hone Hshift].
  assert (Hplus := consecutive_sum_formula__tables_ready (hi - lo) ltac:(lia)).
  rewrite Hzero, Hone.
  rewrite <- Hshift in Hplus.
  assert (Hrel:
    SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun x => x + 1) =
    SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun x => x) +
    (hi - lo)).
  {
    pose proof (sum_Z_range_const 0 (hi - lo) 1 ltac:(lia)) as Hconst.
    replace (hi - lo - 0) with (hi - lo) in Hconst by ring.
    replace ((hi - lo) * 1) with (hi - lo) in Hconst by ring.
    transitivity
      (SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun x => x) +
       SumLib.Sum.sum (fun x : Z => 0 <= x < hi - lo) (fun _ => 1)).
    - rewrite <- sum_Z_range_add.
      apply sum_Z_range_ext. intros x Hx. ring.
    - rewrite Hconst. reflexivity.
  }
  rewrite Hrel in Hplus. split; nia.
Qed.
Lemma rectlookup_prefix_formulas__tables_ready :
  forall matrix sums rows cols n stride x1 y1 x2 y2,
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  1 <= x1 <= x2 -> x2 < stride ->
  1 <= y1 <= y2 -> y2 < stride ->
  RectLookup sums stride x1 y1 x2 y2 =
    SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j)) /\
  RectLookup rows stride x1 y1 x2 y2 =
    SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (i + 1))) /\
  RectLookup cols stride x1 y1 x2 y2 =
    SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (j + 1))).
Proof.
  intros matrix sums rows cols n stride x1 y1 x2 y2
    Htables Hx Hx2 Hy Hy2.
  unfold PrefixTables in Htables.
  destruct Htables as [Hslen [Hrlen [Hclen [Hboundary Hpref]]]].
  assert (Hur := Hpref x2 y2 ltac:(lia) ltac:(lia) ltac:(nia)).
  assert (Hul := Hpref (x1 - 1) y2 ltac:(lia) ltac:(lia) ltac:(nia)).
  assert (Hlr := Hpref x2 (y1 - 1) ltac:(lia) ltac:(lia) ltac:(nia)).
  assert (Hll := Hpref (x1 - 1) (y1 - 1) ltac:(lia) ltac:(lia) ltac:(nia)).
  destruct Hur as [Hsur [Hrur Hcur]].
  destruct Hul as [Hsul [Hrul Hcul]].
  destruct Hlr as [Hslr [Hrlr Hclr]].
  destruct Hll as [Hsll [Hrll Hcll]].
  replace (x2 * stride + (y1 - 1)) with (x2 * stride + y1 - 1)
    in Hslr, Hrlr, Hclr by ring.
  replace ((x1 - 1) * stride + (y1 - 1))
    with ((x1 - 1) * stride + y1 - 1)
    in Hsll, Hrll, Hcll by ring.
  unfold RectLookup.
  rewrite Hsur, Hsul, Hslr, Hsll,
    Hrur, Hrul, Hrlr, Hrll,
    Hcur, Hcul, Hclr, Hcll.
  unfold PrefixSumValue, PrefixRowValue, PrefixColValue.
  repeat rewrite fold_flat_map_as_nested_sum__tables_ready.
  split.
  - apply prefix_rect_formula_generic__tables_ready; lia.
  - split; apply prefix_rect_formula_generic__tables_ready; lia.
Qed.
Lemma nested_sum_bounds__tables_ready :
  forall (f : Z -> Z -> Z) xl xh yl yh bound,
  xl <= xh -> yl <= yh ->
  (forall i j, xl <= i < xh -> yl <= j < yh -> 0 <= f i j <= bound) ->
  0 <= SumLib.Sum.sum (fun i : Z => xl <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => f i j)) <=
    (xh - xl) * (yh - yl) * bound.
Proof.
  intros f xl xh yl yh bound Hx Hy Hbound.
  pose proof (sum_Z_range_bounds xl xh
    (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => f i j))
    0 ((yh - yl) * bound) Hx) as Houter.
  specialize (Houter ltac:(intros i Hi;
    pose proof (sum_Z_range_bounds yl yh (fun j => f i j) 0 bound Hy
      ltac:(intros j Hj; apply Hbound; assumption)) as Hinner; nia)).
  nia.
Qed.
Lemma shifted_positive_sum_le_full__tables_ready :
  forall lo hi n,
  0 <= lo <= hi -> hi <= n ->
  SumLib.Sum.sum (fun x : Z => lo <= x < hi) (fun x => x + 1) <=
  SumLib.Sum.sum (fun x : Z => 0 <= x < n) (fun x => x + 1).
Proof.
  intros lo hi n Hlo Hhin.
  rewrite (sum_Z_range_split 0 lo n) by lia.
  rewrite (sum_Z_range_split lo hi n) by lia.
  pose proof (sum_nonneg (fun x : Z => 0 <= x < lo) (fun x => x + 1)
    ltac:(intros x Hx; destruct Hx; lia)) as Hleft.
  pose proof (sum_nonneg (fun x : Z => hi <= x < n) (fun x => x + 1)
    ltac:(intros x Hx; destruct Hx; lia)) as Hright.
  lia.
Qed.
Lemma prefix_value_coarse_bounds__tables_ready :
  forall matrix sums rows cols n stride r c,
  1 <= n -> n <= 2000 -> stride = n + 1 ->
  MatrixValuesBounded matrix n ->
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  0 <= r <= n -> 0 <= c <= n ->
  0 <= Znth (r * stride + c) sums 0 <= 4000000000000 /\
  0 <= Znth (r * stride + c) rows 0 <= 8000000000000000 /\
  0 <= Znth (r * stride + c) cols 0 <= 8000000000000000.
Proof.
  intros matrix sums rows cols n stride r c Hn Hnmax Hstride Hmatrix Htables Hr Hc.
  unfold PrefixTables in Htables.
  destruct Htables as [Hslen [Hrlen [Hclen [Hboundary Hpref]]]].
  specialize (Hpref r c ltac:(rewrite Hstride; lia) ltac:(rewrite Hstride; lia)
    ltac:(rewrite Hstride; nia)).
  destruct Hpref as [Hs [Hrow Hcol]].
  rewrite Hs, Hrow, Hcol.
  unfold PrefixSumValue, PrefixRowValue, PrefixColValue.
  repeat rewrite fold_flat_map_as_nested_sum__tables_ready.
  pose proof (nested_sum_bounds__tables_ready
    (fun i j => MatrixCell matrix n i j) 0 r 0 c 1000000 ltac:(lia) ltac:(lia)
    ltac:(intros i j Hi Hj; unfold MatrixCell; pose proof (Hmatrix (i*n+j) ltac:(nia)); lia)) as Hsbound.
  pose proof (nested_sum_bounds__tables_ready
    (fun i j => MatrixCell matrix n i j * (i + 1)) 0 r 0 c (n * 1000000)
    ltac:(lia) ltac:(lia)
    ltac:(intros i j Hi Hj; unfold MatrixCell; pose proof (Hmatrix (i*n+j) ltac:(nia)); nia)) as Hrbound.
  pose proof (nested_sum_bounds__tables_ready
    (fun i j => MatrixCell matrix n i j * (j + 1)) 0 r 0 c (n * 1000000)
    ltac:(lia) ltac:(lia)
    ltac:(intros i j Hi Hj; unfold MatrixCell; pose proof (Hmatrix (i*n+j) ltac:(nia)); nia)) as Hcbound.
  split; [nia|]. split; nia.
Qed.
Lemma prefix_rectangle_bounds__tables_ready :
  forall matrix sums rows cols n stride,
  1 <= n -> n <= 2000 -> stride = n + 1 ->
  MatrixValuesBounded matrix n ->
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  RectanglesBounded sums stride 4000000000000 /\
  RectanglesBounded rows stride 4002000000000000 /\
  RectanglesBounded cols stride 4002000000000000 /\
  RectIntermediatesSafe sums stride /\
  RectIntermediatesSafe rows stride /\
  RectIntermediatesSafe cols stride.
Proof.
  intros matrix sums rows cols n stride Hn Hnmax Hstride Hmatrix Htables.
  assert (Hcell : forall i j, 0 <= i < n -> 0 <= j < n ->
    1 <= MatrixCell matrix n i j <= 1000000).
  {
    intros i j Hi Hj. unfold MatrixCell.
    apply Hmatrix. nia.
  }
  assert (Hrect : forall x1 y1 x2 y2,
    1 <= x1 <= x2 -> x2 < stride ->
    1 <= y1 <= y2 -> y2 < stride ->
    let sm := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j)) in
    let rs := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (i + 1))) in
    let cs := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (j + 1))) in
    0 <= sm <= 4000000000000 /\
    0 <= rs <= 4002000000000000 /\
    0 <= cs <= 4002000000000000).
  {
    intros x1 y1 x2 y2 Hx Hx2 Hy Hy2. cbn beta.
    assert (Hix : 0 <= x1 - 1 <= x2 /\ x2 <= n) by (rewrite Hstride in *; lia).
    assert (Hiy : 0 <= y1 - 1 <= y2 /\ y2 <= n) by (rewrite Hstride in *; lia).
    destruct Hix as [[Hxl Hxh] Hx2n].
    destruct Hiy as [[Hyl Hyh] Hy2n].
    pose proof (nested_sum_bounds__tables_ready
      (fun i j => MatrixCell matrix n i j)
      (x1 - 1) x2 (y1 - 1) y2 1000000 ltac:(lia) ltac:(lia)
      ltac:(intros i j Hi Hj; pose proof (Hcell i j ltac:(lia) ltac:(lia)); lia)) as Hsm.
    assert (Hrs0 : 0 <= SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (i + 1)))).
    {
      apply sum_nonneg. intros i Hi. apply sum_nonneg. intros j Hj.
      pose proof (Hcell i j ltac:(lia) ltac:(lia)). nia.
    }
    assert (Hrs_le :
      SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
        (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
          (fun j => MatrixCell matrix n i j * (i + 1))) <=
      (y2 - (y1 - 1)) * 1000000 *
      SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2) (fun i => i + 1)).
    {
      rewrite <- sum_Z_range_factor_l.
      apply sum_Z_range_le. intros i Hi.
      pose proof (sum_Z_range_bounds (y1 - 1) y2
        (fun j => MatrixCell matrix n i j * (i + 1)) 0
        (1000000 * (i + 1)) ltac:(lia)
        ltac:(intros j Hj; pose proof (Hcell i j ltac:(lia) ltac:(lia)); nia)) as Hb.
      nia.
    }
    pose proof (shifted_positive_sum_le_full__tables_ready
      (x1 - 1) x2 n ltac:(lia) ltac:(lia)) as Hrowsum.
    pose proof (consecutive_sum_formula__tables_ready n ltac:(lia)) as Htri.
    assert (Hfullshift :
      SumLib.Sum.sum (fun i : Z => 0 <= i < n) (fun i => i + 1) =
      SumLib.Sum.sum (fun i : Z => 1 <= i < n + 1) (fun i => i)).
    {
      symmetry. pose proof (sum_Z_range_shift 0 n 1 (fun i => i)) as H.
      replace (0 + 1) with 1 in H by lia. exact H.
    }
    rewrite Hfullshift in Hrowsum.
    assert (Hcs0 : 0 <= SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
      (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (j + 1)))).
    {
      apply sum_nonneg. intros i Hi. apply sum_nonneg. intros j Hj.
      pose proof (Hcell i j ltac:(lia) ltac:(lia)). nia.
    }
    assert (Hcs_inner : forall i, x1 - 1 <= i < x2 ->
      SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => MatrixCell matrix n i j * (j + 1)) <=
      1000000 * SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2) (fun j => j + 1)).
    {
      intros i Hi. rewrite <- sum_Z_range_factor_l.
      apply sum_Z_range_le. intros j Hj.
      pose proof (Hcell i j ltac:(lia) ltac:(lia)). nia.
    }
    assert (Hcs_le :
      SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
        (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
          (fun j => MatrixCell matrix n i j * (j + 1))) <=
      (x2 - (x1 - 1)) *
      (1000000 * SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2) (fun j => j + 1))).
    {
      apply sum_Z_range_upper_bound; [lia|]. exact Hcs_inner.
    }
    pose proof (shifted_positive_sum_le_full__tables_ready
      (y1 - 1) y2 n ltac:(lia) ltac:(lia)) as Hcolsum.
    rewrite Hfullshift in Hcolsum.
    split.
    - nia.
    - split; nia.
  }
  assert (Hforms := rectlookup_prefix_formulas__tables_ready).
  split.
  - unfold RectanglesBounded. intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
    specialize (Hforms matrix sums rows cols n stride x1 y1 x2 y2
      Htables Hx Hx2 Hy Hy2).
    specialize (Hrect x1 y1 x2 y2 Hx Hx2 Hy Hy2).
    destruct Hforms as [Hs [Hr Hc]]. destruct Hrect as [Hsb [Hrb Hcb]].
    rewrite Hs. exact Hsb.
  - split.
    + unfold RectanglesBounded. intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
      specialize (Hforms matrix sums rows cols n stride x1 y1 x2 y2
        Htables Hx Hx2 Hy Hy2).
      specialize (Hrect x1 y1 x2 y2 Hx Hx2 Hy Hy2).
      destruct Hforms as [Hs [Hr Hc]]. destruct Hrect as [Hsb [Hrb Hcb]].
      rewrite Hr. exact Hrb.
    + split.
      * unfold RectanglesBounded. intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
        specialize (Hforms matrix sums rows cols n stride x1 y1 x2 y2
          Htables Hx Hx2 Hy Hy2).
        specialize (Hrect x1 y1 x2 y2 Hx Hx2 Hy Hy2).
        destruct Hforms as [Hs [Hr Hc]]. destruct Hrect as [Hsb [Hrb Hcb]].
        rewrite Hc. exact Hcb.
      * split.
        -- unfold RectIntermediatesSafe. intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
           cbn beta.
           replace (x2 * stride + y1 - 1) with (x2 * stride + (y1 - 1)) by ring.
           pose proof (prefix_value_coarse_bounds__tables_ready
             matrix sums rows cols n stride x2 y2 Hn Hnmax Hstride Hmatrix Htables
             ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hur.
           pose proof (prefix_value_coarse_bounds__tables_ready
             matrix sums rows cols n stride (x1 - 1) y2 Hn Hnmax Hstride Hmatrix Htables
             ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hul.
           pose proof (prefix_value_coarse_bounds__tables_ready
             matrix sums rows cols n stride x2 (y1 - 1) Hn Hnmax Hstride Hmatrix Htables
             ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hlr.
           destruct Hur as [Hur _]. destruct Hul as [Hul _]. destruct Hlr as [Hlr _]. nia.
        -- split.
           ++ unfold RectIntermediatesSafe. intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
              cbn beta.
              replace (x2 * stride + y1 - 1) with (x2 * stride + (y1 - 1)) by ring.
              pose proof (prefix_value_coarse_bounds__tables_ready
                matrix sums rows cols n stride x2 y2 Hn Hnmax Hstride Hmatrix Htables
                ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hur.
              pose proof (prefix_value_coarse_bounds__tables_ready
                matrix sums rows cols n stride (x1 - 1) y2 Hn Hnmax Hstride Hmatrix Htables
                ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hul.
              pose proof (prefix_value_coarse_bounds__tables_ready
                matrix sums rows cols n stride x2 (y1 - 1) Hn Hnmax Hstride Hmatrix Htables
                ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hlr.
              destruct Hur as [_ [Hur _]]. destruct Hul as [_ [Hul _]].
              destruct Hlr as [_ [Hlr _]]. nia.
           ++ unfold RectIntermediatesSafe. intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
              cbn beta.
              replace (x2 * stride + y1 - 1) with (x2 * stride + (y1 - 1)) by ring.
              pose proof (prefix_value_coarse_bounds__tables_ready
                matrix sums rows cols n stride x2 y2 Hn Hnmax Hstride Hmatrix Htables
                ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hur.
              pose proof (prefix_value_coarse_bounds__tables_ready
                matrix sums rows cols n stride (x1 - 1) y2 Hn Hnmax Hstride Hmatrix Htables
                ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hul.
              pose proof (prefix_value_coarse_bounds__tables_ready
                matrix sums rows cols n stride x2 (y1 - 1) Hn Hnmax Hstride Hmatrix Htables
                ltac:(rewrite Hstride in *; lia) ltac:(rewrite Hstride in *; lia)) as Hlr.
              destruct Hur as [_ [_ Hur]]. destruct Hul as [_ [_ Hul]].
              destruct Hlr as [_ [_ Hlr]]. nia.
Qed.
Lemma nested_sum_linear_sub__tables_ready :
  forall (f g : Z -> Z -> Z) xl xh yl yh k,
  SumLib.Sum.sum (fun i : Z => xl <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => f i j)) -
  k * SumLib.Sum.sum (fun i : Z => xl <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh) (fun j => g i j)) =
  SumLib.Sum.sum (fun i : Z => xl <= i < xh)
    (fun i => SumLib.Sum.sum (fun j : Z => yl <= j < yh)
      (fun j => f i j - k * g i j)).
Proof.
  intros f g xl xh yl yh k.
  rewrite <- sum_Z_range_factor_l.
  rewrite <- sum_Z_range_sub.
  apply sum_Z_range_ext. intros i Hi.
  rewrite sum_Z_range_sub, sum_Z_range_factor_l. reflexivity.
Qed.
Lemma query_arithmetic_from_prefix__tables_ready :
  forall matrix sums rows cols n stride x1 y1 x2 y2,
  1 <= n -> n <= 2000 -> stride = n + 1 ->
  MatrixValuesBounded matrix n ->
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  1 <= x1 <= x2 -> x2 < stride ->
  1 <= y1 <= y2 -> y2 < stride ->
  QueryArithmeticSafe sums rows cols stride x1 y1 x2 y2.
Proof.
  intros matrix sums rows cols n stride x1 y1 x2 y2
    Hn Hnmax Hstride Hmatrix Htables Hx Hx2 Hy Hy2.
  pose proof (rectlookup_prefix_formulas__tables_ready
    matrix sums rows cols n stride x1 y1 x2 y2
    Htables Hx Hx2 Hy Hy2) as Hforms.
  destruct Hforms as [Hsm [Hrs Hcs]].
  unfold QueryArithmeticSafe. cbn beta.
  rewrite Hsm, Hrs, Hcs.
  set (SM := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
    (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => MatrixCell matrix n i j))).
  set (RS := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
    (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => MatrixCell matrix n i j * (i + 1)))).
  set (CS := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
    (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => MatrixCell matrix n i j * (j + 1)))).
  set (DR := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
    (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => MatrixCell matrix n i j * (i + 1 - x1)))).
  set (DC := SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
    (fun i => SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => MatrixCell matrix n i j * (j + 1 - (y1 - 1))))).
  assert (Hdr_id : RS - x1 * SM = DR).
  {
    unfold RS, SM, DR.
    rewrite nested_sum_linear_sub__tables_ready.
    apply sum_Z_range_ext. intros i Hi.
    apply sum_Z_range_ext. intros j Hj. ring.
  }
  assert (Hdc_id : CS - (y1 - 1) * SM = DC).
  {
    unfold CS, SM, DC.
    rewrite nested_sum_linear_sub__tables_ready.
    apply sum_Z_range_ext. intros i Hi.
    apply sum_Z_range_ext. intros j Hj. ring.
  }
  rewrite Hdr_id, Hdc_id.
  assert (Hcell : forall i j, 0 <= i < n -> 0 <= j < n ->
    1 <= MatrixCell matrix n i j <= 1000000).
  {
    intros i j Hi Hj. unfold MatrixCell. apply Hmatrix. nia.
  }
  assert (Hranges : 0 <= x1 - 1 <= x2 /\ x2 <= n /\
                    0 <= y1 - 1 <= y2 /\ y2 <= n).
  { rewrite Hstride in *. lia. }
  destruct Hranges as [Hxr [Hx2n [Hyr Hy2n]]].
  set (height := x2 - (x1 - 1)).
  set (width := y2 - (y1 - 1)).
  assert (Hhw : 1 <= height <= 2000 /\ 1 <= width <= 2000).
  { unfold height, width. lia. }
  destruct Hhw as [Hheight Hwidth].
  assert (Hdr0 : 0 <= DR).
  {
    unfold DR. apply sum_nonneg. intros i Hi. apply sum_nonneg. intros j Hj.
    pose proof (Hcell i j ltac:(lia) ltac:(lia)). nia.
  }
  assert (Hdc0 : 0 <= DC).
  {
    unfold DC. apply sum_nonneg. intros i Hi. apply sum_nonneg. intros j Hj.
    pose proof (Hcell i j ltac:(lia) ltac:(lia)). nia.
  }
  pose proof (shifted_offset_sums__tables_ready
    (x1 - 1) x2 ltac:(lia)) as Hrowoffset.
  pose proof (shifted_offset_sums__tables_ready
    (y1 - 1) y2 ltac:(lia)) as Hcoloffset.
  destruct Hrowoffset as [Hrowoffset _].
  destruct Hcoloffset as [_ Hcoloffset].
  assert (Hdr_le :
    DR <= width * 1000000 *
      SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
        (fun i => i - (x1 - 1))).
  {
    unfold DR, width.
    rewrite <- sum_Z_range_factor_l.
    apply sum_Z_range_le. intros i Hi.
    pose proof (sum_Z_range_bounds (y1 - 1) y2
      (fun j => MatrixCell matrix n i j * (i + 1 - x1)) 0
      (1000000 * (i - (x1 - 1))) ltac:(lia)
      ltac:(intros j Hj; pose proof (Hcell i j ltac:(lia) ltac:(lia)); nia)) as Hb.
    nia.
  }
  assert (Hdc_inner : forall i, x1 - 1 <= i < x2 ->
    SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => MatrixCell matrix n i j * (j + 1 - (y1 - 1))) <=
    1000000 * SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
      (fun j => j - (y1 - 1) + 1)).
  {
    intros i Hi. rewrite <- sum_Z_range_factor_l.
    apply sum_Z_range_le. intros j Hj.
    pose proof (Hcell i j ltac:(lia) ltac:(lia)). nia.
  }
  assert (Hdc_le :
    DC <= height * (1000000 *
      SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
        (fun j => j - (y1 - 1) + 1))).
  {
    unfold DC, height.
    apply sum_Z_range_upper_bound; [lia|]. exact Hdc_inner.
  }
  change (2 * SumLib.Sum.sum (fun i : Z => x1 - 1 <= i < x2)
    (fun i => i - (x1 - 1)) = height * (height - 1)) in Hrowoffset.
  change (2 * SumLib.Sum.sum (fun j : Z => y1 - 1 <= j < y2)
    (fun j => j - (y1 - 1) + 1) = width * (width + 1)) in Hcoloffset.
  assert (Hdr2 : 2 * DR <= width * 1000000 * height * (height - 1)).
  {
    replace (width * 1000000 * height * (height - 1))
      with (width * 1000000 * (height * (height - 1))) by ring.
    rewrite <- Hrowoffset.
    clear - Hdr_le. nia.
  }
  assert (Hdc2 : 2 * DC <= height * 1000000 * width * (width + 1)).
  {
    replace (height * 1000000 * width * (width + 1))
      with (height * 1000000 * (width * (width + 1))) by ring.
    rewrite <- Hcoloffset.
    clear - Hdc_le. nia.
  }
  assert (Hprod : 0 <= height * width <= 4000000).
  {
    assert (Hp0 : 0 <= height * width) by
      (clear - Hheight Hwidth; nia).
    assert (Hp1 : 0 <= (2000 - height) * width) by
      (clear - Hheight Hwidth; nia).
    assert (Hp2 : 0 <= 2000 * (2000 - width)) by
      (clear - Hheight Hwidth; nia).
    assert (Hp3 : height * width <= 2000 * width) by
      (clear - Hp1; nia).
    assert (Hp4 : 2000 * width <= 4000000) by
      (clear - Hwidth; nia).
    lia.
  }
  assert (Hquartic :
    height * width * (height * width + 1) <= 4000000 * 4000001).
  {
    assert (0 <= (4000000 - height * width) *
      (4000001 + height * width)) by (clear - Hprod; nia).
    clear - Hprod H. nia.
  }
  replace (y2 - y1 + 1) with width by (unfold width; ring).
  replace (width * DR + CS - (y1 - 1) * SM) with (width * DR + DC)
    by (rewrite <- Hdc_id; ring).
  split.
  - split; [exact Hdr0|].
    assert (0 <= (2000 - width) * height * (height - 1))
      by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia).
    assert (0 <= width * (2000 - height) * (height + 1999))
      by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia).
    clear - Hdr2 Hheight Hwidth H H0. nia.
  - split.
    + split; [exact Hdc0|].
      assert (0 <= (2000 - height) * width * (width + 1))
        by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia).
      assert (0 <= height * (2000 - width) * (width + 2001))
        by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia).
      clear - Hdc2 Hheight Hwidth H H0. nia.
    + split.
      * assert (0 <= width * DR) by
          (apply Z.mul_nonneg_nonneg; lia).
        lia.
      *
      assert (Hdrw : width * (2 * DR) <=
        width * (width * 1000000 * height * (height - 1))).
      {
        apply Z.mul_le_mono_nonneg_l; [lia|exact Hdr2].
      }
      assert (Hcombine :
        2 * (width * DR + DC) <=
        1000000 * height * width * (height * width + 1)).
      {
        replace (1000000 * height * width * (height * width + 1)) with
          (width * (width * 1000000 * height * (height - 1)) +
           height * 1000000 * width * (width + 1)) by ring.
        clear - Hdrw Hdc2. nia.
      }
      assert (Hquartic_scaled :
        1000000 * (height * width * (height * width + 1)) <=
        1000000 * (4000000 * 4000001)).
      {
        apply Z.mul_le_mono_nonneg_l; [lia|exact Hquartic].
      }
      replace (1000000 * height * width * (height * width + 1)) with
        (1000000 * (height * width * (height * width + 1)))
        in Hcombine by ring.
      replace (1000000 * (4000000 * 4000001)) with
        16000004000000000000 in Hquartic_scaled by ring.
      assert (Hhalf : forall a b : Z,
        2 * a <= b -> b <= 16000004000000000000 ->
        a <= 8000002000000000000).
      {
        intros a b Ha Hb. lia.
      }
      eapply Hhalf; [exact Hcombine|exact Hquartic_scaled].
Qed.
Lemma full_prefix_tables_imply_tables_ready__tables_ready :
  forall matrix sums rows cols n stride,
  1 <= n -> n <= 2000 -> stride = n + 1 ->
  MatrixValuesBounded matrix n ->
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  TablesReady matrix sums rows cols n stride.
Proof.
  intros matrix sums rows cols n stride Hn Hnmax Hstride Hmatrix Htables.
  pose proof (prefix_rectangle_bounds__tables_ready
    matrix sums rows cols n stride Hn Hnmax Hstride Hmatrix Htables) as Hbounds.
  destruct Hbounds as [Hs [Hr [Hc [His [Hir Hic]]]]].
  unfold TablesReady.
  split; [exact Htables|].
  split; [exact Hs|].
  split; [exact Hr|].
  split; [exact Hc|].
  split; [exact His|].
  split; [exact Hir|].
  split; [exact Hic|].
  intros x1 y1 x2 y2 Hx Hx2 Hy Hy2.
  eapply query_arithmetic_from_prefix__tables_ready; eauto.
Qed.
Lemma raw_queries_encode_nth__query_setup :
  forall (queries : list (Z * Z * Z * Z)) (raw : list Z) (n i : Z),
    0 <= i < Zlength queries ->
    RawQueriesEncode queries raw ->
    QueriesBounded queries n ->
    let q := Znth i queries (0, 0, 0, 0) in
    Znth (4 * i) raw 0 = zquad_1 q + 1 /\
    Znth (4 * i + 1) raw 0 = zquad_2 q + 1 /\
    Znth (4 * i + 2) raw 0 = zquad_3 q + 1 /\
    Znth (4 * i + 3) raw 0 = zquad_4 q + 1 /\
    0 <= zquad_1 q <= zquad_3 q /\ zquad_3 q < n /\
    0 <= zquad_2 q <= zquad_4 q /\ zquad_4 q < n.
Proof.
  intros queries raw n i Hi Hencode Hbounded.
  destruct Hencode as [_ Hencode].
  specialize (Hencode i Hi).
  unfold QueriesBounded in Hbounded.
  apply Forall_forall with
      (x := Znth i queries (0, 0, 0, 0)) in Hbounded.
  2: { apply Znth_In_Zlength. exact Hi. }
  destruct (Znth i queries (0, 0, 0, 0)) as [[[x1 y1] x2] y2].
  simpl in Hencode, Hbounded |- *.
  tauto.
Qed.
Lemma fold_map__output_step : forall (A : Type) (xs : list A) (f : A -> Z),
  fold_right Z.add 0 (map f xs) = fold_right (fun x acc => f x + acc) 0 xs.
Proof.
  intros A xs f. induction xs; simpl; [reflexivity|]. rewrite IHxs. reflexivity.
Qed.
Lemma fold_rect__output_step : forall (A B : Type) (xs : list A) (ys : list B) f,
  fold_right Z.add 0 (flat_map (fun x => map (f x) ys) xs) =
  fold_right (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc) 0 xs.
Proof.
  intros A B xs ys f. induction xs as [|x xs IH]; [reflexivity|].
  change (ListLib.sum (map (f x) ys ++ flat_map (fun x => map (f x) ys) xs) =
    fold_right (fun y acc => f x y + acc) 0 ys +
    fold_right (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc) 0 xs).
  rewrite ListLib.sum_app. unfold ListLib.sum.
  rewrite fold_map__output_step, IH. reflexivity.
Qed.
Lemma map_rect__output_step : forall (A B C D : Type) (f : C -> D) (g : A -> B -> C) xs ys,
  map f (flat_map (fun x => map (g x) ys) xs) =
  flat_map (fun x => map (fun y => f (g x y)) ys) xs.
Proof.
  intros A B C D f g xs ys. induction xs; simpl; [reflexivity|].
  rewrite map_app, map_map, IHxs. reflexivity.
Qed.
Lemma fold_rect_sum__output_step : forall xl xh yl yh (f : Z -> Z -> Z),
  fold_right Z.add 0 (flat_map (fun i => map (f i) (Zrange yl yh)) (Zrange xl xh)) =
  SumLib.Sum.sum (fun i => xl <= i < xh) (fun i =>
    SumLib.Sum.sum (fun j => yl <= j < yh) (f i)).
Proof.
  intros xl xh yl yh f. rewrite fold_rect__output_step.
  rewrite SumLib.ZRange.sum_range_unfold.
  generalize (Zrange xl xh) as xs. intro xs.
  induction xs; simpl; [reflexivity|].
  rewrite IHxs, SumLib.ZRange.sum_range_unfold. reflexivity.
Qed.
Lemma rect_prefix_inclusion_exclusion__output_step :
  forall xl xh yl yh (f : Z -> Z -> Z),
  0 <= xl <= xh -> 0 <= yl <= yh ->
  SumLib.Sum.sum (fun i => 0 <= i < xh) (fun i => SumLib.Sum.sum (fun j => 0 <= j < yh) (f i)) -
  SumLib.Sum.sum (fun i => 0 <= i < xl) (fun i => SumLib.Sum.sum (fun j => 0 <= j < yh) (f i)) -
  SumLib.Sum.sum (fun i => 0 <= i < xh) (fun i => SumLib.Sum.sum (fun j => 0 <= j < yl) (f i)) +
  SumLib.Sum.sum (fun i => 0 <= i < xl) (fun i => SumLib.Sum.sum (fun j => 0 <= j < yl) (f i)) =
  SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => yl <= j < yh) (f i)).
Proof.
  intros xl xh yl yh f Hx Hy.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 xl xh
    (fun i => SumLib.Sum.sum (fun j => 0 <= j < yh) (f i))) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 xl xh
    (fun i => SumLib.Sum.sum (fun j => 0 <= j < yl) (f i))) by lia.
  transitivity (SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => 0 <= j < yh) (f i)) -
    SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => 0 <= j < yl) (f i))); [ring|].
  rewrite <- SumLib.ZRange.sum_Z_range_sub.
  apply SumLib.ZRange.sum_Z_range_ext. intros i Hi.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 yl yh (f i)) by lia. ring.
Qed.
Lemma prefix_rectlookup_identities__output_step :
  forall matrix sums rows cols n stride x1 y1 x2 y2,
  1 <= n -> stride = n + 1 ->
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  1 <= x1 <= x2 -> x2 < stride -> 1 <= y1 <= y2 -> y2 < stride ->
  RectLookup sums stride x1 y1 x2 y2 =
    SumLib.Sum.sum (fun i => x1 - 1 <= i < x2) (fun i => SumLib.Sum.sum (fun j => y1 - 1 <= j < y2) (fun j => MatrixCell matrix n i j)) /\
  RectLookup rows stride x1 y1 x2 y2 =
    SumLib.Sum.sum (fun i => x1 - 1 <= i < x2) (fun i => SumLib.Sum.sum (fun j => y1 - 1 <= j < y2) (fun j => MatrixCell matrix n i j * (i + 1))) /\
  RectLookup cols stride x1 y1 x2 y2 =
    SumLib.Sum.sum (fun i => x1 - 1 <= i < x2) (fun i => SumLib.Sum.sum (fun j => y1 - 1 <= j < y2) (fun j => MatrixCell matrix n i j * (j + 1))).
Proof.
  intros matrix sums rows cols n stride x1 y1 x2 y2 Hn Hstride Htables Hx1 Hx2 Hy1 Hy2.
  destruct Htables as [_ [_ [_ [_ Hlookup]]]].
  pose proof (Hlookup x2 y2 ltac:(lia) ltac:(lia) ltac:(nia)) as [Hs22 [Hr22 Hc22]].
  pose proof (Hlookup (x1 - 1) y2 ltac:(lia) ltac:(lia) ltac:(nia)) as [Hs12 [Hr12 Hc12]].
  pose proof (Hlookup x2 (y1 - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [Hs21 [Hr21 Hc21]].
  pose proof (Hlookup (x1 - 1) (y1 - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [Hs11 [Hr11 Hc11]].
  unfold RectLookup.
  replace (x2 * stride + y1 - 1) with (x2 * stride + (y1 - 1)) by ring.
  replace ((x1 - 1) * stride + y1 - 1) with ((x1 - 1) * stride + (y1 - 1)) by ring.
  rewrite Hs22, Hs12, Hs21, Hs11, Hr22, Hr12, Hr21, Hr11, Hc22, Hc12, Hc21, Hc11.
  unfold PrefixSumValue, PrefixRowValue, PrefixColValue.
  repeat rewrite fold_rect_sum__output_step.
  repeat split; apply rect_prefix_inclusion_exclusion__output_step; lia.
Qed.
Lemma weighted_nested_sum_identity__output_step :
  forall xl xh yl yh xbase width (f : Z -> Z -> Z), xbase = xl + 1 ->
  width * (SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j * (i + 1))) -
    xbase * SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j))) +
  SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j * (j + 1))) -
    yl * SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j)) =
  SumLib.Sum.sum (fun i => xl <= i < xh) (fun i => SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j * ((i - xl) * width + (j - yl) + 1))).
Proof.
  intros xl xh yl yh xbase width f Hbase. symmetry.
  transitivity (SumLib.Sum.sum (fun i => xl <= i < xh) (fun i =>
    width * (SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j * (i + 1)) -
      xbase * SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j)) +
    (SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j * (j + 1)) -
      yl * SumLib.Sum.sum (fun j => yl <= j < yh) (fun j => f i j)))).
  - apply SumLib.ZRange.sum_Z_range_ext. intros i Hi.
    rewrite <- (SumLib.ZRange.sum_Z_range_factor_l yl yh xbase (fun j => f i j)).
    rewrite <- SumLib.ZRange.sum_Z_range_sub.
    rewrite <- (SumLib.ZRange.sum_Z_range_factor_l yl yh width (fun j => f i j * (i + 1) - xbase * f i j)).
    rewrite <- (SumLib.ZRange.sum_Z_range_factor_l yl yh yl (fun j => f i j)).
    rewrite <- SumLib.ZRange.sum_Z_range_sub.
    rewrite <- SumLib.ZRange.sum_Z_range_add.
    apply SumLib.ZRange.sum_Z_range_ext. intros j Hj. rewrite Hbase. ring.
  - rewrite SumLib.ZRange.sum_Z_range_add, SumLib.ZRange.sum_Z_range_factor_l,
      SumLib.ZRange.sum_Z_range_sub, SumLib.ZRange.sum_Z_range_factor_l,
      SumLib.ZRange.sum_Z_range_sub, SumLib.ZRange.sum_Z_range_factor_l. ring.
Qed.
Lemma rectlookup_weighted_flattened_sum__output_step :
  forall matrix sums rows cols n stride x1 y1 x2 y2,
  1 <= n -> stride = n + 1 ->
  PrefixTables matrix sums rows cols n stride (stride * stride) ->
  1 <= x1 <= x2 -> x2 < stride -> 1 <= y1 <= y2 -> y2 < stride ->
  FlattenedWeightedSum matrix n (x1 - 1, y1 - 1, x2 - 1, y2 - 1)
    ((y2 - y1 + 1) * (RectLookup rows stride x1 y1 x2 y2 - x1 * RectLookup sums stride x1 y1 x2 y2) +
      RectLookup cols stride x1 y1 x2 y2 - (y1 - 1) * RectLookup sums stride x1 y1 x2 y2).
Proof.
  intros matrix sums rows cols n stride x1 y1 x2 y2 Hn Hstride Htables Hx1 Hx2 Hy1 Hy2.
  destruct (prefix_rectlookup_identities__output_step matrix sums rows cols n stride x1 y1 x2 y2
    Hn Hstride Htables Hx1 Hx2 Hy1 Hy2) as [Hs [Hr Hc]].
  unfold FlattenedWeightedSum. simpl. rewrite Hs, Hr, Hc.
  rewrite map_rect__output_step, fold_rect_sum__output_step.
  replace (x2 - 1 + 1) with x2 by ring.
  replace (y2 - 1 + 1) with y2 by ring.
  replace (y2 - 1 - (y1 - 1) + 1) with (y2 - y1 + 1) by ring.
  apply weighted_nested_sum_identity__output_step. ring.
Qed.
Lemma output_prefix_snoc__output_step : forall matrix n queries out i v d,
  OutputPrefix matrix n queries out i -> 0 <= i < Zlength queries ->
  FlattenedWeightedSum matrix n (Znth i queries d) v ->
  OutputPrefix matrix n queries (out ++ [v]) (i + 1).
Proof.
  intros matrix n queries out i v d [Hlen Hout] Hi Hv.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite (sublist_split 0 (i + 1) i queries) by lia.
    rewrite (sublist_single d i queries) by lia.
    apply Forall2_app; [exact Hout|]. constructor; [exact Hv|constructor].
Qed.
Lemma output_prefix_complete_spec__final_result :
  forall matrix n queries out q,
    Zlength queries = q ->
    OutputPrefix matrix n queries out q ->
    Spec matrix n queries out.
Proof.
  intros matrix n queries out q Hlen [_ Hprefix].
  unfold Spec.
  rewrite (sublist_self queries q (eq_sym Hlen)) in Hprefix.
  exact Hprefix.
Qed.
