Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition DistanceArray (a b : list Z) : Prop :=
  Zlength b = Zlength a /\
  forall i, 0 <= i < Zlength a ->
    min_value_of_subset Z.le
      (fun j : Z =>
        0 <= j < Zlength a /\ Znth j a 0 <> Znth i a 0)
      (fun j => Z.abs (i-j)) (Znth i b 0).

Definition UsesEveryValue (k : Z) (a : list Z) : Prop :=
  Forall (fun x => 1 <= x <= k) a /\
  forall x, 1 <= x <= k -> In x a.

Definition Pre (n k : Z) : Prop :=
  2 <= n <= 200000 /\ 2 <= k <= Z.min n 10.

#[local] Instance finite_distance (n : Z) : Finite (fun d : Z => 0 <= d < n) :=
  finite_Z_range 0 n.

#[local] Instance finite_distance_array (n : Z) :
    Finite (fun b : list Z =>
      Zlength b = n /\ Forall (fun d => 0 <= d < n) b) :=
  Finite_bounded_lists n (fun d : Z => 0 <= d < n).

Definition Spec (n k out : Z) : Prop :=
  out = #(fun b : list Z =>
    (Zlength b = n /\ Forall (fun d => 0 <= d < n) b) /\
    exists a, Zlength a = n /\ UsesEveryValue k a /\ DistanceArray a b)
    mod 998244353.

(* The following declarations are an append-only mathematical interface for the
   column-major dynamic-programming table used by the implementation. *)
Definition P082Modulus : Z := 998244353.

Definition P082Index (k row col : Z) : Z := row * (k + 1) + col.

Definition P082Norm (x : Z) : Z := x mod P082Modulus.

Definition P082InitState
    (n k next_row : Z) (dp pref : list Z) : Prop :=
  Zlength dp = (n + 1) * (k + 1) /\
  Zlength pref = (n + 1) * (k + 1) /\
  (forall q, 0 <= q < Zlength dp ->
     0 <= Znth q dp 0 < P082Modulus /\
     0 <= Znth q pref 0 < P082Modulus) /\
  (forall row, 1 <= row < next_row ->
     Znth (P082Index k row 1) dp 0 = 1 /\
     Znth (P082Index k row 1) pref 0 = row) /\
  (forall row, next_row <= row <= n ->
     Znth (P082Index k row 1) dp 0 = 0 /\
     Znth (P082Index k row 1) pref 0 = 0) /\
  (forall row col, 0 <= row <= n -> 0 <= col <= k ->
     (row = 0 \/ col = 0 \/ 2 <= col) ->
     Znth (P082Index k row col) dp 0 = 0 /\
     Znth (P082Index k row col) pref 0 = 0).

Definition P082BaseColumns
    (n k : Z) (dp pref : list Z) : Prop :=
  Zlength dp = (n + 1) * (k + 1) /\
  Zlength pref = (n + 1) * (k + 1) /\
  (forall q, 0 <= q < Zlength dp ->
     0 <= Znth q dp 0 < P082Modulus /\
     0 <= Znth q pref 0 < P082Modulus) /\
  (forall row, 1 <= row <= n ->
     Znth (P082Index k row 1) dp 0 = 1 /\
     Znth (P082Index k row 1) pref 0 = row) /\
  (forall col, 0 <= col <= k ->
     Znth (P082Index k 0 col) dp 0 = 0 /\
     Znth (P082Index k 0 col) pref 0 = 0).

Definition P082RawCell
    (k row col : Z) (dp pref : list Z) : Z :=
  Znth (P082Index k (row - 1) (col - 1)) pref 0 -
  (if Z_le_dec 3 row
   then Znth (P082Index k (row - 2) (col - 1)) dp 0
   else 0) +
  (if Z.eq_dec col k
   then Znth (P082Index k (row - 1) k) pref 0 -
        (if Z_le_dec 3 row
         then Znth (P082Index k (row - 2) k) dp 0
         else 0)
   else 0).

Definition P082CellEquation
    (k row col : Z) (dp pref : list Z) : Prop :=
  Znth (P082Index k row col) dp 0 =
    P082Norm (P082RawCell k row col dp pref) /\
  Znth (P082Index k row col) pref 0 =
    P082Norm
      (Znth (P082Index k (row - 1) col) pref 0 +
       Znth (P082Index k row col) dp 0).

Definition P082ColumnsState
    (n k next_col : Z) (dp pref : list Z) : Prop :=
  P082BaseColumns n k dp pref /\
  forall col row, 2 <= col < next_col -> 1 <= row <= n ->
    P082CellEquation k row col dp pref.

Definition P082ColumnProgress
    (n k col next_row : Z) (dp pref : list Z) : Prop :=
  P082ColumnsState n k col dp pref /\
  forall row, 1 <= row < next_row ->
    P082CellEquation k row col dp pref.

Definition P082FinalExpression (k n : Z) (dp : list Z) : Z :=
  P082Norm
    (Znth (P082Index k n k) dp 0 +
     Znth (P082Index k (n - 2) (k - 1)) dp 0 +
     Znth (P082Index k (n - 2) k) dp 0).

Definition P082FinalValue (n k : Z) (dp : list Z) (out : Z) : Prop :=
  out = P082FinalExpression k n dp /\ Spec n k out.

(* This proposition names the sole combinatorial bridge that remains after the
   local table-update obligations: the recurrence classifies the finite set in
   [Spec] by its last structural event.  Group proofs can target it directly. *)
Definition P082CombinatorialBridge (n k : Z) : Prop :=
  forall dp pref,
    P082ColumnsState n k (k + 1) dp pref ->
    Spec n k (P082FinalExpression k n dp).

Require Import Coq.micromega.Lia.

Lemma P082Norm_range : forall x,
  0 <= P082Norm x < P082Modulus.
Proof.
  intro x. unfold P082Norm, P082Modulus. apply Z.mod_pos_bound. lia.
Qed.


Lemma P082Index_bounds : forall n k row col,
  0 <= row <= n -> 0 <= col <= k ->
  0 <= P082Index k row col < (n + 1) * (k + 1).
Proof.
  intros n k row col Hr Hc. unfold P082Index. nia.
Qed.

Lemma P082RawCell_bounds : forall k row col dp pref,
  (forall q, 0 <= q < Zlength dp ->
     0 <= Znth q dp 0 < P082Modulus /\
     0 <= Znth q pref 0 < P082Modulus) ->
  Zlength dp = Zlength pref ->
  0 <= P082Index k (row - 1) (col - 1) < Zlength dp ->
  (3 <= row -> 0 <= P082Index k (row - 2) (col - 1) < Zlength dp) ->
  (col = k ->
    0 <= P082Index k (row - 1) k < Zlength dp /\
    (3 <= row -> 0 <= P082Index k (row - 2) k < Zlength dp)) ->
  -2 * P082Modulus < P082RawCell k row col dp pref <
   2 * P082Modulus.
Proof.
  intros k row col dp pref Hrange Hlen Hprev Hprev2 Hsame.
  unfold P082RawCell.
  pose proof (Hrange _ Hprev) as [_ Hp].
  destruct (Z_le_dec 3 row) as [Hr|Hr].
  - pose proof (Hrange _ (Hprev2 Hr)) as [Hd0 Hd].
    destruct (Z.eq_dec col k) as [Hck|Hck].
    + destruct (Hsame Hck) as [Hs Hs2].
      pose proof (Hrange _ Hs) as [_ Hsp].
      pose proof (Hrange _ (Hs2 Hr)) as [Hsd0 Hsd]. lia.
    + lia.
  - destruct (Z.eq_dec col k) as [Hck|Hck].
    + destruct (Hsame Hck) as [Hs _].
      pose proof (Hrange _ Hs) as [_ Hsp]. lia.
    + lia.
Qed.

Lemma P082InitState_complete : forall n k dp pref,
  0 <= n ->
  P082InitState n k (n + 1) dp pref ->
  P082BaseColumns n k dp pref.
Proof.
  intros n k dp pref Hn [Hdl [Hpl [Hrange [Hdone [Htodo Hzero]]]]].
  unfold P082BaseColumns. split; [exact Hdl|].
  split; [exact Hpl|]. split; [exact Hrange|].
  split.
  - intros row Hrow. apply Hdone. lia.
  - intros col Hcol. apply Hzero; [lia|exact Hcol|]. left; reflexivity.
Qed.

Lemma P082Columns_start : forall n k col dp pref,
  P082ColumnsState n k col dp pref ->
  P082ColumnProgress n k col 1 dp pref.
Proof.
  intros n k col dp pref H. split; [exact H|]. intros row Hrow. lia.
Qed.

Lemma P082ColumnProgress_complete : forall n k col dp pref,
  P082ColumnProgress n k col (n + 1) dp pref ->
  P082ColumnsState n k (col + 1) dp pref.
Proof.
  intros n k col dp pref [Hcols Hcurrent].
  destruct Hcols as [Hbase Hold]. split; [exact Hbase|].
  intros c row Hc Hrow.
  destruct (Z_lt_ge_dec c col) as [Hlt|Hge].
  - apply Hold; lia.
  - assert (c = col) by lia. subst c. apply Hcurrent. lia.
Qed.

Lemma P082RawCell_ordinary : forall k row col dp pref,
  col <> k ->
  P082RawCell k row col dp pref =
    Znth (P082Index k (row - 1) (col - 1)) pref 0 -
    (if Z_le_dec 3 row
     then Znth (P082Index k (row - 2) (col - 1)) dp 0
     else 0).
Proof.
  intros k row col dp pref Hneq. unfold P082RawCell.
  destruct (Z.eq_dec col k); [contradiction|lia].
Qed.

Lemma P082RawCell_saturated : forall k row dp pref,
  P082RawCell k row k dp pref =
    Znth (P082Index k (row - 1) (k - 1)) pref 0 -
    (if Z_le_dec 3 row
     then Znth (P082Index k (row - 2) (k - 1)) dp 0
     else 0) +
    (Znth (P082Index k (row - 1) k) pref 0 -
     (if Z_le_dec 3 row
      then Znth (P082Index k (row - 2) k) dp 0
      else 0)).
Proof.
  intros. unfold P082RawCell. destruct (Z.eq_dec k k); [reflexivity|contradiction].
Qed.

Lemma P082CellEquation_prefix : forall k row col dp pref,
  P082CellEquation k row col dp pref ->
  Znth (P082Index k row col) pref 0 =
    P082Norm
      (Znth (P082Index k (row - 1) col) pref 0 +
       Znth (P082Index k row col) dp 0).
Proof. intros k row col dp pref [_ H]. exact H. Qed.

Lemma P082Columns_final_cell : forall n k dp pref,
  2 <= k -> 1 <= n ->
  P082ColumnsState n k (k + 1) dp pref ->
  P082CellEquation k n k dp pref.
Proof.
  intros n k dp pref Hk Hn [_ Hcells]. apply Hcells; lia.
Qed.

Lemma P082Final_bridge_use : forall n k dp pref,
  P082CombinatorialBridge n k ->
  P082ColumnsState n k (k + 1) dp pref ->
  Spec n k (P082FinalExpression k n dp).
Proof. intros n k dp pref Hbridge Htable. apply Hbridge with pref. exact Htable. Qed.

(* Compatibility realization for the frozen [Extern Coq] identifier. *)
Definition Zmin : Z -> Z -> Z := Z.min.

(* Canonical run-length profiles.  The first run may have length two, while
   every subsequently completed non-final run uses the unique representation
   in which length two has been split into two singleton runs. *)
Definition P082CoreCarrier (size runs : Z) (parts : list Z) : Prop :=
  Zlength parts = runs /\ Forall (fun x => 1 <= x < size + 1) parts.

Definition P082CoreComposition (size runs : Z) (parts : list Z) : Prop :=
  P082CoreCarrier size runs parts /\
  fold_right Z.add 0 parts = size /\
  forall t, 1 <= t < runs -> Znth t parts 0 <> 2.

#[local] Instance P082_finite_part_value (size : Z) :
  Finite (fun x : Z => 1 <= x < size + 1) :=
  finite_Z_range 1 (size + 1).

#[local] Instance P082_finite_core_carrier (size runs : Z) :
  Finite (P082CoreCarrier size runs) :=
  Finite_bounded_lists runs (fun x : Z => 1 <= x < size + 1).

#[local] Instance P082_finite_core_composition (size runs : Z) :
  Finite (P082CoreComposition size runs) :=
  Finite_subset (P082CoreCarrier size runs)
    (fun parts => fold_right Z.add 0 parts = size /\
      forall t, 1 <= t < runs -> Znth t parts 0 <> 2).

Definition P082ExactCoreCount (size runs : Z) : Z :=
  #(P082CoreComposition size runs).

Definition P082SaturatedCoreCount (size threshold : Z) : Z :=
  sum_range threshold size (fun runs => P082ExactCoreCount size runs).

Definition P082PrefixCoreCount
    (size threshold cap : Z) : Z :=
  sum_range 0 size
    (fun total =>
       if Z_lt_dec threshold cap
       then P082ExactCoreCount total threshold
       else P082SaturatedCoreCount total threshold).

Definition P082SemanticCell
    (k row col : Z) (dp pref : list Z) : Prop :=
  Znth (P082Index k row col) dp 0 =
    P082Norm
      (if Z_lt_dec col k
       then P082ExactCoreCount row col
       else P082SaturatedCoreCount row k) /\
  Znth (P082Index k row col) pref 0 =
    P082Norm (P082PrefixCoreCount row col k).

Definition P082SemanticInit
    (n k next_row : Z) (dp pref : list Z) : Prop :=
  forall row, 0 <= row < next_row ->
    P082SemanticCell k row 1 dp pref.

Definition P082SemanticColumns
    (n k next_col : Z) (dp pref : list Z) : Prop :=
  forall col row, 1 <= col < next_col -> 0 <= row <= n ->
    P082SemanticCell k row col dp pref.

Definition P082SemanticProgress
    (n k col next_row : Z) (dp pref : list Z) : Prop :=
  P082SemanticColumns n k col dp pref /\
  forall row, 0 <= row < next_row ->
    P082SemanticCell k row col dp pref.

Definition P082CanonicalAnswer (n k : Z) : Z :=
  P082Norm
    (P082SaturatedCoreCount n k +
     P082ExactCoreCount (n - 2) (k - 1) +
     P082SaturatedCoreCount (n - 2) k).

Definition P082CanonicalProfile (n k : Z) (parts : list Z) : Prop :=
  fold_right Z.add 0 parts = n /\
  k <= Zlength parts /\
  Forall (fun x => 1 <= x <= n) parts /\
  forall t, 1 <= t < Zlength parts - 1 -> Znth t parts 0 <> 2.

Definition P082CanonicalProfileCorrect (n k : Z) : Prop :=
  Spec n k (P082CanonicalAnswer n k).

Lemma P082SemanticColumns_start : forall n k col dp pref,
  P082SemanticColumns n k col dp pref ->
  P082SemanticProgress n k col 0 dp pref.
Proof.
  intros n k col dp pref H. split; [exact H|]. intros row Hrow. lia.
Qed.

Lemma P082SemanticProgress_complete : forall n k col dp pref,
  P082SemanticProgress n k col (n + 1) dp pref ->
  P082SemanticColumns n k (col + 1) dp pref.
Proof.
  intros n k col dp pref [Hcols Hcurrent] c row Hc Hrow.
  destruct (Z_lt_ge_dec c col) as [Hlt|Hge].
  - apply Hcols; lia.
  - assert (c = col) by lia. subst c. apply Hcurrent. lia.
Qed.

Lemma P082Semantic_final_cells : forall n k dp pref,
  2 <= k -> 2 <= n ->
  P082SemanticColumns n k (k + 1) dp pref ->
  Znth (P082Index k n k) dp 0 = P082Norm (P082SaturatedCoreCount n k) /\
  Znth (P082Index k (n - 2) (k - 1)) dp 0 =
    P082Norm (P082ExactCoreCount (n - 2) (k - 1)) /\
  Znth (P082Index k (n - 2) k) dp 0 =
    P082Norm (P082SaturatedCoreCount (n - 2) k).
Proof.
  intros n k dp pref Hk Hn Hsem.
  pose proof (Hsem k n ltac:(lia) ltac:(lia)) as [A _].
  pose proof (Hsem (k-1) (n-2) ltac:(lia) ltac:(lia)) as [B _].
  pose proof (Hsem k (n-2) ltac:(lia) ltac:(lia)) as [C _].
  unfold P082SemanticCell in *. split.
  - destruct (Z_lt_dec k k); [lia|exact A].
  - split.
    + destruct (Z_lt_dec (k-1) k); [exact B|lia].
    + destruct (Z_lt_dec k k); [lia|exact C].
Qed.

Lemma P082Semantic_final_expression : forall n k dp pref,
  2 <= k -> 2 <= n ->
  P082SemanticColumns n k (k + 1) dp pref ->
  P082FinalExpression k n dp = P082CanonicalAnswer n k.
Proof.
  intros n k dp pref Hk Hn Hsem.
  pose proof (P082Semantic_final_cells n k dp pref Hk Hn Hsem)
    as [A [B C]].
  unfold P082FinalExpression, P082CanonicalAnswer, P082Norm in *.
  rewrite A, B, C.
  set (a := P082SaturatedCoreCount n k).
  set (b := P082ExactCoreCount (n - 2) (k - 1)).
  set (c := P082SaturatedCoreCount (n - 2) k).
  assert (HM : P082Modulus <> 0) by (unfold P082Modulus; lia).
  rewrite <- (Z.add_mod_idemp_l (a mod P082Modulus + b mod P082Modulus)
               (c mod P082Modulus) P082Modulus HM).
  rewrite <- (Z.add_mod a b P082Modulus HM).
  rewrite (Z.add_mod_idemp_l (a + b) (c mod P082Modulus)
             P082Modulus HM).
  rewrite (Z.add_mod_idemp_r (a + b) c P082Modulus HM).
  reflexivity.
Qed.

(* Structural part of the final canonical partition.  A core profile already
   is canonical when no terminal length-two block is present. *)
Lemma P082CoreComposition_is_CanonicalProfile : forall n k runs parts,
  0 <= n -> k <= runs ->
  P082CoreComposition n runs parts ->
  P082CanonicalProfile n k parts.
Proof.
  intros n k runs parts Hn Hkr [[Hlen Hbounds] [Hsum Hno2]].
  unfold P082CanonicalProfile.
  split; [exact Hsum|].
  split; [rewrite Hlen; exact Hkr|].
  split.
  - apply Forall_forall. intros x Hx.
    apply Forall_forall with (x := x) in Hbounds; auto. lia.
  - intros t Ht. apply Hno2. lia.
Qed.

(* The complementary canonical class consists of a core profile followed by
   the distinguished terminal block of length two. *)
Lemma P082CoreComposition_snoc_two_is_CanonicalProfile :
  forall n k runs parts,
    2 <= n -> k <= runs + 1 ->
    P082CoreComposition (n - 2) runs parts ->
    P082CanonicalProfile n k (parts ++ (2 :: nil)).
Proof.
  intros n k runs parts Hn Hkr [[Hlen Hbounds] [Hsum Hno2]].
  unfold P082CanonicalProfile.
  rewrite Zlength_app, Hlen. simpl Zlength.
  split.
  - rewrite fold_right_app. simpl.
    assert (Hacc : forall xs acc,
      fold_right Z.add acc xs = fold_right Z.add 0 xs + acc).
    { induction xs as [|x xs IH]; intros acc; simpl; [lia|].
      rewrite IH. lia. }
    rewrite Hacc, Hsum. lia.
  - split; [exact Hkr|]. split.
    + apply Forall_app. split.
      * apply Forall_forall. intros x Hx.
        apply Forall_forall with (x := x) in Hbounds; auto. lia.
      * repeat constructor; lia.
    + intros t [Htlo Hthi].
      assert (Htwo : Zlength (2 :: nil) = 1) by reflexivity.
      rewrite Htwo in Hthi.
      assert (Htupper : t < runs) by lia.
      rewrite app_Znth1.
      2:{ rewrite Hlen. split; [lia|exact Htupper]. }
      apply Hno2. split; assumption.
Qed.

Lemma P082In_has_Znth_witness : forall (x : Z) xs,
  In x xs -> exists i, 0 <= i < Zlength xs /\ Znth i xs 0 = x.
Proof.
  intros x xs. induction xs as [|y ys IH]; intros Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y. exists 0. split.
      * pose proof (Zlength_nonneg ys). rewrite Zlength_cons. lia.
      * apply Znth0_cons.
    + destruct (IH Hin) as [i [[Hilo Hihi] Hi]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        exact Hi.
Qed.

Lemma P082UsesEveryValue_position_witness : forall k a x,
  UsesEveryValue k a -> 1 <= x <= k ->
  exists i, 0 <= i < Zlength a /\ Znth i a 0 = x.
Proof.
  intros k a x [_ Hall] Hx.
  apply P082In_has_Znth_witness. apply Hall. exact Hx.
Qed.

Lemma P082UsesEveryValue_distinct_positions : forall k a x y ix iy,
  UsesEveryValue k a ->
  1 <= x <= k -> 1 <= y <= k -> x <> y ->
  0 <= ix < Zlength a -> 0 <= iy < Zlength a ->
  Znth ix a 0 = x -> Znth iy a 0 = y -> ix <> iy.
Proof.
  intros k a x y ix iy _ _ _ Hxy _ _ Hix Hiy Heq.
  subst iy. apply Hxy. rewrite <- Hix, <- Hiy. reflexivity.
Qed.

Lemma P082DistanceArray_nearest_different_witness : forall a b i,
  DistanceArray a b ->
  0 <= i < Zlength a ->
  exists j,
    0 <= j < Zlength a /\
    Znth j a 0 <> Znth i a 0 /\
    Znth i b 0 = Z.abs (i - j) /\
    forall q,
      0 <= q < Zlength a ->
      Znth q a 0 <> Znth i a 0 ->
      Z.abs (i - j) <= Z.abs (i - q).
Proof.
  intros a b i [_ Hdistance] Hi.
  specialize (Hdistance i Hi).
  unfold min_value_of_subset, min_object_of_subset in Hdistance.
  destruct Hdistance as [j [[[Hj Hneq] Hminimal] Heq]].
  exists j. split; [exact Hj|].
  split; [exact Hneq|].
  split.
  - symmetry. exact Heq.
  - intros q Hq Hqneq. apply Hminimal. split; assumption.
Qed.

Lemma P082DistanceArray_entry_positive : forall a b i,
  DistanceArray a b ->
  0 <= i < Zlength a ->
  0 < Znth i b 0.
Proof.
  intros a b i Harray Hi.
  destruct (P082DistanceArray_nearest_different_witness a b i Harray Hi)
    as [j [Hj [Hneq [Heq _]]]].
  rewrite Heq.
  apply Z.abs_pos.
  intro Hij. apply Hneq.
  assert (i = j) by lia. subst j. reflexivity.
Qed.

Lemma P082DistanceArray_entry_bounded : forall a b i,
  DistanceArray a b ->
  0 <= i < Zlength a ->
  Znth i b 0 < Zlength a.
Proof.
  intros a b i Harray Hi.
  destruct (P082DistanceArray_nearest_different_witness a b i Harray Hi)
    as [j [Hj [_ [Heq _]]]].
  rewrite Heq.
  rewrite Z.abs_lt. lia.
Qed.

Lemma P082DistanceArray_inside_radius_same : forall a b i q,
  DistanceArray a b ->
  0 <= i < Zlength a ->
  0 <= q < Zlength a ->
  Z.abs (i - q) < Znth i b 0 ->
  Znth q a 0 = Znth i a 0.
Proof.
  intros a b i q Harray Hi Hq Hinside.
  destruct (P082DistanceArray_nearest_different_witness a b i Harray Hi)
    as [j [_ [_ [Heq Hminimal]]]].
  destruct (Z.eq_dec (Znth q a 0) (Znth i a 0)) as [Hsame|Hdifferent].
  - exact Hsame.
  - specialize (Hminimal q Hq Hdifferent).
    rewrite Heq in Hinside. lia.
Qed.

Definition P082MaximalSameBlock
    (a : list Z) (lo hi anchor : Z) : Prop :=
  0 <= lo <= anchor /\ anchor < hi <= Zlength a /\
  (forall q, lo <= q < hi -> Znth q a 0 = Znth anchor a 0) /\
  (lo = 0 \/ Znth (lo - 1) a 0 <> Znth anchor a 0) /\
  (hi = Zlength a \/ Znth hi a 0 <> Znth anchor a 0).

Lemma P082MaximalSameBlock_reanchor : forall a lo hi anchor q,
  P082MaximalSameBlock a lo hi anchor ->
  lo <= q < hi ->
  P082MaximalSameBlock a lo hi q.
Proof.
  intros a lo hi anchor q
    [[Hlo Hloa] [[Hahi Hhlen] [Hsame [Hleft Hright]]]] Hq.
  assert (Hqa : Znth q a 0 = Znth anchor a 0) by
    (apply Hsame; exact Hq).
  unfold P082MaximalSameBlock.
  split; [lia|]. split; [lia|]. split.
  - intros r Hr. rewrite Hqa. apply Hsame. exact Hr.
  - split.
    + destruct Hleft as [Hzero|Hdifferent].
      * left. exact Hzero.
      * right. rewrite Hqa. exact Hdifferent.
    + destruct Hright as [Hend|Hdifferent].
      * left. exact Hend.
      * right. rewrite Hqa. exact Hdifferent.
Qed.

Lemma P082MaximalSameBlock_unique_at : forall a lo1 hi1 lo2 hi2 anchor,
  P082MaximalSameBlock a lo1 hi1 anchor ->
  P082MaximalSameBlock a lo2 hi2 anchor ->
  lo1 = lo2 /\ hi1 = hi2.
Proof.
  intros a lo1 hi1 lo2 hi2 anchor Hblock1 Hblock2.
  destruct Hblock1 as
    [[Hlo1 Hlo1a] [[Ha1hi Hhi1len] [Hsame1 [Hleft1 Hright1]]]].
  destruct Hblock2 as
    [[Hlo2 Hlo2a] [[Ha2hi Hhi2len] [Hsame2 [Hleft2 Hright2]]]].
  assert (Hloeq : lo1 = lo2).
  { destruct (Z_lt_ge_dec lo1 lo2) as [Hlt|Hge].
    - destruct Hleft2 as [Hzero|Hdifferent].
      + lia.
      + exfalso. apply Hdifferent.
        rewrite Hsame1 by lia. apply Hsame2. lia.
    - destruct (Z.eq_dec lo1 lo2) as [Heq|Hneq]; [exact Heq|].
      assert (Hgt : lo2 < lo1) by lia.
      destruct Hleft1 as [Hzero|Hdifferent].
      + lia.
      + exfalso. apply Hdifferent.
        rewrite Hsame2 by lia. apply Hsame1. lia. }
  assert (Hhieq : hi1 = hi2).
  { destruct (Z_lt_ge_dec hi1 hi2) as [Hlt|Hge].
    - destruct Hright1 as [Hend|Hdifferent].
      + lia.
      + exfalso. apply Hdifferent.
        rewrite Hsame2 by lia. apply Hsame1. lia.
    - destruct (Z.eq_dec hi1 hi2) as [Heq|Hneq]; [exact Heq|].
      assert (Hgt : hi2 < hi1) by lia.
      destruct Hright2 as [Hend|Hdifferent].
      + lia.
      + exfalso. apply Hdifferent.
        rewrite Hsame1 by lia. apply Hsame2. lia. }
  split; assumption.
Qed.

Lemma P082MaximalSameBlock_overlap_equal : forall
    a lo1 hi1 anchor1 lo2 hi2 anchor2 q,
  P082MaximalSameBlock a lo1 hi1 anchor1 ->
  P082MaximalSameBlock a lo2 hi2 anchor2 ->
  lo1 <= q < hi1 -> lo2 <= q < hi2 ->
  lo1 = lo2 /\ hi1 = hi2.
Proof.
  intros a lo1 hi1 anchor1 lo2 hi2 anchor2 q Hblock1 Hblock2 Hq1 Hq2.
  apply (P082MaximalSameBlock_unique_at a lo1 hi1 lo2 hi2 q).
  - apply (P082MaximalSameBlock_reanchor a lo1 hi1 anchor1 q);
      assumption.
  - apply (P082MaximalSameBlock_reanchor a lo2 hi2 anchor2 q);
      assumption.
Qed.

Lemma P082MaximalSameBlock_disjoint_or_equal : forall
    a lo1 hi1 anchor1 lo2 hi2 anchor2,
  P082MaximalSameBlock a lo1 hi1 anchor1 ->
  P082MaximalSameBlock a lo2 hi2 anchor2 ->
  (lo1 = lo2 /\ hi1 = hi2) \/ hi1 <= lo2 \/ hi2 <= lo1.
Proof.
  intros a lo1 hi1 anchor1 lo2 hi2 anchor2 Hblock1 Hblock2.
  destruct Hblock1 as [Hrange1 Hrest1].
  destruct Hblock2 as [Hrange2 Hrest2].
  destruct (Z_le_dec hi1 lo2) as [Hbefore|Hnotbefore].
  - right. left. exact Hbefore.
  - destruct (Z_le_dec hi2 lo1) as [Hafter|Hnotafter].
    + right. right. exact Hafter.
    + left.
      apply (P082MaximalSameBlock_overlap_equal
        a lo1 hi1 anchor1 lo2 hi2 anchor2
        (if Z_le_dec lo1 lo2 then lo2 else lo1)).
      * split; assumption.
      * split; assumption.
      * destruct (Z_le_dec lo1 lo2); simpl; lia.
      * destruct (Z_le_dec lo1 lo2); simpl; lia.
Qed.

Definition P082OrderedBlockCover
    (a : list Z) (blocks : list (Z * Z)) : Prop :=
  (forall t, 0 <= t < Zlength blocks ->
     let block := Znth t blocks (0, 0) in
     exists anchor,
       P082MaximalSameBlock a (fst block) (snd block) anchor) /\
  (forall t u, 0 <= t < u -> u < Zlength blocks ->
     snd (Znth t blocks (0, 0)) <= fst (Znth u blocks (0, 0))) /\
  (forall q, 0 <= q < Zlength a ->
     exists t, 0 <= t < Zlength blocks /\
       fst (Znth t blocks (0, 0)) <= q <
       snd (Znth t blocks (0, 0))).

Lemma P082OrderedBlockCover_position_exists : forall a blocks q,
  P082OrderedBlockCover a blocks ->
  0 <= q < Zlength a ->
  exists t, 0 <= t < Zlength blocks /\
    fst (Znth t blocks (0, 0)) <= q <
    snd (Znth t blocks (0, 0)).
Proof.
  intros a blocks q [_ [_ Hcover]] Hq.
  apply Hcover. exact Hq.
Qed.

Lemma P082OrderedBlockCover_position_unique : forall a blocks q t u,
  P082OrderedBlockCover a blocks ->
  0 <= t < Zlength blocks ->
  0 <= u < Zlength blocks ->
  fst (Znth t blocks (0, 0)) <= q < snd (Znth t blocks (0, 0)) ->
  fst (Znth u blocks (0, 0)) <= q < snd (Znth u blocks (0, 0)) ->
  t = u.
Proof.
  intros a blocks q t u [_ [Hordered _]] Ht Hu Hqt Hqu.
  destruct (Z_lt_ge_dec t u) as [Htu|Hut].
  - pose proof (Hordered t u ltac:(lia) ltac:(lia)). lia.
  - destruct (Z.eq_dec t u) as [Heq|Hneq]; [exact Heq|].
    assert (Hut' : u < t) by lia.
    pose proof (Hordered u t ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma P082OrderedBlockCover_index_injective : forall a blocks t u,
  P082OrderedBlockCover a blocks ->
  0 <= t < Zlength blocks ->
  0 <= u < Zlength blocks ->
  Znth t blocks (0, 0) = Znth u blocks (0, 0) ->
  t = u.
Proof.
  intros a blocks t u [Hblocks [Hordered Hcover]] Ht Hu Heq.
  pose proof (Hblocks t Ht) as Hblock_t.
  destruct (Znth t blocks (0, 0)) as [lo hi] eqn:Hblock.
  simpl in Hblock_t.
  destruct Hblock_t as [anchor Hmax].
  destruct Hmax as [[Hlo Hloa] [[Hahi Hhlen] Hrest]].
  apply (P082OrderedBlockCover_position_unique a blocks lo t u).
  - repeat split; assumption.
  - exact Ht.
  - exact Hu.
  - rewrite Hblock. simpl. lia.
  - rewrite <- Heq. simpl. lia.
Qed.

Definition P082OrderedBlockLengths (blocks : list (Z * Z)) : list Z :=
  map (fun block => snd block - fst block) blocks.

Lemma P082In_has_Znth_witness_any : forall
    (A : Type) (default x : A) xs,
  In x xs ->
  exists i, 0 <= i < Zlength xs /\ Znth i xs default = x.
Proof.
  intros A default x xs. induction xs as [|y ys IH]; intros Hin;
    simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst y. exists 0. split.
      * pose proof (Zlength_nonneg ys). rewrite Zlength_cons. lia.
      * apply Znth0_cons.
    + destruct (IH Hin) as [i [[Hilo Hihi] Hi]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia. exact Hi.
Qed.

Lemma P082OrderedBlockLengths_length : forall blocks,
  Zlength (P082OrderedBlockLengths blocks) = Zlength blocks.
Proof.
  intro blocks. unfold P082OrderedBlockLengths.
  induction blocks as [|block rest IH]; simpl; [reflexivity|].
  repeat rewrite Zlength_cons. lia.
Qed.

Lemma P082OrderedBlockLengths_bounds : forall a blocks,
  P082OrderedBlockCover a blocks ->
  Forall (fun len => 1 <= len <= Zlength a)
    (P082OrderedBlockLengths blocks).
Proof.
  intros a blocks [Hblocks Hcover].
  unfold P082OrderedBlockLengths.
  apply Forall_forall. intros len Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[lo hi] [Hlen Hinblock]]. simpl in Hlen. subst len.
  destruct (P082In_has_Znth_witness_any
    (Z * Z) (0, 0) (lo, hi) blocks Hinblock)
    as [t [Ht Htblock]].
  specialize (Hblocks t Ht).
  rewrite Htblock in Hblocks. simpl in Hblocks.
  destruct Hblocks as [anchor Hmax].
  destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrest]].
  lia.
Qed.

Inductive P082EndpointChain : Z -> Z -> list (Z * Z) -> Prop :=
| P082EndpointChain_nil : forall endpoint,
    P082EndpointChain endpoint endpoint nil
| P082EndpointChain_cons : forall lo mid hi rest,
    P082EndpointChain mid hi rest ->
    P082EndpointChain lo hi ((lo, mid) :: rest).

Lemma P082EndpointChain_lengths_sum : forall lo hi blocks,
  P082EndpointChain lo hi blocks ->
  fold_right Z.add 0 (P082OrderedBlockLengths blocks) = hi - lo.
Proof.
  intros lo hi blocks Hchain. induction Hchain; simpl.
  - lia.
  - rewrite IHHchain. lia.
Qed.

Lemma P082OrderedBlockCover_lengths_CanonicalProfile : forall a blocks k,
  P082OrderedBlockCover a blocks ->
  P082EndpointChain 0 (Zlength a) blocks ->
  k <= Zlength blocks ->
  (forall t,
    1 <= t < Zlength (P082OrderedBlockLengths blocks) - 1 ->
    Znth t (P082OrderedBlockLengths blocks) 0 <> 2) ->
  P082CanonicalProfile (Zlength a) k (P082OrderedBlockLengths blocks).
Proof.
  intros a blocks k Hcover Hchain Hk Hno2.
  unfold P082CanonicalProfile.
  split.
  - rewrite (P082EndpointChain_lengths_sum 0 (Zlength a) blocks Hchain).
    lia.
  - split.
    + rewrite P082OrderedBlockLengths_length. exact Hk.
    + split.
      * apply P082OrderedBlockLengths_bounds. exact Hcover.
      * exact Hno2.
Qed.

Lemma P082OrderedBlockCover_first_start : forall a lo hi rest,
  P082OrderedBlockCover a ((lo, hi) :: rest) ->
  lo = 0.
Proof.
  intros a lo hi rest [Hblocks [Hordered Hcover]].
  assert (Hrestlen : 0 <= Zlength rest) by apply Zlength_nonneg.
  pose proof (Hblocks 0 ltac:(rewrite Zlength_cons; lia)) as Hfirst.
  rewrite Znth0_cons in Hfirst. simpl in Hfirst.
  destruct Hfirst as [anchor Hmax].
  destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrest]].
  assert (Hlength : 0 < Zlength a) by lia.
  destruct (Hcover 0 ltac:(lia)) as [t [Ht Hcontains]].
  destruct (Z.eq_dec t 0) as [Heq|Hneq].
  - subst t. rewrite Znth0_cons in Hcontains. simpl in Hcontains. lia.
  - assert (Hpositive : 0 < t) by lia.
    pose proof (Hordered 0 t ltac:(lia) ltac:(lia)) as Hbefore.
    rewrite Znth0_cons in Hbefore. simpl in Hbefore. lia.
Qed.

Lemma P082OrderedBlockCover_adjacent : forall a blocks t,
  P082OrderedBlockCover a blocks ->
  0 <= t -> t + 1 < Zlength blocks ->
  snd (Znth t blocks (0, 0)) =
  fst (Znth (t + 1) blocks (0, 0)).
Proof.
  intros a blocks t [Hblocks [Hordered Hcover]] Ht Htnext.
  destruct (Znth t blocks (0, 0)) as [lo hi] eqn:Hcurrent.
  destruct (Znth (t + 1) blocks (0, 0)) as [nextlo nexthi]
    eqn:Hnext.
  simpl.
  pose proof (Hblocks t ltac:(lia)) as Hcurrentmax.
  rewrite Hcurrent in Hcurrentmax. simpl in Hcurrentmax.
  destruct Hcurrentmax as [anchor Hmax].
  destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrest]].
  pose proof (Hblocks (t + 1) ltac:(lia)) as Hnextmax.
  rewrite Hnext in Hnextmax. simpl in Hnextmax.
  destruct Hnextmax as [nextanchor Hnextmax].
  destruct Hnextmax as
    [[Hnextlo Hnextloa] [[Hnextahi Hnexthilength] Hnextrest]].
  pose proof (Hordered t (t + 1) ltac:(lia) ltac:(lia)) as Hle.
  rewrite Hcurrent, Hnext in Hle. simpl in Hle.
  destruct (Z.eq_dec hi nextlo) as [Heq|Hneq]; [exact Heq|].
  assert (Hgap : hi < nextlo) by lia.
  destruct (Hcover hi ltac:(lia)) as [u [Hu Hucontains]].
  destruct (Z_lt_ge_dec u t) as [Hut|Hut].
  - pose proof (Hordered u t ltac:(lia) ltac:(lia)) as Hbefore.
    rewrite Hcurrent in Hbefore. simpl in Hbefore. lia.
  - destruct (Z.eq_dec u t) as [Heq|Hnequt].
    + subst u. rewrite Hcurrent in Hucontains. simpl in Hucontains. lia.
    + assert (Htu : t < u) by lia.
      destruct (Z.eq_dec u (t + 1)) as [Heq|Hnequ].
      * subst u. rewrite Hnext in Hucontains. simpl in Hucontains. lia.
      * assert (Ht1u : t + 1 < u) by lia.
        pose proof (Hordered (t + 1) u ltac:(lia) ltac:(lia))
          as Hafter.
        rewrite Hnext in Hafter. simpl in Hafter. lia.
Qed.

Lemma P082OrderedBlockCover_last_end : forall a blocks,
  P082OrderedBlockCover a blocks ->
  0 < Zlength blocks ->
  snd (Znth (Zlength blocks - 1) blocks (0, 0)) = Zlength a.
Proof.
  intros a blocks [Hblocks [Hordered Hcover]] Hnonempty.
  set (last := Zlength blocks - 1).
  destruct (Znth last blocks (0, 0)) as [lo hi] eqn:Hlast.
  simpl.
  pose proof (Hblocks last ltac:(unfold last; lia)) as Hlastmax.
  rewrite Hlast in Hlastmax. simpl in Hlastmax.
  destruct Hlastmax as [anchor Hmax].
  destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrest]].
  assert (Hlength : 0 < Zlength a) by lia.
  destruct (Hcover (Zlength a - 1) ltac:(lia))
    as [t [Ht Hcontains]].
  destruct (Z.eq_dec t last) as [Heq|Hneq].
  - subst t. rewrite Hlast in Hcontains. simpl in Hcontains. lia.
  - assert (Htlast : t < last) by (unfold last; lia).
    pose proof (Hordered t last ltac:(lia) ltac:(unfold last; lia))
      as Hbefore.
    rewrite Hlast in Hbefore. simpl in Hbefore. lia.
Qed.

Lemma P082EndpointChain_from_indexed_endpoints : forall blocks lo hi,
  0 < Zlength blocks ->
  fst (Znth 0 blocks (0, 0)) = lo ->
  snd (Znth (Zlength blocks - 1) blocks (0, 0)) = hi ->
  (forall t, 0 <= t -> t + 1 < Zlength blocks ->
    snd (Znth t blocks (0, 0)) =
    fst (Znth (t + 1) blocks (0, 0))) ->
  P082EndpointChain lo hi blocks.
Proof.
  induction blocks as [|[blocklo blockhi] rest IH];
    intros lo hi Hnonempty Hfirst Hlast Hadj.
  - change (0 < 0) in Hnonempty. lia.
  - destruct rest as [|[nextlo nexthi] tail].
    + rewrite Znth0_cons in Hfirst. simpl in Hfirst.
      rewrite Zlength_cons in Hlast. simpl Zlength in Hlast.
      replace (1 - 1) with 0 in Hlast by lia.
      rewrite Znth0_cons in Hlast. simpl in Hlast.
      subst lo hi. constructor. constructor.
    + rewrite Znth0_cons in Hfirst. simpl in Hfirst. subst lo.
      assert (Htaillen : 0 <= Zlength tail) by apply Zlength_nonneg.
      apply P082EndpointChain_cons.
      apply (IH blockhi hi).
      * rewrite Zlength_cons. lia.
      * rewrite Znth0_cons. simpl.
        specialize (Hadj 0 ltac:(lia) ltac:(repeat rewrite Zlength_cons; lia)).
        rewrite Znth0_cons in Hadj.
        rewrite Znth_cons in Hadj by lia.
        replace (0 + 1 - 1) with 0 in Hadj by lia.
        rewrite Znth0_cons in Hadj. simpl in Hadj. symmetry. exact Hadj.
      * rewrite Zlength_cons in Hlast.
        rewrite Znth_cons in Hlast by
          (repeat rewrite Zlength_cons; pose proof (Zlength_nonneg tail); lia).
        replace (Z.succ (Zlength ((nextlo, nexthi) :: tail)) - 1 - 1)
          with (Zlength ((nextlo, nexthi) :: tail) - 1) in Hlast by lia.
        exact Hlast.
      * intros t Ht Htnext.
        specialize (Hadj (t + 1) ltac:(lia)
          ltac:(rewrite Zlength_cons; lia)).
        assert (Hleft :
          Znth (t + 1) ((blocklo, blockhi) :: (nextlo, nexthi) :: tail)
            (0, 0) =
          Znth t ((nextlo, nexthi) :: tail) (0, 0)).
        { rewrite Znth_cons by lia. f_equal. lia. }
        assert (Hright :
          Znth (t + 1 + 1)
            ((blocklo, blockhi) :: (nextlo, nexthi) :: tail) (0, 0) =
          Znth (t + 1) ((nextlo, nexthi) :: tail) (0, 0)).
        { rewrite Znth_cons by lia. f_equal. lia. }
        rewrite Hleft, Hright in Hadj.
        exact Hadj.
Qed.

Lemma P082OrderedBlockCover_endpoint_chain : forall a blocks,
  P082OrderedBlockCover a blocks ->
  0 < Zlength blocks ->
  P082EndpointChain 0 (Zlength a) blocks.
Proof.
  intros a blocks Hcover Hnonempty.
  apply P082EndpointChain_from_indexed_endpoints.
  - exact Hnonempty.
  - destruct blocks as [|[lo hi] rest].
    + change (0 < 0) in Hnonempty. lia.
    + rewrite Znth0_cons. simpl.
      apply P082OrderedBlockCover_first_start with
        (a := a) (hi := hi) (rest := rest). exact Hcover.
  - apply P082OrderedBlockCover_last_end; assumption.
  - intros t Ht Htnext.
    apply P082OrderedBlockCover_adjacent with (a := a); assumption.
Qed.

Lemma P082OrderedBlockCover_nonempty : forall a blocks,
  P082OrderedBlockCover a blocks ->
  0 < Zlength a ->
  0 < Zlength blocks.
Proof.
  intros a blocks Hcover Hlength.
  destruct (P082OrderedBlockCover_position_exists a blocks 0 Hcover
    ltac:(lia)) as [t [Ht Hcontains]].
  lia.
Qed.

Lemma P082OrderedBlockCover_total_endpoint_chain : forall a blocks,
  P082OrderedBlockCover a blocks ->
  0 < Zlength a ->
  P082EndpointChain 0 (Zlength a) blocks.
Proof.
  intros a blocks Hcover Hlength.
  apply P082OrderedBlockCover_endpoint_chain; [exact Hcover|].
  apply P082OrderedBlockCover_nonempty with (a := a); assumption.
Qed.

(* A transparent run decomposition, independent of the C dynamic program.
   It scans from right to left and merges the new head into the first run
   exactly when their values agree. *)
Fixpoint P082ComputeRuns (a : list Z) : list (list Z) :=
  match a with
  | nil => nil
  | x :: xs =>
      match P082ComputeRuns xs with
      | nil => (x :: nil) :: nil
      | nil :: rest => (x :: nil) :: nil :: rest
      | (y :: ys) :: rest =>
          if Z.eq_dec x y
          then (x :: y :: ys) :: rest
          else (x :: nil) :: (y :: ys) :: rest
      end
  end.

Definition P082ConstantRun (run : list Z) : Prop :=
  exists x, run <> nil /\ Forall (fun y => y = x) run.

Fixpoint P082SeparatedRuns (runs : list (list Z)) : Prop :=
  match runs with
  | nil => True
  | first :: rest =>
      match rest with
      | nil => True
      | second :: _ =>
          hd 0 first <> hd 0 second /\ P082SeparatedRuns rest
      end
  end.

Lemma P082ComputeRuns_nonempty : forall a run,
  In run (P082ComputeRuns a) -> run <> nil.
Proof.
  induction a as [|x xs IH]; intros run Hin; simpl in Hin.
  - contradiction.
  - remember (P082ComputeRuns xs) as runs eqn:Hruns.
    destruct runs as [|first rest].
    + simpl in Hin. destruct Hin as [<-|[]]. discriminate.
    + destruct first as [|y ys].
      * exfalso.
        pose proof (IH nil (or_introl eq_refl)) as Hbad.
        exact (Hbad eq_refl).
      * destruct (Z.eq_dec x y) as [Heq|Hneq]; simpl in Hin.
        -- destruct Hin as [<-|Hin]; [discriminate|].
           apply (IH run). simpl. right. exact Hin.
        -- destruct Hin as [<-|[<-|Hin]].
           ++ discriminate.
           ++ discriminate.
           ++ apply (IH run). simpl. right. exact Hin.
Qed.

Lemma P082ComputeRuns_concat : forall a,
  concat (P082ComputeRuns a) = a.
Proof.
  induction a as [|x xs IH]; [reflexivity|].
  simpl.
  remember (P082ComputeRuns xs) as runs eqn:Hruns.
  destruct runs as [|first rest].
  - simpl. rewrite <- IH. reflexivity.
  - assert (Hfirst : first <> nil).
    { apply (P082ComputeRuns_nonempty xs first).
      rewrite <- Hruns. simpl. auto. }
    destruct first as [|y ys]; [contradiction|].
    destruct (Z.eq_dec x y); simpl; rewrite <- IH; reflexivity.
Qed.

Lemma P082ComputeRuns_constant : forall a run,
  In run (P082ComputeRuns a) -> P082ConstantRun run.
Proof.
  induction a as [|x xs IH]; intros run Hin; simpl in Hin.
  - contradiction.
  - remember (P082ComputeRuns xs) as runs eqn:Hruns.
    destruct runs as [|first rest].
    + simpl in Hin. destruct Hin as [<-|[]].
      exists x. split; [discriminate|]. constructor; [reflexivity|constructor].
    + destruct first as [|y ys].
      * exfalso.
        destruct (IH nil (or_introl eq_refl)) as [v [Hbad Hforall]].
        exact (Hbad eq_refl).
      * assert (Hfirst : P082ConstantRun (y :: ys)).
        { apply (IH (y :: ys)). simpl. auto. }
        destruct Hfirst as [v [Hnonempty Hforall]].
        inversion Hforall as [|? ? Hy Hys]. subst v.
        destruct (Z.eq_dec x y) as [Heq|Hneq]; simpl in Hin.
        -- destruct Hin as [<-|Hin].
           ++ exists y. split; [discriminate|].
              constructor; [exact Heq|]. exact Hforall.
           ++ apply (IH run). simpl. right. exact Hin.
        -- destruct Hin as [<-|[<-|Hin]].
           ++ exists x. split; [discriminate|].
              constructor; [reflexivity|constructor].
           ++ exists y. split; [discriminate|]. exact Hforall.
           ++ apply (IH run). simpl. right. exact Hin.
Qed.

Lemma P082ComputeRuns_separated : forall a,
  P082SeparatedRuns (P082ComputeRuns a).
Proof.
  induction a as [|x xs IH]; [exact I|].
  simpl.
  remember (P082ComputeRuns xs) as runs eqn:Hruns.
  destruct runs as [|first rest]; [exact I|].
  destruct first as [|y ys].
  - exfalso.
    pose proof (P082ComputeRuns_nonempty xs nil
      ltac:(rewrite <- Hruns; simpl; auto)) as Hbad.
    exact (Hbad eq_refl).
  - destruct (Z.eq_dec x y) as [Heq|Hneq].
    + subst x. destruct rest as [|next tail]; simpl in *; assumption.
    + simpl. split; [exact Hneq|exact IH].
Qed.

Fixpoint P082BlocksFromRuns
    (offset : Z) (runs : list (list Z)) : list (Z * Z) :=
  match runs with
  | nil => nil
  | run :: rest =>
      (offset, offset + Zlength run) ::
      P082BlocksFromRuns (offset + Zlength run) rest
  end.

Definition P082ComputedBlocks (a : list Z) : list (Z * Z) :=
  P082BlocksFromRuns 0 (P082ComputeRuns a).

Lemma P082BlocksFromRuns_length : forall offset runs,
  Zlength (P082BlocksFromRuns offset runs) = Zlength runs.
Proof.
  intros offset runs. revert offset.
  induction runs as [|run rest IH]; intros offset; simpl; [reflexivity|].
  repeat rewrite Zlength_cons. rewrite IH. reflexivity.
Qed.

Lemma P082BlocksFromRuns_last_endpoint : forall offset runs,
  0 < Zlength runs ->
  snd (Znth (Zlength runs - 1) (P082BlocksFromRuns offset runs) (0, 0)) =
  offset + Zlength (concat runs).
Proof.
  intros offset runs Hnonempty. revert offset Hnonempty.
  induction runs as [|run rest IH]; intros offset Hnonempty.
  - change (0 < 0) in Hnonempty. lia.
  - destruct rest as [|next tail].
    + simpl. rewrite app_nil_r. reflexivity.
    + simpl P082BlocksFromRuns.
      rewrite Zlength_cons.
      rewrite Znth_cons by
        (repeat rewrite Zlength_cons; pose proof (Zlength_nonneg tail); lia).
      replace (Z.succ (Zlength (next :: tail)) - 1 - 1)
        with (Zlength (next :: tail) - 1) by lia.
      change
        (snd (Znth (Zlength (next :: tail) - 1)
          (P082BlocksFromRuns (offset + Zlength run) (next :: tail))
          (0, 0)) =
         offset + Zlength (run ++ concat (next :: tail))).
      assert (Hrestpos : 0 < Zlength (next :: tail)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg tail). lia. }
      rewrite (IH (offset + Zlength run) Hrestpos).
      rewrite Zlength_app. lia.
Qed.

Lemma P082ComputedBlocks_length : forall a,
  Zlength (P082ComputedBlocks a) = Zlength (P082ComputeRuns a).
Proof.
  intro a. unfold P082ComputedBlocks. apply P082BlocksFromRuns_length.
Qed.

Lemma P082ConstantRun_Znth : forall run x q,
  run <> nil ->
  Forall (fun y => y = x) run ->
  0 <= q < Zlength run ->
  Znth q run 0 = x.
Proof.
  intros run x q Hnonempty Hforall Hq.
  apply Forall_forall with (x := Znth q run 0) in Hforall.
  - exact Hforall.
  - apply Znth_In_Zlength. exact Hq.
Qed.

Lemma P082MaximalSameBlock_from_run : forall prefix run suffix x,
  run <> nil ->
  Forall (fun y => y = x) run ->
  (prefix = nil \/
    (0 < Zlength prefix /\ Znth (Zlength prefix - 1) prefix 0 <> x)) ->
  (suffix = nil \/ Znth 0 suffix 0 <> x) ->
  P082MaximalSameBlock (prefix ++ run ++ suffix)
    (Zlength prefix) (Zlength prefix + Zlength run) (Zlength prefix).
Proof.
  intros prefix run suffix x Hnonempty Hconstant Hleft Hright.
  assert (Hrunpos : 0 < Zlength run).
  { destruct run; [contradiction|]. rewrite Zlength_cons.
    pose proof (Zlength_nonneg run). lia. }
  assert (Hanchor :
    Znth (Zlength prefix) (prefix ++ run ++ suffix) 0 = x).
  { rewrite app_Znth2 by lia.
    replace (Zlength prefix - Zlength prefix) with 0 by lia.
    rewrite app_Znth1 by lia.
    apply P082ConstantRun_Znth; try assumption. lia. }
  unfold P082MaximalSameBlock.
  repeat rewrite Zlength_app.
  pose proof (Zlength_nonneg prefix).
  pose proof (Zlength_nonneg suffix).
  split; [lia|]. split; [lia|]. split.
  - intros q Hq.
    rewrite Hanchor.
    rewrite app_Znth2 by lia.
    rewrite app_Znth1 by lia.
    apply P082ConstantRun_Znth; try assumption. lia.
  - split.
    + destruct Hleft as [Hnil|Hdifferent].
      * left. subst prefix. reflexivity.
      * destruct Hdifferent as [Hprefixpos Hdifferent].
        right. rewrite Hanchor.
        rewrite app_Znth1 by
          lia.
        exact Hdifferent.
    + destruct Hright as [Hnil|Hdifferent].
      * left. subst suffix. unfold Zlength. simpl. lia.
      * right. rewrite Hanchor.
        rewrite app_Znth2 by lia.
        rewrite app_Znth2 by lia.
        replace
          (Zlength prefix + Zlength run - Zlength prefix - Zlength run)
          with 0 by lia.
        exact Hdifferent.
Qed.

Definition P082RunDecomposition
    (a : list Z) (runs : list (list Z)) : Prop :=
  concat runs = a /\
  (forall run, In run runs -> P082ConstantRun run) /\
  P082SeparatedRuns runs.

Lemma P082ComputeRuns_decomposition : forall a,
  P082RunDecomposition a (P082ComputeRuns a).
Proof.
  intro a. unfold P082RunDecomposition.
  split; [apply P082ComputeRuns_concat|]. split.
  - intros run Hin. apply P082ComputeRuns_constant with (a := a). exact Hin.
  - apply P082ComputeRuns_separated.
Qed.

Lemma P082BlocksFromRuns_endpoint_chain : forall offset runs,
  P082EndpointChain offset (offset + Zlength (concat runs))
    (P082BlocksFromRuns offset runs).
Proof.
  intros offset runs. revert offset.
  induction runs as [|run rest IH]; intros offset.
  - simpl. replace (offset + Zlength (@nil Z)) with offset.
    + constructor.
    + unfold Zlength. simpl. lia.
  - simpl P082BlocksFromRuns. apply P082EndpointChain_cons.
    change (P082EndpointChain (offset + Zlength run)
      (offset + Zlength (run ++ concat rest))
      (P082BlocksFromRuns (offset + Zlength run) rest)).
    replace (offset + Zlength (run ++ concat rest))
      with ((offset + Zlength run) + Zlength (concat rest)).
    + apply IH.
    + rewrite Zlength_app. lia.
Qed.

Lemma P082ComputedBlocks_endpoint_chain : forall a,
  P082EndpointChain 0 (Zlength a) (P082ComputedBlocks a).
Proof.
  intro a. unfold P082ComputedBlocks.
  pose proof (P082BlocksFromRuns_endpoint_chain 0 (P082ComputeRuns a))
    as Hchain.
  rewrite P082ComputeRuns_concat in Hchain. replace (0 + Zlength a)
    with (Zlength a) in Hchain by lia. exact Hchain.
Qed.

Lemma P082ComputeRuns_nonempty_iff : forall a,
  P082ComputeRuns a = nil <-> a = nil.
Proof.
  intro a. split; intro H.
  - pose proof (P082ComputeRuns_concat a).
    rewrite H in H0. simpl in H0. symmetry. exact H0.
  - subst a. reflexivity.
Qed.

Lemma P082ComputedBlocks_nonempty : forall a,
  0 < Zlength a -> 0 < Zlength (P082ComputedBlocks a).
Proof.
  intros a Ha.
  rewrite P082ComputedBlocks_length.
  destruct (P082ComputeRuns a) as [|run rest] eqn:Hruns.
  - apply P082ComputeRuns_nonempty_iff in Hruns. subst a.
    change (0 < 0) in Ha. lia.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia.
Qed.

Lemma P082BlocksFromRuns_Znth_context : forall runs offset t,
  0 <= t < Zlength runs ->
  exists before run after,
    runs = before ++ run :: after /\
    t = Zlength before /\
    Znth t (P082BlocksFromRuns offset runs) (0, 0) =
      (offset + Zlength (concat before),
       offset + Zlength (concat before) + Zlength run).
Proof.
  induction runs as [|first rest IH]; intros offset t Ht.
  - change (0 <= t < 0) in Ht. lia.
  - destruct (Z.eq_dec t 0) as [Htzero|Htnonzero].
    + subst t. exists nil, first, rest. split; [reflexivity|]. split.
      * unfold Zlength. simpl. reflexivity.
      * simpl. unfold Zlength. simpl. rewrite Znth0_cons. simpl.
        f_equal; lia.
    + assert (Htpos : 0 < t) by lia.
      assert (Htail : 0 <= t - 1 < Zlength rest).
      { rewrite Zlength_cons in Ht. lia. }
      destruct (IH (offset + Zlength first) (t - 1) Htail)
        as [before [run [after [Hrest [Hindex Hblock]]]]].
      exists (first :: before), run, after.
      split.
      * simpl. rewrite Hrest. reflexivity.
      * split.
        -- rewrite Zlength_cons. lia.
        -- change (Znth t
             ((offset, offset + Zlength first) ::
              P082BlocksFromRuns (offset + Zlength first) rest) (0, 0) =
             (offset + Zlength (concat (first :: before)),
              offset + Zlength (concat (first :: before)) + Zlength run)).
           rewrite Znth_cons by lia.
           rewrite Hblock. simpl concat. rewrite Zlength_app.
           f_equal; lia.
Qed.

Lemma P082BlocksFromRuns_positive : forall runs offset,
  (forall run, In run runs -> run <> nil) ->
  forall t, 0 <= t < Zlength (P082BlocksFromRuns offset runs) ->
    fst (Znth t (P082BlocksFromRuns offset runs) (0, 0)) <
    snd (Znth t (P082BlocksFromRuns offset runs) (0, 0)).
Proof.
  intros runs offset Hnonempty t Ht.
  rewrite P082BlocksFromRuns_length in Ht.
  destruct (P082BlocksFromRuns_Znth_context runs offset t Ht)
    as [before [run [after [Hruns [Hindex Hblock]]]]].
  rewrite Hblock. simpl.
  assert (Hin : In run runs).
  { rewrite Hruns. apply in_or_app. right. simpl. auto. }
  specialize (Hnonempty run Hin).
  destruct run; [contradiction|]. rewrite Zlength_cons.
  pose proof (Zlength_nonneg run). lia.
Qed.

Lemma P082EndpointChain_endpoints_ordered : forall lo hi blocks,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  lo <= hi.
Proof.
  intros lo hi blocks Hchain. induction Hchain; intros Hpositive.
  - lia.
  - assert (Hfirst : lo < mid).
    { specialize (Hpositive 0).
      simpl in Hpositive.
      pose proof (Zlength_nonneg rest).
      apply Hpositive. rewrite Zlength_cons. lia. }
    assert (Htail : mid <= hi).
    { apply IHHchain. intros t Ht.
      specialize (Hpositive (t + 1)).
      rewrite Znth_cons in Hpositive by lia.
      replace (t + 1 - 1) with t in Hpositive by lia.
      apply Hpositive. rewrite Zlength_cons. lia. }
    lia.
Qed.

Lemma P082EndpointChain_block_bounds : forall lo hi blocks,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  forall t, 0 <= t < Zlength blocks ->
    lo <= fst (Znth t blocks (0, 0)) /\
    snd (Znth t blocks (0, 0)) <= hi.
Proof.
  intros lo hi blocks Hchain. induction Hchain;
    intros Hpositive t Ht.
  - change (0 <= t < 0) in Ht. lia.
  - destruct (Z.eq_dec t 0) as [Htzero|Htnonzero].
    + subst t. simpl.
      assert (Hfirst : lo < mid).
      { specialize (Hpositive 0). simpl in Hpositive.
        pose proof (Zlength_nonneg rest).
        apply Hpositive. rewrite Zlength_cons. lia. }
      assert (Htail : mid <= hi).
      { apply (P082EndpointChain_endpoints_ordered mid hi rest Hchain).
        intros u Hu. specialize (Hpositive (u + 1)).
        rewrite Znth_cons in Hpositive by lia.
        replace (u + 1 - 1) with u in Hpositive by lia.
        apply Hpositive. rewrite Zlength_cons. lia. }
      split; lia.
    + assert (Htpos : 0 < t) by lia.
      assert (Htail : 0 <= t - 1 < Zlength rest).
      { rewrite Zlength_cons in Ht. lia. }
      assert (Hpositive_tail : forall u, 0 <= u < Zlength rest ->
        fst (Znth u rest (0, 0)) < snd (Znth u rest (0, 0))).
      { intros u Hu.
        pose proof (Hpositive (u + 1)
          ltac:(rewrite Zlength_cons; lia)) as Hp.
        rewrite Znth_cons in Hp by lia.
        replace (u + 1 - 1) with u in Hp by lia. exact Hp. }
      specialize (IHHchain Hpositive_tail (t - 1) Htail).
      assert (Hfirst : lo < mid).
      { specialize (Hpositive 0). simpl in Hpositive.
        pose proof (Zlength_nonneg rest).
        apply Hpositive. rewrite Zlength_cons. lia. }
      rewrite Znth_cons by lia.
      destruct IHHchain as [Hlower Hupper]. split; [lia|exact Hupper].
Qed.

Lemma P082EndpointChain_ordered : forall lo hi blocks,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  forall t u, 0 <= t < u -> u < Zlength blocks ->
    snd (Znth t blocks (0, 0)) <= fst (Znth u blocks (0, 0)).
Proof.
  intros lo hi blocks Hchain. induction Hchain;
    intros Hpositive t u Htu Hu.
  - change (u < 0) in Hu. lia.
  - assert (Hpositive_tail : forall v, 0 <= v < Zlength rest ->
      fst (Znth v rest (0, 0)) < snd (Znth v rest (0, 0))).
    { intros v Hv.
      pose proof (Hpositive (v + 1)
        ltac:(rewrite Zlength_cons; lia)) as Hp.
      rewrite Znth_cons in Hp by lia.
      replace (v + 1 - 1) with v in Hp by lia. exact Hp. }
    destruct (Z.eq_dec t 0) as [Htzero|Htnonzero].
    + subst t. simpl.
      assert (Hub : 0 <= u - 1 < Zlength rest).
      { rewrite Zlength_cons in Hu. lia. }
      pose proof (P082EndpointChain_block_bounds mid hi rest Hchain
        Hpositive_tail (u - 1) Hub) as [Hlo _].
      rewrite Znth_cons by lia. exact Hlo.
    + assert (Htpos : 0 < t) by lia.
      specialize (IHHchain Hpositive_tail
        (t - 1) (u - 1) ltac:(lia)
        ltac:(rewrite Zlength_cons in Hu; lia)).
      repeat rewrite Znth_cons by lia. exact IHHchain.
Qed.

Lemma P082EndpointChain_position_exists : forall lo hi blocks q,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  lo <= q < hi ->
  exists t, 0 <= t < Zlength blocks /\
    fst (Znth t blocks (0, 0)) <= q <
    snd (Znth t blocks (0, 0)).
Proof.
  intros lo hi blocks q Hchain. induction Hchain;
    intros Hpositive Hq.
  - lia.
  - assert (Hpositive_tail : forall v, 0 <= v < Zlength rest ->
      fst (Znth v rest (0, 0)) < snd (Znth v rest (0, 0))).
    { intros v Hv.
      pose proof (Hpositive (v + 1)
        ltac:(rewrite Zlength_cons; lia)) as Hp.
      rewrite Znth_cons in Hp by lia.
      replace (v + 1 - 1) with v in Hp by lia. exact Hp. }
    destruct (Z_lt_ge_dec q mid) as [Hbefore|Hafter].
    + exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia.
      * simpl. lia.
    + destruct (IHHchain Hpositive_tail ltac:(lia))
        as [t [Ht Hcontains]].
      exists (t + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia.
        replace (t + 1 - 1) with t by lia. exact Hcontains.
Qed.

Lemma P082List_unsnoc : forall (A : Type) (xs : list A),
  xs <> nil -> exists prefix last, xs = prefix ++ last :: nil.
Proof.
  intros A xs. induction xs as [|x rest IH]; intro Hnonempty.
  - contradiction.
  - destruct rest as [|y tail].
    + exists nil, x. reflexivity.
    + destruct (IH ltac:(discriminate)) as [prefix [last Hrest]].
      exists (x :: prefix), last. simpl. rewrite Hrest. reflexivity.
Qed.

Lemma P082SeparatedRuns_app_two : forall prefix left right suffix,
  P082SeparatedRuns (prefix ++ left :: right :: suffix) ->
  hd 0 left <> hd 0 right.
Proof.
  induction prefix as [|first rest IH]; intros left right suffix Hsep.
  - simpl in Hsep. tauto.
  - simpl in Hsep. destruct rest as [|second tail].
    + simpl in Hsep. tauto.
    + apply (IH left right suffix). simpl in Hsep. tauto.
Qed.

Lemma P082ConstantRun_head : forall run x,
  run <> nil -> Forall (fun y => y = x) run -> hd 0 run = x.
Proof.
  intros run x Hnonempty Hconstant.
  destruct run as [|first rest]; [contradiction|].
  inversion Hconstant. simpl. assumption.
Qed.

Lemma P082ConstantRun_last : forall run x,
  run <> nil -> Forall (fun y => y = x) run ->
  Znth (Zlength run - 1) run 0 = x.
Proof.
  intros run x Hnonempty Hconstant.
  apply P082ConstantRun_Znth; try assumption.
  destruct run; [contradiction|]. rewrite Zlength_cons.
  pose proof (Zlength_nonneg run). lia.
Qed.

Lemma P082RunDecomposition_blocks_maximal : forall a runs offset t,
  P082RunDecomposition a runs ->
  0 <= t < Zlength runs ->
  let block := Znth t (P082BlocksFromRuns offset runs) (0, 0) in
  exists anchor,
    P082MaximalSameBlock a
      (fst block - offset) (snd block - offset) anchor.
Proof.
  intros a runs offset t [Hconcat [Hconstant Hseparated]] Ht.
  destruct (P082BlocksFromRuns_Znth_context runs offset t Ht)
    as [before [run [after [Hruns [Hindex Hblock]]]]].
  assert (Hinrun : In run runs).
  { rewrite Hruns. apply in_or_app. right. simpl. auto. }
  destruct (Hconstant run Hinrun) as [x [Hrun_nonempty Hrun_constant]].
  assert (Hrun_head : hd 0 run = x) by
    (apply P082ConstantRun_head; assumption).
  assert (Hleft :
    concat before = nil \/
    (0 < Zlength (concat before) /\
     Znth (Zlength (concat before) - 1) (concat before) 0 <> x)).
  { destruct before as [|first rest].
    - left. reflexivity.
    - right.
      assert (Hbefore_nonempty : first :: rest <> nil) by discriminate.
      destruct (P082List_unsnoc (list Z) (first :: rest) Hbefore_nonempty)
        as [prefix [previous Hbefore]].
      assert (Hinprevious : In previous runs).
      { rewrite Hruns, Hbefore. apply in_or_app. left.
        apply in_or_app. right. simpl. auto. }
      destruct (Hconstant previous Hinprevious)
        as [previous_value [Hprevious_nonempty Hprevious_constant]].
      assert (Hdifferent : hd 0 previous <> hd 0 run).
      { rewrite Hruns in Hseparated. rewrite Hbefore in Hseparated.
        replace ((prefix ++ previous :: nil) ++ run :: after)
          with (prefix ++ previous :: run :: after) in Hseparated.
        2: { rewrite <- app_assoc. reflexivity. }
        apply (P082SeparatedRuns_app_two prefix previous run after).
        exact Hseparated. }
      split.
      + rewrite Hbefore. rewrite concat_app. simpl. rewrite app_nil_r.
        rewrite Zlength_app.
        assert (0 < Zlength previous).
        { destruct previous; [contradiction|]. rewrite Zlength_cons.
          pose proof (Zlength_nonneg previous). lia. }
        pose proof (Zlength_nonneg (concat prefix)). lia.
      + rewrite Hbefore. rewrite concat_app. simpl. rewrite app_nil_r.
        rewrite Zlength_app.
        rewrite app_Znth2 by
          (assert (0 < Zlength previous) by
             (destruct previous; [contradiction|]; rewrite Zlength_cons;
              pose proof (Zlength_nonneg previous); lia);
           pose proof (Zlength_nonneg (concat prefix)); lia).
        replace
          (Zlength (concat prefix) + Zlength previous - 1 -
           Zlength (concat prefix))
          with (Zlength previous - 1) by lia.
        rewrite (P082ConstantRun_last previous previous_value
          Hprevious_nonempty Hprevious_constant).
        intro Heq. apply Hdifferent.
        rewrite (P082ConstantRun_head previous previous_value
          Hprevious_nonempty Hprevious_constant), Hrun_head.
        exact Heq. }
  assert (Hright :
    concat after = nil \/ Znth 0 (concat after) 0 <> x).
  { destruct after as [|next tail].
    - left. reflexivity.
    - right.
      assert (Hinnext : In next runs).
      { rewrite Hruns. apply in_or_app. right. simpl. auto. }
      destruct (Hconstant next Hinnext)
        as [next_value [Hnext_nonempty Hnext_constant]].
      assert (Hdifferent : hd 0 run <> hd 0 next).
      { rewrite Hruns in Hseparated.
        apply (P082SeparatedRuns_app_two before run next tail).
        exact Hseparated. }
      simpl concat. rewrite app_Znth1 by
        (destruct next; [contradiction|]; rewrite Zlength_cons;
         pose proof (Zlength_nonneg next); lia).
      replace (Znth 0 next 0) with (hd 0 next).
      2: { destruct next; [contradiction|]. reflexivity. }
      intro Heq. apply Hdifferent. rewrite Hrun_head. symmetry. exact Heq. }
  rewrite Hruns in Hconcat. simpl concat in Hconcat.
  rewrite Hblock. simpl.
  replace
    (offset + Zlength (concat before) - offset)
    with (Zlength (concat before)) by lia.
  replace
    (offset + Zlength (concat before) + Zlength run - offset)
    with (Zlength (concat before) + Zlength run) by lia.
  exists (Zlength (concat before)).
  rewrite <- Hconcat.
  rewrite concat_app. simpl.
  apply P082MaximalSameBlock_from_run with (x := x); assumption.
Qed.

Lemma P082RunDecomposition_ordered_cover : forall a runs,
  P082RunDecomposition a runs ->
  P082OrderedBlockCover a (P082BlocksFromRuns 0 runs).
Proof.
  intros a runs Hdecomposition.
  destruct Hdecomposition as [Hconcat [Hconstant Hseparated]].
  assert (Hdecomposition : P082RunDecomposition a runs).
  { repeat split; assumption. }
  assert (Hnonempty : forall run, In run runs -> run <> nil).
  { intros run Hin. destruct (Hconstant run Hin) as [x [Hrun _]].
    exact Hrun. }
  assert (Hpositive : forall t,
    0 <= t < Zlength (P082BlocksFromRuns 0 runs) ->
    fst (Znth t (P082BlocksFromRuns 0 runs) (0, 0)) <
    snd (Znth t (P082BlocksFromRuns 0 runs) (0, 0))).
  { apply P082BlocksFromRuns_positive. exact Hnonempty. }
  pose proof (P082BlocksFromRuns_endpoint_chain 0 runs) as Hchain.
  unfold P082OrderedBlockCover. split.
  - intros t Ht.
    pose proof (P082RunDecomposition_blocks_maximal
      a runs 0 t Hdecomposition) as Hmaximal.
    rewrite P082BlocksFromRuns_length in Ht.
    specialize (Hmaximal Ht).
    remember (Znth t (P082BlocksFromRuns 0 runs) (0, 0)) as block.
    destruct block as [lo hi]. simpl in Hmaximal |- *.
    destruct Hmaximal as [anchor Hmaximal]. exists anchor.
    replace (lo - 0) with lo in Hmaximal by lia.
    replace (hi - 0) with hi in Hmaximal by lia.
    exact Hmaximal.
  - split.
    + apply (P082EndpointChain_ordered 0
        (0 + Zlength (concat runs))
        (P082BlocksFromRuns 0 runs) Hchain Hpositive).
    + intros q Hq.
      apply (P082EndpointChain_position_exists 0
        (0 + Zlength (concat runs))
        (P082BlocksFromRuns 0 runs) q Hchain Hpositive).
      rewrite Hconcat. lia.
Qed.

Lemma P082ComputedBlocks_ordered_cover : forall a,
  P082OrderedBlockCover a (P082ComputedBlocks a).
Proof.
  intro a. unfold P082ComputedBlocks.
  apply P082RunDecomposition_ordered_cover.
  apply P082ComputeRuns_decomposition.
Qed.

Lemma P082ComputedBlocks_lengths_CanonicalProfile : forall a k,
  k <= Zlength (P082ComputedBlocks a) ->
  (forall t,
    1 <= t < Zlength
      (P082OrderedBlockLengths (P082ComputedBlocks a)) - 1 ->
    Znth t (P082OrderedBlockLengths (P082ComputedBlocks a)) 0 <> 2) ->
  P082CanonicalProfile (Zlength a) k
    (P082OrderedBlockLengths (P082ComputedBlocks a)).
Proof.
  intros a k Hk Hno2.
  apply P082OrderedBlockCover_lengths_CanonicalProfile.
  - apply P082ComputedBlocks_ordered_cover.
  - apply P082ComputedBlocks_endpoint_chain.
  - exact Hk.
  - exact Hno2.
Qed.

Definition P082RunHeads (runs : list (list Z)) : list Z :=
  map (hd 0) runs.

Lemma P082RunDecomposition_value_in_heads : forall a runs x,
  P082RunDecomposition a runs ->
  In x a -> In x (P082RunHeads runs).
Proof.
  intros a runs x [Hconcat [Hconstant _]] Hin.
  rewrite <- Hconcat in Hin.
  apply in_concat in Hin.
  destruct Hin as [run [Hinrun Hinx]].
  destruct (Hconstant run Hinrun) as [value [Hnonempty Hforall]].
  unfold P082RunHeads. apply in_map_iff. exists run. split.
  - assert (Hhead : hd 0 run = value).
    { apply P082ConstantRun_head; assumption. }
    assert (Hx : x = value).
    { apply Forall_forall with (x := x) in Hforall; assumption. }
    lia.
  - exact Hinrun.
Qed.

Lemma P082UsesEveryValue_run_count : forall k a runs,
  0 <= k ->
  UsesEveryValue k a ->
  P082RunDecomposition a runs ->
  k <= Zlength runs.
Proof.
  intros k a runs Hk Huses Hdecomposition.
  assert (Hincl : incl (seq 1 (Z.to_nat k))
    (map Z.to_nat (P082RunHeads runs))).
  { intros index Hindex.
    apply in_seq in Hindex.
    apply in_map_iff.
    exists (Z.of_nat index). split.
    - rewrite Nat2Z.id. reflexivity.
    - apply P082RunDecomposition_value_in_heads with (a := a).
      + exact Hdecomposition.
      + destruct Huses as [_ Hvalues]. apply Hvalues.
        split.
        * change (Z.of_nat 1 <= Z.of_nat index).
          apply Nat2Z.inj_le. lia.
        * rewrite <- Z2Nat.id by exact Hk.
          apply Nat2Z.inj_le. lia. }
  pose proof (NoDup_incl_length (seq_NoDup (Z.to_nat k) 1) Hincl)
    as Hlength.
  rewrite length_seq, length_map in Hlength.
  apply Nat2Z.inj_le in Hlength.
  rewrite Z2Nat.id in Hlength by exact Hk.
  unfold P082RunHeads in Hlength. rewrite length_map in Hlength.
  rewrite Zlength_correct. exact Hlength.
Qed.

Lemma P082UsesEveryValue_computed_blocks_count : forall k a,
  0 <= k -> UsesEveryValue k a ->
  k <= Zlength (P082ComputedBlocks a).
Proof.
  intros k a Hk Huses. unfold P082ComputedBlocks.
  rewrite P082BlocksFromRuns_length.
  apply P082UsesEveryValue_run_count with (a := a); try assumption.
  apply P082ComputeRuns_decomposition.
Qed.

Fixpoint P082NormalizeProfileTail (parts : list Z) : list Z :=
  match parts with
  | nil => nil
  | x :: nil => x :: nil
  | x :: ((y :: rest) as tail) =>
      if Z.eq_dec x 2
      then 1 :: 1 :: P082NormalizeProfileTail tail
      else x :: P082NormalizeProfileTail tail
  end.

Definition P082NormalizeProfile (parts : list Z) : list Z :=
  match parts with
  | nil => nil
  | first :: rest => first :: P082NormalizeProfileTail rest
  end.

Lemma P082NormalizeProfileTail_cons_nonfinal : forall x y rest,
  P082NormalizeProfileTail (x :: y :: rest) =
    if Z.eq_dec x 2
    then 1 :: 1 :: P082NormalizeProfileTail (y :: rest)
    else x :: P082NormalizeProfileTail (y :: rest).
Proof. reflexivity. Qed.

Lemma P082NormalizeProfileTail_sum : forall parts,
  fold_right Z.add 0 (P082NormalizeProfileTail parts) =
  fold_right Z.add 0 parts.
Proof.
  induction parts as [|x rest IH]; [reflexivity|].
  destruct rest as [|y tail]; [reflexivity|].
  remember (P082NormalizeProfileTail (y :: tail)) as normalized
    eqn:Hnormalized in *.
  rewrite P082NormalizeProfileTail_cons_nonfinal.
  rewrite <- Hnormalized.
  destruct (Z.eq_dec x 2) as [Heq|Hneq].
  - change (1 + (1 + fold_right Z.add 0 normalized) =
      x + fold_right Z.add 0 (y :: tail)).
    rewrite IH. subst x. ring.
  - change (x + fold_right Z.add 0 normalized =
      x + fold_right Z.add 0 (y :: tail)).
    rewrite IH. reflexivity.
Qed.

Lemma P082NormalizeProfile_sum : forall parts,
  fold_right Z.add 0 (P082NormalizeProfile parts) =
  fold_right Z.add 0 parts.
Proof.
  intros [|first rest]; [reflexivity|].
  simpl. rewrite P082NormalizeProfileTail_sum. reflexivity.
Qed.

Lemma P082NormalizeProfileTail_length : forall parts,
  Zlength parts <= Zlength (P082NormalizeProfileTail parts).
Proof.
  induction parts as [|x rest IH]; [reflexivity|].
  destruct rest as [|y tail].
  - reflexivity.
  - remember (P082NormalizeProfileTail (y :: tail)) as normalized
      eqn:Hnormalized in *.
    rewrite P082NormalizeProfileTail_cons_nonfinal, <- Hnormalized.
    destruct (Z.eq_dec x 2).
    + rewrite !Zlength_cons. rewrite Zlength_cons in IH. lia.
    + rewrite !Zlength_cons. rewrite Zlength_cons in IH. lia.
Qed.

Lemma P082NormalizeProfile_length : forall parts,
  Zlength parts <= Zlength (P082NormalizeProfile parts).
Proof.
  intros [|first rest]; [reflexivity|].
  change (Zlength (first :: rest) <=
    Zlength (first :: P082NormalizeProfileTail rest)).
  rewrite !Zlength_cons.
  pose proof (P082NormalizeProfileTail_length rest). lia.
Qed.

Lemma P082NormalizeProfileTail_bounds : forall n parts,
  1 <= n ->
  Forall (fun x => 1 <= x <= n) parts ->
  Forall (fun x => 1 <= x <= n) (P082NormalizeProfileTail parts).
Proof.
  intros n parts Hn Hbounds. induction Hbounds as [|x rest Hx Hrest IH].
  - constructor.
  - destruct rest as [|y tail].
    + change (Forall (fun z => 1 <= z <= n) (x :: nil)).
      constructor; [exact Hx|constructor].
    + rewrite P082NormalizeProfileTail_cons_nonfinal.
      destruct (Z.eq_dec x 2).
      * constructor; [lia|]. constructor; [lia|]. exact IH.
      * constructor; assumption.
Qed.

Lemma P082NormalizeProfile_bounds : forall n parts,
  1 <= n ->
  Forall (fun x => 1 <= x <= n) parts ->
  Forall (fun x => 1 <= x <= n) (P082NormalizeProfile parts).
Proof.
  intros n [|first rest] Hn Hbounds; [constructor|].
  inversion Hbounds as [|? ? Hfirst Hrest]. subst.
  simpl. constructor; [exact Hfirst|].
  apply P082NormalizeProfileTail_bounds; assumption.
Qed.

Lemma P082NormalizeProfileTail_no_two_before_last : forall parts t,
  0 <= t < Zlength (P082NormalizeProfileTail parts) - 1 ->
  Znth t (P082NormalizeProfileTail parts) 0 <> 2.
Proof.
  induction parts as [|x rest IH]; intros t Ht.
  - change (0 <= t < -1) in Ht. lia.
  - destruct rest as [|y tail].
    + change (0 <= t < 0) in Ht. lia.
    + remember (P082NormalizeProfileTail (y :: tail)) as normalized
        eqn:Hnormalized in *.
      rewrite P082NormalizeProfileTail_cons_nonfinal, <- Hnormalized
        in Ht |- *.
      destruct (Z.eq_dec x 2) as [Htwo|Hnot].
      * destruct (Z.eq_dec t 0) as [Htzero|Htnonzero].
        -- subst t. rewrite Znth0_cons. lia.
        -- destruct (Z.eq_dec t 1) as [Htone|Htnotone].
           ++ subst t. rewrite Znth_cons by lia.
              replace (1 - 1) with 0 by lia. rewrite Znth0_cons. lia.
           ++ repeat rewrite Znth_cons by lia.
              replace (t - 1 - 1) with (t - 2) by lia.
              assert (Hrecursive :
                0 <= t - 2 <
                Zlength normalized - 1).
              { change (0 <= t < Zlength
                  (1 :: 1 :: normalized) - 1)
                  in Ht.
                rewrite !Zlength_cons in Ht. lia. }
              exact (IH (t - 2) Hrecursive).
      * destruct (Z.eq_dec t 0) as [Htzero|Htnonzero].
        -- subst t. rewrite Znth0_cons. exact Hnot.
        -- rewrite Znth_cons by lia.
           assert (Hrecursive :
             0 <= t - 1 <
             Zlength normalized - 1).
           { change (0 <= t < Zlength
               (x :: normalized) - 1) in Ht.
             rewrite Zlength_cons in Ht. lia. }
           exact (IH (t - 1) Hrecursive).
Qed.

Lemma P082NormalizeProfile_no_internal_two : forall parts t,
  1 <= t < Zlength (P082NormalizeProfile parts) - 1 ->
  Znth t (P082NormalizeProfile parts) 0 <> 2.
Proof.
  intros [|first rest] t Ht.
  - change (1 <= t < -1) in Ht. lia.
  - change (Znth t (first :: P082NormalizeProfileTail rest) 0 <> 2).
    rewrite Znth_cons by lia.
    apply P082NormalizeProfileTail_no_two_before_last.
    change (1 <= t <
      Zlength (first :: P082NormalizeProfileTail rest) - 1) in Ht.
    rewrite Zlength_cons in Ht. lia.
Qed.

Lemma P082NormalizeProfile_is_CanonicalProfile : forall n k parts,
  1 <= n ->
  fold_right Z.add 0 parts = n ->
  k <= Zlength parts ->
  Forall (fun x => 1 <= x <= n) parts ->
  P082CanonicalProfile n k (P082NormalizeProfile parts).
Proof.
  intros n k parts Hn Hsum Hk Hbounds.
  unfold P082CanonicalProfile. split.
  - rewrite P082NormalizeProfile_sum. exact Hsum.
  - split.
    + pose proof (P082NormalizeProfile_length parts). lia.
    + split.
      * apply P082NormalizeProfile_bounds; assumption.
      * apply P082NormalizeProfile_no_internal_two.
Qed.

Lemma P082UsesEveryValue_normalized_computed_profile : forall n k a,
  1 <= n ->
  Zlength a = n ->
  0 <= k ->
  UsesEveryValue k a ->
  P082CanonicalProfile n k
    (P082NormalizeProfile
      (P082OrderedBlockLengths (P082ComputedBlocks a))).
Proof.
  intros n k a Hn Hlength Hk Huses.
  apply P082NormalizeProfile_is_CanonicalProfile.
  - exact Hn.
  - pose proof (P082EndpointChain_lengths_sum 0 (Zlength a)
      (P082ComputedBlocks a) (P082ComputedBlocks_endpoint_chain a))
      as Hsum.
    rewrite Hlength in Hsum. lia.
  - rewrite P082OrderedBlockLengths_length.
    apply P082UsesEveryValue_computed_blocks_count; assumption.
  - rewrite <- Hlength. apply P082OrderedBlockLengths_bounds.
    apply P082ComputedBlocks_ordered_cover.
Qed.

Lemma P082DistanceArray_internal_block_formula : forall a b lo hi anchor q,
  DistanceArray a b ->
  P082MaximalSameBlock a lo hi anchor ->
  0 < lo -> hi < Zlength a ->
  lo <= q < hi ->
  Znth q b 0 = Z.min (q - lo + 1) (hi - q).
Proof.
  intros a b lo hi anchor q Hdistance Hblock Hlo Hhi Hq.
  destruct Hblock as
    [[Hlo0 Hloanchor]
     [[Hanchorhi Hhilength] [Hsame [Hleft Hright]]]].
  assert (Hqbound : 0 <= q < Zlength a) by lia.
  assert (Hqanchor : Znth q a 0 = Znth anchor a 0).
  { apply Hsame. exact Hq. }
  assert (Hleftdifferent :
    Znth (lo - 1) a 0 <> Znth q a 0).
  { destruct Hleft as [Hzero|Hdifferent]; [lia|].
    rewrite Hqanchor. exact Hdifferent. }
  assert (Hrightdifferent : Znth hi a 0 <> Znth q a 0).
  { destruct Hright as [Hend|Hdifferent]; [lia|].
    rewrite Hqanchor. exact Hdifferent. }
  destruct (P082DistanceArray_nearest_different_witness
    a b q Hdistance Hqbound)
    as [j [Hj [Hjdifferent [Hvalue Hminimal]]]].
  assert (Hupperleft : Znth q b 0 <= q - lo + 1).
  { rewrite Hvalue.
    pose proof (Hminimal (lo - 1) ltac:(lia) Hleftdifferent)
      as Hminimumleft.
    replace (Z.abs (q - (lo - 1))) with (q - lo + 1)
      in Hminimumleft by (rewrite Z.abs_eq by lia; lia).
    exact Hminimumleft. }
  assert (Hupperright : Znth q b 0 <= hi - q).
  { rewrite Hvalue.
    pose proof (Hminimal hi ltac:(lia) Hrightdifferent)
      as Hminimumright.
    replace (Z.abs (q - hi)) with (hi - q)
      in Hminimumright by (rewrite Z.abs_neq by lia; lia).
    exact Hminimumright. }
  assert (Houtside : j < lo \/ hi <= j).
  { destruct (Z_lt_ge_dec j lo) as [Hjleft|Hjnotleft].
    - left. exact Hjleft.
    - right. destruct (Z_lt_ge_dec j hi) as [Hjinside|Hjright].
      + exfalso. apply Hjdifferent.
        rewrite Hqanchor. apply Hsame. lia.
      + lia. }
  destruct (Z_le_dec (q - lo + 1) (hi - q)) as [Hminleft|Hminright].
  - rewrite Z.min_l by exact Hminleft.
    destruct Houtside as [Hjleft|Hjright].
    + rewrite Hvalue, Z.abs_eq by lia. lia.
    + rewrite Hvalue, Z.abs_neq by lia. lia.
  - rewrite Z.min_r by lia.
    destruct Houtside as [Hjleft|Hjright].
    + rewrite Hvalue, Z.abs_eq by lia. lia.
    + rewrite Hvalue, Z.abs_neq by lia. lia.
Qed.

Lemma P082DistanceArray_internal_two_values : forall a b lo anchor,
  DistanceArray a b ->
  P082MaximalSameBlock a lo (lo + 2) anchor ->
  0 < lo -> lo + 2 < Zlength a ->
  Znth lo b 0 = 1 /\ Znth (lo + 1) b 0 = 1.
Proof.
  intros a b lo anchor Hdistance Hblock Hlo Hhi. split.
  - rewrite (P082DistanceArray_internal_block_formula
      a b lo (lo + 2) anchor lo Hdistance Hblock) by lia.
    rewrite Z.min_l by lia. lia.
  - rewrite (P082DistanceArray_internal_block_formula
      a b lo (lo + 2) anchor (lo + 1) Hdistance Hblock) by lia.
    rewrite Z.min_r by lia. lia.
Qed.

(* A concrete observation list determined only by a block-length profile.  The
   first and last blocks see their sole outer boundary; every internal block
   sees the nearer of its two boundaries. *)
Definition P082IncreasingObservation (len : Z) : list Z :=
  map (fun q : nat => Z.of_nat q + 1) (seq 0 (Z.to_nat len)).

Definition P082DecreasingObservation (len : Z) : list Z :=
  map (fun q : nat => len - Z.of_nat q) (seq 0 (Z.to_nat len)).

Definition P082InternalObservation (len : Z) : list Z :=
  map (fun q : nat =>
    Z.min (Z.of_nat q + 1) (len - Z.of_nat q))
    (seq 0 (Z.to_nat len)).

Fixpoint P082ProfileObservationTail (parts : list Z) : list Z :=
  match parts with
  | nil => nil
  | last :: nil => P082IncreasingObservation last
  | x :: ((_ :: _) as rest) =>
      P082InternalObservation x ++ P082ProfileObservationTail rest
  end.

Definition P082ProfileObservation (parts : list Z) : list Z :=
  match parts with
  | nil => nil
  | only :: nil => repeat 0 (Z.to_nat only)
  | first :: ((_ :: _) as rest) =>
      P082DecreasingObservation first ++ P082ProfileObservationTail rest
  end.

Lemma P082NormalizeProfileTail_nonempty : forall parts,
  parts <> nil -> P082NormalizeProfileTail parts <> nil.
Proof.
  intros [|x rest] Hparts; [contradiction|].
  destruct rest as [|y tail].
  - simpl. discriminate.
  - rewrite P082NormalizeProfileTail_cons_nonfinal.
    destruct (Z.eq_dec x 2); discriminate.
Qed.

Lemma P082InternalObservation_one :
  P082InternalObservation 1 = 1 :: nil.
Proof. reflexivity. Qed.

Lemma P082InternalObservation_two :
  P082InternalObservation 2 = 1 :: 1 :: nil.
Proof. reflexivity. Qed.

Lemma P082ProfileObservationTail_normalize : forall parts,
  P082ProfileObservationTail (P082NormalizeProfileTail parts) =
  P082ProfileObservationTail parts.
Proof.
  induction parts as [|x rest IH]; [reflexivity|].
  destruct rest as [|y tail]; [reflexivity|].
  rewrite P082NormalizeProfileTail_cons_nonfinal.
  remember (P082NormalizeProfileTail (y :: tail)) as normalized
    eqn:Hnormalized.
  assert (Hnonempty : normalized <> nil).
  { rewrite Hnormalized. apply P082NormalizeProfileTail_nonempty.
    discriminate. }
  destruct normalized as [|z zs]; [contradiction|].
  destruct (Z.eq_dec x 2) as [Htwo|Hnot].
  - subst x.
    change (P082InternalObservation 1 ++
      P082InternalObservation 1 ++ P082ProfileObservationTail (z :: zs) =
      P082InternalObservation 2 ++
      P082ProfileObservationTail (y :: tail)).
    rewrite P082InternalObservation_one,
      P082InternalObservation_two.
    change (1 :: 1 :: P082ProfileObservationTail (z :: zs) =
      1 :: 1 :: P082ProfileObservationTail (y :: tail)).
    rewrite IH. reflexivity.
  - change (P082InternalObservation x ++
      P082ProfileObservationTail (z :: zs) =
      P082InternalObservation x ++
      P082ProfileObservationTail (y :: tail)).
    rewrite IH. reflexivity.
Qed.

Lemma P082ProfileObservation_normalize : forall parts,
  P082ProfileObservation (P082NormalizeProfile parts) =
  P082ProfileObservation parts.
Proof.
  intros [|first rest]; [reflexivity|].
  destruct rest as [|second tail]; [reflexivity|].
  unfold P082NormalizeProfile, P082ProfileObservation.
  remember (P082NormalizeProfileTail (second :: tail)) as normalized
    eqn:Hnormalized.
  assert (Hnonempty : normalized <> nil).
  { rewrite Hnormalized. apply P082NormalizeProfileTail_nonempty.
    discriminate. }
  destruct normalized as [|z zs]; [contradiction|].
  change (P082DecreasingObservation first ++
    P082ProfileObservationTail (z :: zs) =
    P082DecreasingObservation first ++
    P082ProfileObservationTail (second :: tail)).
  rewrite Hnormalized.
  rewrite P082ProfileObservationTail_normalize. reflexivity.
Qed.

Lemma P082IncreasingObservation_length : forall len,
  0 <= len -> Zlength (P082IncreasingObservation len) = len.
Proof.
  intros len Hlen. unfold P082IncreasingObservation.
  rewrite Zlength_correct, length_map, length_seq, Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma P082DecreasingObservation_length : forall len,
  0 <= len -> Zlength (P082DecreasingObservation len) = len.
Proof.
  intros len Hlen. unfold P082DecreasingObservation.
  rewrite Zlength_correct, length_map, length_seq, Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma P082InternalObservation_length : forall len,
  0 <= len -> Zlength (P082InternalObservation len) = len.
Proof.
  intros len Hlen. unfold P082InternalObservation.
  rewrite Zlength_correct, length_map, length_seq, Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma P082ProfileObservationTail_length : forall parts,
  Forall (fun x => 0 <= x) parts ->
  Zlength (P082ProfileObservationTail parts) =
  fold_right Z.add 0 parts.
Proof.
  intros parts Hparts. induction Hparts as [|x rest Hx Hrest IH].
  - reflexivity.
  - destruct rest as [|y tail].
    + simpl. rewrite P082IncreasingObservation_length by exact Hx. lia.
    + change (Zlength
        (P082InternalObservation x ++
         P082ProfileObservationTail (y :: tail)) =
        x + fold_right Z.add 0 (y :: tail)).
      rewrite Zlength_app, P082InternalObservation_length by exact Hx.
      rewrite IH. reflexivity.
Qed.

Lemma P082ProfileObservation_length : forall parts,
  Forall (fun x => 0 <= x) parts ->
  Zlength (P082ProfileObservation parts) =
  fold_right Z.add 0 parts.
Proof.
  intros parts Hparts. inversion Hparts as [|first rest Hfirst Hrest].
  - reflexivity.
  - subst. destruct rest as [|second tail].
    + simpl. rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
      lia.
    + change (Zlength
        (P082DecreasingObservation first ++
         P082ProfileObservationTail (second :: tail)) =
        first + fold_right Z.add 0 (second :: tail)).
      rewrite Zlength_app, P082DecreasingObservation_length
        by exact Hfirst.
      apply P082ProfileObservationTail_length in Hrest.
      rewrite Hrest. reflexivity.
Qed.

Definition P082ProfileLabel (k block_index : Z) : Z :=
  1 + block_index mod k.

Fixpoint P082RealizeProfileFrom
    (k block_index : Z) (parts : list Z) : list Z :=
  match parts with
  | nil => nil
  | len :: rest =>
      repeat (P082ProfileLabel k block_index) (Z.to_nat len) ++
      P082RealizeProfileFrom k (block_index + 1) rest
  end.

Definition P082RealizeProfile (k : Z) (parts : list Z) : list Z :=
  P082RealizeProfileFrom k 0 parts.

Lemma P082RealizeProfileFrom_length : forall k block_index parts,
  Forall (fun x => 0 <= x) parts ->
  Zlength (P082RealizeProfileFrom k block_index parts) =
  fold_right Z.add 0 parts.
Proof.
  intros k block_index parts Hparts. revert block_index.
  induction Hparts as [|len rest Hlen Hrest IH]; intro block_index.
  - reflexivity.
  - simpl. rewrite Zlength_app, Zlength_correct, repeat_length,
      Z2Nat.id by lia.
    rewrite IH. reflexivity.
Qed.

Lemma P082RealizeProfile_length : forall k parts,
  Forall (fun x => 0 <= x) parts ->
  Zlength (P082RealizeProfile k parts) =
  fold_right Z.add 0 parts.
Proof.
  intros k parts Hparts. unfold P082RealizeProfile.
  apply P082RealizeProfileFrom_length. exact Hparts.
Qed.

Lemma P082ProfileLabel_bounds : forall k block_index,
  1 <= k -> 1 <= P082ProfileLabel k block_index <= k.
Proof.
  intros k block_index Hk. unfold P082ProfileLabel.
  pose proof (Z.mod_pos_bound block_index k ltac:(lia)). lia.
Qed.

Lemma P082RealizeProfileFrom_bounds : forall k block_index parts,
  1 <= k ->
  Forall (fun x => 1 <= x) parts ->
  Forall (fun value => 1 <= value <= k)
    (P082RealizeProfileFrom k block_index parts).
Proof.
  intros k block_index parts Hk Hparts. revert block_index.
  induction Hparts as [|len rest Hlen Hrest IH]; intro block_index.
  - constructor.
  - simpl. apply Forall_app. split.
    + apply Forall_forall. intros value Hin.
      apply repeat_spec in Hin. subst value.
      apply P082ProfileLabel_bounds. exact Hk.
    + apply IH.
Qed.

Lemma P082RealizeProfile_bounds : forall k parts,
  1 <= k ->
  Forall (fun x => 1 <= x) parts ->
  Forall (fun value => 1 <= value <= k)
    (P082RealizeProfile k parts).
Proof.
  intros k parts Hk Hparts. unfold P082RealizeProfile.
  apply P082RealizeProfileFrom_bounds; assumption.
Qed.

Lemma P082RealizeProfileFrom_contains_block_label :
  forall k block_index parts offset,
  Forall (fun x => 1 <= x) parts ->
  0 <= offset < Zlength parts ->
  In (P082ProfileLabel k (block_index + offset))
    (P082RealizeProfileFrom k block_index parts).
Proof.
  intros k block_index parts offset Hparts. revert block_index offset.
  induction Hparts as [|len rest Hlen Hrest IH];
    intros block_index offset Hoffset.
  - change (0 <= offset < 0) in Hoffset. lia.
  - simpl P082RealizeProfileFrom.
    destruct (Z.eq_dec offset 0) as [Hzero|Hnonzero].
    + subst offset. apply in_or_app. left.
      replace (block_index + 0) with block_index by lia.
      assert (Hnat : Z.to_nat len <> O).
      { intro Hzero. apply (f_equal Z.of_nat) in Hzero.
        rewrite Z2Nat.id in Hzero by lia. simpl in Hzero. lia. }
      destruct (Z.to_nat len) as [|count] eqn:Hcount;
        [contradiction|].
      simpl. left. reflexivity.
    + apply in_or_app. right.
      replace (block_index + offset) with
        ((block_index + 1) + (offset - 1)) by lia.
      apply IH. rewrite Zlength_cons in Hoffset. lia.
Qed.

Lemma P082RealizeProfile_UsesEveryValue : forall k parts,
  1 <= k ->
  k <= Zlength parts ->
  Forall (fun x => 1 <= x) parts ->
  UsesEveryValue k (P082RealizeProfile k parts).
Proof.
  intros k parts Hk Hcount Hparts.
  unfold UsesEveryValue. split.
  - apply P082RealizeProfile_bounds; assumption.
  - intros value Hvalue. unfold P082RealizeProfile.
    pose proof (P082RealizeProfileFrom_contains_block_label
      k 0 parts (value - 1) Hparts ltac:(lia)) as Hin.
    replace (P082ProfileLabel k (0 + (value - 1))) with value in Hin.
    + exact Hin.
    + unfold P082ProfileLabel.
      rewrite Z.mod_small by lia. lia.
Qed.

Lemma P082DistanceArray_first_block_formula : forall a b hi anchor q,
  DistanceArray a b ->
  P082MaximalSameBlock a 0 hi anchor ->
  hi < Zlength a ->
  0 <= q < hi ->
  Znth q b 0 = hi - q.
Proof.
  intros a b hi anchor q Hdistance Hblock Hhi Hq.
  destruct Hblock as
    [[Hlo Hloanchor]
     [[Hanchorhi Hhilength] [Hsame [Hleft Hright]]]].
  assert (Hqbound : 0 <= q < Zlength a) by lia.
  assert (Hqanchor : Znth q a 0 = Znth anchor a 0).
  { apply Hsame. exact Hq. }
  assert (Hrightdifferent : Znth hi a 0 <> Znth q a 0).
  { destruct Hright as [Hend|Hdifferent]; [lia|].
    rewrite Hqanchor. exact Hdifferent. }
  destruct (P082DistanceArray_nearest_different_witness
    a b q Hdistance Hqbound)
    as [j [Hj [Hjdifferent [Hvalue Hminimal]]]].
  assert (Hupper : Znth q b 0 <= hi - q).
  { rewrite Hvalue.
    pose proof (Hminimal hi ltac:(lia) Hrightdifferent) as Hminimum.
    replace (Z.abs (q - hi)) with (hi - q) in Hminimum
      by (rewrite Z.abs_neq by lia; lia).
    exact Hminimum. }
  assert (Hjright : hi <= j).
  { destruct (Z_lt_ge_dec j hi) as [Hinside|Houtside]; [|lia].
    exfalso. apply Hjdifferent. rewrite Hqanchor.
    apply Hsame. lia. }
  rewrite Hvalue, Z.abs_neq by lia. lia.
Qed.

Lemma P082DistanceArray_last_block_formula : forall a b lo anchor q,
  DistanceArray a b ->
  P082MaximalSameBlock a lo (Zlength a) anchor ->
  0 < lo ->
  lo <= q < Zlength a ->
  Znth q b 0 = q - lo + 1.
Proof.
  intros a b lo anchor q Hdistance Hblock Hlo Hq.
  destruct Hblock as
    [[Hlo0 Hloanchor]
     [[Hanchorhi Hhilength] [Hsame [Hleft Hright]]]].
  assert (Hqanchor : Znth q a 0 = Znth anchor a 0).
  { apply Hsame. exact Hq. }
  assert (Hleftdifferent :
    Znth (lo - 1) a 0 <> Znth q a 0).
  { destruct Hleft as [Hzero|Hdifferent]; [lia|].
    rewrite Hqanchor. exact Hdifferent. }
  destruct (P082DistanceArray_nearest_different_witness
    a b q Hdistance ltac:(lia))
    as [j [Hj [Hjdifferent [Hvalue Hminimal]]]].
  assert (Hupper : Znth q b 0 <= q - lo + 1).
  { rewrite Hvalue.
    pose proof (Hminimal (lo - 1) ltac:(lia) Hleftdifferent)
      as Hminimum.
    replace (Z.abs (q - (lo - 1))) with (q - lo + 1)
      in Hminimum by (rewrite Z.abs_eq by lia; lia).
    exact Hminimum. }
  assert (Hjleft : j < lo).
  { destruct (Z_lt_ge_dec j lo) as [Houtside|Hinside]; [exact Houtside|].
    exfalso. apply Hjdifferent. rewrite Hqanchor.
    apply Hsame. lia. }
  rewrite Hvalue, Z.abs_eq by lia. lia.
Qed.

Lemma P082DistanceArray_block_has_outer_boundary :
  forall a b lo hi anchor,
  DistanceArray a b ->
  P082MaximalSameBlock a lo hi anchor ->
  0 < lo \/ hi < Zlength a.
Proof.
  intros a b lo hi anchor Hdistance Hblock.
  destruct Hblock as
    [[Hlo Hloanchor]
     [[Hanchorhi Hhilength] [Hsame [Hleft Hright]]]].
  destruct (P082DistanceArray_nearest_different_witness
    a b anchor Hdistance ltac:(lia))
    as [j [Hj [Hdifferent Hrest]]].
  destruct (Z_lt_ge_dec j lo) as [Hjleft|Hjnotleft].
  - left. lia.
  - right. destruct (Z_lt_ge_dec j hi) as [Hjinside|Hjright].
    + exfalso. apply Hdifferent. apply Hsame. lia.
    + lia.
Qed.

Definition P082BlockObservationCorrect
    (a b : list Z) (blocks : list (Z * Z)) : Prop :=
  forall t, 0 <= t < Zlength blocks ->
    let block := Znth t blocks (0, 0) in
    forall q, fst block <= q < snd block ->
      Znth q b 0 =
      if Z.eq_dec (fst block) 0
      then snd block - q
      else if Z.eq_dec (snd block) (Zlength a)
      then q - fst block + 1
      else Z.min (q - fst block + 1) (snd block - q).

Lemma P082DistanceArray_block_observation_correct :
  forall a b blocks,
  DistanceArray a b ->
  P082OrderedBlockCover a blocks ->
  P082BlockObservationCorrect a b blocks.
Proof.
  intros a b blocks Hdistance [Hblocks [Hordered Hcover]] t Ht.
  pose proof (Hblocks t Ht) as Hblock.
  destruct (Znth t blocks (0, 0)) as [lo hi] eqn:Hselected.
  simpl in Hblock |- *.
  destruct Hblock as [anchor Hmaximal]. intros q Hq.
  pose proof Hmaximal as Hmaximal_bounds.
  destruct Hmaximal_bounds as
    [[Hlozero Hloanchor]
     [[Hanchorhi Hhilength] Hmaximal_rest]].
  pose proof (P082DistanceArray_block_has_outer_boundary
    a b lo hi anchor Hdistance Hmaximal) as Hboundary.
  destruct (Z.eq_dec lo 0) as [Hfirst|Hnotfirst].
  - subst lo. apply (P082DistanceArray_first_block_formula
      a b hi anchor q); try assumption; lia.
  - destruct (Z.eq_dec hi (Zlength a)) as [Hlast|Hnotlast].
    + subst hi. apply (P082DistanceArray_last_block_formula
        a b lo anchor q); try assumption; lia.
    + apply (P082DistanceArray_internal_block_formula
        a b lo hi anchor q); try assumption; lia.
Qed.

Lemma P082DistanceArray_computed_block_observation_correct :
  forall a b,
  DistanceArray a b ->
  P082BlockObservationCorrect a b (P082ComputedBlocks a).
Proof.
  intros a b Hdistance.
  apply P082DistanceArray_block_observation_correct; [exact Hdistance|].
  apply P082ComputedBlocks_ordered_cover.
Qed.

Lemma P082ProfileLabel_next_neq : forall k block_index,
  2 <= k ->
  P082ProfileLabel k block_index <>
  P082ProfileLabel k (block_index + 1).
Proof.
  intros k block_index Hk Hequal. unfold P082ProfileLabel in Hequal.
  assert (Hrange : 0 <= block_index mod k < k).
  { apply Z.mod_pos_bound. lia. }
  rewrite Z.add_mod in Hequal by lia.
  replace (1 mod k) with 1 in Hequal by
    (symmetry; apply Z.mod_small; lia).
  destruct (Z_lt_ge_dec (block_index mod k + 1) k) as [Hsmall|Hwrap].
  - replace ((block_index mod k + 1) mod k) with
      (block_index mod k + 1) in Hequal by
      (symmetry; apply Z.mod_small; lia).
    lia.
  - assert (Hedge : block_index mod k + 1 = k) by lia.
    rewrite Hedge, Z.mod_same in Hequal by lia. lia.
Qed.

Lemma P082_hd_repeat_positive : forall value len,
  1 <= len -> hd 0 (repeat value (Z.to_nat len)) = value.
Proof.
  intros value len Hlen.
  assert (Hnat : Z.to_nat len <> O).
  { intro Hzero. apply (f_equal Z.of_nat) in Hzero.
    rewrite Z2Nat.id in Hzero by lia. simpl in Hzero. lia. }
  destruct (Z.to_nat len) as [|count] eqn:Hcount;
    [contradiction|reflexivity].
Qed.

Fixpoint P082ProfileRunsFrom
    (k block_index : Z) (parts : list Z) : list (list Z) :=
  match parts with
  | nil => nil
  | len :: rest =>
      repeat (P082ProfileLabel k block_index) (Z.to_nat len) ::
      P082ProfileRunsFrom k (block_index + 1) rest
  end.

Definition P082ProfileRuns (k : Z) (parts : list Z) : list (list Z) :=
  P082ProfileRunsFrom k 0 parts.

Lemma P082ProfileRunsFrom_concat : forall k block_index parts,
  concat (P082ProfileRunsFrom k block_index parts) =
  P082RealizeProfileFrom k block_index parts.
Proof.
  intros k block_index parts. revert block_index.
  induction parts as [|len rest IH]; intro block_index.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma P082ProfileRuns_concat : forall k parts,
  concat (P082ProfileRuns k parts) = P082RealizeProfile k parts.
Proof.
  intros k parts. unfold P082ProfileRuns, P082RealizeProfile.
  apply P082ProfileRunsFrom_concat.
Qed.

Lemma P082ProfileRunsFrom_constant : forall k block_index parts run,
  Forall (fun len => 1 <= len) parts ->
  In run (P082ProfileRunsFrom k block_index parts) ->
  P082ConstantRun run.
Proof.
  intros k block_index parts run Hparts. revert block_index run.
  induction Hparts as [|len rest Hlen Hrest IH];
    intros block_index run Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [Hfirst|Hlater].
    + subst run. exists (P082ProfileLabel k block_index). split.
      * assert (Hnat : Z.to_nat len <> O).
        { intro Hzero. apply (f_equal Z.of_nat) in Hzero.
          rewrite Z2Nat.id in Hzero by lia. simpl in Hzero. lia. }
        destruct (Z.to_nat len) as [|count] eqn:Hcount;
          [contradiction|discriminate].
      * apply Forall_forall. intros value Hvalue.
        apply repeat_spec in Hvalue. exact Hvalue.
    + apply IH with (block_index := block_index + 1). exact Hlater.
Qed.

Lemma P082ProfileRunsFrom_separated : forall k block_index parts,
  2 <= k ->
  Forall (fun len => 1 <= len) parts ->
  P082SeparatedRuns (P082ProfileRunsFrom k block_index parts).
Proof.
  intros k block_index parts Hk Hparts. revert block_index.
  induction Hparts as [|len rest Hlen Hrest IH]; intro block_index.
  - exact I.
  - destruct rest as [|next tail].
    + exact I.
    + simpl. split.
      * rewrite !P082_hd_repeat_positive.
        -- apply P082ProfileLabel_next_neq. exact Hk.
        -- inversion Hrest. assumption.
        -- exact Hlen.
      * apply IH.
Qed.

Lemma P082RealizeProfile_run_decomposition : forall k parts,
  2 <= k ->
  Forall (fun len => 1 <= len) parts ->
  P082RunDecomposition (P082RealizeProfile k parts)
    (P082ProfileRuns k parts).
Proof.
  intros k parts Hk Hparts. unfold P082RunDecomposition.
  split; [apply P082ProfileRuns_concat|]. split.
  - intros run Hin. unfold P082ProfileRuns in Hin.
    apply P082ProfileRunsFrom_constant with
      (k := k) (block_index := 0) (parts := parts); assumption.
  - unfold P082ProfileRuns.
    apply P082ProfileRunsFrom_separated; assumption.
Qed.

Lemma P082RealizeProfile_ordered_cover : forall k parts,
  2 <= k ->
  Forall (fun len => 1 <= len) parts ->
  P082OrderedBlockCover (P082RealizeProfile k parts)
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts)).
Proof.
  intros k parts Hk Hparts.
  apply P082RunDecomposition_ordered_cover.
  apply P082RealizeProfile_run_decomposition; assumption.
Qed.

Lemma P082ProfileRunsFrom_block_lengths : forall k block_index offset parts,
  Forall (fun len => 1 <= len) parts ->
  P082OrderedBlockLengths
    (P082BlocksFromRuns offset
      (P082ProfileRunsFrom k block_index parts)) = parts.
Proof.
  intros k block_index offset parts Hparts.
  revert block_index offset.
  induction Hparts as [|len rest Hlen Hrest IH];
    intros block_index offset.
  - reflexivity.
  - simpl. rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    f_equal; [lia|apply IH].
Qed.

Lemma P082RealizeProfile_block_lengths : forall k parts,
  Forall (fun len => 1 <= len) parts ->
  P082OrderedBlockLengths
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts)) = parts.
Proof.
  intros k parts Hparts. unfold P082ProfileRuns.
  apply P082ProfileRunsFrom_block_lengths. exact Hparts.
Qed.

Lemma P082_Znth_map_seq : forall (f : nat -> Z) count q,
  0 <= q < Z.of_nat count ->
  Znth q (map f (seq 0 count)) 0 = f (Z.to_nat q).
Proof.
  intros f count q Hq. unfold Znth.
  apply nth_error_nth.
  rewrite nth_error_map, nth_error_seq.
  assert (Hnat : (Z.to_nat q < count)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  rewrite (proj2 (Nat.ltb_lt _ _) Hnat). simpl.
  replace (0 + Z.to_nat q)%nat with (Z.to_nat q) by lia.
  reflexivity.
Qed.

Lemma P082IncreasingObservation_Znth : forall len q,
  0 <= q < len ->
  Znth q (P082IncreasingObservation len) 0 = q + 1.
Proof.
  intros len q Hq. unfold P082IncreasingObservation.
  rewrite P082_Znth_map_seq.
  - rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Z2Nat.id by lia. exact Hq.
Qed.

Lemma P082DecreasingObservation_Znth : forall len q,
  0 <= q < len ->
  Znth q (P082DecreasingObservation len) 0 = len - q.
Proof.
  intros len q Hq. unfold P082DecreasingObservation.
  rewrite P082_Znth_map_seq.
  - rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Z2Nat.id by lia. exact Hq.
Qed.

Lemma P082InternalObservation_Znth : forall len q,
  0 <= q < len ->
  Znth q (P082InternalObservation len) 0 =
  Z.min (q + 1) (len - q).
Proof.
  intros len q Hq. unfold P082InternalObservation.
  rewrite P082_Znth_map_seq.
  - rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Z2Nat.id by lia. exact Hq.
Qed.

Lemma P082_Znth_app_left : forall (A : Type) (default : A) left right q,
  0 <= q < Zlength left ->
  Znth q (left ++ right) default = Znth q left default.
Proof.
  intros A default left right q Hq. unfold Znth. apply app_nth1.
  rewrite Zlength_correct in Hq. lia.
Qed.

Lemma P082_Znth_app_right : forall (A : Type) (default : A) left right q,
  Zlength left <= q ->
  Znth q (left ++ right) default =
  Znth (q - Zlength left) right default.
Proof.
  intros A default left right q Hq. unfold Znth. rewrite app_nth2.
  - f_equal. rewrite Zlength_correct. lia.
  - rewrite Zlength_correct in Hq. lia.
Qed.

Definition P082BlockObservation (n : Z) (block : Z * Z) : list Z :=
  let lo := fst block in
  let hi := snd block in
  if Z.eq_dec lo 0
  then P082DecreasingObservation (hi - lo)
  else if Z.eq_dec hi n
  then P082IncreasingObservation (hi - lo)
  else P082InternalObservation (hi - lo).

Definition P082ObservationFromBlocks
    (n : Z) (blocks : list (Z * Z)) : list Z :=
  concat (map (P082BlockObservation n) blocks).

Lemma P082BlockObservation_length : forall n lo hi,
  lo <= hi ->
  Zlength (P082BlockObservation n (lo, hi)) = hi - lo.
Proof.
  intros n lo hi Horder. unfold P082BlockObservation. simpl.
  destruct (Z.eq_dec lo 0).
  - apply P082DecreasingObservation_length. lia.
  - destruct (Z.eq_dec hi n).
    + apply P082IncreasingObservation_length. lia.
    + apply P082InternalObservation_length. lia.
Qed.

Lemma P082ObservationFromBlocks_length : forall n lo hi blocks,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  Zlength (P082ObservationFromBlocks n blocks) = hi - lo.
Proof.
  intros n lo hi blocks Hchain. induction Hchain;
    intros Hpositive.
  - unfold P082ObservationFromBlocks. simpl. rewrite Zlength_nil. lia.
  - unfold P082ObservationFromBlocks in *. simpl.
    assert (Hfirst : lo < mid).
    { specialize (Hpositive 0). simpl in Hpositive.
      apply Hpositive. rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest). lia. }
    rewrite Zlength_app, P082BlockObservation_length by lia.
    rewrite IHHchain.
    + lia.
    + intros t Ht. specialize (Hpositive (t + 1)).
      rewrite Znth_cons in Hpositive by lia.
      replace (t + 1 - 1) with t in Hpositive by lia.
      apply Hpositive. rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest). lia.
Qed.

Lemma P082ObservationFromBlocks_Znth : forall n lo hi blocks,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  forall t q,
  0 <= t < Zlength blocks ->
  fst (Znth t blocks (0, 0)) <= q <
    snd (Znth t blocks (0, 0)) ->
  Znth (q - lo) (P082ObservationFromBlocks n blocks) 0 =
  Znth (q - fst (Znth t blocks (0, 0)))
    (P082BlockObservation n (Znth t blocks (0, 0))) 0.
Proof.
  intros n lo hi blocks Hchain. induction Hchain;
    intros Hpositive t q Ht Hq.
  - change (0 <= t < 0) in Ht. lia.
  - assert (Hfirst : lo < mid).
    { specialize (Hpositive 0). simpl in Hpositive.
      apply Hpositive. rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest). lia. }
    assert (Hpositive_tail : forall u,
      0 <= u < Zlength rest ->
      fst (Znth u rest (0, 0)) < snd (Znth u rest (0, 0))).
    { intros u Hu. specialize (Hpositive (u + 1)).
      rewrite Znth_cons in Hpositive by lia.
      replace (u + 1 - 1) with u in Hpositive by lia.
      apply Hpositive. rewrite Zlength_cons. lia. }
    destruct (Z.eq_dec t 0) as [Htzero|Htnonzero].
    + subst t. rewrite Znth0_cons in Hq |- *. simpl in Hq |- *.
      unfold P082ObservationFromBlocks. simpl.
      apply P082_Znth_app_left.
      rewrite P082BlockObservation_length by lia. lia.
    + assert (Htpos : 0 < t) by lia.
      assert (Htailindex : 0 <= t - 1 < Zlength rest).
      { rewrite Zlength_cons in Ht. lia. }
      rewrite Znth_cons in Hq |- * by lia.
      replace (t - 1) with (t - 1) in Hq by reflexivity.
      pose proof (P082EndpointChain_block_bounds mid hi rest Hchain
        Hpositive_tail (t - 1) Htailindex) as [Hblocklo Hblockhi].
      unfold P082ObservationFromBlocks. simpl.
      rewrite P082_Znth_app_right.
      * rewrite P082BlockObservation_length by lia.
        replace (q - lo - (mid - lo)) with (q - mid) by lia.
        apply IHHchain; assumption.
      * rewrite P082BlockObservation_length by lia. lia.
Qed.

Lemma P082BlockObservation_Znth : forall n lo hi q,
  lo <= q < hi ->
  Znth (q - lo) (P082BlockObservation n (lo, hi)) 0 =
  if Z.eq_dec lo 0
  then hi - q
  else if Z.eq_dec hi n
  then q - lo + 1
  else Z.min (q - lo + 1) (hi - q).
Proof.
  intros n lo hi q Hq. unfold P082BlockObservation. simpl.
  destruct (Z.eq_dec lo 0) as [Hfirst|Hnotfirst].
  - rewrite P082DecreasingObservation_Znth by lia. lia.
  - destruct (Z.eq_dec hi n) as [Hlast|Hnotlast].
    + rewrite P082IncreasingObservation_Znth by lia. lia.
    + rewrite P082InternalObservation_Znth by lia.
      replace (hi - lo - (q - lo)) with (hi - q) by lia.
      reflexivity.
Qed.

Lemma P082ObservationFromBlocks_correct : forall a blocks,
  P082EndpointChain 0 (Zlength a) blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  P082BlockObservationCorrect a
    (P082ObservationFromBlocks (Zlength a) blocks) blocks.
Proof.
  intros a blocks Hchain Hpositive t Ht.
  destruct (Znth t blocks (0, 0)) as [lo hi] eqn:Hblock.
  simpl. intros q Hq.
  pose proof (P082ObservationFromBlocks_Znth
    (Zlength a) 0 (Zlength a) blocks Hchain Hpositive
    t q Ht) as Hobservation.
  rewrite Hblock in Hobservation. simpl in Hobservation.
  specialize (Hobservation Hq).
  replace (q - 0) with q in Hobservation by lia.
  rewrite Hobservation.
  apply P082BlockObservation_Znth. exact Hq.
Qed.

Lemma P082ProfileObservationTail_from_blocks :
  forall k block_index offset parts n,
  0 < offset ->
  Forall (fun len => 1 <= len) parts ->
  n = offset + fold_right Z.add 0 parts ->
  P082ObservationFromBlocks n
    (P082BlocksFromRuns offset
      (P082ProfileRunsFrom k block_index parts)) =
  P082ProfileObservationTail parts.
Proof.
  intros k block_index offset parts n Hoffset Hparts.
  revert block_index offset n Hoffset.
  induction Hparts as [|len rest Hlen Hrest IH];
    intros block_index offset n Hoffset Htotal.
  - unfold P082ObservationFromBlocks. reflexivity.
  - destruct rest as [|next tail].
    + change (P082BlockObservation n
        (offset, offset + Zlength
          (repeat (P082ProfileLabel k block_index) (Z.to_nat len))) ++ nil =
        P082IncreasingObservation len).
      rewrite app_nil_r.
      rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
      unfold P082BlockObservation. simpl.
      simpl in Htotal.
      destruct (Z.eq_dec offset 0); [lia|].
      destruct (Z.eq_dec (offset + len) n); [|lia].
      f_equal. lia.
    + change (P082ObservationFromBlocks n
        ((offset, offset + Zlength
          (repeat (P082ProfileLabel k block_index) (Z.to_nat len))) ::
         P082BlocksFromRuns
           (offset + Zlength
             (repeat (P082ProfileLabel k block_index) (Z.to_nat len)))
           (P082ProfileRunsFrom k (block_index + 1) (next :: tail))) =
        P082InternalObservation len ++
        P082ProfileObservationTail (next :: tail)).
      rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
      unfold P082ObservationFromBlocks at 1. simpl.
      unfold P082BlockObservation at 1. simpl.
      destruct (Z.eq_dec offset 0); [lia|].
      destruct (Z.eq_dec (offset + len) n) as [Hlast|Hnotlast].
      * assert (Hnextpositive : 1 <= next).
        { inversion Hrest. assumption. }
        assert (Htailbounds : Forall (fun value => 1 <= value) tail).
        { inversion Hrest. assumption. }
        assert (Htailsum : 0 <= fold_right Z.add 0 tail).
        { clear -Htailbounds.
          induction tail as [|value values IHvalues]; simpl; [lia|].
          inversion Htailbounds as [|? ? Hvalue Hvalues]. subst.
          specialize (IHvalues Hvalues). lia. }
        simpl in Htotal. lia.
      * replace (offset + len - offset) with len by lia.
        f_equal. apply IH; [lia|].
        change (n = offset +
          (len + fold_right Z.add 0 (next :: tail))) in Htotal.
        change (n = offset + len +
          fold_right Z.add 0 (next :: tail)). lia.
Qed.

Lemma P082ProfileObservation_from_blocks : forall k parts,
  Forall (fun len => 1 <= len) parts ->
  2 <= Zlength parts ->
  P082ObservationFromBlocks (fold_right Z.add 0 parts)
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts)) =
  P082ProfileObservation parts.
Proof.
  intros k parts Hparts Hcount.
  destruct parts as [|first rest].
  - change (2 <= 0) in Hcount. lia.
  - inversion Hparts as [|? ? Hfirst Hrest]. subst.
    destruct rest as [|second tail].
    + rewrite Zlength_cons, Zlength_nil in Hcount. lia.
    + unfold P082ProfileRuns. simpl P082ProfileRunsFrom.
    unfold P082BlocksFromRuns at 1; fold P082BlocksFromRuns.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    change (P082ObservationFromBlocks
      (first + fold_right Z.add 0 (second :: tail))
      ((0, first) ::
       P082BlocksFromRuns first
         (P082ProfileRunsFrom k 1 (second :: tail))) =
      P082DecreasingObservation first ++
      P082ProfileObservationTail (second :: tail)).
    unfold P082ObservationFromBlocks at 1. simpl.
    unfold P082BlockObservation at 1. simpl.
    replace (first - 0) with first by lia.
    f_equal.
    change (P082ObservationFromBlocks
      (first + fold_right Z.add 0 (second :: tail))
      (P082BlocksFromRuns first
        (P082ProfileRunsFrom k 1 (second :: tail))) =
      P082ProfileObservationTail (second :: tail)).
    apply P082ProfileObservationTail_from_blocks;
      [lia|exact Hrest|reflexivity].
Qed.

Lemma P082RealizeProfile_blocks_positive : forall k parts t,
  2 <= k ->
  Forall (fun len => 1 <= len) parts ->
  0 <= t < Zlength
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts)) ->
  fst (Znth t (P082BlocksFromRuns 0 (P082ProfileRuns k parts)) (0, 0)) <
  snd (Znth t (P082BlocksFromRuns 0 (P082ProfileRuns k parts)) (0, 0)).
Proof.
  intros k parts t Hk Hparts Ht.
  pose proof (P082RealizeProfile_ordered_cover k parts Hk Hparts)
    as [Hblocks Hcover].
  specialize (Hblocks t Ht).
  destruct (Znth t (P082BlocksFromRuns 0 (P082ProfileRuns k parts))
    (0, 0)) as [lo hi]. simpl in Hblocks |- *.
  destruct Hblocks as [anchor Hmaximal].
  destruct Hmaximal as [[Hlo Hloanchor] [[Hanchorhi Hhilength] Hrest]].
  lia.
Qed.

Lemma P082RealizeProfile_block_observation_correct : forall k parts,
  2 <= k ->
  Forall (fun len => 1 <= len) parts ->
  2 <= Zlength parts ->
  P082BlockObservationCorrect (P082RealizeProfile k parts)
    (P082ProfileObservation parts)
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts)).
Proof.
  intros k parts Hk Hparts Hcount.
  assert (Hchain : P082EndpointChain 0
    (Zlength (P082RealizeProfile k parts))
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts))).
  { pose proof (P082BlocksFromRuns_endpoint_chain 0
      (P082ProfileRuns k parts)) as Hchain.
    rewrite P082ProfileRuns_concat in Hchain.
    replace (0 + Zlength (P082RealizeProfile k parts)) with
      (Zlength (P082RealizeProfile k parts)) in Hchain by lia.
    exact Hchain. }
  assert (Hpositive : forall t,
    0 <= t < Zlength
      (P082BlocksFromRuns 0 (P082ProfileRuns k parts)) ->
    fst (Znth t (P082BlocksFromRuns 0 (P082ProfileRuns k parts))
      (0, 0)) <
    snd (Znth t (P082BlocksFromRuns 0 (P082ProfileRuns k parts))
      (0, 0))).
  { intros t Ht. apply P082RealizeProfile_blocks_positive;
      assumption. }
  pose proof (P082ObservationFromBlocks_correct
    (P082RealizeProfile k parts)
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts))
    Hchain Hpositive) as Hcorrect.
  rewrite P082RealizeProfile_length in Hcorrect by
    (apply Forall_impl with (P := fun len => 1 <= len);
     [intros; lia|exact Hparts]).
  rewrite P082ProfileObservation_from_blocks in Hcorrect by assumption.
  exact Hcorrect.
Qed.

Lemma P082OrderedBlockCover_two_outer_boundary : forall a blocks t,
  P082OrderedBlockCover a blocks ->
  2 <= Zlength blocks ->
  0 <= t < Zlength blocks ->
  let block := Znth t blocks (0, 0) in
  0 < fst block \/ snd block < Zlength a.
Proof.
  intros a blocks t [Hallblocks [Hordered Hcover]] Hcount Ht.
  pose proof (Hallblocks t Ht) as Hblocks.
  destruct (Znth t blocks (0, 0)) as [lo hi] eqn:Hselected.
  simpl in Hblocks |- *.
  destruct Hblocks as [anchor Hmax].
  destruct Hmax as
    [[Hlo Hloanchor] [[Hanchorhi Hhilength] Hrest]].
  destruct (Z_lt_ge_dec 0 lo) as [Hpositive|Hnotpositive].
  - left. lia.
  - right. assert (Hlozero : lo = 0) by lia. subst lo.
    assert (Htzero : t = 0).
    { destruct (Z.eq_dec t 0); [assumption|].
      assert (Hprevious : 0 <= t - 1 < t) by lia.
      pose proof (Hordered (t - 1) t Hprevious ltac:(lia)) as Hbefore.
      pose proof (Hallblocks (t - 1) ltac:(lia)) as Hprevblock.
      destruct (Znth (t - 1) blocks (0, 0)) as [plo phi]
        eqn:Hprevselected.
      rewrite Hselected in Hbefore. simpl in Hbefore, Hprevblock.
      destruct Hprevblock as [panchor P].
      destruct P as [[Hplo Hploa] [[Hpahi Hphilen] Prest]]. lia. }
    subst t.
    pose proof (Hallblocks 1 ltac:(lia)) as Hnextblock.
    destruct (Znth 1 blocks (0, 0)) as [nlo nhi] eqn:Hnextselected.
    simpl in Hnextblock.
    destruct Hnextblock as [nanchor Hnextmax].
    destruct Hnextmax as
      [[Hnlo Hnloa] [[Hnanhi Hnhilen] Hnextrest]].
    pose proof (Hordered 0 1 ltac:(lia) ltac:(lia)) as Hbefore.
    rewrite Hselected, Hnextselected in Hbefore. simpl in Hbefore. lia.
Qed.

Lemma P082BlockObservationCorrect_DistanceArray : forall a b blocks,
  Zlength b = Zlength a ->
  2 <= Zlength blocks ->
  P082OrderedBlockCover a blocks ->
  P082BlockObservationCorrect a b blocks ->
  DistanceArray a b.
Proof.
  intros a b blocks Hlength Hcount Hcover Hobs.
  split; [exact Hlength|]. intros i Hi.
  destruct (P082OrderedBlockCover_position_exists a blocks i Hcover Hi)
    as [t [Ht Hit]].
  destruct Hcover as [Hblocks [Hordered Hcovers]].
  pose proof (Hblocks t Ht) as Hblock.
  destruct (Znth t blocks (0, 0)) as [lo hi] eqn:Hselected.
  simpl in Hblock, Hit.
  destruct Hblock as [anchor Hmax].
  pose proof Hmax as Hmaxparts.
  destruct Hmaxparts as
    [[Hlo Hloanchor]
     [[Hanchorhi Hhilength] [Hsame [Hleft Hright]]]].
  specialize (Hobs t Ht). rewrite Hselected in Hobs. simpl in Hobs.
  specialize (Hobs i Hit).
  assert (Hianchor : Znth i a 0 = Znth anchor a 0).
  { apply Hsame. exact Hit. }
  assert (Houtside : forall j,
    0 <= j < Zlength a -> Znth j a 0 <> Znth i a 0 ->
    j < lo \/ hi <= j).
  { intros j Hj Hneq. destruct (Z_lt_ge_dec j lo); [left; assumption|].
    right. destruct (Z_lt_ge_dec j hi); [|lia].
    exfalso. apply Hneq. rewrite Hianchor. apply Hsame. lia. }
  pose proof (P082OrderedBlockCover_two_outer_boundary
    a blocks t (conj Hblocks (conj Hordered Hcovers)) Hcount Ht)
    as Houter.
  rewrite Hselected in Houter. simpl in Houter.
  unfold min_value_of_subset. unfold min_object_of_subset.
  destruct (Z.eq_dec lo 0) as [Hfirst|Hnotfirst].
  - subst lo. assert (Hhi : hi < Zlength a) by (destruct Houter; lia).
    exists hi. split.
    + split.
      * split; [lia|]. destruct Hright as [Hend|Hneq]; [lia|].
        rewrite Hianchor. exact Hneq.
      * intros j [Hj Hneq]. specialize (Houtside j Hj Hneq).
        rewrite Z.abs_neq by lia. lia.
    + rewrite Hobs. rewrite Z.abs_neq by lia. lia.
  - destruct (Z.eq_dec hi (Zlength a)) as [Hlast|Hnotlast].
    + subst hi. assert (Hlo0 : 0 < lo) by (destruct Houter; lia).
      exists (lo - 1). split.
      * split.
        -- split; [lia|]. destruct Hleft as [Hzero|Hneq]; [lia|].
           rewrite Hianchor. exact Hneq.
        -- intros j [Hj Hneq]. specialize (Houtside j Hj Hneq).
           rewrite Z.abs_eq by lia. lia.
      * rewrite Hobs. rewrite Z.abs_eq by lia. lia.
    + assert (Hlo0 : 0 < lo) by lia.
      assert (Hhi : hi < Zlength a) by lia.
      destruct (Z_le_dec (i - lo + 1) (hi - i)) as [Hnearleft|Hnearright].
      * exists (lo - 1). split.
        -- split.
           ++ split; [lia|]. destruct Hleft as [Hzero|Hneq]; [lia|].
              rewrite Hianchor. exact Hneq.
           ++ intros j [Hj Hneq]. specialize (Houtside j Hj Hneq).
              rewrite Z.abs_eq by lia.
              destruct Houtside; [rewrite Z.abs_eq by lia|rewrite Z.abs_neq by lia]; lia.
        -- rewrite Hobs, Z.min_l by exact Hnearleft.
           rewrite Z.abs_eq by lia. lia.
      * exists hi. split.
        -- split.
           ++ split; [lia|]. destruct Hright as [Hend|Hneq]; [lia|].
              rewrite Hianchor. exact Hneq.
           ++ intros j [Hj Hneq]. specialize (Houtside j Hj Hneq).
              rewrite Z.abs_neq by lia.
              destruct Houtside; [rewrite Z.abs_eq by lia|rewrite Z.abs_neq by lia]; lia.
        -- rewrite Hobs, Z.min_r by lia.
           rewrite Z.abs_neq by lia. lia.
Qed.

Theorem P082RealizeProfile_DistanceArray : forall k parts,
  2 <= k ->
  Forall (fun len => 1 <= len) parts ->
  2 <= Zlength parts ->
  DistanceArray (P082RealizeProfile k parts)
    (P082ProfileObservation parts).
Proof.
  intros k parts Hk Hparts Hcount.
  apply (P082BlockObservationCorrect_DistanceArray
    (P082RealizeProfile k parts) (P082ProfileObservation parts)
    (P082BlocksFromRuns 0 (P082ProfileRuns k parts))).
  - assert (Hnonnegative : Forall (fun len => 0 <= len) parts).
    { apply Forall_impl with (P := fun len => 1 <= len);
      [intros; lia|exact Hparts]. }
    rewrite P082ProfileObservation_length by exact Hnonnegative.
    rewrite P082RealizeProfile_length by exact Hnonnegative.
    reflexivity.
  - rewrite <- P082OrderedBlockLengths_length.
    rewrite P082RealizeProfile_block_lengths by exact Hparts.
    exact Hcount.
  - apply P082RealizeProfile_ordered_cover; assumption.
  - apply P082RealizeProfile_block_observation_correct; assumption.
Qed.

Lemma P082BlockObservationCorrect_unique : forall a b1 b2 blocks,
  Zlength b1 = Zlength a ->
  Zlength b2 = Zlength a ->
  P082OrderedBlockCover a blocks ->
  P082BlockObservationCorrect a b1 blocks ->
  P082BlockObservationCorrect a b2 blocks ->
  b1 = b2.
Proof.
  intros a b1 b2 blocks Hlen1 Hlen2 Hcover Hobs1 Hobs2.
  apply (proj2 (list_eq_ext b1 b2 0)). split; [lia|].
  intros i Hi.
  destruct (P082OrderedBlockCover_position_exists a blocks i Hcover
    ltac:(lia)) as [t [Ht Hit]].
  specialize (Hobs1 t Ht). specialize (Hobs2 t Ht).
  specialize (Hobs1 i Hit). specialize (Hobs2 i Hit).
  rewrite Hobs1. symmetry. exact Hobs2.
Qed.

Lemma P082BlocksFromProfileLengths_rebuild : forall k block_index lo hi blocks,
  P082EndpointChain lo hi blocks ->
  (forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))) ->
  P082BlocksFromRuns lo
    (P082ProfileRunsFrom k block_index
      (P082OrderedBlockLengths blocks)) = blocks.
Proof.
  intros k block_index lo hi blocks Hchain. revert k block_index.
  induction Hchain as [endpoint|lo mid hi rest Htail IH];
    intros k block_index Hpositive.
  - reflexivity.
  - unfold P082OrderedBlockLengths at 1. simpl.
    assert (Hfirst : lo < mid).
    { specialize (Hpositive 0).
      rewrite Zlength_cons, Znth0_cons in Hpositive. simpl in Hpositive.
      apply Hpositive. pose proof (Zlength_nonneg rest). lia. }
    simpl P082ProfileRunsFrom. simpl P082BlocksFromRuns.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    f_equal.
    + f_equal; lia.
    + replace (lo + (mid - lo)) with mid by lia. apply IH.
      intros t Ht. specialize (Hpositive (t + 1)).
      rewrite Znth_cons in Hpositive by lia.
      replace (t + 1 - 1) with t in Hpositive by lia.
      apply Hpositive. rewrite Zlength_cons. lia.
Qed.

Lemma P082ObservationFromBlocks_profile : forall a blocks,
  P082OrderedBlockCover a blocks ->
  2 <= Zlength blocks ->
  P082ObservationFromBlocks (Zlength a) blocks =
  P082ProfileObservation (P082OrderedBlockLengths blocks).
Proof.
  intros a blocks Hcover Hcount.
  assert (Halen : 0 < Zlength a).
  { destruct Hcover as [Hblocks Hrest].
    pose proof (Hblocks 0 ltac:(lia)) as Hfirst.
    destruct (Znth 0 blocks (0, 0)) as [lo hi]. simpl in Hfirst.
    destruct Hfirst as [anchor Hmax].
    destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrestmax]]. lia. }
  assert (Hchain : P082EndpointChain 0 (Zlength a) blocks).
  { apply P082OrderedBlockCover_total_endpoint_chain; [exact Hcover|exact Halen]. }
  assert (Hpositive : forall t, 0 <= t < Zlength blocks ->
    fst (Znth t blocks (0, 0)) < snd (Znth t blocks (0, 0))).
  { intros t Ht. destruct Hcover as [Hblocks Hrest].
    specialize (Hblocks t Ht).
    destruct (Znth t blocks (0, 0)) as [lo hi]. simpl in Hblocks |- *.
    destruct Hblocks as [anchor Hmax].
    destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrestmax]]. lia. }
  pose proof (P082BlocksFromProfileLengths_rebuild
    2 0 0 (Zlength a) blocks Hchain Hpositive) as Hrebuild.
  assert (Hpartspositive : Forall (fun len => 1 <= len)
    (P082OrderedBlockLengths blocks)).
  { apply Forall_impl with
      (P := fun len => 1 <= len <= Zlength a).
    - intros len Hlen. lia.
    - apply P082OrderedBlockLengths_bounds. exact Hcover. }
  pose proof (P082ProfileObservation_from_blocks 2
    (P082OrderedBlockLengths blocks) Hpartspositive) as Hprofile.
  assert (Hpartscount : 2 <= Zlength (P082OrderedBlockLengths blocks)).
  { rewrite P082OrderedBlockLengths_length. exact Hcount. }
  specialize (Hprofile Hpartscount).
  pose proof (P082EndpointChain_lengths_sum 0 (Zlength a) blocks Hchain)
    as Hsum.
  rewrite Hsum in Hprofile.
  replace (Zlength a - 0) with (Zlength a) in Hprofile by lia.
  unfold P082ProfileRuns in Hprofile.
  rewrite Hrebuild in Hprofile. exact Hprofile.
Qed.

Lemma P082DistanceArray_computed_profile_observation : forall a b,
  2 <= Zlength (P082ComputedBlocks a) ->
  DistanceArray a b ->
  b = P082ProfileObservation
    (P082OrderedBlockLengths (P082ComputedBlocks a)).
Proof.
  intros a b Hcount Hdistance.
  assert (Hcover : P082OrderedBlockCover a (P082ComputedBlocks a)).
  { apply P082ComputedBlocks_ordered_cover. }
  assert (Hchain : P082EndpointChain 0 (Zlength a)
    (P082ComputedBlocks a)).
  { apply P082ComputedBlocks_endpoint_chain. }
  assert (Hpositive : forall t,
    0 <= t < Zlength (P082ComputedBlocks a) ->
    fst (Znth t (P082ComputedBlocks a) (0, 0)) <
    snd (Znth t (P082ComputedBlocks a) (0, 0))).
  { intros t Ht. destruct Hcover as [Hblocks Hrest].
    specialize (Hblocks t Ht).
    destruct (Znth t (P082ComputedBlocks a) (0, 0)) as [lo hi].
    simpl in Hblocks |- *. destruct Hblocks as [anchor Hmax].
    destruct Hmax as [[Hlo Hloa] [[Hahi Hhilength] Hrestmax]]. lia. }
  assert (Hgenerated_length :
    Zlength (P082ObservationFromBlocks (Zlength a)
      (P082ComputedBlocks a)) = Zlength a).
  { rewrite (P082ObservationFromBlocks_length
      (Zlength a) 0 (Zlength a) (P082ComputedBlocks a)
      Hchain Hpositive). lia. }
  assert (Hsource_length : Zlength b = Zlength a).
  { exact (proj1 Hdistance). }
  assert (Heq : b = P082ObservationFromBlocks (Zlength a)
    (P082ComputedBlocks a)).
  { apply (P082BlockObservationCorrect_unique a b
      (P082ObservationFromBlocks (Zlength a) (P082ComputedBlocks a))
      (P082ComputedBlocks a)); try assumption.
    - apply P082DistanceArray_computed_block_observation_correct.
      exact Hdistance.
    - apply P082ObservationFromBlocks_correct; assumption. }
  rewrite Heq. eapply P082ObservationFromBlocks_profile; assumption.
Qed.

Theorem P082DistanceArray_normalized_same_observation_witness :
  forall n k a b,
  1 <= n -> Zlength a = n -> 2 <= k ->
  UsesEveryValue k a -> DistanceArray a b ->
  exists realized,
    Zlength realized = n /\
    UsesEveryValue k realized /\
    DistanceArray realized b.
Proof.
  intros n k a b Hn Hlength Hk Huses Hdistance.
  set (parts := P082OrderedBlockLengths (P082ComputedBlocks a)).
  set (normalized := P082NormalizeProfile parts).
  pose proof (P082UsesEveryValue_normalized_computed_profile
    n k a Hn Hlength ltac:(lia) Huses) as Hcanonical.
  change (P082CanonicalProfile n k normalized) in Hcanonical.
  destruct Hcanonical as [Hsum [Hcount [Hbounds Hno2]]].
  assert (Hpositive : Forall (fun len => 1 <= len) normalized).
  { apply Forall_impl with (P := fun len => 1 <= len <= n);
    [intros; lia|exact Hbounds]. }
  assert (Htwo : 2 <= Zlength normalized) by lia.
  exists (P082RealizeProfile k normalized). split.
  - rewrite P082RealizeProfile_length.
    + exact Hsum.
    + apply Forall_impl with (P := fun len => 1 <= len);
      [intros; lia|exact Hpositive].
  - split.
    + apply P082RealizeProfile_UsesEveryValue; [lia|lia|exact Hpositive].
    + pose proof (P082RealizeProfile_DistanceArray
        k normalized Hk Hpositive Htwo) as Hrealized.
      unfold normalized in Hrealized.
      rewrite P082ProfileObservation_normalize in Hrealized.
      assert (Hblockcount : 2 <= Zlength (P082ComputedBlocks a)).
      { pose proof (P082UsesEveryValue_computed_blocks_count
          k a ltac:(lia) Huses). lia. }
      pose proof (P082DistanceArray_computed_profile_observation
        a b Hblockcount Hdistance) as Hobservation.
      unfold parts in Hrealized. rewrite <- Hobservation in Hrealized.
      exact Hrealized.
Qed.

Lemma P082NormalizeProfileTail_fixed : forall parts,
  (forall t, 0 <= t < Zlength parts - 1 -> Znth t parts 0 <> 2) ->
  P082NormalizeProfileTail parts = parts.
Proof.
  induction parts as [|x rest IH]; intros Hno2; [reflexivity|].
  destruct rest as [|y tail]; [reflexivity|].
  rewrite P082NormalizeProfileTail_cons_nonfinal.
  destruct (Z.eq_dec x 2) as [Heq|Hneq].
  - exfalso. apply (Hno2 0).
    + rewrite !Zlength_cons. pose proof (Zlength_nonneg tail). lia.
    + rewrite Znth0_cons. exact Heq.
  - f_equal. apply IH. intros t Ht.
    specialize (Hno2 (t + 1)).
    rewrite Znth_cons in Hno2 by lia.
    replace (t + 1 - 1) with t in Hno2 by lia.
    apply Hno2. rewrite !Zlength_cons in *. lia.
Qed.

Lemma P082NormalizeProfile_fixed : forall parts,
  (forall t, 1 <= t < Zlength parts - 1 -> Znth t parts 0 <> 2) ->
  P082NormalizeProfile parts = parts.
Proof.
  intros [|first rest] Hno2; [reflexivity|].
  unfold P082NormalizeProfile. f_equal.
  apply P082NormalizeProfileTail_fixed. intros t Ht.
  specialize (Hno2 (t + 1)).
  rewrite Znth_cons in Hno2 by lia.
  replace (t + 1 - 1) with t in Hno2 by lia.
  apply Hno2. rewrite Zlength_cons. lia.
Qed.

Lemma P082CanonicalProfile_normalization_fixed : forall n k parts,
  P082CanonicalProfile n k parts ->
  P082NormalizeProfile parts = parts.
Proof.
  intros n k parts [_ [_ [_ Hno2]]].
  apply P082NormalizeProfile_fixed. exact Hno2.
Qed.

Lemma P082ProfileObservation_first_entry : forall first second tail,
  1 <= first ->
  Znth 0 (P082ProfileObservation (first :: second :: tail)) 0 = first.
Proof.
  intros first second tail Hfirst.
  unfold P082ProfileObservation.
  rewrite P082_Znth_app_left.
  - rewrite P082DecreasingObservation_Znth by lia. lia.
  - rewrite P082DecreasingObservation_length by lia. lia.
Qed.

Lemma P082ProfileObservation_equal_first : forall
    first1 second1 tail1 first2 second2 tail2,
  1 <= first1 -> 1 <= first2 ->
  P082ProfileObservation (first1 :: second1 :: tail1) =
  P082ProfileObservation (first2 :: second2 :: tail2) ->
  first1 = first2.
Proof.
  intros first1 second1 tail1 first2 second2 tail2 Hfirst1 Hfirst2 Heq.
  pose proof (P082ProfileObservation_first_entry
    first1 second1 tail1 Hfirst1) as Hentry1.
  pose proof (P082ProfileObservation_first_entry
    first2 second2 tail2 Hfirst2) as Hentry2.
  rewrite Heq in Hentry1.
  congruence.
Qed.

Lemma P082ProfileObservation_equal_tail : forall
    first second1 tail1 second2 tail2,
  P082ProfileObservation (first :: second1 :: tail1) =
  P082ProfileObservation (first :: second2 :: tail2) ->
  P082ProfileObservationTail (second1 :: tail1) =
  P082ProfileObservationTail (second2 :: tail2).
Proof.
  intros first second1 tail1 second2 tail2 Heq.
  unfold P082ProfileObservation in Heq.
  apply app_inv_head in Heq. exact Heq.
Qed.

Lemma P082ProfileObservation_equal_first_tail : forall
    first1 second1 tail1 first2 second2 tail2,
  1 <= first1 -> 1 <= first2 ->
  P082ProfileObservation (first1 :: second1 :: tail1) =
  P082ProfileObservation (first2 :: second2 :: tail2) ->
  first1 = first2 /\
  P082ProfileObservationTail (second1 :: tail1) =
  P082ProfileObservationTail (second2 :: tail2).
Proof.
  intros first1 second1 tail1 first2 second2 tail2
    Hfirst1 Hfirst2 Heq.
  assert (Hfirst : first1 = first2).
  { apply (P082ProfileObservation_equal_first
      first1 second1 tail1 first2 second2 tail2); assumption. }
  split; [exact Hfirst|]. subst first2.
  apply (P082ProfileObservation_equal_tail
    first1 second1 tail1 second2 tail2). exact Heq.
Qed.

(* Inside a canonical non-final block (whose length cannot be two), the two
   consecutive ones used as a block delimiter cannot occur internally. *)
Lemma P082InternalObservation_no_adjacent_ones : forall len q,
  3 <= len -> 0 <= q < len - 1 ->
  ~ (Znth q (P082InternalObservation len) 0 = 1 /\
     Znth (q + 1) (P082InternalObservation len) 0 = 1).
Proof.
  intros len q Hlen Hq [Hhere Hnext].
  rewrite P082InternalObservation_Znth in Hhere by lia.
  rewrite P082InternalObservation_Znth in Hnext by lia.
  destruct (Z_le_gt_dec (q + 1) (len - q)) as [Hleft|Hright].
  - rewrite Z.min_l in Hhere by exact Hleft.
    assert (q = 0) by lia. subst q.
    rewrite Z.min_l in Hnext by lia. lia.
  - rewrite Z.min_r in Hhere by lia. lia.
Qed.

Lemma P082IncreasingObservation_no_adjacent_ones : forall len q,
  1 <= len -> 0 <= q < len - 1 ->
  ~ (Znth q (P082IncreasingObservation len) 0 = 1 /\
     Znth (q + 1) (P082IncreasingObservation len) 0 = 1).
Proof.
  intros len q Hlen Hq [Hhere Hnext].
  rewrite P082IncreasingObservation_Znth in Hhere by lia.
  rewrite P082IncreasingObservation_Znth in Hnext by lia.
  lia.
Qed.

Definition P082FirstOnePair (obs : list Z) (boundary : Z) : Prop :=
  0 <= boundary /\ boundary + 1 < Zlength obs /\
  Znth boundary obs 0 = 1 /\ Znth (boundary + 1) obs 0 = 1 /\
  forall q, 0 <= q < boundary ->
    ~ (Znth q obs 0 = 1 /\ Znth (q + 1) obs 0 = 1).

Lemma P082FirstOnePair_unique : forall obs b1 b2,
  P082FirstOnePair obs b1 -> P082FirstOnePair obs b2 -> b1 = b2.
Proof.
  intros obs b1 b2 [Hb1 [_ [H11 [H12 Hmin1]]]]
    [Hb2 [_ [H21 [H22 Hmin2]]]].
  destruct (Z_lt_ge_dec b1 b2) as [Hlt|Hge].
  - exfalso. apply (Hmin2 b1); auto.
  - destruct (Z.eq_dec b1 b2) as [Heq|Hneq]; [exact Heq|].
    exfalso. apply (Hmin1 b2); auto; lia.
Qed.

Lemma P082ProfileObservationTail_first : forall first rest,
  1 <= first ->
  Znth 0 (P082ProfileObservationTail (first :: rest)) 0 = 1.
Proof.
  intros first rest Hfirst. destruct rest as [|second tail].
  - simpl. rewrite P082IncreasingObservation_Znth by lia. lia.
  - change (Znth 0
      (P082InternalObservation first ++
       P082ProfileObservationTail (second :: tail)) 0 = 1).
    rewrite P082_Znth_app_left.
    + rewrite P082InternalObservation_Znth by lia.
      rewrite Z.min_l by lia. lia.
    + rewrite P082InternalObservation_length by lia. lia.
Qed.

Lemma P082InternalObservation_last : forall len,
  1 <= len ->
  Znth (len - 1) (P082InternalObservation len) 0 = 1.
Proof.
  intros len Hlen. rewrite P082InternalObservation_Znth by lia.
  rewrite Z.min_r by lia. lia.
Qed.

Lemma P082ProfileObservationTail_first_pair : forall first second rest,
  Forall (fun x => 1 <= x) (first :: second :: rest) ->
  first <> 2 ->
  P082FirstOnePair
    (P082ProfileObservationTail (first :: second :: rest)) (first - 1).
Proof.
  intros first second rest Hpositive Hnot2.
  inversion Hpositive as [|? ? Hfirst Hpositive_rest]; subst.
  inversion Hpositive_rest as [|? ? Hsecond Hpositive_tail]; subst.
  assert (Htail_nonneg : Forall (fun x => 0 <= x) (second :: rest)).
  { apply Forall_impl with (P := fun x => 1 <= x); [intros; lia|].
    constructor; assumption. }
  unfold P082FirstOnePair.
  rewrite P082ProfileObservationTail_length.
  2: { apply Forall_impl with (P := fun x => 1 <= x); [intros; lia|].
       exact Hpositive. }
  cbn [P082ProfileObservationTail].
  assert (Hrestsum : 0 <= fold_right Z.add 0 rest).
  { clear -Hpositive_tail. induction rest as [|x xs IH]; simpl; [lia|].
    inversion Hpositive_tail as [|? ? Hx Hxs]. subst.
    specialize (IH Hxs). lia. }
  repeat split.
  - lia.
  - simpl. lia.
  - rewrite P082_Znth_app_left.
    + apply P082InternalObservation_last. lia.
    + rewrite P082InternalObservation_length by lia. lia.
  - replace (first - 1 + 1) with first by lia.
    rewrite P082_Znth_app_right.
    + rewrite P082InternalObservation_length by lia.
      replace (first - first) with 0 by lia.
      apply P082ProfileObservationTail_first. exact Hsecond.
    + rewrite P082InternalObservation_length by lia. lia.
  - intros q Hq [Hq1 Hq2].
    rewrite P082_Znth_app_left in Hq1.
    2: { rewrite P082InternalObservation_length by lia. lia. }
    rewrite P082_Znth_app_left in Hq2.
    2: { rewrite P082InternalObservation_length by lia. lia. }
    assert (first = 1 \/ 3 <= first) by lia.
    destruct H as [Hone|Hthree].
    + lia.
    + eapply P082InternalObservation_no_adjacent_ones; eauto.
Qed.

Lemma P082IncreasingObservation_has_no_first_pair : forall len boundary,
  1 <= len ->
  ~ P082FirstOnePair (P082IncreasingObservation len) boundary.
Proof.
  intros len boundary Hlen
    [Hboundary [Hbound [Hone1 [Hone2 Hminimal]]]].
  rewrite P082IncreasingObservation_length in Hbound by lia.
  eapply (P082IncreasingObservation_no_adjacent_ones len boundary);
    [lia|lia|]. split; assumption.
Qed.

Lemma P082ProfileObservationTail_equal_first : forall
    first1 second1 rest1 first2 second2 rest2,
  Forall (fun x => 1 <= x) (first1 :: second1 :: rest1) ->
  Forall (fun x => 1 <= x) (first2 :: second2 :: rest2) ->
  first1 <> 2 -> first2 <> 2 ->
  P082ProfileObservationTail (first1 :: second1 :: rest1) =
  P082ProfileObservationTail (first2 :: second2 :: rest2) ->
  first1 = first2.
Proof.
  intros first1 second1 rest1 first2 second2 rest2
    Hpositive1 Hpositive2 Hnot1 Hnot2 Heq.
  pose proof (P082ProfileObservationTail_first_pair
    first1 second1 rest1 Hpositive1 Hnot1) as Hpair1.
  pose proof (P082ProfileObservationTail_first_pair
    first2 second2 rest2 Hpositive2 Hnot2) as Hpair2.
  rewrite Heq in Hpair1.
  pose proof (P082FirstOnePair_unique _ _ _ Hpair1 Hpair2).
  lia.
Qed.

Lemma P082ProfileObservationTail_multi_not_single : forall
    first second rest last,
  Forall (fun x => 1 <= x) (first :: second :: rest) ->
  1 <= last -> first <> 2 ->
  P082ProfileObservationTail (first :: second :: rest) <>
  P082ProfileObservationTail (last :: nil).
Proof.
  intros first second rest last Hpositive Hlast Hnot Heq.
  pose proof (P082ProfileObservationTail_first_pair
    first second rest Hpositive Hnot) as Hpair.
  rewrite Heq in Hpair. simpl in Hpair.
  eapply P082IncreasingObservation_has_no_first_pair; eauto.
Qed.

Definition P082CanonicalTail (parts : list Z) : Prop :=
  Forall (fun x => 1 <= x) parts /\
  forall t, 0 <= t < Zlength parts - 1 -> Znth t parts 0 <> 2.

Lemma P082CanonicalTail_rest : forall first rest,
  rest <> nil -> P082CanonicalTail (first :: rest) ->
  first <> 2 /\ P082CanonicalTail rest.
Proof.
  intros first rest Hrest [Hpositive Hno2].
  inversion Hpositive as [|? ? Hfirst Hpositive_rest]. subst.
  assert (Hrestlength : 0 < Zlength rest).
  { rewrite Zlength_correct. destruct rest; [contradiction|]. simpl. lia. }
  split.
  - intro Htwo. apply (Hno2 0).
    + rewrite Zlength_cons. lia.
    + rewrite Znth0_cons. exact Htwo.
  - split; [exact Hpositive_rest|]. intros t Ht.
    specialize (Hno2 (t + 1)).
    rewrite Znth_cons in Hno2 by lia.
    replace (t + 1 - 1) with t in Hno2 by lia.
    apply Hno2. rewrite Zlength_cons. lia.
Qed.

Lemma P082_positive_sum_nonempty : forall parts,
  parts <> nil -> Forall (fun x => 1 <= x) parts ->
  1 <= fold_right Z.add 0 parts.
Proof.
  intros [|x xs] Hnonempty Hpositive; [contradiction|].
  inversion Hpositive as [|? ? Hx Hxs]. subst.
  assert (Hsum : 0 <= fold_right Z.add 0 xs).
  { clear -Hxs. induction xs as [|y ys IH]; simpl; [lia|].
    inversion Hxs as [|? ? Hy Hys]. subst. specialize (IH Hys). lia. }
  simpl. lia.
Qed.

Lemma P082ProfileObservationTail_nonempty : forall parts,
  parts <> nil -> Forall (fun x => 1 <= x) parts ->
  P082ProfileObservationTail parts <> nil.
Proof.
  intros parts Hparts Hpositive Hnil.
  pose proof (P082ProfileObservationTail_length parts) as Hlength.
  assert (Hnonneg : Forall (fun x => 0 <= x) parts).
  { apply Forall_impl with (P := fun x => 1 <= x); [intros; lia|assumption]. }
  specialize (Hlength Hnonneg). rewrite Hnil, Zlength_nil in Hlength.
  pose proof (P082_positive_sum_nonempty parts Hparts Hpositive). lia.
Qed.

Lemma P082ProfileObservationTail_injective : forall parts1 parts2,
  P082CanonicalTail parts1 -> P082CanonicalTail parts2 ->
  P082ProfileObservationTail parts1 = P082ProfileObservationTail parts2 ->
  parts1 = parts2.
Proof.
  induction parts1 as [|first1 rest1 IH]; intros parts2 Hcan1 Hcan2 Heq.
  - destruct parts2 as [|first2 rest2]; [reflexivity|].
    exfalso.
    pose proof (P082ProfileObservationTail_nonempty
      (first2 :: rest2) ltac:(discriminate) (proj1 Hcan2)) as Hnonempty.
    apply Hnonempty. symmetry. exact Heq.
  - destruct parts2 as [|first2 rest2].
    + exfalso.
      pose proof (P082ProfileObservationTail_nonempty
        (first1 :: rest1) ltac:(discriminate) (proj1 Hcan1)) as Hnonempty.
      apply Hnonempty. exact Heq.
    + destruct rest1 as [|second1 tail1].
      * destruct rest2 as [|second2 tail2].
        -- simpl in Heq. f_equal.
           pose proof (f_equal (@Zlength Z) Heq) as Hlength.
           rewrite !P082IncreasingObservation_length in Hlength.
           ++ exact Hlength.
           ++ pose proof (proj1 Hcan2) as Hpositive2.
              inversion Hpositive2. lia.
           ++ pose proof (proj1 Hcan1) as Hpositive1.
              inversion Hpositive1. lia.
        -- exfalso.
           pose proof (P082CanonicalTail_rest first2
             (second2 :: tail2) ltac:(discriminate) Hcan2) as [Hnot2 Htailcan2].
           apply (P082ProfileObservationTail_multi_not_single
             first2 second2 tail2 first1 (proj1 Hcan2)).
           ++ pose proof (proj1 Hcan1) as Hpositive1.
              inversion Hpositive1. lia.
           ++ exact Hnot2.
           ++ symmetry. exact Heq.
      * destruct rest2 as [|second2 tail2].
        -- exfalso.
           pose proof (P082CanonicalTail_rest first1
             (second1 :: tail1) ltac:(discriminate) Hcan1) as [Hnot1 Htailcan1].
           eapply (P082ProfileObservationTail_multi_not_single
             first1 second1 tail1 first2 (proj1 Hcan1)); eauto.
           pose proof (proj1 Hcan2) as Hpositive2.
           inversion Hpositive2. lia.
        -- pose proof (P082CanonicalTail_rest first1
             (second1 :: tail1) ltac:(discriminate) Hcan1) as [Hnot1 Hrestcan1].
           pose proof (P082CanonicalTail_rest first2
             (second2 :: tail2) ltac:(discriminate) Hcan2) as [Hnot2 Hrestcan2].
           assert (Hfirst : first1 = first2).
           { eapply P082ProfileObservationTail_equal_first; eauto.
             - exact (proj1 Hcan1).
             - exact (proj1 Hcan2). }
           subst first2. f_equal.
           apply IH; [exact Hrestcan1|exact Hrestcan2|].
           cbn [P082ProfileObservationTail] in Heq.
           apply app_inv_head in Heq. exact Heq.
Qed.

Lemma P082CanonicalProfile_tail : forall n k first rest,
  P082CanonicalProfile n k (first :: rest) ->
  P082CanonicalTail rest.
Proof.
  intros n k first rest [_ [_ [Hpositive Hno2]]].
  inversion Hpositive as [|? ? Hfirst Hpositive_rest]. subst.
  split.
  - apply Forall_impl with (P := fun x => 1 <= x <= n);
      [intros; lia|exact Hpositive_rest].
  - intros t Ht.
  specialize (Hno2 (t + 1)).
  rewrite Znth_cons in Hno2 by lia.
  replace (t + 1 - 1) with t in Hno2 by lia.
  apply Hno2. rewrite Zlength_cons. lia.
Qed.

Lemma P082CanonicalProfile_observation_injective : forall n k parts1 parts2,
  2 <= k ->
  P082CanonicalProfile n k parts1 ->
  P082CanonicalProfile n k parts2 ->
  P082ProfileObservation parts1 = P082ProfileObservation parts2 ->
  parts1 = parts2.
Proof.
  intros n k parts1 parts2 Hk Hcan1 Hcan2 Heq.
  destruct parts1 as [|first1 rest1].
  { destruct Hcan1 as [_ [Hlength _]]. rewrite Zlength_nil in Hlength. lia. }
  destruct rest1 as [|second1 tail1].
  { destruct Hcan1 as [_ [Hlength _]].
    rewrite Zlength_cons, Zlength_nil in Hlength. lia. }
  destruct parts2 as [|first2 rest2].
  { destruct Hcan2 as [_ [Hlength _]]. rewrite Zlength_nil in Hlength. lia. }
  destruct rest2 as [|second2 tail2].
  { destruct Hcan2 as [_ [Hlength _]].
    rewrite Zlength_cons, Zlength_nil in Hlength. lia. }
  pose proof (proj1 (proj2 (proj2 Hcan1))) as Hpositive1.
  pose proof (proj1 (proj2 (proj2 Hcan2))) as Hpositive2.
  inversion Hpositive1 as [|? ? Hfirst1 Hpositive_rest1]. subst.
  inversion Hpositive2 as [|? ? Hfirst2 Hpositive_rest2]. subst.
  destruct Hfirst1 as [Hfirst1 Hfirst1_bound].
  destruct Hfirst2 as [Hfirst2 Hfirst2_bound].
  pose proof (P082ProfileObservation_equal_first_tail
    first1 second1 tail1 first2 second2 tail2
    Hfirst1 Hfirst2 Heq) as [Hfirst Htail].
  subst first2. f_equal.
  apply P082ProfileObservationTail_injective; [| |exact Htail].
  - apply (P082CanonicalProfile_tail n k first1 (second1 :: tail1)).
    exact Hcan1.
  - apply (P082CanonicalProfile_tail n k first1 (second2 :: tail2)).
    exact Hcan2.
Qed.

Definition P082CanonicalObservation (n k : Z) (b : list Z) : Prop :=
  exists parts,
    P082CanonicalProfile n k parts /\
    b = P082ProfileObservation parts.

Lemma P082DistanceArray_output_carrier : forall n a b,
  Zlength a = n -> DistanceArray a b ->
  Zlength b = n /\ Forall (fun d => 0 <= d < n) b.
Proof.
  intros n a b Hlength Hdistance. split.
  - pose proof Hdistance as [Hblength _]. lia.
  - apply Forall_forall. intros d Hin.
    destruct (P082In_has_Znth_witness d b Hin) as [i [Hi Hid]].
    pose proof Hdistance as [Hblength Hentries].
    assert (Hia : 0 <= i < Zlength a) by lia.
    rewrite <- Hid. split.
    + apply Z.lt_le_incl.
      exact (P082DistanceArray_entry_positive a b i Hdistance Hia).
    + rewrite <- Hlength.
      exact (P082DistanceArray_entry_bounded a b i Hdistance Hia).
Qed.

Lemma P082Spec_carrier_iff_canonical_observation : forall n k b,
  2 <= n -> 2 <= k ->
  ((Zlength b = n /\ Forall (fun d => 0 <= d < n) b) /\
    exists a, Zlength a = n /\ UsesEveryValue k a /\ DistanceArray a b) <->
  P082CanonicalObservation n k b.
Proof.
  intros n k b Hn Hk. split.
  - intros [_ [a [Hlength [Huses Hdistance]]]].
    set (raw := P082OrderedBlockLengths (P082ComputedBlocks a)).
    set (parts := P082NormalizeProfile raw).
    exists parts. split.
    + apply P082UsesEveryValue_normalized_computed_profile;
        [lia|exact Hlength|lia|exact Huses].
    + assert (Hblocks : 2 <= Zlength (P082ComputedBlocks a)).
      { pose proof (P082UsesEveryValue_computed_blocks_count
          k a ltac:(lia) Huses). lia. }
      pose proof (P082DistanceArray_computed_profile_observation
        a b Hblocks Hdistance) as Hobservation.
      unfold raw, parts.
      rewrite P082ProfileObservation_normalize.
      exact Hobservation.
  - intros [parts [Hcanonical Hb]]. subst b.
    destruct Hcanonical as [Hsum [Hcount [Hbounds Hno2]]].
    assert (Hpositive : Forall (fun x => 1 <= x) parts).
    { apply Forall_impl with (P := fun x => 1 <= x <= n);
        [intros; lia|exact Hbounds]. }
    assert (Hnonnegative : Forall (fun x => 0 <= x) parts).
    { apply Forall_impl with (P := fun x => 1 <= x);
        [intros; lia|exact Hpositive]. }
    assert (Htwo : 2 <= Zlength parts) by lia.
    set (a := P082RealizeProfile k parts).
    assert (Halength : Zlength a = n).
    { unfold a. rewrite P082RealizeProfile_length by exact Hnonnegative.
      exact Hsum. }
    assert (Hauses : UsesEveryValue k a).
    { unfold a. apply P082RealizeProfile_UsesEveryValue;
        [lia|exact Hcount|exact Hpositive]. }
    assert (Hadistance : DistanceArray a (P082ProfileObservation parts)).
    { unfold a. apply P082RealizeProfile_DistanceArray;
        [exact Hk|exact Hpositive|exact Htwo]. }
    split.
    + apply P082DistanceArray_output_carrier with a; assumption.
    + exists a. split; [exact Halength|].
      split; [exact Hauses|exact Hadistance].
Qed.

Lemma P082CanonicalObservation_unique_profile : forall n k b parts1 parts2,
  2 <= k ->
  P082CanonicalProfile n k parts1 ->
  P082CanonicalProfile n k parts2 ->
  b = P082ProfileObservation parts1 ->
  b = P082ProfileObservation parts2 ->
  parts1 = parts2.
Proof.
  intros n k b parts1 parts2 Hk Hcan1 Hcan2 Hb1 Hb2.
  apply (P082CanonicalProfile_observation_injective
    n k parts1 parts2 Hk Hcan1 Hcan2).
  congruence.
Qed.

Lemma P082Spec_carrier_iff_unique_profile : forall n k b,
  2 <= n -> 2 <= k ->
  ((Zlength b = n /\ Forall (fun d => 0 <= d < n) b) /\
    exists a, Zlength a = n /\ UsesEveryValue k a /\ DistanceArray a b) <->
  exists! parts,
    P082CanonicalProfile n k parts /\
    b = P082ProfileObservation parts.
Proof.
  intros n k b Hn Hk. split.
  - intro Hcarrier.
    apply (proj1 (P082Spec_carrier_iff_canonical_observation
      n k b Hn Hk)) in Hcarrier.
    destruct Hcarrier as [parts [Hcanonical Hb]].
    exists parts. split.
    + exact (conj Hcanonical Hb).
    + intros other [Hother Hbother].
      eapply P082CanonicalObservation_unique_profile; eauto.
  - intros [parts [[Hcanonical Hb] Hunique]].
    apply (proj2 (P082Spec_carrier_iff_canonical_observation
      n k b Hn Hk)).
    exists parts. split; assumption.
Qed.

Lemma P082CanonicalProfile_to_CoreComposition : forall n k parts,
  P082CanonicalProfile n k parts ->
  Znth (Zlength parts - 1) parts 0 <> 2 ->
  P082CoreComposition n (Zlength parts) parts.
Proof.
  intros n k parts [Hsum [Hcount [Hbounds Hinternal]]] Hlast.
  unfold P082CoreComposition, P082CoreCarrier.
  split.
  - split; [reflexivity|].
    apply Forall_impl with (P := fun x => 1 <= x <= n);
      [intros; lia|exact Hbounds].
  - split; [exact Hsum|]. intros t Ht.
    destruct (Z_lt_ge_dec t (Zlength parts - 1)) as [Hbefore|Hfinal].
    + apply Hinternal. lia.
    + assert (t = Zlength parts - 1) by lia. subst t. exact Hlast.
Qed.

Lemma P082_positive_member_le_sum : forall parts x,
  Forall (fun y => 1 <= y) parts -> In x parts ->
  x <= fold_right Z.add 0 parts.
Proof.
  intros parts x Hpositive Hin. induction Hpositive as [|y ys Hy Hys IH].
  - contradiction.
  - simpl in Hin |- *. destruct Hin as [Heq|Hin].
    + subst y. assert (0 <= fold_right Z.add 0 ys).
      { clear -Hys. induction Hys; simpl; lia. } lia.
    + specialize (IH Hin). lia.
Qed.

Lemma P082CanonicalProfile_terminal_two_core : forall n k core,
  P082CanonicalProfile n k (core ++ 2 :: nil) ->
  P082CoreComposition (n - 2) (Zlength core) core.
Proof.
  intros n k core [Hsum [Hcount [Hbounds Hinternal]]].
  assert (Hpositive_all : Forall (fun x => 1 <= x) (core ++ 2 :: nil)).
  { apply Forall_impl with (P := fun x => 1 <= x <= n);
      [intros; lia|exact Hbounds]. }
  apply Forall_app in Hpositive_all as [Hpositive_core Hpositive_last].
  assert (Hcoresum : fold_right Z.add 0 core = n - 2).
  { rewrite fold_right_app in Hsum. simpl in Hsum.
    assert (Hacc : forall xs acc,
      fold_right Z.add acc xs = fold_right Z.add 0 xs + acc).
    { induction xs as [|x xs IH]; intros acc; simpl; [lia|].
      rewrite IH. lia. }
    rewrite Hacc in Hsum. lia. }
  unfold P082CoreComposition, P082CoreCarrier. split.
  - split; [reflexivity|]. apply Forall_forall. intros x Hin.
    split.
    + apply Forall_forall with (x := x) in Hpositive_core; assumption.
    + pose proof (P082_positive_member_le_sum core x Hpositive_core Hin).
      lia.
  - split; [exact Hcoresum|]. intros t Ht.
    assert (Hnot := Hinternal t ltac:(
      rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)).
    intro Htwo. apply Hnot.
    rewrite P082_Znth_app_left.
    + exact Htwo.
    + lia.
Qed.

Lemma P082_Znth_last_nonempty : forall (A : Type) (xs : list A) d,
  xs <> nil -> Znth (Zlength xs - 1) xs d = last xs d.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros d Hnonempty;
    [contradiction|].
  destruct xs as [|y ys].
  - simpl. rewrite Znth0_cons. reflexivity.
  - rewrite Zlength_cons.
    rewrite Znth_cons by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg ys); lia).
    replace (Z.succ (Zlength (y :: ys)) - 1 - 1)
      with (Zlength (y :: ys) - 1) by lia.
    change (Znth (Zlength (y :: ys) - 1) (y :: ys) d = last (y :: ys) d).
    apply IH. discriminate.
Qed.

Lemma P082_Zlength_removelast_nonempty : forall (A : Type) (xs : list A),
  xs <> nil -> Zlength (removelast xs) = Zlength xs - 1.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros Hnonempty;
    [contradiction|].
  destruct xs as [|y ys]; [reflexivity|].
  change (Zlength (x :: removelast (y :: ys)) =
    Zlength (x :: y :: ys) - 1).
  repeat rewrite Zlength_cons. rewrite IH by discriminate.
  rewrite Zlength_cons. lia.
Qed.

Lemma P082_positive_length_le_sum : forall parts,
  Forall (fun x => 1 <= x) parts ->
  Zlength parts <= fold_right Z.add 0 parts.
Proof.
  intros parts Hpositive. induction Hpositive.
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. simpl. lia.
Qed.

Lemma P082CanonicalProfile_partition : forall n k parts,
  2 <= k -> P082CanonicalProfile n k parts ->
  (exists runs,
      k <= runs <= n /\ P082CoreComposition n runs parts) \/
  (exists runs core,
      k - 1 <= runs <= n - 2 /\
      parts = core ++ 2 :: nil /\
      P082CoreComposition (n - 2) runs core).
Proof.
  intros n k parts Hk Hcanonical.
  destruct Hcanonical as [Hsum [Hcount [Hbounds Hinternal]]].
  assert (Hpositive : Forall (fun x => 1 <= x) parts).
  { apply Forall_impl with (P := fun x => 1 <= x <= n);
      [intros; lia|exact Hbounds]. }
  assert (Hnonempty : parts <> nil).
  { intro Hnil. subst parts. rewrite Zlength_nil in Hcount. lia. }
  pose proof (P082_positive_length_le_sum parts Hpositive) as Hrunupper.
  rewrite Hsum in Hrunupper.
  destruct (Z.eq_dec (last parts 0) 2) as [Hlasttwo|Hlastnot].
  - right. exists (Zlength parts - 1), (removelast parts).
    assert (Hdecomp : parts = removelast parts ++ 2 :: nil).
    { pose proof (app_removelast_last 0 Hnonempty) as Hdecomp.
      rewrite Hlasttwo in Hdecomp. exact Hdecomp. }
    assert (Hcore : P082CoreComposition (n - 2)
      (Zlength (removelast parts)) (removelast parts)).
    { apply (P082CanonicalProfile_terminal_two_core
        n k (removelast parts)).
      rewrite <- Hdecomp. repeat split; assumption. }
    split.
    + split; [lia|].
      pose proof Hcore as [[Hcorelen Hcorebounds] [Hcoresum Hcoreno2]].
      assert (Hcorepositive : Forall (fun x => 1 <= x) (removelast parts)).
      { apply Forall_impl with (P := fun x => 1 <= x < n - 2 + 1);
          [intros; lia|exact Hcorebounds]. }
      pose proof (P082_positive_length_le_sum
        (removelast parts) Hcorepositive) as Hlen.
      rewrite Hcoresum in Hlen.
      rewrite P082_Zlength_removelast_nonempty in Hlen by exact Hnonempty.
      exact Hlen.
    + split; [exact Hdecomp|].
      rewrite <- (P082_Zlength_removelast_nonempty Z parts Hnonempty).
      exact Hcore.
  - left. exists (Zlength parts). split.
    + lia.
    + apply (P082CanonicalProfile_to_CoreComposition n k parts).
      * repeat split; assumption.
      * rewrite P082_Znth_last_nonempty by exact Hnonempty. exact Hlastnot.
Qed.

Lemma P082CanonicalProfile_partition_iff : forall n k parts,
  2 <= n -> 2 <= k ->
  P082CanonicalProfile n k parts <->
  (exists runs,
      k <= runs <= n /\ P082CoreComposition n runs parts) \/
  (exists runs core,
      k - 1 <= runs <= n - 2 /\
      parts = core ++ 2 :: nil /\
      P082CoreComposition (n - 2) runs core).
Proof.
  intros n k parts Hn Hk. split.
  - apply P082CanonicalProfile_partition. exact Hk.
  - intros [[runs [[Hkruns Hrunsn] Hcore]]|
      [runs [core [[Hkruns Hrunsn] [Hparts Hcore]]]]].
    + apply (P082CoreComposition_is_CanonicalProfile n k runs parts);
        [lia|exact Hkruns|exact Hcore].
    + subst parts.
      apply (P082CoreComposition_snoc_two_is_CanonicalProfile
        n k runs core); [exact Hn|lia|exact Hcore].
Qed.

(** A concrete enumeration of the two disjoint profile classes isolated by
    [P082CanonicalProfile_partition_iff].  These definitions deliberately use
    the very same core-composition enumerations as the counting recurrence. *)
Definition P082CoreEnum (size runs : Z) : list (list Z) :=
  @enum (list Z) (P082CoreComposition size runs)
    (P082_finite_core_composition size runs).

Definition P082OrdinaryProfileEnum (n k : Z) : list (list Z) :=
  flat_map (fun runs => P082CoreEnum n runs) (Zrange k (n + 1)).

Definition P082TerminalProfileEnum (n k : Z) : list (list Z) :=
  flat_map
    (fun runs => map (fun core => core ++ 2 :: nil)
      (P082CoreEnum (n - 2) runs))
    (Zrange (k - 1) (n - 1)).

Definition P082CanonicalProfileEnum (n k : Z) : list (list Z) :=
  P082OrdinaryProfileEnum n k ++ P082TerminalProfileEnum n k.

Lemma P082CoreEnum_ok : forall size runs parts,
  In parts (P082CoreEnum size runs) <->
  P082CoreComposition size runs parts.
Proof.
  intros size runs parts. unfold P082CoreEnum.
  symmetry. apply enum_ok.
Qed.

Lemma P082OrdinaryProfileEnum_ok : forall n k parts,
  In parts (P082OrdinaryProfileEnum n k) <->
  exists runs, k <= runs <= n /\ P082CoreComposition n runs parts.
Proof.
  intros n k parts. unfold P082OrdinaryProfileEnum.
  rewrite in_flat_map. split.
  - intros [runs [Hruns Hparts]]. exists runs. split.
    + apply In_Zrange in Hruns. lia.
    + apply P082CoreEnum_ok. exact Hparts.
  - intros [runs [[Hlow Hhigh] Hparts]]. exists runs. split.
    + apply In_Zrange. lia.
    + apply P082CoreEnum_ok. exact Hparts.
Qed.

Lemma P082TerminalProfileEnum_ok : forall n k parts,
  In parts (P082TerminalProfileEnum n k) <->
  exists runs core,
    k - 1 <= runs <= n - 2 /\
    parts = core ++ 2 :: nil /\
    P082CoreComposition (n - 2) runs core.
Proof.
  intros n k parts. unfold P082TerminalProfileEnum.
  rewrite in_flat_map. split.
  - intros [runs [Hruns Hparts]].
    apply in_map_iff in Hparts as [core [Hparts Hcore]].
    exists runs, core. split.
    + apply In_Zrange in Hruns. lia.
    + split; [symmetry; exact Hparts|].
      apply P082CoreEnum_ok. exact Hcore.
  - intros [runs [core [[Hlow Hhigh] [Hparts Hcore]]]].
    exists runs. split.
    + apply In_Zrange. lia.
    + apply in_map_iff. exists core. split.
      * symmetry. exact Hparts.
      * apply P082CoreEnum_ok. exact Hcore.
Qed.

Lemma P082CanonicalProfileEnum_ok : forall n k parts,
  2 <= n -> 2 <= k ->
  In parts (P082CanonicalProfileEnum n k) <->
  P082CanonicalProfile n k parts.
Proof.
  intros n k parts Hn Hk. unfold P082CanonicalProfileEnum.
  rewrite in_app_iff, P082OrdinaryProfileEnum_ok,
    P082TerminalProfileEnum_ok.
  symmetry. apply P082CanonicalProfile_partition_iff; assumption.
Qed.

Lemma P082_NoDup_flat_map_disjoint : forall
    (I A : Type) (indices : list I) (fibers : I -> list A),
  NoDup indices ->
  (forall i, In i indices -> NoDup (fibers i)) ->
  (forall i j, In i indices -> In j indices -> i <> j ->
    forall x, In x (fibers i) -> ~ In x (fibers j)) ->
  NoDup (flat_map fibers indices).
Proof.
  intros I A indices. induction indices as [|i indices IH];
    intros fibers Hindices Hfiber Hdisjoint; simpl.
  - constructor.
  - inversion Hindices as [|? ? Hnotin Htail]; subst.
    apply NoDup_app. repeat split.
    + apply Hfiber. left. reflexivity.
    + apply IH.
      * exact Htail.
      * intros j Hj. apply Hfiber. right. exact Hj.
      * intros j l Hj Hl Hjl x Hx.
        exact (Hdisjoint j l (or_intror Hj) (or_intror Hl) Hjl x Hx).
    + intros x Hxi Hxrest.
      apply in_flat_map in Hxrest as [j [Hj Hxj]].
      exact (Hdisjoint i j (or_introl eq_refl) (or_intror Hj)
        ltac:(intro Heq; subst j; contradiction) x Hxi Hxj).
Qed.

Lemma P082_NoDup_map_injective : forall (A B : Type) (f : A -> B) xs,
  NoDup xs ->
  (forall x y, f x = f y -> x = y) ->
  NoDup (map f xs).
Proof.
  intros A B f xs Hnodup Hinjective.
  induction Hnodup as [|x xs Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin as [y [Heq Hy]].
      apply Hnotin. replace x with y; [exact Hy|].
      apply Hinjective. exact Heq.
    + exact IH.
Qed.

Lemma P082CoreComposition_runs_unique : forall size runs1 runs2 parts,
  P082CoreComposition size runs1 parts ->
  P082CoreComposition size runs2 parts ->
  runs1 = runs2.
Proof.
  intros size runs1 runs2 parts [[Hlen1 _] _] [[Hlen2 _] _].
  lia.
Qed.

Lemma P082CoreEnum_nodup : forall size runs,
  NoDup (P082CoreEnum size runs).
Proof.
  intros. unfold P082CoreEnum. apply enum_nodup.
Qed.

Lemma P082OrdinaryProfileEnum_nodup : forall n k,
  NoDup (P082OrdinaryProfileEnum n k).
Proof.
  intros n k. unfold P082OrdinaryProfileEnum.
  apply P082_NoDup_flat_map_disjoint.
  - apply NoDup_Zrange.
  - intros runs Hruns. apply P082CoreEnum_nodup.
  - intros runs1 runs2 Hruns1 Hruns2 Hneq parts Hparts1 Hparts2.
    apply Hneq. eapply P082CoreComposition_runs_unique.
    + apply P082CoreEnum_ok. exact Hparts1.
    + apply P082CoreEnum_ok. exact Hparts2.
Qed.

Lemma P082_snoc_two_injective : forall xs ys : list Z,
  xs ++ 2 :: nil = ys ++ 2 :: nil -> xs = ys.
Proof.
  intros xs ys Heq. apply app_inv_tail in Heq. exact Heq.
Qed.

Lemma P082TerminalProfileEnum_nodup : forall n k,
  NoDup (P082TerminalProfileEnum n k).
Proof.
  intros n k. unfold P082TerminalProfileEnum.
  apply P082_NoDup_flat_map_disjoint.
  - apply NoDup_Zrange.
  - intros runs Hruns. apply P082_NoDup_map_injective.
    + apply P082CoreEnum_nodup.
    + intros xs ys Heq. apply P082_snoc_two_injective. exact Heq.
  - intros runs1 runs2 Hruns1 Hruns2 Hneq parts Hparts1 Hparts2.
    apply in_map_iff in Hparts1 as [core1 [Heq1 Hcore1]].
    apply in_map_iff in Hparts2 as [core2 [Heq2 Hcore2]].
    apply Hneq.
    assert (Hcores : core1 = core2).
    { apply P082_snoc_two_injective. congruence. }
    subst core2. eapply P082CoreComposition_runs_unique.
    + apply P082CoreEnum_ok. exact Hcore1.
    + apply P082CoreEnum_ok. exact Hcore2.
Qed.

Lemma P082_snoc_two_last : forall core,
  Znth (Zlength (core ++ 2 :: nil) - 1) (core ++ 2 :: nil) 0 = 2.
Proof.
  intros core. rewrite P082_Znth_last_nonempty.
  - rewrite last_last. reflexivity.
  - destruct core; discriminate.
Qed.

Lemma P082CoreComposition_last_not_two : forall size runs parts,
  2 <= runs -> P082CoreComposition size runs parts ->
  Znth (Zlength parts - 1) parts 0 <> 2.
Proof.
  intros size runs parts Hruns [[Hlength Hbounds] [Hsum Hno2]].
  apply Hno2. lia.
Qed.

Lemma P082OrdinaryTerminalProfileEnum_disjoint : forall n k parts,
  2 <= k ->
  In parts (P082OrdinaryProfileEnum n k) ->
  ~ In parts (P082TerminalProfileEnum n k).
Proof.
  intros n k parts Hk Hordinary Hterminal.
  apply P082OrdinaryProfileEnum_ok in Hordinary as
    [runs [[Hkruns Hrunsn] Hcore]].
  apply P082TerminalProfileEnum_ok in Hterminal as
    [runs' [core' [Hruns' [Hparts Hcore']]]].
  pose proof (P082CoreComposition_last_not_two n runs parts
    ltac:(lia) Hcore) as Hnot.
  subst parts. apply Hnot. apply P082_snoc_two_last.
Qed.

Lemma P082CanonicalProfileEnum_nodup : forall n k,
  2 <= k -> NoDup (P082CanonicalProfileEnum n k).
Proof.
  intros n k Hk. unfold P082CanonicalProfileEnum.
  apply NoDup_app. repeat split.
  - apply P082OrdinaryProfileEnum_nodup.
  - apply P082TerminalProfileEnum_nodup.
  - intros parts Hordinary Hterminal.
    eapply P082OrdinaryTerminalProfileEnum_disjoint; eauto.
Qed.

Definition P082_finite_canonical_profile (n k : Z)
    (Hn : 2 <= n) (Hk : 2 <= k) :
  Finite (P082CanonicalProfile n k).
Proof.
  refine {| enum := P082CanonicalProfileEnum n k |}.
  - intros parts. symmetry. apply P082CanonicalProfileEnum_ok; assumption.
  - apply P082CanonicalProfileEnum_nodup. exact Hk.
Defined.

Definition P082Ones {A : Type} (xs : list A) : Z :=
  fold_right (fun _ acc => 1 + acc) 0 xs.

Lemma P082Ones_app : forall (A : Type) (xs ys : list A),
  P082Ones (xs ++ ys) = P082Ones xs + P082Ones ys.
Proof.
  intros A xs ys. unfold P082Ones. rewrite fold_right_app.
  assert (Hacc : forall zs acc,
    fold_right (fun _ : A => fun acc : Z => 1 + acc) acc zs =
    fold_right (fun _ : A => fun acc : Z => 1 + acc) 0 zs + acc).
  { intros zs. induction zs as [|z zs IH]; intros acc.
    - reflexivity.
    - change (1 + fold_right (fun _ : A => fun a : Z => 1 + a) acc zs =
        1 + fold_right (fun _ : A => fun a : Z => 1 + a) 0 zs + acc).
      rewrite IH. lia. }
  rewrite Hacc. reflexivity.
Qed.

Lemma P082Ones_map : forall (A B : Type) (f : A -> B) xs,
  P082Ones (map f xs) = P082Ones xs.
Proof.
  intros A B f xs. unfold P082Ones. induction xs as [|x xs IH].
  - reflexivity.
  - change (1 + fold_right (fun _ : B => fun a : Z => 1 + a) 0
      (map f xs) =
      1 + fold_right (fun _ : A => fun a : Z => 1 + a) 0 xs).
    rewrite IH. reflexivity.
Qed.

Lemma P082Ones_flat_map : forall (I A : Type) (fibers : I -> list A) indices,
  P082Ones (flat_map fibers indices) =
  fold_right (fun i acc => P082Ones (fibers i) + acc) 0 indices.
Proof.
  intros I A fibers indices. induction indices as [|i indices IH]; simpl.
  - reflexivity.
  - rewrite P082Ones_app, IH. reflexivity.
Qed.

Lemma P082CoreEnum_count : forall size runs,
  P082Ones (P082CoreEnum size runs) = P082ExactCoreCount size runs.
Proof.
  intros size runs.
  unfold P082Ones, P082CoreEnum, P082ExactCoreCount, set_card, sum.
  reflexivity.
Qed.

Lemma P082OrdinaryProfileEnum_count : forall n k,
  P082Ones (P082OrdinaryProfileEnum n k) =
  P082SaturatedCoreCount n k.
Proof.
  intros n k. unfold P082OrdinaryProfileEnum.
  rewrite P082Ones_flat_map.
  unfold P082SaturatedCoreCount, sum_range.
  rewrite sum_range_unfold.
  induction (Zrange k (n + 1)) as [|runs indices IH]; simpl.
  - reflexivity.
  - rewrite P082CoreEnum_count, IH. reflexivity.
Qed.

Lemma P082TerminalProfileEnum_count : forall n k,
  P082Ones (P082TerminalProfileEnum n k) =
  P082SaturatedCoreCount (n - 2) (k - 1).
Proof.
  intros n k. unfold P082TerminalProfileEnum.
  rewrite P082Ones_flat_map.
  unfold P082SaturatedCoreCount, sum_range.
  rewrite sum_range_unfold.
  replace (n - 2 + 1) with (n - 1) by lia.
  induction (Zrange (k - 1) (n - 1)) as [|runs indices IH]; simpl.
  - reflexivity.
  - rewrite P082Ones_map, P082CoreEnum_count, IH. reflexivity.
Qed.

Lemma P082CanonicalProfileEnum_count : forall n k,
  P082Ones (P082CanonicalProfileEnum n k) =
  P082SaturatedCoreCount n k +
  P082SaturatedCoreCount (n - 2) (k - 1).
Proof.
  intros n k. unfold P082CanonicalProfileEnum.
  rewrite P082Ones_app, P082OrdinaryProfileEnum_count,
    P082TerminalProfileEnum_count. reflexivity.
Qed.

Lemma P082ExactCoreCount_zero_too_many : forall size runs,
  size < runs -> P082ExactCoreCount size runs = 0.
Proof.
  intros size runs Htoo.
  rewrite <- P082CoreEnum_count.
  destruct (P082CoreEnum size runs) as [|parts rest] eqn:Henum.
  - reflexivity.
  - exfalso.
    assert (Hin : In parts (P082CoreEnum size runs)).
    { rewrite Henum. left. reflexivity. }
    apply P082CoreEnum_ok in Hin as [[Hlength Hbounds] [Hsum Hno2]].
    assert (Hpositive : Forall (fun x => 1 <= x) parts).
    { apply Forall_impl with (P := fun x => 1 <= x < size + 1);
        [intros; lia|exact Hbounds]. }
    pose proof (P082_positive_length_le_sum parts Hpositive).
    lia.
Qed.

Lemma P082TerminalSaturated_split : forall n k,
  k <= n ->
  P082SaturatedCoreCount (n - 2) (k - 1) =
  P082ExactCoreCount (n - 2) (k - 1) +
  P082SaturatedCoreCount (n - 2) k.
Proof.
  intros n k Hkn.
  destruct (proj1 (Z.lt_eq_cases k n) Hkn) as [Hlt|Heq].
  - unfold P082SaturatedCoreCount, sum_range.
    replace (n - 2 + 1) with (n - 1) by lia.
    rewrite sum_Z_range_cons by lia.
    replace (k - 1 + 1) with k by lia. reflexivity.
  - subst k. rewrite P082ExactCoreCount_zero_too_many by lia.
    unfold P082SaturatedCoreCount, sum_range.
    replace (n - 2 + 1) with (n - 1) by lia.
    rewrite !sum_Z_range_empty by lia. lia.
Qed.

Lemma P082CanonicalProfileEnum_answer_count : forall n k,
  k <= n ->
  P082Ones (P082CanonicalProfileEnum n k) =
  P082SaturatedCoreCount n k +
  P082ExactCoreCount (n - 2) (k - 1) +
  P082SaturatedCoreCount (n - 2) k.
Proof.
  intros n k Hkn. rewrite P082CanonicalProfileEnum_count,
    P082TerminalSaturated_split by exact Hkn. lia.
Qed.

Lemma P082CanonicalProfile_cardinality : forall n k Hn Hk,
  k <= n ->
  @set_card (list Z) (P082CanonicalProfile n k)
    (P082_finite_canonical_profile n k Hn Hk) =
  P082SaturatedCoreCount n k +
  P082ExactCoreCount (n - 2) (k - 1) +
  P082SaturatedCoreCount (n - 2) k.
Proof.
  intros n k Hn Hk Hkn.
  unfold set_card, sum. change
    (P082Ones (P082CanonicalProfileEnum n k) =
      P082SaturatedCoreCount n k +
      P082ExactCoreCount (n - 2) (k - 1) +
      P082SaturatedCoreCount (n - 2) k).
  apply P082CanonicalProfileEnum_answer_count. exact Hkn.
Qed.

Lemma P082_NoDup_map_injective_on : forall
    (A B : Type) (P : A -> Prop) (f : A -> B) xs,
  NoDup xs ->
  (forall x, In x xs -> P x) ->
  (forall x y, P x -> P y -> f x = f y -> x = y) ->
  NoDup (map f xs).
Proof.
  intros A B P f xs Hnodup Hall Hinjective.
  induction Hnodup as [|x xs Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin as [y [Heq Hy]].
      assert (Hxy : x = y).
      { apply (Hinjective x y).
        - apply Hall. left. reflexivity.
        - apply Hall. right. exact Hy.
        - symmetry. exact Heq. }
      subst y. contradiction.
    + apply IH.
      intros y Hy. apply Hall. right. exact Hy.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma P082Ones_Zlength : forall (A : Type) (xs : list A),
  P082Ones xs = Zlength xs.
Proof.
  intros A xs. unfold P082Ones. induction xs as [|x xs IH].
  - reflexivity.
  - change (1 + fold_right (fun _ : A => fun a : Z => 1 + a) 0 xs =
      Zlength (x :: xs)).
    rewrite Zlength_cons, IH. lia.
Qed.

Lemma P082Ones_permutation : forall (A : Type) (xs ys : list A),
  Permutation xs ys -> P082Ones xs = P082Ones ys.
Proof.
  intros A xs ys Hperm. rewrite !P082Ones_Zlength, !Zlength_correct.
  f_equal. exact (Permutation_length Hperm).
Qed.

Lemma P082_finite_cardinality_bijection : forall
    (A B : Type) (P : A -> Prop) (Q : B -> Prop)
    (FP : Finite P) (FQ : Finite Q) (f : A -> B),
  (forall x, P x -> Q (f x)) ->
  (forall x y, P x -> P y -> f x = f y -> x = y) ->
  (forall z, Q z -> exists x, P x /\ f x = z) ->
  @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmaps Hinjective Honto.
  unfold set_card, sum. change
    (P082Ones (@enum A P FP) = P082Ones (@enum B Q FQ)).
  rewrite <- (P082Ones_map A B f (@enum A P FP)).
  apply P082Ones_permutation. apply NoDup_Permutation.
  - apply P082_NoDup_map_injective_on with (P := P).
    + exact (@enum_nodup A P FP).
    + intros x Hx. apply (proj2 (@enum_ok A P FP x)). exact Hx.
    + exact Hinjective.
  - exact (@enum_nodup B Q FQ).
  - intros z. rewrite in_map_iff. split.
    + intros [x [Heq Hx]]. apply (proj1 (@enum_ok B Q FQ z)).
      subst z. apply Hmaps. apply (proj2 (@enum_ok A P FP x)). exact Hx.
    + intro Hz. apply (proj2 (@enum_ok B Q FQ z)) in Hz.
      destruct (Honto z Hz) as [x [Hx Heq]]. exists x. split.
      * exact Heq.
      * apply (proj1 (@enum_ok A P FP x)). exact Hx.
Qed.

Lemma P082SpecCarrier_profile_cardinality : forall n k Hn Hk,
  k <= n ->
  #(fun b : list Z =>
    (Zlength b = n /\ Forall (fun d => 0 <= d < n) b) /\
    exists a, Zlength a = n /\ UsesEveryValue k a /\ DistanceArray a b) =
  @set_card (list Z) (P082CanonicalProfile n k)
    (P082_finite_canonical_profile n k Hn Hk).
Proof.
  intros n k Hn Hk Hkn. symmetry.
  apply P082_finite_cardinality_bijection
    with (f := P082ProfileObservation).
  - intros parts Hcanonical.
    apply (proj2 (P082Spec_carrier_iff_canonical_observation
      n k (P082ProfileObservation parts) Hn Hk)).
    exists parts. split; [exact Hcanonical|reflexivity].
  - intros parts1 parts2 Hcanonical1 Hcanonical2 Heq.
    eapply P082CanonicalProfile_observation_injective; eauto.
  - intros b Hcarrier.
    apply (proj1 (P082Spec_carrier_iff_canonical_observation
      n k b Hn Hk)) in Hcarrier.
    destruct Hcarrier as [parts [Hcanonical Hb]].
    exists parts. split; [exact Hcanonical|]. symmetry. exact Hb.
Qed.

Lemma P082Spec_CanonicalAnswer : forall n k,
  2 <= n -> 2 <= k -> k <= n ->
  Spec n k (P082CanonicalAnswer n k).
Proof.
  intros n k Hn Hk Hkn.
  pose proof (P082SpecCarrier_profile_cardinality
    n k Hn Hk Hkn) as Hcarrier.
  rewrite (P082CanonicalProfile_cardinality n k Hn Hk Hkn) in Hcarrier.
  unfold Spec, P082CanonicalAnswer, P082Norm, P082Modulus.
  rewrite Hcarrier. reflexivity.
Qed.

Lemma P082CanonicalProfileCorrect_proved : forall n k,
  2 <= n -> 2 <= k -> k <= n ->
  P082CanonicalProfileCorrect n k.
Proof.
  intros n k Hn Hk Hkn. unfold P082CanonicalProfileCorrect.
  apply P082Spec_CanonicalAnswer; assumption.
Qed.

Lemma P082_fold_add_app : forall (xs ys : list Z),
  fold_right Z.add 0 (xs ++ ys) =
  fold_right Z.add 0 xs + fold_right Z.add 0 ys.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma P082CoreComposition_snoc_iff : forall size runs parts,
  2 <= runs ->
  (P082CoreComposition size runs parts <->
   exists prefix x,
     parts = prefix ++ x :: nil /\
     P082CoreComposition (size - x) (runs - 1) prefix /\
     1 <= x /\ x <> 2).
Proof.
  intros size runs parts Hruns. split.
  - intros [[Hlength Hbounds] [Hsum Hno2]].
    assert (Hnonempty : parts <> nil).
    { intro Hnil. subst parts. rewrite Zlength_nil in Hlength. lia. }
    apply exists_last in Hnonempty as [prefix [x Hparts]].
    subst parts. exists prefix, x. split; [reflexivity|].
    apply Forall_app in Hbounds as [Hprefix Hx].
    inversion Hx as [|x0 xs Hxbound Hnil]; subst x0 xs.
    assert (Hprefix_positive : Forall (fun y => 1 <= y) prefix).
    { apply Forall_impl with (P := fun y => 1 <= y < size + 1);
        [intros; lia|exact Hprefix]. }
    assert (Hprefix_nonempty : prefix <> nil).
    { intro Hnilprefix. subst prefix.
      rewrite Zlength_app, Zlength_nil, Zlength_cons, Zlength_nil in Hlength.
      lia. }
    assert (Hprefixsum : fold_right Z.add 0 prefix = size - x).
    { rewrite P082_fold_add_app in Hsum. simpl in Hsum. lia. }
    split.
    + unfold P082CoreComposition, P082CoreCarrier. repeat split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlength. lia.
      * apply Forall_forall. intros y Hy. split.
        -- apply Forall_forall with (x := y) in Hprefix_positive; assumption.
        -- pose proof (P082_positive_member_le_sum
             prefix y Hprefix_positive Hy). lia.
      * exact Hprefixsum.
      * intros t Ht Htwo. apply (Hno2 t).
        -- lia.
        -- rewrite P082_Znth_app_left.
           ++ exact Htwo.
           ++ rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlength. lia.
    + split; [lia|]. intro Hx2. apply (Hno2 (runs - 1)).
      * rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlength. lia.
      * rewrite P082_Znth_app_right.
        -- replace (runs - 1 - Zlength prefix) with 0 by
             (rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlength; lia).
           rewrite Znth0_cons. exact Hx2.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlength. lia.
  - intros [prefix [x [Hparts [Hcore [Hx Hxnot]]]]]. subst parts.
    destruct Hcore as [[Hprefixlen Hprefixbounds] [Hprefixsum Hprefixno2]].
    assert (Hprefixpositive : Forall (fun y => 1 <= y) prefix).
    { apply Forall_impl with
        (P := fun y => 1 <= y < size - x + 1); [intros; lia|].
      exact Hprefixbounds. }
    assert (Hprefix_nonempty : prefix <> nil).
    { intro Hnil. subst prefix. rewrite Zlength_nil in Hprefixlen. lia. }
    assert (Hprefixsum_pos : 1 <= fold_right Z.add 0 prefix).
    { apply P082_positive_sum_nonempty; assumption. }
    unfold P082CoreComposition, P082CoreCarrier. repeat split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + apply Forall_app. split.
      * apply Forall_forall. intros y Hy. split.
        -- apply Forall_forall with (x := y) in Hprefixpositive; assumption.
        -- pose proof (P082_positive_member_le_sum
             prefix y Hprefixpositive Hy). lia.
      * constructor; [lia|constructor].
    + rewrite P082_fold_add_app. simpl. lia.
    + intros t Ht.
      destruct (Z_lt_ge_dec t (runs - 1)) as [Hbefore|Hlast].
      * rewrite P082_Znth_app_left.
        -- apply Hprefixno2. lia.
        -- lia.
      * assert (Htlast : t = runs - 1) by lia. subst t.
        rewrite P082_Znth_app_right.
        -- replace (runs - 1 - Zlength prefix) with 0 by lia.
           rewrite Znth0_cons. exact Hxnot.
        -- lia.
Qed.

Definition P082ExtensionEnum (size runs : Z) : list (list Z) :=
  flat_map
    (fun total => map (fun prefix => prefix ++ (size - total) :: nil)
      (P082CoreEnum total (runs - 1)))
    (Zrange 0 size).

Lemma P082ExtensionEnum_ok : forall size runs parts,
  In parts (P082ExtensionEnum size runs) <->
  exists total prefix,
    0 <= total < size /\
    P082CoreComposition total (runs - 1) prefix /\
    parts = prefix ++ (size - total) :: nil.
Proof.
  intros size runs parts. unfold P082ExtensionEnum.
  rewrite in_flat_map. split.
  - intros [total [Htotal Hparts]].
    apply in_map_iff in Hparts as [prefix [Hparts Hprefix]].
    exists total, prefix. split.
    + apply In_Zrange in Htotal. exact Htotal.
    + split.
      * apply P082CoreEnum_ok. exact Hprefix.
      * symmetry. exact Hparts.
  - intros [total [prefix [Htotal [Hprefix Hparts]]]].
    exists total. split.
    + apply In_Zrange. exact Htotal.
    + apply in_map_iff. exists prefix. split; [symmetry; exact Hparts|].
      apply P082CoreEnum_ok. exact Hprefix.
Qed.

Lemma P082ExtensionEnum_nodup : forall size runs,
  NoDup (P082ExtensionEnum size runs).
Proof.
  intros size runs. unfold P082ExtensionEnum.
  apply P082_NoDup_flat_map_disjoint.
  - apply NoDup_Zrange.
  - intros total Htotal. apply P082_NoDup_map_injective.
    + apply P082CoreEnum_nodup.
    + intros xs ys Heq. apply app_inj_tail in Heq as [Heq Hlast]. exact Heq.
  - intros total1 total2 Htotal1 Htotal2 Hneq parts Hparts1 Hparts2.
    apply in_map_iff in Hparts1 as [prefix1 [Heq1 Hprefix1]].
    apply in_map_iff in Hparts2 as [prefix2 [Heq2 Hprefix2]].
    apply Hneq. assert (Heq :
      prefix1 ++ (size - total1) :: nil =
      prefix2 ++ (size - total2) :: nil) by congruence.
    apply app_inj_tail in Heq as [Hprefix Hlast]. lia.
Qed.

Lemma P082ExtensionEnum_count : forall size runs cap,
  runs - 1 < cap ->
  P082Ones (P082ExtensionEnum size runs) =
  P082PrefixCoreCount (size - 1) (runs - 1) cap.
Proof.
  intros size runs cap Hcap. unfold P082ExtensionEnum.
  rewrite P082Ones_flat_map.
  unfold P082PrefixCoreCount, sum_range.
  rewrite sum_range_unfold.
  replace (size - 1 + 1) with size by lia.
  induction (Zrange 0 size) as [|total totals IH]; simpl.
  - reflexivity.
  - destruct (Z_lt_dec (runs - 1) cap); [|lia].
    rewrite P082Ones_map, P082CoreEnum_count, IH. reflexivity.
Qed.

Definition P082ForbiddenTwoEnum (size runs : Z) : list (list Z) :=
  map (fun prefix => prefix ++ 2 :: nil)
    (P082CoreEnum (size - 2) (runs - 1)).

Lemma P082ForbiddenTwoEnum_ok : forall size runs parts,
  In parts (P082ForbiddenTwoEnum size runs) <->
  exists prefix,
    P082CoreComposition (size - 2) (runs - 1) prefix /\
    parts = prefix ++ 2 :: nil.
Proof.
  intros size runs parts. unfold P082ForbiddenTwoEnum.
  rewrite in_map_iff. split.
  - intros [prefix [Heq Hprefix]]. exists prefix. split.
    + apply P082CoreEnum_ok. exact Hprefix.
    + symmetry. exact Heq.
  - intros [prefix [Hprefix Heq]]. exists prefix. split.
    + symmetry. exact Heq.
    + apply P082CoreEnum_ok. exact Hprefix.
Qed.

Lemma P082ForbiddenTwoEnum_nodup : forall size runs,
  NoDup (P082ForbiddenTwoEnum size runs).
Proof.
  intros size runs. unfold P082ForbiddenTwoEnum.
  apply P082_NoDup_map_injective.
  - apply P082CoreEnum_nodup.
  - intros xs ys Heq. apply P082_snoc_two_injective. exact Heq.
Qed.

Lemma P082ForbiddenTwoEnum_count : forall size runs,
  P082Ones (P082ForbiddenTwoEnum size runs) =
  P082ExactCoreCount (size - 2) (runs - 1).
Proof.
  intros. unfold P082ForbiddenTwoEnum.
  rewrite P082Ones_map, P082CoreEnum_count. reflexivity.
Qed.

Lemma P082ExactForbidden_nodup : forall size runs,
  2 <= runs ->
  NoDup (P082CoreEnum size runs ++ P082ForbiddenTwoEnum size runs).
Proof.
  intros size runs Hruns. apply NoDup_app. repeat split.
  - apply P082CoreEnum_nodup.
  - apply P082ForbiddenTwoEnum_nodup.
  - intros parts Hexact Hbad.
    apply P082CoreEnum_ok in Hexact.
    apply P082ForbiddenTwoEnum_ok in Hbad as [prefix [Hprefix Hparts]].
    pose proof (P082CoreComposition_last_not_two size runs parts
      Hruns Hexact) as Hnot. subst parts.
    apply Hnot. apply P082_snoc_two_last.
Qed.

Lemma P082ExactForbidden_extension_permutation : forall size runs,
  3 <= size -> 2 <= runs ->
  Permutation
    (P082CoreEnum size runs ++ P082ForbiddenTwoEnum size runs)
    (P082ExtensionEnum size runs).
Proof.
  intros size runs Hsize Hruns. apply NoDup_Permutation.
  - apply P082ExactForbidden_nodup. exact Hruns.
  - apply P082ExtensionEnum_nodup.
  - intros parts. rewrite in_app_iff. split.
    + intros [Hexact|Hbad].
      * apply P082CoreEnum_ok in Hexact.
        apply P082CoreComposition_snoc_iff in Hexact as
          [prefix [x [Hparts [Hprefix [Hx Hnot2]]]]]; [|exact Hruns].
        pose proof Hprefix as [[Hplen Hpbounds] [Hpsum Hpno2]].
        assert (Hppositive : Forall (fun y => 1 <= y) prefix).
        { apply Forall_impl with
            (P := fun y => 1 <= y < size - x + 1); [intros; lia|].
          exact Hpbounds. }
        pose proof (P082_positive_length_le_sum prefix Hppositive).
        apply P082ExtensionEnum_ok. exists (size - x), prefix.
        split; [lia|]. split.
        -- replace (size - (size - x)) with x by lia. exact Hprefix.
        -- replace (size - (size - x)) with x by lia. exact Hparts.
      * apply P082ForbiddenTwoEnum_ok in Hbad as
          [prefix [Hprefix Hparts]].
        apply P082ExtensionEnum_ok. exists (size - 2), prefix.
        split; [lia|]. split; [exact Hprefix|].
        replace (size - (size - 2)) with 2 by lia. exact Hparts.
    + intro Hextension.
      apply P082ExtensionEnum_ok in Hextension as
        [total [prefix [Htotal [Hprefix Hparts]]]].
      destruct (Z.eq_dec (size - total) 2) as [Htwo|Hnot2].
      * right. apply P082ForbiddenTwoEnum_ok. exists prefix. split.
        -- replace (size - 2) with total by lia. exact Hprefix.
        -- rewrite <- Htwo. exact Hparts.
      * left. apply P082CoreEnum_ok.
        apply P082CoreComposition_snoc_iff; [exact Hruns|].
        exists prefix, (size - total).
        replace (size - (size - total)) with total by lia.
        split; [exact Hparts|].
        split; [exact Hprefix|]. split; [lia|exact Hnot2].
Qed.

Lemma P082ExactCoreCount_recurrence_large : forall size runs cap,
  3 <= size -> 2 <= runs -> runs <= cap ->
  P082ExactCoreCount size runs =
  P082PrefixCoreCount (size - 1) (runs - 1) cap -
  P082ExactCoreCount (size - 2) (runs - 1).
Proof.
  intros size runs cap Hsize Hruns Hcap.
  pose proof (P082Ones_permutation _ _ _
    (P082ExactForbidden_extension_permutation size runs Hsize Hruns)) as Hperm.
  rewrite P082Ones_app, P082CoreEnum_count,
    P082ForbiddenTwoEnum_count,
    (P082ExtensionEnum_count size runs cap) in Hperm by lia.
  lia.
Qed.

Lemma P082Exact_extension_permutation_small : forall size runs,
  1 <= size -> size < 3 -> 2 <= runs ->
  Permutation
    (P082CoreEnum size runs)
    (P082ExtensionEnum size runs).
Proof.
  intros size runs Hsize Hsmall Hruns. apply NoDup_Permutation.
  - apply P082CoreEnum_nodup.
  - apply P082ExtensionEnum_nodup.
  - intros parts. split.
    + intro Hexact. apply P082CoreEnum_ok in Hexact.
      apply P082CoreComposition_snoc_iff in Hexact as
        [prefix [x [Hparts [Hprefix [Hx Hnot2]]]]]; [|exact Hruns].
      pose proof Hprefix as [[Hplen Hpbounds] [Hpsum Hpno2]].
      assert (Hppositive : Forall (fun y => 1 <= y) prefix).
      { apply Forall_impl with
          (P := fun y => 1 <= y < size - x + 1); [intros; lia|].
        exact Hpbounds. }
      pose proof (P082_positive_length_le_sum prefix Hppositive).
      apply P082ExtensionEnum_ok. exists (size - x), prefix.
      split; [lia|]. split.
      * replace (size - (size - x)) with x by lia. exact Hprefix.
      * replace (size - (size - x)) with x by lia. exact Hparts.
    + intro Hextension.
      apply P082ExtensionEnum_ok in Hextension as
        [total [prefix [Htotal [Hprefix Hparts]]]].
      apply P082CoreEnum_ok.
      apply P082CoreComposition_snoc_iff; [exact Hruns|].
      exists prefix, (size - total).
      replace (size - (size - total)) with total by lia.
      split; [exact Hparts|]. split; [exact Hprefix|].
      split; [lia|].
      pose proof Hprefix as [[Hplen Hpbounds] [Hpsum Hpno2]].
      assert (Hppositive : Forall (fun y => 1 <= y) prefix).
      { apply Forall_impl with
          (P := fun y => 1 <= y < total + 1); [intros; lia|].
        exact Hpbounds. }
      pose proof (P082_positive_length_le_sum prefix Hppositive).
      lia.
Qed.

Lemma P082ExactCoreCount_recurrence_small : forall size runs cap,
  1 <= size -> size < 3 -> 2 <= runs -> runs <= cap ->
  P082ExactCoreCount size runs =
  P082PrefixCoreCount (size - 1) (runs - 1) cap.
Proof.
  intros size runs cap Hsize Hsmall Hruns Hcap.
  pose proof (P082Ones_permutation _ _ _
    (P082Exact_extension_permutation_small size runs
      Hsize Hsmall Hruns)) as Hperm.
  rewrite P082CoreEnum_count,
    (P082ExtensionEnum_count size runs cap) in Hperm by lia.
  exact Hperm.
Qed.

Lemma P082PrefixCoreCount_recurrence_exact : forall size threshold cap,
  0 <= size -> threshold < cap ->
  P082PrefixCoreCount size threshold cap =
  P082PrefixCoreCount (size - 1) threshold cap +
  P082ExactCoreCount size threshold.
Proof.
  intros size threshold cap Hsize Hthreshold.
  unfold P082PrefixCoreCount, sum_range.
  replace (size + 1) with ((size - 1 + 1) + 1) by lia.
  rewrite sum_Z_range_extend_right by lia.
  replace (size - 1 + 1) with size by lia.
  destruct (Z_lt_dec threshold cap); [reflexivity|lia].
Qed.

Lemma P082PrefixCoreCount_recurrence_saturated : forall size threshold cap,
  0 <= size -> cap <= threshold ->
  P082PrefixCoreCount size threshold cap =
  P082PrefixCoreCount (size - 1) threshold cap +
  P082SaturatedCoreCount size threshold.
Proof.
  intros size threshold cap Hsize Hthreshold.
  unfold P082PrefixCoreCount, sum_range.
  replace (size + 1) with ((size - 1 + 1) + 1) by lia.
  rewrite sum_Z_range_extend_right by lia.
  replace (size - 1 + 1) with size by lia.
  destruct (Z_lt_dec threshold cap); [lia|reflexivity].
Qed.

From SumLib Require Import ZRect.

Lemma P082ExactCoreCount_tail_zero : forall total low high,
  total < low ->
  SumLib.Sum.sum (fun runs : Z => low <= runs < high)
    (fun runs => P082ExactCoreCount total runs) = 0.
Proof.
  intros total low high Hlow.
  rewrite <- (sum_Z_range_zero low high). apply sum_Z_range_ext.
  intros runs Hruns. apply P082ExactCoreCount_zero_too_many. lia.
Qed.

Lemma P082ExactCoreCount_extend_to_rectangle : forall total threshold size,
  0 <= total <= size ->
  SumLib.Sum.sum (fun runs : Z => threshold <= runs < total + 1)
    (fun runs => P082ExactCoreCount total runs) =
  SumLib.Sum.sum (fun runs : Z => threshold <= runs < size + 1)
    (fun runs => P082ExactCoreCount total runs).
Proof.
  intros total threshold size Htotal.
  destruct (Z_le_dec threshold (total + 1)) as [Hthreshold|Hthreshold].
  - rewrite (sum_Z_range_split threshold (total + 1) (size + 1)) by lia.
    rewrite (P082ExactCoreCount_tail_zero total (total + 1) (size + 1)) by lia.
    lia.
  - rewrite sum_Z_range_empty by lia.
    apply eq_sym. apply P082ExactCoreCount_tail_zero. lia.
Qed.

Lemma P082PrefixSaturated_as_exact_prefix_sum : forall size threshold,
  0 <= size ->
  P082PrefixCoreCount size threshold threshold =
  sum_range threshold size
    (fun runs => P082PrefixCoreCount size runs (runs + 1)).
Proof.
  intros size threshold Hsize.
  unfold P082PrefixCoreCount at 1.
  destruct (Z_lt_dec threshold threshold); [lia|].
  unfold P082SaturatedCoreCount, sum_range.
  change
    (SumLib.Sum.sum (fun total : Z => 0 <= total < size + 1)
      (fun total =>
        SumLib.Sum.sum (fun runs : Z => threshold <= runs < total + 1)
          (fun runs => P082ExactCoreCount total runs)) =
     SumLib.Sum.sum (fun runs : Z => threshold <= runs < size + 1)
      (fun runs => P082PrefixCoreCount size runs (runs + 1))).
  assert (Hextend :
    SumLib.Sum.sum (fun total : Z => 0 <= total < size + 1)
      (fun total =>
        SumLib.Sum.sum (fun runs : Z => threshold <= runs < total + 1)
          (fun runs => P082ExactCoreCount total runs)) =
    SumLib.Sum.sum (fun total : Z => 0 <= total < size + 1)
      (fun total =>
        SumLib.Sum.sum (fun runs : Z => threshold <= runs < size + 1)
          (fun runs => P082ExactCoreCount total runs))).
  { apply sum_Z_range_ext. intros total Htotal.
    apply P082ExactCoreCount_extend_to_rectangle. lia. }
  rewrite Hextend, sum_Z_rect_swap.
  apply sum_Z_range_ext. intros runs Hruns.
  unfold P082PrefixCoreCount, sum_range.
  destruct (Z_lt_dec runs (runs + 1)); [reflexivity|lia].
Qed.

Lemma P082PrefixRecurrence_sum_shift : forall size threshold,
  1 <= size -> 1 <= threshold <= size ->
  sum_range threshold size
    (fun runs => P082PrefixCoreCount (size - 1) (runs - 1) runs) =
  P082PrefixCoreCount (size - 1) (threshold - 1) threshold +
  P082PrefixCoreCount (size - 1) threshold threshold.
Proof.
  intros size threshold Hsize Hthreshold. unfold sum_range at 1.
  pose proof (sum_Z_range_shift_1 (threshold - 1) size
    (fun runs => P082PrefixCoreCount (size - 1) (runs - 1) runs))
    as Hshift.
  replace (threshold - 1 + 1) with threshold in Hshift by lia.
  rewrite Hshift.
  rewrite sum_Z_range_cons by lia.
  replace (threshold - 1 + 1 - 1) with (threshold - 1) by lia.
  replace (threshold - 1 + 1) with threshold by lia.
  erewrite sum_Z_range_ext with
    (g := fun runs => P082PrefixCoreCount (size - 1) runs (runs + 1)).
  2:{ intros runs Hruns. f_equal; lia. }
  pose proof (P082PrefixSaturated_as_exact_prefix_sum
    (size - 1) threshold ltac:(lia)) as Hsat.
  unfold sum_range in Hsat.
  replace (size - 1 + 1) with size in Hsat by lia.
  rewrite <- Hsat.
  reflexivity.
Qed.

Lemma P082ExactRecurrence_subtraction_sum : forall size threshold,
  3 <= size -> 2 <= threshold <= size ->
  sum_range threshold size
    (fun runs => P082ExactCoreCount (size - 2) (runs - 1)) =
  P082ExactCoreCount (size - 2) (threshold - 1) +
  P082SaturatedCoreCount (size - 2) threshold.
Proof.
  intros size threshold Hsize Hthreshold. unfold sum_range at 1.
  pose proof (sum_Z_range_shift_1 (threshold - 1) size
    (fun runs => P082ExactCoreCount (size - 2) (runs - 1))) as Hshift.
  replace (threshold - 1 + 1) with threshold in Hshift by lia.
  rewrite Hshift.
  rewrite sum_Z_range_cons by lia.
  replace (threshold - 1 + 1 - 1) with (threshold - 1) by lia.
  replace (threshold - 1 + 1) with threshold by lia.
  erewrite sum_Z_range_ext with
    (g := fun runs => P082ExactCoreCount (size - 2) runs).
  2:{ intros runs Hruns. f_equal; lia. }
  destruct (Z_lt_ge_dec threshold size) as [Hlt|Heq].
  - pose proof (sum_Z_range_extend_right threshold (size - 1)
      (fun runs => P082ExactCoreCount (size - 2) runs) ltac:(lia)) as Hext.
    replace (size - 1 + 1) with size in Hext by lia. rewrite Hext.
    rewrite (P082ExactCoreCount_zero_too_many (size - 2) (size - 1)) by lia.
    unfold P082SaturatedCoreCount, sum_range.
    replace (size - 2 + 1) with (size - 1) by lia. lia.
  - assert (Heq' : threshold = size) by lia. subst threshold.
    rewrite sum_Z_range_empty by lia.
    unfold P082SaturatedCoreCount, sum_range.
    rewrite sum_Z_range_empty by lia. lia.
Qed.

Lemma P082SaturatedCoreCount_recurrence_large : forall size threshold,
  3 <= size -> 2 <= threshold <= size ->
  P082SaturatedCoreCount size threshold =
  P082PrefixCoreCount (size - 1) (threshold - 1) threshold -
  P082ExactCoreCount (size - 2) (threshold - 1) +
  P082PrefixCoreCount (size - 1) threshold threshold -
  P082SaturatedCoreCount (size - 2) threshold.
Proof.
  intros size threshold Hsize Hthreshold.
  unfold P082SaturatedCoreCount at 1. unfold sum_range at 1.
  erewrite sum_Z_range_ext with
    (g := fun runs =>
      P082PrefixCoreCount (size - 1) (runs - 1) runs -
      P082ExactCoreCount (size - 2) (runs - 1)).
  2:{ intros runs Hruns. apply P082ExactCoreCount_recurrence_large; lia. }
  rewrite sum_Z_range_sub.
  pose proof (P082PrefixRecurrence_sum_shift size threshold
    ltac:(lia) ltac:(lia)) as Hprefix.
  pose proof (P082ExactRecurrence_subtraction_sum size threshold
    ltac:(lia) ltac:(lia)) as Hsubtract.
  unfold sum_range in Hprefix, Hsubtract.
  rewrite Hprefix, Hsubtract.
  lia.
Qed.

Lemma P082SaturatedCoreCount_zero_too_many : forall size threshold,
  size < threshold -> P082SaturatedCoreCount size threshold = 0.
Proof.
  intros size threshold Htoo.
  unfold P082SaturatedCoreCount, sum_range.
  rewrite sum_Z_range_empty by lia. reflexivity.
Qed.

Lemma P082PrefixCoreCount_zero_too_many : forall size threshold cap,
  0 <= size -> size < threshold ->
  P082PrefixCoreCount size threshold cap = 0.
Proof.
  intros size threshold cap Hsize Htoo.
  unfold P082PrefixCoreCount, sum_range.
  transitivity (SumLib.Sum.sum (fun total : Z => 0 <= total < size + 1)
    (fun _ => 0)).
  - apply sum_Z_range_ext. intros total Htotal.
    destruct (Z_lt_dec threshold cap).
    + apply P082ExactCoreCount_zero_too_many. lia.
    + apply P082SaturatedCoreCount_zero_too_many. lia.
  - apply sum_Z_range_zero.
Qed.

Lemma P082SaturatedCoreCount_recurrence_small : forall size threshold,
  1 <= size -> size < 3 -> 2 <= threshold ->
  P082SaturatedCoreCount size threshold =
  P082PrefixCoreCount (size - 1) (threshold - 1) threshold +
  P082PrefixCoreCount (size - 1) threshold threshold.
Proof.
  intros size threshold Hsize Hsmall Hthreshold.
  destruct (Z_le_dec threshold size) as [Hwithin|Houtside].
  - unfold P082SaturatedCoreCount at 1. unfold sum_range at 1.
    erewrite sum_Z_range_ext with
      (g := fun runs =>
        P082PrefixCoreCount (size - 1) (runs - 1) runs).
    2:{ intros runs Hruns. apply P082ExactCoreCount_recurrence_small;
        lia. }
    pose proof (P082PrefixRecurrence_sum_shift size threshold
      ltac:(lia) ltac:(lia)) as Hprefix.
    unfold sum_range in Hprefix. exact Hprefix.
  - rewrite P082SaturatedCoreCount_zero_too_many by lia.
    rewrite (P082PrefixCoreCount_zero_too_many
      (size - 1) (threshold - 1) threshold) by lia.
    rewrite (P082PrefixCoreCount_zero_too_many
      (size - 1) threshold threshold) by lia.
    lia.
Qed.

Lemma replace_nth_length__saturated_updates :
  forall (A : Type) (n : nat) (l : list A) (v : A),
    length (replace_nth n l v) = length l.
Proof.
  intros A n l. revert n.
  induction l as [|x l IH]; intros [|n] v; simpl; auto.
Qed.
Lemma Zlength_replace_Znth__saturated_updates :
  forall (A : Type) (i : Z) (l : list A) (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A i l v.
  rewrite !Zlength_correct. unfold replace_Znth.
  now rewrite replace_nth_length__saturated_updates.
Qed.
Lemma P082Index_column_injective__saturated_updates :
  forall k r1 c1 r2 c2,
    0 <= c1 < k + 1 -> 0 <= c2 < k + 1 ->
    P082Index k r1 c1 = P082Index k r2 c2 ->
    c1 = c2.
Proof.
  intros k r1 c1 r2 c2 Hc1 Hc2 Heq.
  unfold P082Index in Heq.
  destruct (Z_lt_ge_dec r1 r2) as [Hlt|Hge].
  - assert (Ha : r1 * (k + 1) + c1 < (r1 + 1) * (k + 1)).
    { replace ((r1 + 1) * (k + 1)) with
        (r1 * (k + 1) + (k + 1)) by ring. lia. }
    assert (Hb : (r1 + 1) * (k + 1) <= r2 * (k + 1)).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia.
  - destruct (Z.eq_dec r1 r2) as [->|Hne].
    + lia.
    + assert (Ha : r2 * (k + 1) + c2 < (r2 + 1) * (k + 1)).
      { replace ((r2 + 1) * (k + 1)) with
          (r2 * (k + 1) + (k + 1)) by ring. lia. }
      assert (Hb : (r2 + 1) * (k + 1) <= r1 * (k + 1)).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
Qed.
Lemma P082Znth_replace_diff_column__saturated_updates :
  forall k wr wc qr qc l v,
    0 <= P082Index k wr wc < Zlength l ->
    0 <= P082Index k qr qc < Zlength l ->
    0 <= wc < k + 1 -> 0 <= qc < k + 1 -> wc <> qc ->
    Znth (P082Index k qr qc)
      (replace_Znth (P082Index k wr wc) v l) 0 =
    Znth (P082Index k qr qc) l 0.
Proof.
  intros k wr wc qr qc l v Hw Hq Hwc Hqc Hne.
  apply Znth_replace_Znth_Diff; try assumption.
  intro Heq. apply P082Index_column_injective__saturated_updates in Heq;
    auto.
Qed.
Lemma P082Znth_replace_diff_row__saturated_updates :
  forall k wr col qr l v,
    0 <= k -> wr <> qr ->
    0 <= P082Index k wr col < Zlength l ->
    0 <= P082Index k qr col < Zlength l ->
    Znth (P082Index k qr col)
      (replace_Znth (P082Index k wr col) v l) 0 =
    Znth (P082Index k qr col) l 0.
Proof.
  intros k wr col qr l v Hk Hne Hw Hq.
  apply Znth_replace_Znth_Diff; try assumption.
  intro Heq. unfold P082Index in Heq.
  assert (Hmul : wr * (k + 1) = qr * (k + 1)) by lia.
  apply Z.mul_reg_r in Hmul; [contradiction|lia].
Qed.
Lemma P082ColumnProgress_step_saturated__saturated_updates :
  forall n k row dp pref dv pv,
    1 <= row <= n ->
    2 <= k ->
    P082ColumnProgress n k k row dp pref ->
    dv = P082Norm (P082RawCell k row k dp pref) ->
    pv = P082Norm
      (Znth (P082Index k (row - 1) k) pref 0 + dv) ->
    P082ColumnProgress n k k (row + 1)
      (replace_Znth (P082Index k row k) dv dp)
      (replace_Znth (P082Index k row k) pv pref).
Proof.
  intros n k row dp pref dv pv Hrow Hk Hprogress Hdv Hpv.
  destruct Hprogress as [Hcolumns Hcurrent].
  destruct Hcolumns as [Hbase Hold].
  destruct Hbase as [Hdl [Hpl [Hrange [Hcol1 Hrow0]]]].
  assert (Hidx : 0 <= P082Index k row k < Zlength dp).
  { rewrite Hdl. apply P082Index_bounds; lia. }
  assert (Hidxp : 0 <= P082Index k row k < Zlength pref).
  { rewrite Hpl. apply P082Index_bounds; lia. }
  assert (Hdv_range : 0 <= dv < P082Modulus).
  { rewrite Hdv. apply P082Norm_range. }
  assert (Hpv_range : 0 <= pv < P082Modulus).
  { rewrite Hpv. apply P082Norm_range. }
  split.
  - split.
    + unfold P082BaseColumns.
      split.
      * now rewrite Zlength_replace_Znth__saturated_updates.
      * split.
        -- now rewrite Zlength_replace_Znth__saturated_updates.
        -- split.
           ++ intros q Hq.
              rewrite Zlength_replace_Znth__saturated_updates in Hq.
              destruct (Z.eq_dec q (P082Index k row k)) as [Heq|Hneq].
              { subst q.
                rewrite !Znth_replace_Znth_Same by assumption.
                exact (conj Hdv_range Hpv_range). }
              { rewrite !Znth_replace_Znth_Diff by (try assumption; lia).
                apply Hrange. exact Hq. }
           ++ split.
              ** intros r Hr.
                 rewrite (@Znth_replace_Znth_Diff Z 0 pref
                   (P082Index k row k) (P082Index k r 1) pv).
                 2: exact Hidxp.
                 2: { rewrite Hpl. apply P082Index_bounds; lia. }
                 2: { intro Heq.
                      apply P082Index_column_injective__saturated_updates in Heq; lia. }
                 rewrite (@Znth_replace_Znth_Diff Z 0 dp
                   (P082Index k row k) (P082Index k r 1) dv).
                 2: exact Hidx.
                 2: { rewrite Hdl. apply P082Index_bounds; lia. }
                 2: { intro Heq.
                      apply P082Index_column_injective__saturated_updates in Heq; lia. }
                 apply Hcol1. exact Hr.
              ** intros c Hc.
                 rewrite (@Znth_replace_Znth_Diff Z 0 pref
                   (P082Index k row k) (P082Index k 0 c) pv).
                 2: exact Hidxp.
                 2: { rewrite Hpl. apply P082Index_bounds; lia. }
                 2: { intro Heq. unfold P082Index in Heq. nia. }
                 rewrite (@Znth_replace_Znth_Diff Z 0 dp
                   (P082Index k row k) (P082Index k 0 c) dv).
                 2: exact Hidx.
                 2: { rewrite Hdl. apply P082Index_bounds; lia. }
                 2: { intro Heq. unfold P082Index in Heq. nia. }
                 apply Hrow0. exact Hc.
    + intros c r Hc Hr.
      specialize (Hold c r Hc Hr).
      unfold P082CellEquation in *.
      destruct Hold as [Hdp Hpref].
      split.
      * rewrite (@Znth_replace_Znth_Diff Z 0 dp
          (P082Index k row k) (P082Index k r c) dv).
        2: exact Hidx.
        2: { rewrite Hdl. apply P082Index_bounds; lia. }
        2: { intro Heq. apply P082Index_column_injective__saturated_updates in Heq; lia. }
        rewrite Hdp. f_equal.
        change (P082RawCell k r c dp pref =
          P082RawCell k r c
            (replace_Znth (P082Index k row k) dv dp)
            (replace_Znth (P082Index k row k) pv pref)).
        symmetry.
        rewrite !P082RawCell_ordinary by lia.
        rewrite P082Znth_replace_diff_column__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        destruct (Z_le_dec 3 r) as [Hr3|Hr3].
        -- rewrite P082Znth_replace_diff_column__saturated_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           reflexivity.
        -- reflexivity.
      * rewrite (@Znth_replace_Znth_Diff Z 0 pref
          (P082Index k row k) (P082Index k r c) pv).
        2: exact Hidxp.
        2: { rewrite Hpl. apply P082Index_bounds; lia. }
        2: { intro Heq. apply P082Index_column_injective__saturated_updates in Heq; lia. }
        rewrite Hpref. f_equal.
        rewrite P082Znth_replace_diff_column__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        rewrite P082Znth_replace_diff_column__saturated_updates by
          (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
        reflexivity.
  - intros r Hr.
    destruct (Z.eq_dec r row) as [Heq|Hneq].
    + subst r. unfold P082CellEquation.
      rewrite !Znth_replace_Znth_Same by assumption.
      split.
      * transitivity (P082Norm (P082RawCell k row k dp pref));
          [exact Hdv|].
        f_equal.
        change (P082RawCell k row k dp pref =
          P082RawCell k row k
            (replace_Znth (P082Index k row k) dv dp)
            (replace_Znth (P082Index k row k) pv pref)).
        symmetry. unfold P082RawCell.
        rewrite P082Znth_replace_diff_column__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        destruct (Z_le_dec 3 row) as [Hr3|Hr3].
        -- rewrite P082Znth_replace_diff_column__saturated_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           rewrite P082Znth_replace_diff_row__saturated_updates by
             (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
           rewrite P082Znth_replace_diff_row__saturated_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           reflexivity.
        -- rewrite P082Znth_replace_diff_row__saturated_updates by
             (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
           reflexivity.
      * transitivity
          (P082Norm (Znth (P082Index k (row - 1) k) pref 0 + dv));
          [exact Hpv|].
        f_equal.
        rewrite P082Znth_replace_diff_row__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        reflexivity.
    + assert (Hr_old : 1 <= r < row) by lia.
      specialize (Hcurrent r Hr_old).
      unfold P082CellEquation in *.
      destruct Hcurrent as [Hdp Hpref].
      split.
      * rewrite P082Znth_replace_diff_row__saturated_updates by
          (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
        rewrite Hdp. f_equal.
        change (P082RawCell k r k dp pref =
          P082RawCell k r k
            (replace_Znth (P082Index k row k) dv dp)
            (replace_Znth (P082Index k row k) pv pref)).
        symmetry. unfold P082RawCell.
        rewrite P082Znth_replace_diff_column__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        destruct (Z_le_dec 3 r) as [Hr3|Hr3].
        -- rewrite P082Znth_replace_diff_column__saturated_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           rewrite P082Znth_replace_diff_row__saturated_updates by
             (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
           rewrite P082Znth_replace_diff_row__saturated_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           reflexivity.
        -- rewrite P082Znth_replace_diff_row__saturated_updates by
             (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
           reflexivity.
      * rewrite P082Znth_replace_diff_row__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        rewrite Hpref. f_equal.
        rewrite P082Znth_replace_diff_row__saturated_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        rewrite P082Znth_replace_diff_row__saturated_updates by
          (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
        reflexivity.
Qed.
Lemma P082Norm_c_normalize__semantic_updates : forall x,
  Z.rem (Z.rem x 998244353 + 998244353) 998244353 = P082Norm x.
Proof.
  intro x.
  pose proof (Z.rem_bound_abs x 998244353 ltac:(lia)) as Hbound.
  assert (Hnonneg : 0 <= Z.rem x 998244353 + 998244353).
  { destruct (Z_le_gt_dec 0 (Z.rem x 998244353)); [lia|].
    rewrite Z.abs_neq in Hbound by lia. lia. }
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.rem_eq by lia.
  unfold P082Norm, P082Modulus.
  replace (x - 998244353 * (x ÷ 998244353) + 998244353)
    with (x + (1 - x ÷ 998244353) * 998244353) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma P082Norm_add_norm__semantic_updates : forall a b,
  P082Norm (P082Norm a + P082Norm b) = P082Norm (a + b).
Proof.
  intros a b. unfold P082Norm, P082Modulus.
  symmetry. apply Zplus_mod.
Qed.
Lemma P082Norm_four_norm__semantic_updates : forall a b c d,
  P082Norm (P082Norm a - P082Norm b + P082Norm c - P082Norm d) =
  P082Norm (a - b + c - d).
Proof.
  intros a b c d. unfold P082Norm, P082Modulus.
  rewrite (Zminus_mod_idemp_r
    (a mod 998244353 - b mod 998244353 + c mod 998244353)
    d 998244353).
  replace (a mod 998244353 - b mod 998244353 + c mod 998244353 - d)
    with (c mod 998244353 + (a mod 998244353 - b mod 998244353 - d)) by ring.
  rewrite (Zplus_mod_idemp_l c
    (a mod 998244353 - b mod 998244353 - d) 998244353).
  replace (c + (a mod 998244353 - b mod 998244353 - d))
    with (a mod 998244353 + (c - b mod 998244353 - d)) by ring.
  rewrite (Zplus_mod_idemp_l a
    (c - b mod 998244353 - d) 998244353).
  replace (a + (c - b mod 998244353 - d))
    with (a + c - d - b mod 998244353) by ring.
  rewrite (Zminus_mod_idemp_r (a + c - d) b 998244353).
  f_equal. ring.
Qed.
Lemma replace_nth_length__ordinary_updates :
  forall (A : Type) (n : nat) (l : list A) (v : A),
    length (replace_nth n l v) = length l.
Proof.
  intros A n l. revert n.
  induction l as [|x l IH]; intros [|n] v; simpl; auto.
Qed.
Lemma Zlength_replace_Znth__ordinary_updates :
  forall (A : Type) (i : Z) (l : list A) (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A i l v.
  rewrite !Zlength_correct. unfold replace_Znth.
  now rewrite replace_nth_length__ordinary_updates.
Qed.
Lemma P082Index_column_injective__ordinary_updates :
  forall k r1 c1 r2 c2,
    0 <= c1 < k + 1 -> 0 <= c2 < k + 1 ->
    P082Index k r1 c1 = P082Index k r2 c2 ->
    c1 = c2.
Proof.
  intros k r1 c1 r2 c2 Hc1 Hc2 Heq.
  unfold P082Index in Heq.
  destruct (Z_lt_ge_dec r1 r2) as [Hlt|Hge].
  - assert (Ha : r1 * (k + 1) + c1 < (r1 + 1) * (k + 1)).
    { replace ((r1 + 1) * (k + 1)) with
        (r1 * (k + 1) + (k + 1)) by ring. lia. }
    assert (Hb : (r1 + 1) * (k + 1) <= r2 * (k + 1)).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia.
  - destruct (Z.eq_dec r1 r2) as [->|Hne].
    + lia.
    + assert (Ha : r2 * (k + 1) + c2 < (r2 + 1) * (k + 1)).
      { replace ((r2 + 1) * (k + 1)) with
          (r2 * (k + 1) + (k + 1)) by ring. lia. }
      assert (Hb : (r2 + 1) * (k + 1) <= r1 * (k + 1)).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
Qed.
Lemma P082Znth_replace_diff_column__ordinary_updates :
  forall k wr wc qr qc l v,
    0 <= P082Index k wr wc < Zlength l ->
    0 <= P082Index k qr qc < Zlength l ->
    0 <= wc < k + 1 -> 0 <= qc < k + 1 -> wc <> qc ->
    Znth (P082Index k qr qc)
      (replace_Znth (P082Index k wr wc) v l) 0 =
    Znth (P082Index k qr qc) l 0.
Proof.
  intros k wr wc qr qc l v Hw Hq Hwc Hqc Hne.
  apply Znth_replace_Znth_Diff; try assumption.
  intro Heq. apply P082Index_column_injective__ordinary_updates in Heq;
    auto.
Qed.
Lemma P082Znth_replace_diff_row__ordinary_updates :
  forall k wr col qr l v,
    0 <= k -> wr <> qr ->
    0 <= P082Index k wr col < Zlength l ->
    0 <= P082Index k qr col < Zlength l ->
    Znth (P082Index k qr col)
      (replace_Znth (P082Index k wr col) v l) 0 =
    Znth (P082Index k qr col) l 0.
Proof.
  intros k wr col qr l v Hk Hne Hw Hq.
  apply Znth_replace_Znth_Diff; try assumption.
  intro Heq. unfold P082Index in Heq.
  assert (Hmul : wr * (k + 1) = qr * (k + 1)) by lia.
  apply Z.mul_reg_r in Hmul; [contradiction|lia].
Qed.
Lemma P082ColumnProgress_step_ordinary__ordinary_updates :
  forall n k col row dp pref dv pv,
    1 <= row <= n ->
    2 <= col <= k ->
    col <> k ->
    P082ColumnProgress n k col row dp pref ->
    dv = P082Norm (P082RawCell k row col dp pref) ->
    pv = Z.rem
      (Znth (P082Index k (row - 1) col) pref 0 +
       Znth (P082Index k row col)
         (replace_Znth (P082Index k row col) dv dp) 0)
      P082Modulus ->
    P082ColumnProgress n k col (row + 1)
      (replace_Znth (P082Index k row col) dv dp)
      (replace_Znth (P082Index k row col) pv pref).
Proof.
  intros n k col row dp pref dv pv Hrow Hcol Hordinary Hprogress Hdv Hpv.
  destruct Hprogress as [Hcolumns Hcurrent].
  destruct Hcolumns as [Hbase Hold].
  destruct Hbase as [Hdl [Hpl [Hrange [Hcol1 Hrow0]]]].
  assert (Hidx : 0 <= P082Index k row col < Zlength dp).
  { rewrite Hdl. apply P082Index_bounds; lia. }
  assert (Hidxp : 0 <= P082Index k row col < Zlength pref).
  { rewrite Hpl. apply P082Index_bounds; lia. }
  assert (Hprev : 0 <= P082Index k (row - 1) col < Zlength dp).
  { rewrite Hdl. apply P082Index_bounds; lia. }
  pose proof (Hrange _ Hprev) as [_ Hprev_range].
  assert (Hdv_range : 0 <= dv < P082Modulus).
  { rewrite Hdv. apply P082Norm_range. }
  assert (Hpv_plain : pv = P082Norm
      (Znth (P082Index k (row - 1) col) pref 0 + dv)).
  { rewrite Hpv, Znth_replace_Znth_Same by exact Hidx.
    unfold P082Norm.
    rewrite Z.rem_mod_nonneg by (unfold P082Modulus; lia).
    reflexivity. }
  assert (Hpv_range : 0 <= pv < P082Modulus).
  { rewrite Hpv_plain. apply P082Norm_range. }
  split.
  - split.
    + unfold P082BaseColumns.
      split.
      * now rewrite Zlength_replace_Znth__ordinary_updates.
      * split.
        -- now rewrite Zlength_replace_Znth__ordinary_updates.
        -- split.
           ++ intros q Hq.
              rewrite Zlength_replace_Znth__ordinary_updates in Hq.
              destruct (Z.eq_dec q (P082Index k row col)) as [Heq|Hneq].
              { subst q.
                rewrite !Znth_replace_Znth_Same by assumption.
                exact (conj Hdv_range Hpv_range). }
              { rewrite !Znth_replace_Znth_Diff by (try assumption; lia).
                apply Hrange. exact Hq. }
           ++ split.
              ** intros r Hr.
                 rewrite (@Znth_replace_Znth_Diff Z 0 pref
                   (P082Index k row col) (P082Index k r 1) pv).
                 2: exact Hidxp.
                 2: { rewrite Hpl. apply P082Index_bounds; lia. }
                 2: { intro Heq. apply P082Index_column_injective__ordinary_updates in Heq; lia. }
                 rewrite (@Znth_replace_Znth_Diff Z 0 dp
                   (P082Index k row col) (P082Index k r 1) dv).
                 2: exact Hidx.
                 2: { rewrite Hdl. apply P082Index_bounds; lia. }
                 2: { intro Heq. apply P082Index_column_injective__ordinary_updates in Heq; lia. }
                 apply Hcol1. exact Hr.
              ** intros c Hc.
                 rewrite (@Znth_replace_Znth_Diff Z 0 pref
                   (P082Index k row col) (P082Index k 0 c) pv).
                 2: exact Hidxp.
                 2: { rewrite Hpl. apply P082Index_bounds; lia. }
                 2: { intro Heq. unfold P082Index in Heq. nia. }
                 rewrite (@Znth_replace_Znth_Diff Z 0 dp
                   (P082Index k row col) (P082Index k 0 c) dv).
                 2: exact Hidx.
                 2: { rewrite Hdl. apply P082Index_bounds; lia. }
                 2: { intro Heq. unfold P082Index in Heq. nia. }
                 apply Hrow0. exact Hc.
    + intros c r Hc Hr.
      specialize (Hold c r Hc Hr).
      unfold P082CellEquation in *.
      destruct Hold as [Hdp Hpref].
      split.
      * rewrite (@Znth_replace_Znth_Diff Z 0 dp
          (P082Index k row col) (P082Index k r c) dv).
        2: exact Hidx.
        2: { rewrite Hdl. apply P082Index_bounds; lia. }
        2: { intro Heq. apply P082Index_column_injective__ordinary_updates in Heq; lia. }
        rewrite Hdp. f_equal.
        change (P082RawCell k r c dp pref =
          P082RawCell k r c
            (replace_Znth (P082Index k row col) dv dp)
            (replace_Znth (P082Index k row col) pv pref)).
        symmetry.
        rewrite !P082RawCell_ordinary by lia.
        rewrite P082Znth_replace_diff_column__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        destruct (Z_le_dec 3 r) as [Hr3|Hr3].
        -- rewrite P082Znth_replace_diff_column__ordinary_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           reflexivity.
        -- reflexivity.
      * rewrite (@Znth_replace_Znth_Diff Z 0 pref
          (P082Index k row col) (P082Index k r c) pv).
        2: exact Hidxp.
        2: { rewrite Hpl. apply P082Index_bounds; lia. }
        2: { intro Heq. apply P082Index_column_injective__ordinary_updates in Heq; lia. }
        rewrite Hpref. f_equal.
        rewrite P082Znth_replace_diff_column__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        rewrite P082Znth_replace_diff_column__ordinary_updates by
          (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
        reflexivity.
  - intros r Hr.
    destruct (Z.eq_dec r row) as [Heq|Hneq].
    + subst r. unfold P082CellEquation.
      rewrite !Znth_replace_Znth_Same by assumption.
      split.
      * transitivity (P082Norm (P082RawCell k row col dp pref));
          [exact Hdv|].
        f_equal.
        change (P082RawCell k row col dp pref =
          P082RawCell k row col
            (replace_Znth (P082Index k row col) dv dp)
            (replace_Znth (P082Index k row col) pv pref)).
        symmetry. rewrite !P082RawCell_ordinary by assumption.
        rewrite P082Znth_replace_diff_column__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        destruct (Z_le_dec 3 row) as [Hr3|Hr3].
        -- rewrite P082Znth_replace_diff_column__ordinary_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           reflexivity.
        -- reflexivity.
      * transitivity
          (P082Norm (Znth (P082Index k (row - 1) col) pref 0 + dv));
          [exact Hpv_plain|].
        f_equal.
        rewrite P082Znth_replace_diff_row__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        reflexivity.
    + assert (Hr_old : 1 <= r < row) by lia.
      specialize (Hcurrent r Hr_old).
      unfold P082CellEquation in *.
      destruct Hcurrent as [Hdp Hpref].
      split.
      * rewrite P082Znth_replace_diff_row__ordinary_updates by
          (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
        rewrite Hdp. f_equal.
        change (P082RawCell k r col dp pref =
          P082RawCell k r col
            (replace_Znth (P082Index k row col) dv dp)
            (replace_Znth (P082Index k row col) pv pref)).
        symmetry. rewrite !P082RawCell_ordinary by assumption.
        rewrite P082Znth_replace_diff_column__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        destruct (Z_le_dec 3 r) as [Hr3|Hr3].
        -- rewrite P082Znth_replace_diff_column__ordinary_updates by
             (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
           reflexivity.
        -- reflexivity.
      * rewrite P082Znth_replace_diff_row__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        rewrite Hpref. f_equal.
        rewrite P082Znth_replace_diff_row__ordinary_updates by
          (try exact Hidxp; try rewrite Hpl; try apply P082Index_bounds; lia).
        rewrite P082Znth_replace_diff_row__ordinary_updates by
          (try exact Hidx; try rewrite Hdl; try apply P082Index_bounds; lia).
        reflexivity.
Qed.
Lemma P082Norm_sub_norm__semantic_updates : forall a b,
  P082Norm (P082Norm a - P082Norm b) = P082Norm (a - b).
Proof.
  intros a b. unfold P082Norm, P082Modulus.
  symmetry. apply Zminus_mod.
Qed.
Lemma P082InitState_zero__initialization : forall n k len,
  0 <= n -> 0 <= k ->
  len = (n + 1) * (k + 1) ->
  P082InitState n k 1 (repeat 0 (Z.to_nat len)) (repeat 0 (Z.to_nat len)).
Proof.
  intros n k len Hn Hk Hlen. subst len.
  assert (Hsize : 0 <= (n + 1) * (k + 1)) by nia.
  assert (Hlength :
    Zlength (repeat 0 (Z.to_nat ((n + 1) * (k + 1)))) =
      (n + 1) * (k + 1)).
  { rewrite Zlength_correct, repeat_length, Z2Nat.id; lia. }
  unfold P082InitState.
  split; [exact Hlength |].
  split; [exact Hlength |].
  split.
  - intros q Hq. rewrite !Znth_repeat.
    unfold P082Modulus. lia.
  - split.
    + intros row Hrow. lia.
    + split.
      * intros row Hrow. rewrite !Znth_repeat. auto.
      * intros row col Hrow Hcol Hshape.
        rewrite !Znth_repeat. auto.
Qed.
Lemma Zlength_replace_Znth__initialization :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n. revert n.
  induction l; simpl; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma P082InitState_step__initialization :
  forall n k i dp pref,
    2 <= k -> 1 <= i <= n -> n < P082Modulus ->
    P082InitState n k i dp pref ->
    P082InitState n k (i + 1)
      (replace_Znth (P082Index k i 1) 1 dp)
      (replace_Znth (P082Index k i 1)
        (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353)
        pref).
Proof.
  intros n k i dp pref Hk Hi Hnmod Hstate.
  destruct Hstate as
    [Hdl [Hpl [Hrange [Hdone [Htodo Hzero]]]]].
  assert (Hidx : 0 <= P082Index k i 1 < Zlength dp).
  { rewrite Hdl. apply P082Index_bounds; lia. }
  assert (Hidxp : 0 <= P082Index k i 1 < Zlength pref).
  { rewrite Hpl. apply P082Index_bounds; lia. }
  assert (Hprev : Znth (P082Index k (i - 1) 1) pref 0 = i - 1).
  { destruct (Z.eq_dec i 1) as [Heq | Hneq].
    - subst i. specialize (Hzero 0 1 ltac:(lia) ltac:(lia) (or_introl eq_refl)).
      destruct Hzero as [_ Hz]. unfold P082Index in *. simpl in *. exact Hz.
    - specialize (Hdone (i - 1) ltac:(lia)). tauto. }
  unfold P082InitState.
  split; [rewrite Zlength_replace_Znth__initialization; exact Hdl |].
  split; [rewrite Zlength_replace_Znth__initialization; exact Hpl |].
  split.
  - intros q Hq.
    rewrite Zlength_replace_Znth__initialization in Hq.
    destruct (Z.eq_dec q (P082Index k i 1)) as [Heq | Hneq].
    + subst q. rewrite (Znth_replace_Znth_Same 0 dp),
        (Znth_replace_Znth_Same 0 pref) by assumption.
      rewrite Hprev. unfold P082Modulus in *. rewrite Z.rem_small by lia. lia.
    + rewrite (Znth_replace_Znth_Diff 0 dp (P082Index k i 1) q 1)
        by (try assumption; congruence).
      rewrite (Znth_replace_Znth_Diff 0 pref (P082Index k i 1) q
        (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353))
        by (try assumption; congruence).
      apply Hrange. lia.
  - split.
    + intros row Hrow.
      assert (Hrowidx : 0 <= P082Index k row 1 < Zlength dp).
      { rewrite Hdl. apply P082Index_bounds; lia. }
      assert (Hrowidxp : 0 <= P082Index k row 1 < Zlength pref).
      { rewrite Hpl. apply P082Index_bounds; lia. }
      destruct (Z.eq_dec row i) as [Heq | Hneq].
      * subst row. rewrite (Znth_replace_Znth_Same 0 dp),
        (Znth_replace_Znth_Same 0 pref) by assumption.
        rewrite Hprev. rewrite Z.rem_small by (unfold P082Modulus in Hnmod; lia).
        lia.
      * assert (Hindices : P082Index k i 1 <> P082Index k row 1).
        { unfold P082Index. nia. }
        rewrite (Znth_replace_Znth_Diff 0 dp (P082Index k i 1)
          (P082Index k row 1) 1) by assumption.
        rewrite (Znth_replace_Znth_Diff 0 pref (P082Index k i 1)
          (P082Index k row 1)
          (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353))
          by assumption.
        apply Hdone. lia.
    + split.
      * intros row Hrow.
        assert (Hrowidx : 0 <= P082Index k row 1 < Zlength dp).
        { rewrite Hdl. apply P082Index_bounds; lia. }
        assert (Hrowidxp : 0 <= P082Index k row 1 < Zlength pref).
        { rewrite Hpl. apply P082Index_bounds; lia. }
        assert (Hindices : P082Index k i 1 <> P082Index k row 1).
        { unfold P082Index. nia. }
        rewrite (Znth_replace_Znth_Diff 0 dp (P082Index k i 1)
          (P082Index k row 1) 1) by assumption.
        rewrite (Znth_replace_Znth_Diff 0 pref (P082Index k i 1)
          (P082Index k row 1)
          (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353))
          by assumption.
        apply Htodo. lia.
      * intros row col Hrow Hcol Hshape.
        assert (Hcell : 0 <= P082Index k row col < Zlength dp).
        { rewrite Hdl. apply P082Index_bounds; assumption. }
        assert (Hcellp : 0 <= P082Index k row col < Zlength pref).
        { rewrite Hpl. apply P082Index_bounds; assumption. }
        assert (Hindices : P082Index k i 1 <> P082Index k row col).
        { intro Hind. unfold P082Index in Hind.
          destruct Hshape as [Hrow0 | [Hcol0 | Hcol2]].
          - subst row. nia.
          - subst col. destruct (Z_lt_ge_dec i row) as [Hlt | Hge].
            + nia.
            + destruct (Z.eq_dec i row) as [Heq | Hneq].
              * subst row. nia.
              * assert (row < i) by lia. nia.
          - destruct (Z_lt_ge_dec i row) as [Hlt | Hge].
            + nia.
            + destruct (Z.eq_dec i row) as [Heq | Hneq].
              * subst row. nia.
              * assert (row < i) by lia. nia. }
        rewrite (Znth_replace_Znth_Diff 0 dp (P082Index k i 1)
          (P082Index k row col) 1) by assumption.
        rewrite (Znth_replace_Znth_Diff 0 pref (P082Index k i 1)
          (P082Index k row col)
          (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353))
          by assumption.
        apply Hzero; assumption.
Qed.
Lemma P082InitArrays_zero__initialization_semantics : forall n k len,
  0 <= n -> 2 <= k -> len = (n + 1) * (k + 1) ->
  P082InitState n k 1
    (repeat 0 (Z.to_nat len)) (repeat 0 (Z.to_nat len)) /\
  P082SemanticInit n k 1
    (repeat 0 (Z.to_nat len)) (repeat 0 (Z.to_nat len)).
Proof.
  intros n k len Hn Hk Hlen. split.
  - apply P082InitState_zero__initialization; lia.
  - intros row Hrow. assert (row = 0) by lia. subst row.
    unfold P082SemanticCell. rewrite !Znth_repeat. split.
    + destruct (Z_lt_dec 1 k); [|lia].
      rewrite P082ExactCoreCount_zero_too_many by lia.
      unfold P082Norm, P082Modulus. reflexivity.
    + rewrite P082PrefixCoreCount_zero_too_many by lia.
      unfold P082Norm, P082Modulus. reflexivity.
Qed.
Lemma P082InitRow_step__initialization_semantics : forall n k i dp pref,
  2 <= k -> 1 <= i <= n -> n <= 200000 ->
  P082InitState n k i dp pref ->
  P082SemanticInit n k i dp pref ->
  let dp' := replace_Znth (P082Index k i 1) 1 dp in
  let pref' := replace_Znth (P082Index k i 1)
    (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353) pref in
  P082InitState n k (i + 1) dp' pref' /\
  P082SemanticInit n k (i + 1) dp' pref'.
Proof.
  intros n k i dp pref Hk Hi Hn Hstate Hsem. cbn. split.
  - apply P082InitState_step__initialization; try assumption.
    unfold P082Modulus. lia.
  - assert (Hexact_one : forall size,
      1 <= size -> P082ExactCoreCount size 1 = 1).
    { intros size Hsize. rewrite <- P082CoreEnum_count.
      assert (Hcharacterize : forall parts,
        In parts (P082CoreEnum size 1) <-> parts = size :: nil).
      { intro parts. rewrite P082CoreEnum_ok. split.
        - intros [[Hlen Hbounds] [Hsum Hno]].
          rewrite Zlength_correct in Hlen.
          destruct parts as [|x parts]; simpl in Hlen; [lia|].
          destruct parts as [|y parts]; simpl in Hlen; [|lia].
          simpl in Hsum. f_equal. lia.
        - intro Heq. subst parts. unfold P082CoreComposition, P082CoreCarrier.
          repeat split; simpl; try lia.
          constructor; [lia|constructor]. }
      destruct (P082CoreEnum size 1) as [|x xs] eqn:Heq.
      + exfalso. specialize (Hcharacterize (size :: nil)).
        simpl in Hcharacterize. tauto.
      + assert (Hx : x = size :: nil).
        { apply (proj1 (Hcharacterize x)). left. reflexivity. }
        subst x.
        assert (Hxs : xs = nil).
        { destruct xs as [|y ys]; [reflexivity|].
          exfalso.
          assert (Hy : y = size :: nil).
          { apply (proj1 (Hcharacterize y)). right. left. reflexivity. }
          subst y.
          pose proof (P082CoreEnum_nodup size 1) as Hnd.
          rewrite Heq in Hnd.
          inversion Hnd as [|a l Hnotin Htail]; subst.
          apply Hnotin. left. reflexivity. }
        subst xs. reflexivity. }
    assert (Hprefix_one : forall size cap,
      0 <= size -> 2 <= cap -> P082PrefixCoreCount size 1 cap = size).
    { intros size cap Hsize Hcap. unfold P082PrefixCoreCount.
      destruct (Z_lt_dec 1 cap) as [_|Hbad]; [|lia].
      unfold sum_range.
      rewrite (sum_Z_range_cons 0 (size + 1)) by lia.
      rewrite P082ExactCoreCount_zero_too_many by lia. simpl.
      rewrite (sum_Z_range_ext 1 (size + 1)
        (fun total => P082ExactCoreCount total 1) (fun _ => 1)).
      - rewrite sum_Z_range_const by lia. lia.
      - intros total Htotal. apply Hexact_one. lia. }
    unfold P082SemanticInit in *. intros row Hrow.
    assert (Hidxd : 0 <= P082Index k i 1 < Zlength dp).
    { destruct Hstate as [Hdl _]. rewrite Hdl. apply P082Index_bounds; lia. }
    assert (Hidxp : 0 <= P082Index k i 1 < Zlength pref).
    { destruct Hstate as [_ [Hpl _]]. rewrite Hpl. apply P082Index_bounds; lia. }
    destruct (Z.eq_dec row i) as [Heq|Hneq].
    + subst row. unfold P082SemanticCell.
      rewrite (Znth_replace_Znth_Same 0 dp),
        (Znth_replace_Znth_Same 0 pref) by assumption.
      pose proof (Hsem (i - 1) ltac:(lia)) as [_ Hprevious].
      unfold P082SemanticCell in Hprevious.
      rewrite Hprefix_one in Hprevious by lia.
      unfold P082Norm, P082Modulus in Hprevious.
      rewrite Z.mod_small in Hprevious by lia. rewrite Hprevious.
      rewrite Hexact_one by lia. rewrite Hprefix_one by lia.
      destruct (Z_lt_dec 1 k) as [_|Hbad]; [|lia].
      unfold P082Norm, P082Modulus.
      rewrite Z.rem_small by lia. rewrite !Z.mod_small by lia.
      replace (i - 1 + 1) with i by lia. split; reflexivity.
    + pose proof (Hsem row ltac:(lia)) as [Hcell1 Hcell2].
      unfold P082SemanticCell in *. split.
      * rewrite (Znth_replace_Znth_Diff 0 dp (P082Index k i 1)
          (P082Index k row 1) 1).
        -- exact Hcell1.
        -- exact Hidxd.
        -- destruct Hstate as [Hdl _]. rewrite Hdl.
           apply P082Index_bounds; lia.
        -- unfold P082Index. nia.
      * rewrite (Znth_replace_Znth_Diff 0 pref (P082Index k i 1)
          (P082Index k row 1)
          (Z.rem (Znth (P082Index k (i - 1) 1) pref 0 + 1) 998244353)).
        -- exact Hcell2.
        -- exact Hidxp.
        -- destruct Hstate as [_ [Hpl _]]. rewrite Hpl.
           apply P082Index_bounds; lia.
        -- unfold P082Index. nia.
Qed.
Lemma P082_mod_plus_bounds__safety_updates_a : forall x,
  -9223372036854775808 <= Z.rem x 998244353 + 998244353 <=
  9223372036854775807.
Proof.
  intro x.
  pose proof (Z.rem_bound_abs x 998244353 ltac:(lia)) as Habs.
  replace (Z.abs 998244353) with 998244353 in Habs
    by (symmetry; apply Z.abs_eq; lia).
  destruct (Z_le_gt_dec 0 (Z.rem x 998244353)) as [Hnonneg|Hneg].
  - rewrite Z.abs_eq in Habs by lia. lia.
  - rewrite Z.abs_neq in Habs by lia. lia.
Qed.
