Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From compcert.lib Require Import Integers.
From Flocq.IEEE754 Require Import Bits.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib FloatLib.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Record PointF : Type := pointf_mk {
  pointf_x : fp32;
  pointf_y : fp32
}.

Definition pointf_get_x (p : PointF) : fp32 := pointf_x p.
Definition pointf_get_y (p : PointF) : fp32 := pointf_y p.

Definition default_pointf : PointF :=
  pointf_mk fp32_zero fp32_zero.

Axiom sizeof_PointF :
  sizeof_front_end_type (FET_alias "PointF") = 8.

Inductive FlatPointFs : list fp32 -> list PointF -> Prop :=
| FlatPointFs_nil : FlatPointFs nil nil
| FlatPointFs_cons : forall vx vy flat pts,
    FlatPointFs flat pts ->
    FlatPointFs (vx :: vy :: flat) (pointf_mk vx vy :: pts).

Definition store_pointf (p : addr) (pt : PointF) : Assertion :=
  (&((p) # "PointF" ->ₛ "x") # Float |-> pointf_x pt) **
  (&((p) # "PointF" ->ₛ "y") # Float |-> pointf_y pt).

Definition undef_pointf (p : addr) : Assertion :=
  (&((p) # "PointF" ->ₛ "x") # Float |->_) **
  (&((p) # "PointF" ->ₛ "y") # Float |->_).

(* Bit-level companions used by the float field projection strategies. *)
Definition store_pointf_x_bits (p : addr) (bits : Z) : Assertion :=
  poly_store FET_float p bits.

Definition store_pointf_y_bits (p : addr) (bits : Z) : Assertion :=
  poly_store FET_float p bits.

Lemma fp32_of_bits_of_fp32 : forall v,
  fp32_of_bits (bits_of_fp32 v) = v.
Proof.
  intros.
  unfold fp32_of_bits, bits_of_fp32, b32_of_bits, bits_of_b32.
  exact (@binary_float_of_bits_of_binary_float
    23 8 (refl_equal _) (refl_equal _) (refl_equal _) v).
Qed.

Module StorePointFAsElement <: ELEMENT_STORE.
  Definition A := PointF.
  Definition sizeA : Z := sizeof_front_end_type (FET_alias "PointF").
  Definition storeA (base : addr) (lo : Z) (a : PointF) : Assertion :=
    store_pointf (base + lo * sizeA) a.
  Definition undefstoreA (base : addr) (lo : Z) : Assertion :=
    undef_pointf (base + lo * sizeA).

  Lemma store_to_undefstore : forall base lo a,
    storeA base lo a |-- undefstoreA base lo.
  Proof.
    intros. unfold storeA, undefstoreA, store_pointf, undef_pointf.
    sep_apply store_float_undef_store_float.
    sep_apply store_float_undef_store_float.
    entailer!.
  Qed.

  Lemma storeA_shift : forall base n lo a,
    storeA (base + n * sizeA) lo a --||-- storeA base (lo + n) a.
  Proof.
    intros. unfold storeA.
    replace (base + n * sizeA + lo * sizeA)
      with (base + (lo + n) * sizeA) by lia.
    split; reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall base n lo,
    undefstoreA (base + n * sizeA) lo --||-- undefstoreA base (lo + n).
  Proof.
    intros. unfold undefstoreA.
    replace (base + n * sizeA + lo * sizeA)
      with (base + (lo + n) * sizeA) by lia.
    split; reflexivity.
  Qed.

  Lemma store_to_align : forall base lo a,
    storeA base lo a |-- store_align_n sizeA.
  Proof.
    intros. unfold storeA, store_pointf, sizeA.
    rewrite sizeof_PointF.
    sep_apply store_float_align4.
    sep_apply store_float_align4.
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma undefstore_to_align : forall base lo,
    undefstoreA base lo |-- store_align_n sizeA.
  Proof.
    intros. unfold undefstoreA, undef_pointf, sizeA.
    rewrite sizeof_PointF.
    sep_apply undef_store_float_align4.
    sep_apply undef_store_float_align4.
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA. rewrite sizeof_PointF.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.
End StorePointFAsElement.

Local Close Scope string_scope.

Module PointFArray := ArrayLib (StorePointFAsElement).

Lemma pointf_full_split_to_missing_i : forall p i n l a,
  0 <= i < n ->
  PointFArray.full p n l |--
  store_pointf (p + i * 8) (Znth i l a) **
  PointFArray.missing_i p i 0 n l.
Proof.
  intros. rewrite <- sizeof_PointF.
  apply PointFArray.full_split_to_missing_i. exact H.
Qed.

Lemma pointf_seg_split_to_missing_i : forall p x i y l a,
  x <= i < y ->
  PointFArray.seg p x y l |--
  store_pointf (p + i * 8) (Znth (i - x) l a) **
  PointFArray.missing_i p i x y l.
Proof.
  intros. rewrite <- sizeof_PointF.
  apply PointFArray.seg_split_to_missing_i. exact H.
Qed.

Lemma pointf_missing_i_merge_to_full : forall p i n a l,
  0 <= i < n ->
  store_pointf (p + i * 8) a **
  PointFArray.missing_i p i 0 n l |--
  PointFArray.full p n (replace_Znth i a l).
Proof.
  intros. rewrite <- sizeof_PointF.
  apply PointFArray.missing_i_merge_to_full. exact H.
Qed.

Lemma pointf_missing_i_merge_to_seg : forall p x i y a l,
  x <= i < y ->
  store_pointf (p + i * 8) a **
  PointFArray.missing_i p i x y l |--
  PointFArray.seg p x y (replace_Znth (i - x) a l).
Proof.
  intros. rewrite <- sizeof_PointF.
  apply PointFArray.missing_i_merge_to_seg. exact H.
Qed.

Lemma pointf_array_seg_snoc_store : forall base lo hi l a,
  lo <= hi ->
  PointFArray.seg base lo hi l **
  store_pointf (base + hi * 8) a |--
  PointFArray.seg base lo (hi + 1) (l ++ a :: nil).
Proof.
  intros.
  rewrite <- sizeof_PointF.
  change (sizeof_front_end_type (FET_alias "PointF")) with StorePointFAsElement.sizeA.
  fold (StorePointFAsElement.storeA base hi a).
  sep_apply PointFArray.seg_single.
  transitivity (PointFArray.seg base lo hi l **
                PointFArray.seg base hi (hi + 1) (a :: nil)).
  - cancel.
  - apply (PointFArray.seg_merge_to_seg base lo hi (hi + 1) l (a :: nil)); lia.
Qed.

Lemma pointf_array_store_undef_tail_to_undef_seg : forall base lo hi a,
  lo < hi ->
  store_pointf (base + lo * 8) a **
  PointFArray.undef_seg base (lo + 1) hi |--
  PointFArray.undef_seg base lo hi.
Proof.
  intros.
  rewrite <- sizeof_PointF.
  change (sizeof_front_end_type (FET_alias "PointF")) with StorePointFAsElement.sizeA.
  fold (StorePointFAsElement.storeA base lo a).
  sep_apply (StorePointFAsElement.store_to_undefstore base lo a).
  unfold StorePointFAsElement.undefstoreA.
  sep_apply PointFArray.undef_seg_single.
  apply (PointFArray.undef_seg_merge_to_undef_seg base lo (lo + 1) hi); lia.
Qed.

Definition pointf_finite (p : PointF) : Prop :=
  fp32_isFinite (pointf_x p) /\ fp32_isFinite (pointf_y p).

Definition pointsf_finite (l : list PointF) : Prop :=
  Forall pointf_finite l.

Definition pointf_cmp_xy (a b : PointF) : Z :=
  match fp32_compare (pointf_x a) (pointf_x b) with
  | Some Datatypes.Lt => -1
  | Some Datatypes.Gt => 1
  | Some Datatypes.Eq =>
      match fp32_compare (pointf_y a) (pointf_y b) with
      | Some Datatypes.Lt => -1
      | Some Datatypes.Gt => 1
      | _ => 0
      end
  | _ => 0
  end.

Definition pointf_cross (a b c : PointF) : fp32 :=
  fp32_sub
    (fp32_mul (fp32_sub (pointf_x b) (pointf_x a))
              (fp32_sub (pointf_y c) (pointf_y a)))
    (fp32_mul (fp32_sub (pointf_y b) (pointf_y a))
              (fp32_sub (pointf_x c) (pointf_x a))).

Definition pointf_cross_finite (a b c : PointF) : Prop :=
  fp32_isFinite (fp32_sub (pointf_x b) (pointf_x a)) /\
  fp32_isFinite (fp32_sub (pointf_y c) (pointf_y a)) /\
  fp32_isFinite (fp32_sub (pointf_y b) (pointf_y a)) /\
  fp32_isFinite (fp32_sub (pointf_x c) (pointf_x a)) /\
  fp32_isFinite
    (fp32_mul (fp32_sub (pointf_x b) (pointf_x a))
              (fp32_sub (pointf_y c) (pointf_y a))) /\
  fp32_isFinite
    (fp32_mul (fp32_sub (pointf_y b) (pointf_y a))
              (fp32_sub (pointf_x c) (pointf_x a))) /\
  fp32_isFinite (pointf_cross a b c).

Definition all_pointf_cross_finite (l : list PointF) : Prop :=
  forall a b c, In a l -> In b l -> In c l -> pointf_cross_finite a b c.

Definition pointf_swap (l : list PointF) (i j : Z) : list PointF :=
  replace_Znth j (Znth i l default_pointf)
    (replace_Znth i (Znth j l default_pointf) l).

Definition pointf_permutation : list PointF -> list PointF -> Prop :=
  @Permutation PointF.

Definition pointf_xy_sorted_range
    (l : list PointF) (lo hi : Z) : Prop :=
  forall i j, lo <= i <= j -> j <= hi ->
    pointf_cmp_xy (Znth i l default_pointf)
                  (Znth j l default_pointf) <= 0.

Definition pointf_xy_sorted (l : list PointF) : Prop :=
  pointf_xy_sorted_range l 0 (Zlength l - 1).

Definition pointf_same_outside_range
    (before cur : list PointF) (lo hi : Z) : Prop :=
  Zlength before = Zlength cur /\
  forall k,
    0 <= k < Zlength before ->
    (k < lo \/ hi < k) ->
    Znth k cur default_pointf = Znth k before default_pointf.

Definition pointf_xy_partitioned_at
    (l : list PointF) (lo hi pivot : Z) : Prop :=
  lo <= pivot <= hi /\
  Forall
    (fun p => pointf_cmp_xy p (Znth pivot l default_pointf) <= 0)
    (sublist lo pivot l) /\
  Forall
    (fun p => pointf_cmp_xy (Znth pivot l default_pointf) p < 0)
    (sublist (pivot + 1) (hi + 1) l).

Definition pointf_xy_partition_scan_inv
    (before cur : list PointF)
    (lo hi : Z) (pivot : PointF) (split scan : Z) : Prop :=
  pointf_permutation before cur /\
  pointf_same_outside_range before cur lo hi /\
  Znth hi cur default_pointf = pivot /\
  (forall k,
     lo <= k <= split ->
     pointf_cmp_xy (Znth k cur default_pointf) pivot <= 0) /\
  (forall k,
     split < k < scan ->
     pointf_cmp_xy pivot (Znth k cur default_pointf) < 0).

Definition pointf_insertion_outer_inv
    (before cur : list PointF) (i : Z) : Prop :=
  pointf_permutation before cur /\
  pointf_xy_sorted_range cur 0 (i - 1).

Definition pointf_insertion_inner_inv
    (before cur : list PointF) (i j : Z) : Prop :=
  pointf_permutation before cur /\
  pointf_xy_sorted_range cur 0 (j - 1) /\
  pointf_xy_sorted_range cur j i.

Definition pointf_ccw (a b c : PointF) : Prop :=
  fp32_gt (pointf_cross a b c) fp32_zero.

Inductive pointf_pop_until (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_pop_until_short : forall s,
    Zlength s < 2 -> pointf_pop_until p s s
| pointf_pop_until_ccw : forall s,
    2 <= Zlength s ->
    pointf_ccw (Znth (Zlength s - 2) s default_pointf)
               (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_pop_until p s s
| pointf_pop_until_pop : forall s out,
    2 <= Zlength s ->
    ~ pointf_ccw (Znth (Zlength s - 2) s default_pointf)
                 (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_pop_until p (removelast s) out ->
    pointf_pop_until p s out.

Inductive pointf_pop_trace (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_pop_trace_refl : forall s,
    pointf_pop_trace p s s
| pointf_pop_trace_pop : forall before cur,
    pointf_pop_trace p before cur ->
    2 <= Zlength cur ->
    ~ pointf_ccw (Znth (Zlength cur - 2) cur default_pointf)
                 (Znth (Zlength cur - 1) cur default_pointf) p ->
    pointf_pop_trace p before (removelast cur).

Inductive pointf_upper_pop_until
    (lower_bound : Z) (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_upper_pop_until_boundary : forall s,
    Zlength s <= lower_bound -> pointf_upper_pop_until lower_bound p s s
| pointf_upper_pop_until_short : forall s,
    Zlength s < 2 -> pointf_upper_pop_until lower_bound p s s
| pointf_upper_pop_until_ccw : forall s,
    lower_bound < Zlength s ->
    2 <= Zlength s ->
    pointf_ccw (Znth (Zlength s - 2) s default_pointf)
               (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_upper_pop_until lower_bound p s s
| pointf_upper_pop_until_pop : forall s out,
    lower_bound < Zlength s ->
    2 <= Zlength s ->
    ~ pointf_ccw (Znth (Zlength s - 2) s default_pointf)
                 (Znth (Zlength s - 1) s default_pointf) p ->
    pointf_upper_pop_until lower_bound p (removelast s) out ->
    pointf_upper_pop_until lower_bound p s out.

Inductive pointf_upper_pop_trace
    (lower_bound : Z) (p : PointF) : list PointF -> list PointF -> Prop :=
| pointf_upper_pop_trace_refl : forall s,
    pointf_upper_pop_trace lower_bound p s s
| pointf_upper_pop_trace_pop : forall before cur,
    pointf_upper_pop_trace lower_bound p before cur ->
    lower_bound < Zlength cur ->
    2 <= Zlength cur ->
    ~ pointf_ccw (Znth (Zlength cur - 2) cur default_pointf)
                 (Znth (Zlength cur - 1) cur default_pointf) p ->
    pointf_upper_pop_trace lower_bound p before (removelast cur).

Definition pointf_scan_step
    (before : list PointF) (p : PointF) (after : list PointF) : Prop :=
  exists reduced,
    pointf_pop_until p before reduced /\ after = reduced ++ [p].

Inductive pointf_scan_from : list PointF -> list PointF -> list PointF -> Prop :=
| pointf_scan_from_nil : forall initial,
    pointf_scan_from initial [] initial
| pointf_scan_from_snoc : forall initial input before p after,
    pointf_scan_from initial input before ->
    pointf_scan_step before p after ->
    pointf_scan_from initial (input ++ [p]) after.

Definition pointf_upper_scan_step
    (lower_bound : Z)
    (before : list PointF) (p : PointF) (after : list PointF) : Prop :=
  exists reduced,
    pointf_upper_pop_until lower_bound p before reduced /\
    after = reduced ++ [p].

Inductive pointf_upper_scan_from
    (lower_bound : Z) : list PointF -> list PointF -> list PointF -> Prop :=
| pointf_upper_scan_from_nil : forall initial,
    pointf_upper_scan_from lower_bound initial [] initial
| pointf_upper_scan_from_snoc : forall initial input before p after,
    pointf_upper_scan_from lower_bound initial input before ->
    pointf_upper_scan_step lower_bound before p after ->
    pointf_upper_scan_from lower_bound initial (input ++ [p]) after.

Definition pointf_lower_scan_inv
    (sorted chain : list PointF) (read top : Z) : Prop :=
  0 <= read <= Zlength sorted /\ top = Zlength chain /\
  pointf_scan_from [] (sublist 0 read sorted) chain /\
  (Zlength sorted <= read -> 2 <= top).

Definition pointf_lower_pop_inv
    (sorted before chain : list PointF) (read top : Z) : Prop :=
  pointf_lower_scan_inv sorted before read (Zlength before) /\
  pointf_pop_trace (Znth read sorted default_pointf) before chain /\
  top = Zlength chain.

Definition pointf_upper_capacity
    (sorted chain : list PointF) (read lower_n : Z) : Prop :=
  lower_n <= Zlength sorted /\
  Zlength chain <= lower_n + (Zlength sorted - read) /\
  (1 <= read -> Zlength chain < 2 * Zlength sorted) /\
  (read <= 0 -> lower_n < Zlength chain).

Definition pointf_upper_scan_inv
    (sorted lower chain : list PointF) (read top lower_n : Z) : Prop :=
  0 <= read <= Zlength sorted /\ top = Zlength chain /\
  lower_n = Zlength lower /\
  lower = sublist 0 lower_n chain /\
  lower_n <= top /\
  pointf_scan_from [] sorted lower /\
  pointf_upper_scan_from lower_n lower
    (rev (sublist read (Zlength sorted - 1) sorted)) chain /\
  pointf_upper_capacity sorted chain read lower_n.

Definition pointf_upper_pop_inv
    (sorted lower before chain : list PointF) (read top lower_n : Z) : Prop :=
  pointf_upper_scan_inv sorted lower before (read + 1) (Zlength before) lower_n /\
  pointf_upper_pop_trace lower_n (Znth read sorted default_pointf) before chain /\
  top = Zlength chain /\
  lower = sublist 0 lower_n chain /\
  lower_n <= top.

Definition pointf_drop_last (l : list PointF) : list PointF := removelast l.

Definition is_andrew_hull_float
    (input sorted hull : list PointF) : Prop :=
  pointf_permutation input sorted /\
  pointf_xy_sorted sorted /\
  if Z.leb (Zlength sorted) 1 then
    hull = sorted
  else
    exists lower combined,
      pointf_scan_from [] sorted lower /\
      pointf_upper_scan_from (Zlength lower) lower
        (rev (sublist 0 (Zlength sorted - 1) sorted)) combined /\
      hull = pointf_drop_last combined.
Lemma pointf_same_outside_range_refl__swap_partition :
  forall l low high, pointf_same_outside_range l l low high.
Proof.
  intros. unfold pointf_same_outside_range.
  split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma pointf_same_outside_range_swap_inside__swap_partition :
  forall before cur low high i j,
    pointf_same_outside_range before cur low high ->
    low <= i <= high ->
    low <= j <= high ->
    0 <= i < Zlength cur ->
    0 <= j < Zlength cur ->
    pointf_same_outside_range before (pointf_swap cur i j) low high.
Proof.
  intros before cur low high i j Hsame Hi_range Hj_range Hi_len Hj_len.
  destruct Hsame as [Hlen Houtside].
  unfold pointf_same_outside_range, pointf_swap.
  split.
  - repeat rewrite Zlength_replace_Znth. exact Hlen.
  - intros k Hk Houtside_range.
    rewrite Znth_replace_Znth_Diff.
    2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
    2:{ rewrite Zlength_replace_Znth. rewrite <- Hlen. exact Hk. }
    2:{ lia. }
    rewrite Znth_replace_Znth_Diff.
    2:{ exact Hi_len. }
    2:{ rewrite <- Hlen. exact Hk. }
    2:{ lia. }
    apply Houtside; auto.
Qed.

Lemma replace_Znth_swap_form__swap_partition :
  forall (l1 l2 l3 : list PointF) (xi xj : PointF),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3))
    by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := PointF) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
               xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3))
    by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := PointF) (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := PointF) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1. reflexivity.
Qed.

Lemma pointf_permutation_swap_Znth_lt__swap_partition :
  forall (l : list PointF) i j d,
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
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
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0. reflexivity.
  }
  assert (Hj_lr : (nj < List.length lr)%nat).
  {
    subst nj lr ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni. rewrite Heqxj0. unfold Znth. rewrite nth_skipn.
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
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni. rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj. rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  rewrite replace_Znth_swap_form__swap_partition.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma replace_nth_comm_PointF__swap_partition :
  forall ni nj (l : list PointF) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq. revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal. apply IHni. intros Heq. apply Hneq. now f_equal.
Qed.

Lemma replace_Znth_comm_PointF__swap_partition :
  forall (l : list PointF) i j a b,
    0 <= i -> 0 <= j -> i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq. unfold replace_Znth.
  apply replace_nth_comm_PointF__swap_partition.
  intro Heq. apply Hneq. apply Z2Nat.inj in Heq; lia.
Qed.

Lemma pointf_swap_permutation__swap_partition :
  forall l i j,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    pointf_permutation l (pointf_swap l i j).
Proof.
  intros l i j Hi Hj. unfold pointf_swap, pointf_permutation.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply pointf_permutation_swap_Znth_lt__swap_partition. lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm_PointF__swap_partition by lia.
      apply pointf_permutation_swap_Znth_lt__swap_partition. lia.
    + assert (i = j) by lia. subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma pointf_swap_length__swap_partition :
  forall l i j, Zlength (pointf_swap l i j) = Zlength l.
Proof.
  intros. unfold pointf_swap. repeat rewrite Zlength_replace_Znth. reflexivity.
Qed.

Lemma pointf_swap_same__swap_partition :
  forall l i,
    0 <= i < Zlength l ->
    pointf_swap l i i = l.
Proof.
  intros l i Hi. unfold pointf_swap.
  rewrite replace_Znth_Znth by exact Hi.
  rewrite replace_Znth_Znth by exact Hi.
  reflexivity.
Qed.

Lemma pointf_swap_Znth_other__swap_partition :
  forall l i j k,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    0 <= k < Zlength l ->
    k <> i ->
    k <> j ->
    Znth k (pointf_swap l i j) default_pointf =
    Znth k l default_pointf.
Proof.
  intros l i j k Hi Hj Hk Hki Hkj. unfold pointf_swap.
  rewrite Znth_replace_Znth_Diff.
  2:{ rewrite Zlength_replace_Znth. exact Hj. }
  2:{ rewrite Zlength_replace_Znth. exact Hk. }
  2:{ lia. }
  rewrite Znth_replace_Znth_Diff; auto; lia.
Qed.

Lemma pointsf_finite_Znth__swap_partition :
  forall l i,
    pointsf_finite l ->
    0 <= i < Zlength l ->
    pointf_finite (Znth i l default_pointf).
Proof.
  intros l i Hfin Hi. unfold pointsf_finite in Hfin.
  revert i Hi. induction Hfin as [|x xs Hx Hxs IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [->|Hneq].
    + exact Hx.
    + rewrite Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.

Lemma pointsf_finite_permutation__swap_partition :
  forall l1 l2,
    pointf_permutation l1 l2 ->
    pointsf_finite l1 ->
    pointsf_finite l2.
Proof.
  intros l1 l2 Hperm Hfinite.
  unfold pointf_permutation in Hperm.
  unfold pointsf_finite in *.
  eapply Permutation_Forall; eauto.
Qed.

Lemma all_pointf_cross_finite_permutation__swap_partition :
  forall l1 l2,
    pointf_permutation l1 l2 ->
    all_pointf_cross_finite l1 ->
    all_pointf_cross_finite l2.
Proof.
  intros l1 l2 Hperm Hall a b c Ha Hb Hc.
  apply Hall.
  - eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Ha].
  - eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hb].
  - eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hc].
Qed.

Lemma pointf_partition_scan_inv_init__swap_partition :
  forall l low high,
    0 <= low ->
    low <= high ->
    pointf_xy_partition_scan_inv l l low high
      (Znth high l default_pointf) (low - 1) low.
Proof.
  intros. unfold pointf_xy_partition_scan_inv.
  split.
  - unfold pointf_permutation. apply Permutation_refl.
  - split.
    + apply pointf_same_outside_range_refl__swap_partition.
    + split; [reflexivity|]. split; intros; lia.
Qed.

Lemma pointf_partition_scan_inv_step_gt__swap_partition :
  forall before cur low high pivot i j,
    pointf_cmp_xy pivot (Znth j cur default_pointf) < 0 ->
    j < high ->
    pointf_xy_partition_scan_inv before cur low high pivot i j ->
    pointf_xy_partition_scan_inv before cur low high pivot i (j + 1).
Proof.
  intros before cur low high pivot i j Hguard Hj_high Hinv.
  destruct Hinv as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  unfold pointf_xy_partition_scan_inv.
  split; [exact Hperm|].
  split; [exact Hsame|].
  split; [exact Hpivot|].
  split; [exact Hle|].
  intros k Hk. assert (k = j \/ i < k < j) as [->|Hmid] by lia.
  - exact Hguard.
  - apply Hgt; exact Hmid.
Qed.

Lemma pointf_partition_scan_inv_step_le__swap_partition :
  forall before cur low high pivot i j,
    0 <= low ->
    low <= high ->
    high < Zlength cur ->
    pointf_cmp_xy (Znth j cur default_pointf) pivot <= 0 ->
    j < high ->
    low - 1 <= i ->
    i < j ->
    j <= high ->
    pointf_xy_partition_scan_inv before cur low high pivot i j ->
    pointf_xy_partition_scan_inv before (pointf_swap cur (i + 1) j)
      low high pivot (i + 1) (j + 1).
Proof.
  intros before cur low high pivot i j Hlow Hlow_high Hhigh_len
    Hguard Hj_high Hlow_i Hij Hj_le Hinv.
  destruct Hinv as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  assert (Hi1_len : 0 <= i + 1 < Zlength cur) by lia.
  assert (Hj_len : 0 <= j < Zlength cur) by lia.
  unfold pointf_xy_partition_scan_inv.
  split.
  - eapply Permutation_trans; [exact Hperm|].
    apply pointf_swap_permutation__swap_partition; lia.
  - split.
    + apply pointf_same_outside_range_swap_inside__swap_partition; auto; lia.
    + split.
      * unfold pointf_swap.
        rewrite Znth_replace_Znth_Diff.
        2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
        2:{ rewrite Zlength_replace_Znth. lia. }
        2:{ lia. }
        rewrite Znth_replace_Znth_Diff by lia. exact Hpivot.
      * split.
        -- intros k Hk. unfold pointf_swap.
           destruct (Z.eq_dec k (i + 1)) as [Hki|Hki].
           ++ subst k. destruct (Z.eq_dec j (i + 1)) as [Hji|Hji].
              ** subst j. rewrite Znth_replace_Znth_Same.
                 2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
                 exact Hguard.
              ** rewrite Znth_replace_Znth_Diff.
                 2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
                 2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
                 2:{ exact Hji. }
                 rewrite Znth_replace_Znth_Same by exact Hi1_len.
                 exact Hguard.
           ++ rewrite Znth_replace_Znth_Diff.
              2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
              2:{ rewrite Zlength_replace_Znth. lia. }
              2:{ lia. }
              rewrite Znth_replace_Znth_Diff by lia. apply Hle; lia.
        -- intros k Hk. unfold pointf_swap.
           destruct (Z.eq_dec k j) as [Hkj|Hkj].
           ++ subst k. rewrite Znth_replace_Znth_Same.
              2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
              apply Hgt; lia.
           ++ rewrite Znth_replace_Znth_Diff.
              2:{ rewrite Zlength_replace_Znth. exact Hj_len. }
              2:{ rewrite Zlength_replace_Znth. lia. }
              2:{ lia. }
              rewrite Znth_replace_Znth_Diff by lia. apply Hgt; lia.
Qed.

Lemma Forall_sublist_pointf_by_Znth__swap_partition :
  forall (P : PointF -> Prop) l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l default_pointf)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhi_len Hrange. apply Forall_forall.
  intros x Hin.
  destruct (In_nth (sublist lo hi l) x default_pointf Hin)
    as [n [Hn Hnth]].
  assert (HnZ : 0 <= Z.of_nat n < Zlength (sublist lo hi l)).
  { rewrite Zlength_correct. lia. }
  rewrite Zlength_sublist in HnZ by lia.
  assert (Hz : Znth (Z.of_nat n) (sublist lo hi l) default_pointf = x).
  { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
  rewrite <- Hz. rewrite Znth_sublist_lt by lia. apply Hrange; lia.
Qed.

Lemma pointf_partition_scan_final_partitioned__swap_partition :
  forall before cur low high pivot i j,
    0 <= low ->
    low <= high ->
    low - 1 <= i ->
    high < Zlength cur ->
    j >= high ->
    i < j ->
    j <= high ->
    pointf_xy_partition_scan_inv before cur low high pivot i j ->
    pointf_xy_partitioned_at (pointf_swap cur (i + 1) high)
      low high (i + 1).
Proof.
  intros before cur low high pivot i j Hlow Hlow_high Hlow_i Hhigh_len
    Hj_ge Hij Hj_le Hinv.
  assert (Hj_eq : j = high) by lia. subst j.
  destruct Hinv as [Hperm [Hsame [Hpivot [Hle Hgt]]]].
  set (out := pointf_swap cur (i + 1) high).
  assert (Hi1_len : 0 <= i + 1 < Zlength cur) by lia.
  assert (Hhigh_len' : 0 <= high < Zlength cur) by lia.
  assert (Hpivot_out : Znth (i + 1) out default_pointf = pivot).
  {
    subst out. unfold pointf_swap.
    destruct (Z.eq_dec high (i + 1)) as [Hhi|Hhi].
    - subst high. rewrite Znth_replace_Znth_Same.
      2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
      exact Hpivot.
    - rewrite Znth_replace_Znth_Diff.
      2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
      2:{ rewrite Zlength_replace_Znth. exact Hi1_len. }
      2:{ exact Hhi. }
      rewrite Znth_replace_Znth_Same by exact Hi1_len. exact Hpivot.
  }
  unfold pointf_xy_partitioned_at.
  split; [lia|]. split.
  - apply Forall_sublist_pointf_by_Znth__swap_partition.
    + lia.
    + subst out. unfold pointf_swap. repeat rewrite Zlength_replace_Znth. lia.
    + intros k Hk. rewrite Hpivot_out. subst out. unfold pointf_swap.
      rewrite Znth_replace_Znth_Diff.
      2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
      2:{ rewrite Zlength_replace_Znth. lia. }
      2:{ lia. }
      rewrite Znth_replace_Znth_Diff by lia. apply Hle; lia.
  - apply Forall_sublist_pointf_by_Znth__swap_partition.
    + lia.
    + subst out. unfold pointf_swap. repeat rewrite Zlength_replace_Znth. lia.
    + intros k Hk. rewrite Hpivot_out. subst out. unfold pointf_swap.
      destruct (Z.eq_dec k high) as [Hkh|Hkh].
      * subst k. rewrite Znth_replace_Znth_Same.
        2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
        apply Hgt; lia.
      * rewrite Znth_replace_Znth_Diff.
        2:{ rewrite Zlength_replace_Znth. exact Hhigh_len'. }
        2:{ rewrite Zlength_replace_Znth. lia. }
        2:{ lia. }
        rewrite Znth_replace_Znth_Diff by lia. apply Hgt; lia.
Qed.

Lemma pointf_partition_scan_final_same_outside__swap_partition :
  forall before cur low high pivot i j,
    0 <= low -> low <= high -> low - 1 <= i ->
    high < Zlength cur -> j >= high -> i < j -> j <= high ->
    pointf_xy_partition_scan_inv before cur low high pivot i j ->
    pointf_same_outside_range before (pointf_swap cur (i + 1) high)
      low high.
Proof.
  intros before cur low high pivot i j Hlow Hlow_high Hlow_i Hhigh_len
    Hj_ge Hij Hj_le Hinv.
  assert (j = high) by lia. subst j.
  destruct Hinv as [_ [Hsame _]].
  apply pointf_same_outside_range_swap_inside__swap_partition; auto; lia.
Qed.

Lemma pointf_partition_scan_final_permutation__swap_partition :
  forall before cur low high pivot i j,
    0 <= low -> low <= high -> low - 1 <= i ->
    high < Zlength cur -> j >= high -> i < j -> j <= high ->
    pointf_xy_partition_scan_inv before cur low high pivot i j ->
    pointf_permutation before (pointf_swap cur (i + 1) high).
Proof.
  intros before cur low high pivot i j Hlow Hlow_high Hlow_i Hhigh_len
    Hj_ge Hij Hj_le Hinv.
  assert (j = high) by lia. subst j.
  destruct Hinv as [Hperm _].
  eapply Permutation_trans; [exact Hperm|].
  apply pointf_swap_permutation__swap_partition; lia.
Qed.

Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Lemma fp32_compare_finite_refl__partition :
  forall f, fp32_isFinite f -> fp32_compare f f = Some Datatypes.Eq.
Proof.
  intros f Hfin.
  unfold fp32_compare, fp32_isFinite in *.
  rewrite Binary.Bcompare_correct by exact Hfin.
  destruct (Flocq.Core.Raux.Rcompare_spec
    (Binary.B2R 24 128 f) (Binary.B2R 24 128 f));
    try lra; reflexivity.
Qed.
Lemma pointf_x_eq_self__partition :
  forall p, pointf_finite p -> fp32_eq (pointf_x p) (pointf_x p).
Proof.
  intros [px py] [Hpx _].
  unfold fp32_eq; simpl.
  apply fp32_compare_finite_refl__partition; exact Hpx.
Qed.
Lemma pointf_y_eq_self__partition :
  forall p, pointf_finite p -> fp32_eq (pointf_y p) (pointf_y p).
Proof.
  intros [px py] [_ Hpy].
  unfold fp32_eq; simpl.
  apply fp32_compare_finite_refl__partition; exact Hpy.
Qed.
Lemma fp32_compare_swap__partition :
  forall x y,
    fp32_compare y x =
    match fp32_compare x y with
    | Some c => Some (CompOpp c)
    | None => None
    end.
Proof.
  intros x y.
  unfold fp32_compare.
  apply Binary.Bcompare_swap.
Qed.
Lemma pointf_cmp_xy_gt_flip__partition :
  forall a b, pointf_cmp_xy a b > 0 -> pointf_cmp_xy b a < 0.
Proof.
  intros a b Hgt.
  destruct a as [ax ay].
  destruct b as [bx by0].
  unfold pointf_cmp_xy in *; simpl in *.
  destruct (fp32_compare ax bx) as [cmpx |] eqn:Hx;
    simpl in Hgt; try lia.
  destruct cmpx; simpl in Hgt; try lia.
  - rewrite (fp32_compare_swap__partition ax bx).
    rewrite Hx. simpl.
    destruct (fp32_compare ay by0) as [cmpy |] eqn:Hy;
      simpl in Hgt; try lia.
    destruct cmpy; simpl in Hgt; try lia.
    rewrite (fp32_compare_swap__partition ay by0).
    rewrite Hy. simpl. lia.
  - rewrite (fp32_compare_swap__partition ax bx).
    rewrite Hx. simpl. lia.
Qed.
Lemma pointf_same_outside_range_trans__quicksort_top :
  forall l1 l2 l3 low high,
    pointf_same_outside_range l1 l2 low high ->
    pointf_same_outside_range l2 l3 low high ->
    pointf_same_outside_range l1 l3 low high.
Proof.
  intros l1 l2 l3 low high [Hlen12 Heq12] [Hlen23 Heq23].
  split; [lia|].
  intros k Hk Hout.
  rewrite Heq23.
  - apply Heq12; auto.
  - rewrite <- Hlen12. exact Hk.
  - exact Hout.
Qed.
Lemma pointf_same_outside_range_weaken__quicksort_top :
  forall l1 l2 low high low' high',
    low' <= low ->
    high <= high' ->
    pointf_same_outside_range l1 l2 low high ->
    pointf_same_outside_range l1 l2 low' high'.
Proof.
  intros l1 l2 low high low' high' Hlow Hhigh [Hlen Heq].
  split; [exact Hlen|].
  intros k Hk Hout. apply Heq; auto.
  destruct Hout as [Hout | Hout]; [left | right]; lia.
Qed.
Lemma Forall_pointf_permutation__quicksort_top :
  forall (P : PointF -> Prop) l1 l2,
    pointf_permutation l1 l2 ->
    Forall P l1 ->
    Forall P l2.
Proof.
  intros P l1 l2 Hperm Hforall.
  unfold pointf_permutation in Hperm.
  eapply Permutation_Forall; eauto.
Qed.
Lemma Forall_Znth_pointf__quicksort_top :
  forall (P : PointF -> Prop) (l : list PointF) i d,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l d).
Proof.
  intros P l i d Hforall Hrange.
  apply Forall_forall with (x := Znth i l d) in Hforall.
  - exact Hforall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.
Lemma sublist_eq_from_Znth_pointf__quicksort_top :
  forall (l1 l2 : list PointF) lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi ->
      Znth k l1 default_pointf = Znth k l2 default_pointf) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2)
          default_pointf)).
  split.
  - repeat rewrite Zlength_correct.
    repeat rewrite sublist_length by
      (try exact Hlohi; try rewrite <- Hlen; exact Hhilen).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    {
      rewrite Zlength_sublist in Hi by lia.
      exact Hi.
    }
    rewrite (@Znth_sublist_lt PointF default_pointf lo hi l1 i).
    2: exact Hlohi.
    2: { exact Hhilen. }
    2: exact Hi'.
    rewrite (@Znth_sublist_lt PointF default_pointf lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint. lia.
Qed.
Lemma pointf_same_outside_range_prefix__quicksort_top :
  forall l1 l2 left right,
    pointf_same_outside_range l1 l2 left right ->
    0 <= left <= Zlength l1 ->
    sublist 0 left l2 = sublist 0 left l1.
Proof.
  intros l1 l2 left right [Hlen Heq] Hrange.
  apply sublist_eq_from_Znth_pointf__quicksort_top.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk. apply Heq; [lia|left; lia].
Qed.
Lemma pointf_same_outside_range_suffix__quicksort_top :
  forall l1 l2 left right,
    pointf_same_outside_range l1 l2 left right ->
    0 <= right + 1 <= Zlength l1 ->
    sublist (right + 1) (Zlength l2) l2 =
    sublist (right + 1) (Zlength l1) l1.
Proof.
  intros l1 l2 left right [Hlen Heq] Hrange.
  rewrite <- Hlen.
  apply sublist_eq_from_Znth_pointf__quicksort_top.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk. apply Heq; [rewrite Hlen; lia|right; lia].
Qed.
Lemma list_decompose_sublist_pointf__quicksort_top :
  forall (l : list PointF) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = sublist 0 lo l ++ sublist lo hi l ++ sublist hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhilen.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l).
  2: lia.
  2: { split; [transitivity hi; lia|lia]. }
  rewrite (sublist_split lo (Zlength l) hi l).
  2: lia.
  2: { split; [exact Hhilen|lia]. }
  reflexivity.
Qed.
Lemma middle_permutation_pointf_of_same_outside__quicksort_top :
  forall l1 l2 left right,
    pointf_permutation l1 l2 ->
    pointf_same_outside_range l1 l2 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l1 ->
    pointf_permutation
      (sublist left (right + 1) l1)
      (sublist left (right + 1) l2).
Proof.
  intros l1 l2 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (pointf_same_outside_range_prefix__quicksort_top
                _ _ _ _ Hsame0) as Hpre.
  pose proof (pointf_same_outside_range_suffix__quicksort_top
                _ _ _ _ Hsame0) as Hsuf.
  rewrite (list_decompose_sublist_pointf__quicksort_top
             l1 left (right + 1)) in Hperm by lia.
  assert (Hlenr2 : right + 1 <= Zlength l2) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist_pointf__quicksort_top
             l2 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma pointf_xy_partitioned_at_preserved_by_left__quicksort_top :
  forall l1 l2 left right p,
    pointf_permutation l1 l2 ->
    0 <= left ->
    pointf_same_outside_range l1 l2 left (p - 1) ->
    right < Zlength l1 ->
    pointf_xy_partitioned_at l1 left right p ->
    pointf_xy_partitioned_at l2 left right p.
Proof.
  intros l1 l2 left right p Hperm Hleft0 Hsame Hrightlen Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l2 default_pointf = Znth p l1 default_pointf).
  {
    apply Heq.
    - lia.
    - right. lia.
  }
  split; [lia|].
  split.
  - rewrite Hpiv.
    eapply Forall_pointf_permutation__quicksort_top.
    + assert (Hmid :
          pointf_permutation
            (sublist left (p - 1 + 1) l1)
            (sublist left (p - 1 + 1) l2)).
      {
        eapply middle_permutation_pointf_of_same_outside__quicksort_top
          with (left := left) (right := p - 1).
        - exact Hperm.
        - exact (conj Hlen Heq).
        - lia.
        - lia.
      }
      replace (p - 1 + 1) with p in Hmid by lia.
      exact Hmid.
    + exact Hleft.
  - rewrite Hpiv.
    apply Forall_sublist_pointf_by_Znth__swap_partition; try lia.
    intros k Hk.
    rewrite Heq by (try lia; right; lia).
    assert (Hk' :
      0 <= k - (p + 1) <
      Zlength (sublist (p + 1) (right + 1) l1)).
    { rewrite Zlength_sublist by lia; lia. }
    pose proof (Forall_Znth_pointf__quicksort_top
      _ _ (k - (p + 1)) default_pointf Hright Hk') as Hz.
    rewrite (@Znth_sublist_lt PointF default_pointf
      (p + 1) (right + 1) l1 (k - (p + 1))) in Hz.
    2: lia.
    2: { lia. }
    2: { rewrite Zlength_sublist in Hk' by lia; exact Hk'. }
    replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
    exact Hz.
Qed.
Lemma pointf_xy_partitioned_at_preserved_by_right__quicksort_top :
  forall l1 l2 left right p,
    pointf_permutation l1 l2 ->
    0 <= left ->
    pointf_same_outside_range l1 l2 (p + 1) right ->
    right < Zlength l1 ->
    pointf_xy_partitioned_at l1 left right p ->
    pointf_xy_partitioned_at l2 left right p.
Proof.
  intros l1 l2 left right p Hperm Hleft0 Hsame Hrightlen Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l2 default_pointf = Znth p l1 default_pointf).
  {
    apply Heq.
    - lia.
    - left. lia.
  }
  split; [lia|].
  split.
  - rewrite Hpiv.
    assert (Hsub : sublist left p l2 = sublist left p l1).
    {
      apply sublist_eq_from_Znth_pointf__quicksort_top.
      - symmetry. exact Hlen.
      - lia.
      - lia.
      - intros k Hk. apply Heq; [lia|left; lia].
    }
    rewrite Hsub. exact Hleft.
  - rewrite Hpiv.
    eapply Forall_pointf_permutation__quicksort_top.
    + eapply middle_permutation_pointf_of_same_outside__quicksort_top
        with (left := p + 1) (right := right).
      * exact Hperm.
      * exact (conj Hlen Heq).
      * lia.
      * lia.
    + exact Hright.
Qed.
Lemma fp32_compare_finite_cases__quicksort_top :
  forall a b,
    fp32_isFinite a ->
    fp32_isFinite b ->
    (fp32_compare a b = Some Datatypes.Lt /\
      (Binary.B2R 24 128 a < Binary.B2R 24 128 b)%R) \/
    (fp32_compare a b = Some Datatypes.Eq /\
      Binary.B2R 24 128 a = Binary.B2R 24 128 b) \/
    (fp32_compare a b = Some Datatypes.Gt /\
      (Binary.B2R 24 128 b < Binary.B2R 24 128 a)%R).
Proof.
  intros a b Ha Hb.
  unfold fp32_compare, fp32_isFinite in *.
  rewrite Binary.Bcompare_correct by assumption.
  destruct (Flocq.Core.Raux.Rcompare_spec
    (Binary.B2R 24 128 a) (Binary.B2R 24 128 b)) as [Hlt | Heq | Hgt].
  - left. split; [reflexivity|exact Hlt].
  - right; left. split; [reflexivity|exact Heq].
  - right; right. split; [reflexivity|exact Hgt].
Qed.
Lemma pointf_cmp_xy_le_real__quicksort_top :
  forall a b,
    pointf_finite a ->
    pointf_finite b ->
    pointf_cmp_xy a b <= 0 ->
    ((Binary.B2R 24 128 (pointf_x a) <
      Binary.B2R 24 128 (pointf_x b))%R \/
     (Binary.B2R 24 128 (pointf_x a) =
      Binary.B2R 24 128 (pointf_x b) /\
      (Binary.B2R 24 128 (pointf_y a) <=
       Binary.B2R 24 128 (pointf_y b))%R)).
Proof.
  intros a b [Hax Hay] [Hbx Hby] Hcmp.
  unfold pointf_cmp_xy in Hcmp.
  pose proof (fp32_compare_finite_cases__quicksort_top
    (pointf_x a) (pointf_x b) Hax Hbx) as Hx.
  destruct Hx as [[Hx HxR] | [[Hx HxR] | [Hx HxR]]]; rewrite Hx in Hcmp.
  - left. exact HxR.
  - pose proof (fp32_compare_finite_cases__quicksort_top
      (pointf_y a) (pointf_y b) Hay Hby) as Hy.
    destruct Hy as [[Hy HyR] | [[Hy HyR] | [Hy HyR]]]; rewrite Hy in Hcmp.
    + right. split; [exact HxR|lra].
    + right. split; [exact HxR|lra].
    + lia.
  - lia.
Qed.
Lemma pointf_cmp_xy_lt_real__quicksort_top :
  forall a b,
    pointf_finite a ->
    pointf_finite b ->
    pointf_cmp_xy a b < 0 ->
    ((Binary.B2R 24 128 (pointf_x a) <
      Binary.B2R 24 128 (pointf_x b))%R \/
     (Binary.B2R 24 128 (pointf_x a) =
      Binary.B2R 24 128 (pointf_x b) /\
      (Binary.B2R 24 128 (pointf_y a) <
       Binary.B2R 24 128 (pointf_y b))%R)).
Proof.
  intros a b [Hax Hay] [Hbx Hby] Hcmp.
  unfold pointf_cmp_xy in Hcmp.
  pose proof (fp32_compare_finite_cases__quicksort_top
    (pointf_x a) (pointf_x b) Hax Hbx) as Hx.
  destruct Hx as [[Hx HxR] | [[Hx HxR] | [Hx HxR]]]; rewrite Hx in Hcmp.
  - left. exact HxR.
  - pose proof (fp32_compare_finite_cases__quicksort_top
      (pointf_y a) (pointf_y b) Hay Hby) as Hy.
    destruct Hy as [[Hy HyR] | [[Hy HyR] | [Hy HyR]]]; rewrite Hy in Hcmp.
    + right. split; [exact HxR|exact HyR].
    + lia.
    + lia.
  - lia.
Qed.
Lemma pointf_real_le_to_cmp_xy_le__quicksort_top :
  forall a b,
    pointf_finite a ->
    pointf_finite b ->
    ((Binary.B2R 24 128 (pointf_x a) <
      Binary.B2R 24 128 (pointf_x b))%R \/
     (Binary.B2R 24 128 (pointf_x a) =
      Binary.B2R 24 128 (pointf_x b) /\
      (Binary.B2R 24 128 (pointf_y a) <=
       Binary.B2R 24 128 (pointf_y b))%R)) ->
    pointf_cmp_xy a b <= 0.
Proof.
  intros a b [Hax Hay] [Hbx Hby] Hreal.
  unfold pointf_cmp_xy.
  pose proof (fp32_compare_finite_cases__quicksort_top
    (pointf_x a) (pointf_x b) Hax Hbx) as Hx.
  destruct Hx as [[Hx HxR] | [[Hx HxR] | [Hx HxR]]]; rewrite Hx.
  - lia.
  - pose proof (fp32_compare_finite_cases__quicksort_top
      (pointf_y a) (pointf_y b) Hay Hby) as Hy.
    destruct Hy as [[Hy HyR] | [[Hy HyR] | [Hy HyR]]]; rewrite Hy.
    + lia.
    + lia.
    + destruct Hreal as [Hreal | [_ Hreal]]; lra.
  - destruct Hreal as [Hreal | [Hreal _]]; lra.
Qed.
Lemma pointf_cmp_xy_le_trans__quicksort_top :
  forall a b c,
    pointf_finite a ->
    pointf_finite b ->
    pointf_finite c ->
    pointf_cmp_xy a b <= 0 ->
    pointf_cmp_xy b c <= 0 ->
    pointf_cmp_xy a c <= 0.
Proof.
  intros a b c Ha Hb Hc Hab Hbc.
  pose proof (pointf_cmp_xy_le_real__quicksort_top _ _ Ha Hb Hab) as HabR.
  pose proof (pointf_cmp_xy_le_real__quicksort_top _ _ Hb Hc Hbc) as HbcR.
  apply pointf_real_le_to_cmp_xy_le__quicksort_top; auto.
  destruct HabR as [Habx | [Habx Haby]];
  destruct HbcR as [Hbcx | [Hbcx Hbcy]].
  - left. lra.
  - left. lra.
  - left. lra.
  - right. split; lra.
Qed.
Lemma pointf_cmp_xy_refl__quicksort_top :
  forall p,
    pointf_finite p ->
    pointf_cmp_xy p p <= 0.
Proof.
  intros p Hp.
  apply pointf_real_le_to_cmp_xy_le__quicksort_top; auto.
  right. split; lra.
Qed.
Lemma pointsf_finite_Znth__quicksort_top :
  forall l i,
    pointsf_finite l ->
    0 <= i < Zlength l ->
    pointf_finite (Znth i l default_pointf).
Proof.
  intros l i Hfin Hi.
  unfold pointsf_finite in Hfin.
  eapply Forall_Znth_pointf__quicksort_top; eauto.
Qed.
Lemma pointf_xy_partitioned_at_left_Znth_le__quicksort_top :
  forall l left right p k,
    0 <= left ->
    p <= Zlength l ->
    pointf_xy_partitioned_at l left right p ->
    left <= k < p ->
    pointf_cmp_xy (Znth k l default_pointf)
                  (Znth p l default_pointf) <= 0.
Proof.
  intros l left right p k Hleft0 Hp Hpart Hk.
  destruct Hpart as [_ [Hleft _]].
  pose proof (Forall_Znth_pointf__quicksort_top
    (fun x => pointf_cmp_xy x (Znth p l default_pointf) <= 0)
    (sublist left p l) (k - left) default_pointf Hleft) as Hz.
  assert (Hk' : 0 <= k - left < Zlength (sublist left p l)).
  { rewrite Zlength_sublist by lia; lia. }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt PointF default_pointf left p l (k - left)) in Hz.
  2: lia.
  2: { exact Hp. }
  2: { rewrite Zlength_sublist in Hk' by lia; exact Hk'. }
  replace (left + (k - left)) with k in Hz by lia.
  exact Hz.
Qed.
Lemma pointf_xy_partitioned_at_right_Znth_lt__quicksort_top :
  forall l left right p k,
    0 <= left ->
    right < Zlength l ->
    pointf_xy_partitioned_at l left right p ->
    p < k <= right ->
    pointf_cmp_xy (Znth p l default_pointf)
                  (Znth k l default_pointf) < 0.
Proof.
  intros l left right p k Hleft0 Hrightlen Hpart Hk.
  destruct Hpart as [Hprange [_ Hright]].
  pose proof (Forall_Znth_pointf__quicksort_top
    (fun x => pointf_cmp_xy (Znth p l default_pointf) x < 0)
    (sublist (p + 1) (right + 1) l)
    (k - (p + 1)) default_pointf Hright) as Hz.
  assert (Hk' :
    0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)).
  { rewrite Zlength_sublist by lia; lia. }
  specialize (Hz Hk').
  rewrite (@Znth_sublist_lt PointF default_pointf
    (p + 1) (right + 1) l (k - (p + 1))) in Hz.
  2: lia.
  2: { lia. }
  2: { rewrite Zlength_sublist in Hk' by lia; exact Hk'. }
  replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
  exact Hz.
Qed.
Lemma pointf_xy_sorted_range_base__quicksort_top :
  forall l left right,
    pointsf_finite l ->
    0 <= left ->
    right < Zlength l ->
    right <= left ->
    pointf_xy_sorted_range l left right.
Proof.
  intros l left right Hfin Hleft Hrightlen Hbase i j Hij Hj.
  assert (i = j) by lia. subst j.
  apply pointf_cmp_xy_refl__quicksort_top.
  apply pointsf_finite_Znth__quicksort_top; auto; lia.
Qed.
Lemma pointf_xy_sorted_range_from_partition__quicksort_top :
  forall l left right p,
    pointsf_finite l ->
    0 <= left ->
    right < Zlength l ->
    pointf_xy_partitioned_at l left right p ->
    pointf_xy_sorted_range l left (p - 1) ->
    pointf_xy_sorted_range l (p + 1) right ->
    pointf_xy_sorted_range l left right.
Proof.
  intros l left right p Hfin Hleft Hrightlen Hpart Hsorted_left Hsorted_right.
  pose proof Hpart as Hpart_full.
  destruct Hpart_full as [Hprange _].
  unfold pointf_xy_sorted_range in *.
  intros i j Hij Hj.
  assert (Hi_len : 0 <= i < Zlength l) by lia.
  assert (Hj_len : 0 <= j < Zlength l) by lia.
  destruct (Z_lt_ge_dec j p) as [Hjp | Hpj].
  - apply Hsorted_left; lia.
  - destruct (Z_gt_le_dec i p) as [Hip | Hpi].
    + apply Hsorted_right; lia.
    + assert (Hi_cases : i = p \/ i < p) by lia.
      assert (Hj_cases : j = p \/ p < j) by lia.
      destruct Hi_cases as [-> | Hip']; destruct Hj_cases as [-> | Hpj'].
      * apply pointf_cmp_xy_refl__quicksort_top.
        apply pointsf_finite_Znth__quicksort_top; auto; lia.
      * apply Z.lt_le_incl.
        eapply pointf_xy_partitioned_at_right_Znth_lt__quicksort_top.
        -- exact Hleft.
        -- exact Hrightlen.
        -- exact Hpart.
        -- lia.
      * eapply pointf_xy_partitioned_at_left_Znth_le__quicksort_top.
        -- exact Hleft.
        -- lia.
        -- exact Hpart.
        -- lia.
      * eapply pointf_cmp_xy_le_trans__quicksort_top.
        -- apply (pointsf_finite_Znth__quicksort_top l i); auto; lia.
        -- apply (pointsf_finite_Znth__quicksort_top l p); auto; lia.
        -- apply (pointsf_finite_Znth__quicksort_top l j); auto; lia.
        -- eapply pointf_xy_partitioned_at_left_Znth_le__quicksort_top.
           ++ exact Hleft.
           ++ lia.
           ++ exact Hpart.
           ++ lia.
        -- apply Z.lt_le_incl.
           eapply pointf_xy_partitioned_at_right_Znth_lt__quicksort_top.
           ++ exact Hleft.
           ++ exact Hrightlen.
           ++ exact Hpart.
           ++ lia.
Qed.
Lemma pointf_xy_sorted_range_ext__quicksort_top :
  forall l1 l2 left right,
    0 <= left ->
    right < Zlength l1 ->
    Zlength l1 = Zlength l2 ->
    (forall k, left <= k <= right ->
      Znth k l2 default_pointf = Znth k l1 default_pointf) ->
    pointf_xy_sorted_range l1 left right ->
    pointf_xy_sorted_range l2 left right.
Proof.
  intros l1 l2 left right Hleft Hrightlen Hlen Heq Hsorted.
  unfold pointf_xy_sorted_range in *.
  intros i j Hij Hj.
  rewrite Heq by lia.
  rewrite Heq by lia.
  apply Hsorted; lia.
Qed.
Lemma is_andrew_hull_float_permutation_input__quicksort_top :
  forall input mid sorted hull,
    pointf_permutation input mid ->
    pointf_permutation mid sorted ->
    is_andrew_hull_float mid sorted hull ->
    is_andrew_hull_float input sorted hull.
Proof.
  intros input mid sorted hull Hperm1 Hperm2 His.
  unfold is_andrew_hull_float in *.
  destruct His as [Hperm_is His].
  split.
  - eapply Permutation_trans; [exact Hperm1|exact Hperm_is].
  - exact His.
Qed.
Lemma pointsf_finite_replace_Znth__andrew_lower :
  forall l i p,
    pointsf_finite l ->
    pointf_finite p ->
    pointsf_finite (replace_Znth i p l).
Proof.
  unfold pointsf_finite, replace_Znth.
  intros l i p Hfin Hp.
  generalize (Z.to_nat i). clear i.
  induction Hfin as [|x xs Hx Hxs IH]; intros n; destruct n; simpl; constructor; auto.
Qed.
Lemma sublist_replace_Znth_prefix__andrew_lower :
  forall (l : list PointF) k p,
    0 <= k <= Zlength l ->
    sublist 0 k (replace_Znth k p l) = sublist 0 k l.
Proof.
  intros l k p Hk.
  assert (Hl : l = sublist 0 k l ++ sublist k (Zlength l) l).
  {
    rewrite <- (sublist_split 0 (Zlength l) k l) by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  rewrite Hl at 1.
  rewrite replace_Znth_app_r.
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite replace_Znth_nothing.
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite sublist_split_app_l.
  2:{ lia. }
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite sublist_self.
  2:{ rewrite Zlength_sublist by lia. lia. }
  reflexivity.
Qed.
Lemma pointf_pop_trace_prefix_until__andrew_lower :
  forall p before cur out,
    pointf_pop_trace p before cur ->
    pointf_pop_until p cur out ->
    pointf_pop_until p before out.
Proof.
  intros p before cur out Htrace.
  revert out.
  induction Htrace; intros out Huntil.
  - exact Huntil.
  - apply IHHtrace.
    eapply pointf_pop_until_pop; eauto.
Qed.
Lemma pointf_scan_from_nonempty_length__andrew_lower :
  forall initial input out,
    pointf_scan_from initial input out ->
    initial = [] ->
    0 < Zlength input ->
    0 < Zlength out.
Proof.
  intros initial input out Hscan.
  induction Hscan as
    [initial|initial input before p after Hscan IH Hstep]; intros Hinit Hinput.
  - subst. rewrite Zlength_nil in Hinput. lia.
  - destruct (Z_lt_ge_dec 0 (Zlength input)) as [Hinput_pos|Hinput_nonpos].
    + specialize (IH Hinit Hinput_pos).
      destruct Hstep as [reduced [_ Hafter]].
      subst after. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      pose proof (Zlength_nonneg reduced). lia.
    + destruct Hstep as [reduced [_ Hafter]].
      subst after. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      pose proof (Zlength_nonneg reduced). lia.
Qed.
Lemma pointf_pop_trace_positive_length__andrew_lower :
  forall p before chain,
    pointf_pop_trace p before chain ->
    0 < Zlength before ->
    0 < Zlength chain.
Proof.
  intros p before chain Htrace.
  induction Htrace; intros Hpos.
  - exact Hpos.
  - destruct cur as [|a cur']; simpl in *.
    + rewrite Zlength_nil in H. lia.
    + destruct cur' as [|b cur'']; simpl in *.
      * rewrite Zlength_cons, Zlength_nil in H. lia.
      * destruct cur'' as [|c cur''']; simpl.
        -- rewrite Zlength_cons, Zlength_nil. lia.
        -- rewrite Zlength_cons.
           eapply Z.lt_le_trans.
           ++ apply Z.lt_0_1.
           ++ intro Hgt.
              apply Z.compare_gt_iff in Hgt.
              pose proof (Zlength_nonneg
                (b :: match cur''' with
                      | [] => []
                      | _ :: _ => c :: removelast cur'''
                      end)).
              lia.
Qed.
Lemma pointf_lower_scan_inv_after_append__andrew_lower :
  forall sorted before chain read top,
    read < Zlength sorted ->
    pointf_lower_pop_inv sorted before chain read top ->
    pointf_pop_until (Znth read sorted default_pointf) chain chain ->
    (Zlength sorted <= read + 1 -> 2 <= top + 1) ->
    pointf_lower_scan_inv sorted
      (chain ++ [Znth read sorted default_pointf]) (read + 1) (top + 1).
Proof.
  intros sorted before chain read top Hread_lt Hpop Huntil Hdone_next.
  unfold pointf_lower_pop_inv in Hpop.
  destruct Hpop as [Hscan_inv [Htrace Htop]].
  unfold pointf_lower_scan_inv in Hscan_inv.
  destruct Hscan_inv as [[Hread_low Hread_high] [Hbefore_len [Hscan Hdone]]].
  unfold pointf_lower_scan_inv.
  repeat split; try lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite (sublist_split 0 (read + 1) read sorted) by lia.
    rewrite sublist_single with (d := default_pointf) by lia.
    eapply pointf_scan_from_snoc.
    + exact Hscan.
    + unfold pointf_scan_step.
      exists chain. split.
      * eapply pointf_pop_trace_prefix_until__andrew_lower; eauto.
      * reflexivity.
Qed.
Lemma lower_store_prefix__andrew_lower :
  forall hull sorted k i d,
    0 <= k < Zlength hull ->
    0 <= i < Zlength sorted ->
    sublist 0 (k + 1)
      (replace_Znth k
        (pointf_mk
          (pointf_x
            (Znth k
              (replace_Znth k
                (pointf_mk (pointf_x (Znth i sorted d))
                  (pointf_y (Znth k hull d))) hull) d))
          (pointf_y (Znth i sorted d)))
        (replace_Znth k
          (pointf_mk (pointf_x (Znth i sorted d))
            (pointf_y (Znth k hull d))) hull)) =
    sublist 0 k hull ++ [Znth i sorted default_pointf].
Proof.
  intros hull sorted k i d Hk Hi.
  set (hull_x :=
    replace_Znth k
      (pointf_mk (pointf_x (Znth i sorted d))
        (pointf_y (Znth k hull d))) hull).
  set (hull_y :=
    replace_Znth k
      (pointf_mk (pointf_x (Znth k hull_x d))
        (pointf_y (Znth i sorted d))) hull_x).
  change (sublist 0 (k + 1) hull_y =
    sublist 0 k hull ++ [Znth i sorted default_pointf]).
  rewrite (sublist_split 0 (k + 1) k hull_y).
  2:{ split; lia. }
  2:{ subst hull_y hull_x. rewrite Zlength_replace_Znth, Zlength_replace_Znth; lia. }
  subst hull_y.
  rewrite sublist_replace_Znth_prefix__andrew_lower.
  2:{ subst hull_x. rewrite Zlength_replace_Znth. lia. }
  subst hull_x.
  rewrite sublist_replace_Znth_prefix__andrew_lower by lia.
  rewrite sublist_single with (d := d).
  2:{ rewrite Zlength_replace_Znth, Zlength_replace_Znth; lia. }
  rewrite Znth_replace_Znth_Same.
  2:{ rewrite Zlength_replace_Znth. lia. }
  rewrite Znth_replace_Znth_Same by lia.
  rewrite (Znth_indep sorted i d default_pointf) by lia.
  simpl.
  destruct (Znth i sorted default_pointf).
  reflexivity.
Qed.
Lemma pointsf_finite_lower_store__andrew_lower :
  forall hull sorted k i d,
    pointsf_finite hull ->
    pointsf_finite sorted ->
    0 <= k < Zlength hull ->
    0 <= i < Zlength sorted ->
    pointsf_finite
      (replace_Znth k
        (pointf_mk
          (pointf_x
            (Znth k
              (replace_Znth k
                (pointf_mk (pointf_x (Znth i sorted d))
                  (pointf_y (Znth k hull d))) hull) d))
          (pointf_y (Znth i sorted d)))
        (replace_Znth k
          (pointf_mk (pointf_x (Znth i sorted d))
            (pointf_y (Znth k hull d))) hull)).
Proof.
  intros hull sorted k i d Hhull Hsorted Hk Hi.
  assert (Hsorted_i : pointf_finite (Znth i sorted d)).
  {
    rewrite (Znth_indep sorted i d default_pointf) by lia.
    apply pointsf_finite_Znth__swap_partition; auto.
  }
  assert (Hhull_k : pointf_finite (Znth k hull d)).
  {
    rewrite (Znth_indep hull k d default_pointf) by lia.
    apply pointsf_finite_Znth__swap_partition; auto.
  }
  set (hull_x :=
    replace_Znth k
      (pointf_mk (pointf_x (Znth i sorted d))
        (pointf_y (Znth k hull d))) hull).
  assert (Hpx : pointf_finite
    (pointf_mk (pointf_x (Znth i sorted d)) (pointf_y (Znth k hull d)))).
  { split; [apply Hsorted_i|apply Hhull_k]. }
  assert (Hhull_x : pointsf_finite hull_x).
  { subst hull_x. apply pointsf_finite_replace_Znth__andrew_lower; auto. }
  apply pointsf_finite_replace_Znth__andrew_lower.
  - exact Hhull_x.
  - split.
    + assert (Hkx : pointf_finite (Znth k hull_x d)).
      {
        rewrite (Znth_indep hull_x k d default_pointf).
        - apply pointsf_finite_Znth__swap_partition; auto.
          subst hull_x. rewrite Zlength_replace_Znth. lia.
        - subst hull_x. rewrite Zlength_replace_Znth. lia.
      }
      destruct Hkx as [Hkx _]. exact Hkx.
    + apply Hsorted_i.
Qed.
Lemma fp32_compare_zero_of_real__andrew_lower :
  forall x,
    fp32_compare x fp32_zero = fp32_compare x (fp32_of_real 0.0).
Proof.
  intros x.
  replace (fp32_of_real 0.0) with (fp32_of_real 0%R).
  2:{ f_equal; lra. }
  unfold fp32_of_real, rounded32.
  rewrite Flocq.Core.Generic_fmt.round_0
    by apply Flocq.IEEE754.BinarySingleNaN.valid_rnd_round_mode.
  rewrite Flocq.Core.Generic_fmt.scaled_mantissa_0.
  rewrite Flocq.Core.Raux.Ztrunc_IZR.
  rewrite Flocq.Core.Raux.Rlt_bool_false by lra.
  unfold Binary.binary_normalize, BinarySingleNaN.binary_normalize.
  unfold fp32_zero, fp32_of_bits, b32_of_bits.
  simpl.
  destruct x; reflexivity.
Qed.
Lemma lower_scan_after_store_short__andrew_lower :
  forall n_pre sorted before hull k i d,
    k < 2 ->
    2 <= n_pre ->
    0 <= i ->
    i < n_pre ->
    0 <= k ->
    k <= i ->
    Zlength sorted = n_pre ->
    Zlength hull = 2 * n_pre ->
    pointf_lower_pop_inv sorted before (sublist 0 k hull) i k ->
    pointf_lower_scan_inv sorted
      (sublist 0 (k + 1)
        (replace_Znth k
          (pointf_mk
            (pointf_x
              (Znth k
                (replace_Znth k
                  (pointf_mk (pointf_x (Znth i sorted d))
                    (pointf_y (Znth k hull d))) hull) d))
            (pointf_y (Znth i sorted d)))
          (replace_Znth k
            (pointf_mk (pointf_x (Znth i sorted d))
              (pointf_y (Znth k hull d))) hull)))
      (i + 1) (k + 1).
Proof.
  intros n_pre sorted before hull k i d Hshort Hn Hilo Hilt Hklo Hki Hsorted_len
    Hhull_len Hpop.
  rewrite lower_store_prefix__andrew_lower by lia.
  eapply pointf_lower_scan_inv_after_append__andrew_lower; eauto.
  - rewrite Hsorted_len. lia.
  - apply pointf_pop_until_short.
    rewrite Zlength_sublist by lia. lia.
  - intros Hdone_next.
    destruct Hpop as [Hscan [Htrace Htop]].
    assert (Hinput_pos : 0 < Zlength (sublist 0 i sorted)).
    {
      rewrite Zlength_sublist by lia.
      lia.
    }
    unfold pointf_lower_scan_inv in Hscan.
    destruct Hscan as [_ [_ [Hscan_from _]]].
    assert (Hbefore_pos : 0 < Zlength before).
    {
      eapply pointf_scan_from_nonempty_length__andrew_lower; eauto.
    }
    assert (Hchain_pos : 0 < Zlength (sublist 0 k hull)).
    {
      eapply pointf_pop_trace_positive_length__andrew_lower; eauto.
    }
    rewrite Zlength_sublist in Hchain_pos by lia.
    lia.
Qed.
Lemma lower_scan_after_store_ccw__andrew_lower :
  forall n_pre sorted before hull k i d,
    fp32_gt
      (fp32_sub
        (fp32_mul
          (fp32_sub (pointf_x (Znth (k - 1) hull d))
            (pointf_x (Znth (k - 2) hull d)))
          (fp32_sub (pointf_y (Znth i sorted d))
            (pointf_y (Znth (k - 2) hull d))))
        (fp32_mul
          (fp32_sub (pointf_y (Znth (k - 1) hull d))
            (pointf_y (Znth (k - 2) hull d)))
          (fp32_sub (pointf_x (Znth i sorted d))
            (pointf_x (Znth (k - 2) hull d))))) (fp32_of_real 0.0) ->
    k >= 2 ->
    2 <= n_pre ->
    0 <= i ->
    i < n_pre ->
    0 <= k ->
    k <= i ->
    Zlength sorted = n_pre ->
    Zlength hull = 2 * n_pre ->
    pointf_lower_pop_inv sorted before (sublist 0 k hull) i k ->
    pointf_lower_scan_inv sorted
      (sublist 0 (k + 1)
        (replace_Znth k
          (pointf_mk
            (pointf_x
              (Znth k
                (replace_Znth k
                  (pointf_mk (pointf_x (Znth i sorted d))
                    (pointf_y (Znth k hull d))) hull) d))
            (pointf_y (Znth i sorted d)))
          (replace_Znth k
            (pointf_mk (pointf_x (Znth i sorted d))
              (pointf_y (Znth k hull d))) hull)))
      (i + 1) (k + 1).
Proof.
  intros n_pre sorted before hull k i d Hccw Hkge Hn Hilo Hilt Hklo Hki
    Hsorted_len Hhull_len Hpop.
  rewrite lower_store_prefix__andrew_lower by lia.
  eapply pointf_lower_scan_inv_after_append__andrew_lower; eauto.
  - rewrite Hsorted_len. lia.
  - apply pointf_pop_until_ccw.
    + rewrite Zlength_sublist by lia. lia.
    + unfold pointf_ccw, pointf_cross.
      rewrite ?Zlength_sublist by lia.
      rewrite !Znth_sublist0 by lia.
      rewrite ?Zlength_sublist by lia.
      repeat rewrite <- (Znth_indep hull _ d default_pointf) by lia.
      rewrite <- (Znth_indep sorted i d default_pointf) by lia.
      unfold fp32_gt in *.
      rewrite fp32_compare_zero_of_real__andrew_lower.
      replace (k - 0 - 1) with (k - 1) by lia.
      replace (k - 0 - 2) with (k - 2) by lia.
      exact Hccw.
  - intros. lia.
Qed.
Lemma fp32_compare_zero_of_real__andrew_upper :
  forall x,
    fp32_compare x fp32_zero = fp32_compare x (fp32_of_real 0.0).
Proof.
  intros x.
  replace (fp32_of_real 0.0) with (fp32_of_real 0%R).
  2:{ f_equal; lra. }
  unfold fp32_of_real, rounded32.
  rewrite Flocq.Core.Generic_fmt.round_0
    by apply Flocq.IEEE754.BinarySingleNaN.valid_rnd_round_mode.
  rewrite Flocq.Core.Generic_fmt.scaled_mantissa_0.
  rewrite Flocq.Core.Raux.Ztrunc_IZR.
  rewrite Flocq.Core.Raux.Rlt_bool_false by lra.
  unfold Binary.binary_normalize, BinarySingleNaN.binary_normalize.
  unfold fp32_zero, fp32_of_bits, b32_of_bits.
  simpl.
  destruct x; reflexivity.
Qed.
Lemma pointsf_finite_replace_Znth__andrew_upper :
  forall l i p,
    pointsf_finite l ->
    pointf_finite p ->
    pointsf_finite (replace_Znth i p l).
Proof.
  unfold pointsf_finite, replace_Znth.
  intros l i p Hfin Hp.
  generalize (Z.to_nat i). clear i.
  induction Hfin as [|x xs Hx Hxs IH]; intros n; destruct n; simpl; constructor; auto.
Qed.
Lemma sublist_replace_Znth_prefix__andrew_upper :
  forall (l : list PointF) k p,
    0 <= k <= Zlength l ->
    sublist 0 k (replace_Znth k p l) = sublist 0 k l.
Proof.
  intros l k p Hk.
  assert (Hl : l = sublist 0 k l ++ sublist k (Zlength l) l).
  {
    rewrite <- (sublist_split 0 (Zlength l) k l) by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  rewrite Hl at 1.
  rewrite replace_Znth_app_r.
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite replace_Znth_nothing.
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite sublist_split_app_l.
  2:{ lia. }
  2:{ rewrite Zlength_sublist by lia. lia. }
  rewrite sublist_self.
  2:{ rewrite Zlength_sublist by lia. lia. }
  reflexivity.
Qed.
Lemma upper_store_prefix__andrew_upper :
  forall hull sorted k i d,
    0 <= k < Zlength hull ->
    0 <= i < Zlength sorted ->
    sublist 0 (k + 1)
      (replace_Znth k
        (pointf_mk
          (pointf_x
            (Znth k
              (replace_Znth k
                (pointf_mk (pointf_x (Znth i sorted d))
                  (pointf_y (Znth k hull d))) hull) d))
          (pointf_y (Znth i sorted d)))
        (replace_Znth k
          (pointf_mk (pointf_x (Znth i sorted d))
            (pointf_y (Znth k hull d))) hull)) =
    sublist 0 k hull ++ [Znth i sorted default_pointf].
Proof.
  intros hull sorted k i d Hk Hi.
  set (hull_x :=
    replace_Znth k
      (pointf_mk (pointf_x (Znth i sorted d))
        (pointf_y (Znth k hull d))) hull).
  set (hull_y :=
    replace_Znth k
      (pointf_mk (pointf_x (Znth k hull_x d))
        (pointf_y (Znth i sorted d))) hull_x).
  change (sublist 0 (k + 1) hull_y =
    sublist 0 k hull ++ [Znth i sorted default_pointf]).
  rewrite (sublist_split 0 (k + 1) k hull_y).
  2:{ split; lia. }
  2:{ subst hull_y hull_x. rewrite Zlength_replace_Znth, Zlength_replace_Znth; lia. }
  subst hull_y.
  rewrite sublist_replace_Znth_prefix__andrew_upper.
  2:{ subst hull_x. rewrite Zlength_replace_Znth. lia. }
  subst hull_x.
  rewrite sublist_replace_Znth_prefix__andrew_upper by lia.
  rewrite sublist_single with (d := d).
  2:{ rewrite Zlength_replace_Znth, Zlength_replace_Znth; lia. }
  rewrite Znth_replace_Znth_Same.
  2:{ rewrite Zlength_replace_Znth. lia. }
  rewrite Znth_replace_Znth_Same by lia.
  rewrite (Znth_indep sorted i d default_pointf) by lia.
  simpl.
  destruct (Znth i sorted default_pointf).
  reflexivity.
Qed.
Lemma pointsf_finite_upper_store__andrew_upper :
  forall hull sorted k i d,
    pointsf_finite hull ->
    pointsf_finite sorted ->
    0 <= k < Zlength hull ->
    0 <= i < Zlength sorted ->
    pointsf_finite
      (replace_Znth k
        (pointf_mk
          (pointf_x
            (Znth k
              (replace_Znth k
                (pointf_mk (pointf_x (Znth i sorted d))
                  (pointf_y (Znth k hull d))) hull) d))
          (pointf_y (Znth i sorted d)))
        (replace_Znth k
          (pointf_mk (pointf_x (Znth i sorted d))
            (pointf_y (Znth k hull d))) hull)).
Proof.
  intros hull sorted k i d Hhull Hsorted Hk Hi.
  assert (Hsorted_i : pointf_finite (Znth i sorted d)).
  {
    rewrite (Znth_indep sorted i d default_pointf) by lia.
    apply pointsf_finite_Znth__swap_partition; auto.
  }
  assert (Hhull_k : pointf_finite (Znth k hull d)).
  {
    rewrite (Znth_indep hull k d default_pointf) by lia.
    apply pointsf_finite_Znth__swap_partition; auto.
  }
  set (hull_x :=
    replace_Znth k
      (pointf_mk (pointf_x (Znth i sorted d))
        (pointf_y (Znth k hull d))) hull).
  assert (Hpx : pointf_finite
    (pointf_mk (pointf_x (Znth i sorted d)) (pointf_y (Znth k hull d)))).
  { split; [apply Hsorted_i|apply Hhull_k]. }
  assert (Hhull_x : pointsf_finite hull_x).
  { subst hull_x. apply pointsf_finite_replace_Znth__andrew_upper; auto. }
  apply pointsf_finite_replace_Znth__andrew_upper.
  - exact Hhull_x.
  - split.
    + assert (Hkx : pointf_finite (Znth k hull_x d)).
      {
        rewrite (Znth_indep hull_x k d default_pointf).
        - apply pointsf_finite_Znth__swap_partition; auto.
          subst hull_x. rewrite Zlength_replace_Znth. lia.
        - subst hull_x. rewrite Zlength_replace_Znth. lia.
      }
      destruct Hkx as [Hkx _]. exact Hkx.
    + apply Hsorted_i.
Qed.
Lemma length_removelast_le__andrew_upper :
  forall (l : list PointF), (List.length (removelast l) <= List.length l)%nat.
Proof.
  induction l as [|a l IH].
  - simpl. lia.
  - destruct l as [|b l].
    + simpl. lia.
    + simpl. apply le_n_S. exact IH.
Qed.
Lemma Zlength_removelast_le__andrew_upper :
  forall (l : list PointF), Zlength (removelast l) <= Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_le.
  apply length_removelast_le__andrew_upper.
Qed.
Lemma pointf_upper_pop_trace_length_le__andrew_upper :
  forall lower_bound p before cur,
    pointf_upper_pop_trace lower_bound p before cur ->
    Zlength cur <= Zlength before.
Proof.
  intros lower_bound p before cur Htrace.
  induction Htrace.
  - lia.
  - pose proof (Zlength_removelast_le__andrew_upper cur).
    lia.
Qed.
Lemma pointf_upper_pop_trace_prefix_until__andrew_upper :
  forall lower_bound p before cur out,
    pointf_upper_pop_trace lower_bound p before cur ->
    pointf_upper_pop_until lower_bound p cur out ->
    pointf_upper_pop_until lower_bound p before out.
Proof.
  intros lower_bound p before cur out Htrace.
  revert out.
  induction Htrace; intros out Huntil.
  - exact Huntil.
  - apply IHHtrace.
    eapply pointf_upper_pop_until_pop; eauto.
Qed.
Lemma rev_sublist_snoc_Znth__andrew_upper :
  forall sorted read,
    0 <= read < Zlength sorted - 1 ->
    rev (sublist read (Zlength sorted - 1) sorted) =
    rev (sublist (read + 1) (Zlength sorted - 1) sorted) ++
      [Znth read sorted default_pointf].
Proof.
  intros sorted read Hread.
  rewrite (sublist_split read (Zlength sorted - 1) (read + 1) sorted)
    by lia.
  rewrite sublist_single with (d := default_pointf) by lia.
  rewrite rev_app_distr. reflexivity.
Qed.
Lemma sublist_app_prefix__andrew_upper :
  forall (chain : list PointF) p lower_n,
    0 <= lower_n <= Zlength chain ->
    sublist 0 lower_n (chain ++ [p]) = sublist 0 lower_n chain.
Proof.
  intros chain p lower_n Hlower.
  rewrite sublist_split_app_l by lia.
  reflexivity.
Qed.
Lemma pointf_upper_scan_inv_after_append__andrew_upper :
  forall sorted lower before chain read top lower_n,
    0 <= read < Zlength sorted - 1 ->
    pointf_upper_pop_inv sorted lower before chain read top lower_n ->
    pointf_upper_pop_until lower_n (Znth read sorted default_pointf) chain chain ->
    pointf_upper_scan_inv sorted lower
      (chain ++ [Znth read sorted default_pointf]) read (top + 1) lower_n.
Proof.
  intros sorted lower before chain read top lower_n Hread Hpop Huntil.
  unfold pointf_upper_pop_inv in Hpop.
  destruct Hpop as [Hscan [Htrace [Htop [Hlower_chain Hle_chain]]]].
  unfold pointf_upper_scan_inv in Hscan.
  destruct Hscan as
    [Hread_next [Htop_before [Hlower_len
      [Hlower_before [Hle_before [Hscan_lower [Hupper_scan Hcap]]]]]]].
  destruct Hcap as [Hlower_sorted [Hcap_len [Hcap_strict Hcap_done]]].
  pose proof (pointf_upper_pop_trace_length_le__andrew_upper _ _ _ _ Htrace)
    as Hchain_le_before.
  assert (Hlower_chain_len : lower_n <= Zlength chain).
  { rewrite <- Htop. exact Hle_chain. }
  unfold pointf_upper_scan_inv.
  split; [lia|].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split; [exact Hlower_len|].
    split.
    + rewrite Hlower_chain.
      rewrite (sublist_app_prefix__andrew_upper chain
        (Znth read sorted default_pointf) lower_n).
      2:{ rewrite Hlower_len. split; [apply Zlength_nonneg|lia]. }
      reflexivity.
    + split.
      * lia.
      * split; [exact Hscan_lower|].
        split.
        -- rewrite rev_sublist_snoc_Znth__andrew_upper by lia.
           eapply pointf_upper_scan_from_snoc.
           ++ exact Hupper_scan.
           ++ unfold pointf_upper_scan_step.
              exists chain. split; [|reflexivity].
              eapply pointf_upper_pop_trace_prefix_until__andrew_upper; eauto.
        -- unfold pointf_upper_capacity.
           repeat split.
           ++ exact Hlower_sorted.
           ++ rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
           ++ intro Hread_pos.
              rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
           ++ intro Hread_done.
              rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma pointf_drop_last_sublist_prefix__andrew_upper :
  forall l k,
    0 < k <= Zlength l ->
    pointf_drop_last (sublist 0 k l) = sublist 0 (k - 1) l.
Proof.
  intros l k Hk.
  unfold pointf_drop_last.
  rewrite (sublist_split 0 k (k - 1) l) by lia.
  replace (sublist (k - 1) k l)
    with (sublist (k - 1) ((k - 1) + 1) l) by (f_equal; lia).
  rewrite sublist_single with (d := default_pointf) by lia.
  rewrite removelast_last by (rewrite Zlength_sublist by lia; lia).
  reflexivity.
Qed.
Lemma upper_scan_final_is_andrew_hull__andrew_upper :
  forall sorted lower chain k lower_n,
    2 <= Zlength sorted ->
    pointf_xy_sorted sorted ->
    pointf_upper_scan_inv sorted lower chain 0 k lower_n ->
    is_andrew_hull_float sorted sorted (pointf_drop_last chain).
Proof.
  intros sorted lower chain k lower_n Hsorted_len Hsorted Hinv.
  unfold pointf_upper_scan_inv in Hinv.
  destruct Hinv as
    [Hread [Htop [Hlower_len [Hlower_prefix
      [Hlower_le [Hlower_scan [Hupper_scan Hcap]]]]]]].
  unfold is_andrew_hull_float.
  repeat split.
  - unfold pointf_permutation. reflexivity.
  - exact Hsorted.
  - destruct (Z.leb_spec (Zlength sorted) 1) as [Hsmall|Hlarge].
    + lia.
    + exists lower, chain.
      repeat split; auto.
      replace (sublist 0 (Zlength sorted - 1) sorted)
        with (sublist 0 (Zlength sorted - 1) sorted) by reflexivity.
      rewrite <- Hlower_len.
      exact Hupper_scan.
Qed.
