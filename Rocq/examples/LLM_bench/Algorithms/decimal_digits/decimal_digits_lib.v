From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

(** Decode the significant numeric digits of each fixed-width input row. *)
Definition DecimalRowValues (rows : list (list Z)) (lengths : list Z) : list Z :=
  map (fun row_length =>
    fold_left (fun value digit => 10 * value + digit)
      (sublist 0 (snd row_length) (fst row_length)) 0)
    (combine rows lengths).

Example decimal_row_upper_boundary :
  DecimalRowValues [[1;0;0;0;0;0;0;0;0;0]; [9;9;9;9;9;9;9;9;9;9]] [10;10] =
  [1000000000; 9999999999].
Proof. reflexivity. Qed.

From SimpleC.SL Require Import Mem SeparationLogic ArrayLib Array2Lib.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Local Open Scope sac.

Lemma decimal_rows_flat_length rows width :
  Forall (fun row : list Z => Zlength row = width) rows ->
  Zlength (concat rows) = Zlength rows * width.
Proof.
  intros Hrows. induction Hrows; cbn [concat].
  - rewrite !Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, H, IHHrows. ring.
Qed.

Lemma decimal_rows_flatten_at rows x lo hi width :
  Zlength rows = hi - lo -> 0 <= width ->
  store_array_rec (IntArray2.row_store width) x lo hi rows |--
  IntArray.full (x + lo * width * sizeof(INT)) ((hi - lo) * width) (concat rows).
Proof.
  revert x lo hi width. induction rows as [|row rows IH]; intros x lo hi width Hlen Hw.
  - rewrite Zlength_nil in Hlen. cbn [store_array_rec concat].
    replace ((hi - lo) * width) with 0 by nia.
    rewrite IntArray.full_empty. entailer!.
  - rewrite Zlength_cons in Hlen. cbn [store_array_rec concat].
    unfold IntArray2.row_store, IntArray2.row_addr.
    sep_apply (IH x (lo + 1) hi width ltac:(lia) Hw).
    change (IntArray.full (x + lo * width * sizeof(INT)) width row **
      IntArray.full (x + (lo + 1) * width * sizeof(INT)) ((hi - (lo + 1)) * width) (concat rows) |--
      IntArray.full (x + lo * width * sizeof(INT)) ((hi - lo) * width) (row ++ concat rows)).
    replace (x + (lo + 1) * width * sizeof(INT)) with
      (x + lo * width * sizeof(INT) + width * sizeof(INT)) by ring.
    replace ((hi - (lo + 1)) * width) with ((hi - lo) * width - width) by ring.
    apply IntArray.full_merge_to_full.
    pose proof (Zlength_nonneg rows). nia.
Qed.

Lemma decimal_rows_flatten rows x count width :
  Zlength rows = count -> 0 <= width ->
  IntArray2.full x count width rows |-- IntArray.full x (count * width) (concat rows).
Proof.
  intros Hlen Hw. unfold IntArray2.full, store_array.
  pose proof (decimal_rows_flatten_at rows x 0 count width ltac:(lia) Hw) as H.
  replace (x + 0 * width * sizeof(INT)) with x in H by lia.
  replace ((count - 0) * width) with (count * width) in H by ring. exact H.
Qed.

Lemma decimal_rows_unflatten_at rows x lo width :
  Forall (fun row : list Z => Zlength row = width) rows -> 0 <= width ->
  IntArray.full (x + lo * width * sizeof(INT)) (Zlength rows * width) (concat rows) |--
  store_array_rec (IntArray2.row_store width) x lo (lo + Zlength rows) rows.
Proof.
  intros Hrows Hw. revert x lo. induction Hrows as [|row rows Hrow Hrows IH]; intros x lo.
  - cbn [concat store_array_rec]. rewrite Zlength_nil.
    replace (0 * width) with 0 by lia. rewrite IntArray.full_empty. entailer!.
  - cbn [concat store_array_rec]. rewrite Zlength_cons.
    sep_apply (IntArray.full_split_to_full (x + lo * width * sizeof(INT)) width
      ((Zlength rows + 1) * width) (row ++ concat rows)
      ltac:(pose proof (Zlength_nonneg rows); nia)).
    assert (Htail_length : Zlength (concat rows) = Zlength rows * width)
      by (apply decimal_rows_flat_length; exact Hrows).
    replace (sublist 0 width (row ++ concat rows)) with row.
    2: { rewrite <- Hrow. symmetry. apply sublist_app_exact1. }
    replace (sublist width ((Zlength rows + 1) * width) (row ++ concat rows)) with (concat rows).
    2: { replace ((Zlength rows + 1) * width) with (Zlength (row ++ concat rows))
           by (rewrite Zlength_app; nia).
         rewrite <- Hrow. symmetry.
         rewrite sublist_split_app_r with (len := Zlength row)
           by (try reflexivity; rewrite Zlength_app; pose proof (Zlength_nonneg (concat rows)); lia).
         rewrite Zlength_app.
         replace (Zlength row - Zlength row) with 0 by lia.
         replace (Zlength row + Zlength (concat rows) - Zlength row) with (Zlength (concat rows)) by lia.
         apply sublist_self. reflexivity. }
    replace ((Zlength rows + 1) * width - width) with (Zlength rows * width) by ring.
    replace (x + lo * width * sizeof(INT) + width * sizeof(INT)) with
      (x + (lo + 1) * width * sizeof(INT)) by ring.
    sep_apply (IH x (lo + 1)).
    replace (lo + (Zlength rows + 1)) with (lo + 1 + Zlength rows) by lia.
    replace (lo + Z.succ (Zlength rows)) with (lo + 1 + Zlength rows) by lia.
    unfold IntArray2.row_store, IntArray2.row_addr. repeat cancel.
    apply derivable1_refl.
Qed.

Lemma decimal_rows_unflatten rows x count width :
  Zlength rows = count ->
  Forall (fun row : list Z => Zlength row = width) rows -> 0 <= width ->
  IntArray.full x (count * width) (concat rows) |-- IntArray2.full x count width rows.
Proof.
  intros Hcount Hrows Hw.
  pose proof (decimal_rows_unflatten_at rows x 0 width Hrows Hw) as H.
  replace (x + 0 * width * sizeof(INT)) with x in H by lia.
  rewrite Hcount, Z.add_0_l in H. exact H.
Qed.

Lemma decimal_rows_lengths_from_map rows width :
  Forall (eq width) (map (@Zlength Z) rows) ->
  Forall (fun row : list Z => Zlength row = width) rows.
Proof.
  induction rows; cbn; intros H.
  - constructor.
  - inversion H; subst. constructor; [congruence | apply IHrows; assumption].
Qed.

Lemma decimal_rows_flat_row rows width i :
  Forall (fun row : list Z => Zlength row = width) rows -> 0 <= width ->
  0 <= i < Zlength rows ->
  Znth i rows [] = sublist (i * width) ((i + 1) * width) (concat rows).
Proof.
  intros Hrows Hw. revert i. induction Hrows as [|row rows Hrow Hrows IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi. cbn [concat].
    destruct (Z.eq_dec i 0) as [-> | Hpos].
    + rewrite Znth0_cons. replace (0 * width) with 0 by lia.
      replace ((0 + 1) * width) with width by lia.
      rewrite <- Hrow. symmetry. apply sublist_app_exact1.
    + rewrite Znth_cons by lia. rewrite IH by lia.
      rewrite sublist_split_app_r with (len := width) by (try assumption; nia).
      replace (i * width - width) with ((i - 1) * width) by ring.
      replace ((i + 1) * width - width) with ((i - 1 + 1) * width) by ring. reflexivity.
Qed.

Lemma decimal_rows_concat_unique rows flat count width :
  0 < width -> Zlength rows = count -> Zlength flat = count * width ->
  Forall (fun row : list Z => Zlength row = width) rows ->
  (forall i, 0 <= i < count ->
    Znth i rows [] = sublist (i * width) ((i + 1) * width) flat) ->
  flat = concat rows.
Proof.
  intros Hw Hrows Hflat Hwidth Hview.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite decimal_rows_flat_length with (width := width) by exact Hwidth. lia.
  - intros k Hk.
    assert (Hr : 0 <= k / width < count).
    { split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; nia. }
    pose proof (Z.div_mod k width ltac:(lia)) as Hdivide.
    pose proof (Z.mod_pos_bound k width ltac:(lia)) as Hmod.
    pose proof (Hview (k / width) Hr) as Hold.
    pose proof (decimal_rows_flat_row rows width (k / width) Hwidth ltac:(lia) ltac:(lia)) as Hnew.
    assert (Hlength : Zlength (concat rows) = count * width)
      by (rewrite decimal_rows_flat_length with (width := width) by exact Hwidth; lia).
    apply (f_equal (fun row => Znth (k mod width) row 0)) in Hold, Hnew.
    rewrite Znth_sublist in Hold by nia.
    rewrite Znth_sublist in Hnew by nia.
    replace (k mod width + k / width * width) with k in Hold, Hnew by nia.
    congruence.
Qed.
