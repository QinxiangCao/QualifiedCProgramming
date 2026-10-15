Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

Module Array2.

Definition some_rows (l : list (list Z)) : list (list (option Z)) :=
  map (map (@Some Z)) l.

Definition mixed_cell (row : list (option Z)) (j v : Z) : Prop :=
  Znth j row None = Some v.

(* Value stored at column [j] of a partially initialized row, and the side
   condition that the column really is initialized.  A strategy rule needs the
   value as an equation (so the engine can determine it) and the
   definedness as a separate obligation. *)
Definition mixed_val (row : list (option Z)) (j : Z) : Z :=
  match Znth j row None with
  | Some v => v
  | None => 0
  end.

Definition mixed_def (row : list (option Z)) (j : Z) : Prop :=
  exists v, Znth j row None = Some v.

Lemma mixed_def_val : forall row j,
  mixed_def row j -> Znth j row None = Some (mixed_val row j).
Proof.
  intros row j [v Hv]. unfold mixed_val. rewrite Hv. reflexivity.
Qed.

Lemma mixed_cell_def : forall row j v,
  mixed_cell row j v -> mixed_def row j.
Proof.
  intros row j v H. exists v. exact H.
Qed.

Lemma mixed_cell_val : forall row j v,
  mixed_cell row j v -> mixed_val row j = v.
Proof.
  intros row j v H. unfold mixed_val, mixed_cell in *. rewrite H. reflexivity.
Qed.

Definition replace_mixed_row
    (i : Z) (row : list (option Z))
    (rows : list (list (option Z))) : list (list (option Z)) :=
  replace_Znth i row rows.

Definition replace_row
    (i : Z) (row : list Z) (rows : list (list Z)) : list (list Z) :=
  replace_Znth i row rows.

Lemma replace_row_Znth : forall i (rows : list (list Z)) d,
  replace_row i (Znth i rows d) rows = rows.
Proof.
  intros. unfold replace_row. apply replace_Znth_Znth.
Qed.

Lemma replace_mixed_row_Znth : forall i (rows : list (list (option Z))) d,
  replace_mixed_row i (Znth i rows d) rows = rows.
Proof.
  intros. unfold replace_mixed_row. apply replace_Znth_Znth.
Qed.

(* The shape a read-only cell access leaves behind: the 1D rules rewrite the
   row into replace_Znth j (Znth j row) row, and the 2D fold wraps that in
   replace_row.  Both collapse to the identity, so the whole round-trip
   reduces to these two rewrites instead of a separation-logic argument. *)
Lemma replace_row_roundtrip : forall i j (rows : list (list Z)) d d',
  replace_row i (replace_Znth j (Znth j (Znth i rows d) d') (Znth i rows d)) rows
    = rows.
Proof.
  intros. rewrite replace_Znth_Znth. apply replace_row_Znth.
Qed.

Lemma replace_mixed_row_roundtrip :
  forall i j (rows : list (list (option Z))) d d',
  replace_mixed_row i
    (replace_Znth j (Znth j (Znth i rows d) d') (Znth i rows d)) rows
    = rows.
Proof.
  intros. rewrite replace_Znth_Znth. apply replace_mixed_row_Znth.
Qed.

End Array2.

(* Conversions between the 2D undef / mixed / full views.  The 1D library has
   ElemArray.undef_full_to_mixed_full and ElemArray.mixed_full_to_full; the 2D
   functor stops at mixed_full_to_undef_full, so the two directions a
   partially-initialized 2D array actually needs -- entering the mixed world
   from undef storage, and leaving it once every cell is written -- are proved
   here by induction over the row array. *)
Module Array2Convert.

Definition undef_rows (n m : Z) : list (list (option Z)) :=
  repeat (repeat None (Z.to_nat m)) (Z.to_nat n).

Lemma int_undef_rec_to_mixed_rec : forall (k : nat) (x : addr) (lo hi m : Z),
  store_undef_array_rec (IntArray2.undef_row_store m) x lo hi k
  |-- store_array_rec (IntArray2.mixed_row_store m) x lo hi
        (repeat (repeat None (Z.to_nat m)) k).
Proof.
  induction k; intros; simpl.
  - entailer!.
  - unfold IntArray2.undef_row_store, IntArray2.mixed_row_store.
    sep_apply IntArray.undef_full_to_mixed_full.
    sep_apply IHk.
    entailer!.
Qed.

Lemma int_undef_full_to_mixed_full : forall x n m,
  IntArray2.undef_full x n m |-- IntArray2.mixed_full x n m (undef_rows n m).
Proof.
  intros.
  unfold IntArray2.undef_full, IntArray2.mixed_full, undef_rows,
         store_undef_array, store_array.
  apply int_undef_rec_to_mixed_rec.
Qed.

Lemma int_mixed_rec_to_rec : forall (l : list (list Z)) (x : addr) (lo hi m : Z),
  store_array_rec (IntArray2.mixed_row_store m) x lo hi (map (map (@Some Z)) l)
  |-- store_array_rec (IntArray2.row_store m) x lo hi l.
Proof.
  induction l; intros; simpl.
  - entailer!.
  - unfold IntArray2.mixed_row_store, IntArray2.row_store.
    sep_apply IntArray.mixed_full_to_full.
    sep_apply IHl.
    entailer!.
Qed.

Lemma int_mixed_full_to_full : forall x n m l,
  IntArray2.mixed_full x n m (Array2.some_rows l) |-- IntArray2.full x n m l.
Proof.
  intros.
  unfold IntArray2.mixed_full, IntArray2.full, Array2.some_rows, store_array.
  apply int_mixed_rec_to_rec.
Qed.

Lemma char_mixed_rec_to_rec :
  forall (l : list (list Z)) (x : addr) (lo hi m : Z),
  store_array_rec (CharArray2.mixed_row_store m) x lo hi (map (map (@Some Z)) l)
  |-- store_array_rec (CharArray2.row_store m) x lo hi l.
Proof.
  induction l; intros; simpl.
  - entailer!.
  - unfold CharArray2.mixed_row_store, CharArray2.row_store.
    sep_apply CharArray.mixed_full_to_full.
    sep_apply IHl.
    entailer!.
Qed.

Lemma char_mixed_full_to_full : forall x n m l,
  CharArray2.mixed_full x n m (Array2.some_rows l) |-- CharArray2.full x n m l.
Proof.
  intros.
  unfold CharArray2.mixed_full, CharArray2.full, Array2.some_rows, store_array.
  apply char_mixed_rec_to_rec.
Qed.

Lemma char_undef_rec_to_mixed_rec : forall (k : nat) (x : addr) (lo hi m : Z),
  store_undef_array_rec (CharArray2.undef_row_store m) x lo hi k
  |-- store_array_rec (CharArray2.mixed_row_store m) x lo hi
        (repeat (repeat None (Z.to_nat m)) k).
Proof.
  induction k; intros; simpl.
  - entailer!.
  - unfold CharArray2.undef_row_store, CharArray2.mixed_row_store.
    sep_apply CharArray.undef_full_to_mixed_full.
    sep_apply IHk.
    entailer!.
Qed.

Lemma char_undef_full_to_mixed_full : forall x n m,
  CharArray2.undef_full x n m |-- CharArray2.mixed_full x n m (undef_rows n m).
Proof.
  intros.
  unfold CharArray2.undef_full, CharArray2.mixed_full, undef_rows,
         store_undef_array, store_array.
  apply char_undef_rec_to_mixed_rec.
Qed.

End Array2Convert.
