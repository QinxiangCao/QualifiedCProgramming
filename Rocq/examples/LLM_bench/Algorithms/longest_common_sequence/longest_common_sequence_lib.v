From Coq Require Import ZArith List.
From AUXLib Require Import ListLib MonotonicList.
Import ListNotations.
Local Open Scope Z_scope.

(** Row-major address using the caller-selected runtime dimension. *)
Definition LCSNCellIndex (n row col : Z) : Z :=
  row * (n + 1) + col.

(** The mathematical prefix-table equation for one public cell. *)
Definition LCSNCellRecurrence
    (xs ys table : list Z) (n row col : Z) : Prop :=
  ((row = 0 \/ col = 0) /\
     Znth (LCSNCellIndex n row col) table 0 = 0) \/
  (0 < row /\ 0 < col /\
    ((Znth (row - 1) xs 0 = Znth (col - 1) ys 0 /\
       Znth (LCSNCellIndex n row col) table 0 =
         Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1) \/
     (Znth (row - 1) xs 0 <> Znth (col - 1) ys 0 /\
       Znth (LCSNCellIndex n row col) table 0 =
         Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0)))).

(** Complete observable LCS table for equal prefix bounds [n]. *)
Definition LCSNTableResultFacts
    (xs ys : list Z) (n : Z) (table : list Z) : Prop :=
  Zlength table = (n + 1) * (n + 1) /\
  forall row col,
    0 <= row <= n ->
    0 <= col <= n ->
    LCSNCellRecurrence xs ys table n row col.

(** A mixed array retains [None] for cells that the C program has not yet
    initialized.  [table] is the mathematical table being revealed. *)
Definition LCSNLogicalTableShape
    (mixed : list (option Z)) (table : list Z) (n : Z) : Prop :=
  Zlength mixed = (n + 1) * (n + 1) /\
  Zlength table = (n + 1) * (n + 1).

Definition LCSNCellInitialized
    (mixed : list (option Z)) (table : list Z)
    (n row col : Z) : Prop :=
  Znth (LCSNCellIndex n row col) mixed None =
    Some (Znth (LCSNCellIndex n row col) table 0).

Definition LCSNBoundaryCell
    (mixed : list (option Z)) (table : list Z)
    (n row col : Z) : Prop :=
  LCSNCellInitialized mixed table n row col /\
  Znth (LCSNCellIndex n row col) table 0 = 0.

Definition LCSNInteriorCellFacts
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n row col : Z) : Prop :=
  LCSNCellInitialized mixed table n row col /\
  LCSNCellRecurrence xs ys table n row col /\
  0 <= Znth (LCSNCellIndex n row col) table 0 <= Z.min row col.

Definition LCSNCellUndefined
    (mixed : list (option Z)) (n row col : Z) : Prop :=
  Znth (LCSNCellIndex n row col) mixed None = None.

Definition LCSNBoundariesReady
    (mixed : list (option Z)) (table : list Z) (n : Z) : Prop :=
  (forall row,
    0 <= row <= n ->
    LCSNBoundaryCell mixed table n row 0) /\
  (forall col,
    0 <= col <= n ->
    LCSNBoundaryCell mixed table n 0 col).

Definition LCSNCompletedInteriorRowsFacts
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  forall row col,
    1 <= row < rows_done ->
    1 <= col <= n ->
    LCSNInteriorCellFacts xs ys mixed table n row col.

Definition LCSNInteriorRowsUndefinedFromFacts
    (mixed : list (option Z)) (n rows_from : Z) : Prop :=
  forall row col,
    rows_from <= row <= n ->
    1 <= col <= n ->
    LCSNCellUndefined mixed n row col.

(** Stable state of the first, strided initialization loop.  The predicate
    classifies the entire square, not only the written column prefix. *)
Definition LCSNColumnProgressFacts
    (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  (forall row,
    0 <= row < rows_done ->
    LCSNBoundaryCell mixed table n row 0) /\
  (forall row,
    rows_done <= row <= n ->
    LCSNCellUndefined mixed n row 0) /\
  (forall row col,
    0 <= row <= n ->
    1 <= col <= n ->
    LCSNCellUndefined mixed n row col).

(** Stable state of the row-zero initialization loop; the first column is
    already complete, [cols_done] records the row-zero prefix, and every
    complementary cell is explicitly undefined. *)
Definition LCSNBoundaryProgressFacts
    (mixed : list (option Z)) (table : list Z)
    (n cols_done : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  (forall row,
    0 <= row <= n ->
    LCSNBoundaryCell mixed table n row 0) /\
  (forall col,
    1 <= col < cols_done ->
    LCSNBoundaryCell mixed table n 0 col) /\
  (forall col,
    cols_done <= col <= n ->
    LCSNCellUndefined mixed n 0 col) /\
  (forall row col,
    1 <= row <= n ->
    1 <= col <= n ->
    LCSNCellUndefined mixed n row col).

(** Outer-loop state: completed rows have their final meanings, while the
    entire future interior is still undefined. *)
Definition LCSNRowsProgressFacts
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRowsFacts xs ys mixed table n rows_done /\
  LCSNInteriorRowsUndefinedFromFacts mixed n rows_done.

(** Inner-loop state.  Unlike [LCSNRowsProgressFacts], it treats the current row
    separately so that a written prefix can coexist with an undefined suffix. *)
Definition LCSNRowProgressFacts
    (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
    (n row next_col : Z) : Prop :=
  LCSNLogicalTableShape mixed table n /\
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRowsFacts xs ys mixed table n row /\
  (forall col,
    1 <= col < next_col ->
    LCSNInteriorCellFacts xs ys mixed table n row col) /\
  (forall col,
    next_col <= col <= n ->
    LCSNCellUndefined mixed n row col) /\
  LCSNInteriorRowsUndefinedFromFacts mixed n (row + 1).

From Coq Require Import Lia Ring.
From Coq Require Import Lia.
From Coq Require Import micromega.Psatz.
Lemma lcsn_column_progress_zero__column_init_update :
  forall n,
    0 <= n ->
    LCSNColumnProgressFacts
      (repeat (@None Z) (Z.to_nat ((n + 1) * (n + 1))))
      (repeat 0 (Z.to_nat ((n + 1) * (n + 1))))
      n 0.
Proof.
  intros n Hn.
  unfold LCSNColumnProgressFacts.
  split.
  - unfold LCSNLogicalTableShape.
    split;
      rewrite Zlength_correct, repeat_length, Z2Nat.id by nia;
      reflexivity.
  - split.
    + intros row Hrow. exfalso. lia.
    + split.
      * intros row Hrow.
        unfold LCSNCellUndefined.
        apply Znth_repeat.
      * intros row col Hrow Hcol.
        unfold LCSNCellUndefined.
        apply Znth_repeat.
Qed.
Lemma lcsn_column_write_progress__column_init_update :
  forall mixed table n i stride,
    stride = n + 1 ->
    0 <= n ->
    0 <= i <= n ->
    LCSNColumnProgressFacts mixed table n i ->
    LCSNColumnProgressFacts
      (replace_Znth (stride * i) (Some 0) mixed)
      (replace_Znth (stride * i) 0 table)
      n (i + 1).
Proof.
  intros mixed table n i stride Hstride Hn Hi Hprogress.
  subst stride.
  unfold LCSNColumnProgressFacts in Hprogress |-.
  destruct Hprogress as [Hshape [Hprefix [Hcolumn Hother]]].
  unfold LCSNLogicalTableShape in Hshape.
  destruct Hshape as [Hmixed Htable].
  split.
  - unfold LCSNLogicalTableShape.
    rewrite !Zlength_replace_Znth.
    auto.
  - split.
    + intros row Hrow.
      destruct (Z.eq_dec row i) as [-> | Hneq].
      * unfold LCSNBoundaryCell, LCSNCellInitialized, LCSNCellIndex.
        replace (i * (n + 1) + 0) with ((n + 1) * i) by ring.
        split.
        -- rewrite (Znth_replace_Znth_Same None mixed
                      ((n + 1) * i) (Some 0))
             by (rewrite Hmixed; nia).
           rewrite (Znth_replace_Znth_Same 0 table
                      ((n + 1) * i) 0)
             by (rewrite Htable; nia).
           reflexivity.
        -- rewrite (Znth_replace_Znth_Same 0 table
                      ((n + 1) * i) 0)
             by (rewrite Htable; nia).
           reflexivity.
      * specialize (Hprefix row ltac:(lia)).
        unfold LCSNBoundaryCell, LCSNCellInitialized, LCSNCellIndex
          in Hprefix |-.
        destruct Hprefix as [Hinit Hzero].
        split.
        -- unfold LCSNCellInitialized, LCSNCellIndex in Hinit.
           unfold LCSNCellInitialized, LCSNCellIndex.
           rewrite (Znth_replace_Znth_Diff None mixed
                      ((n + 1) * i) (row * (n + 1) + 0) (Some 0))
             by (try rewrite Hmixed; unfold LCSNCellIndex; nia).
           rewrite (Znth_replace_Znth_Diff 0 table
                      ((n + 1) * i) (row * (n + 1) + 0) 0)
             by (try rewrite Htable; unfold LCSNCellIndex; nia).
           exact Hinit.
        -- unfold LCSNCellIndex in Hzero.
           unfold LCSNCellIndex.
           rewrite (Znth_replace_Znth_Diff 0 table
                      ((n + 1) * i) (row * (n + 1) + 0) 0)
             by (try rewrite Htable; unfold LCSNCellIndex; nia).
           exact Hzero.
    + split.
      * intros row Hrow.
        specialize (Hcolumn row ltac:(lia)).
        unfold LCSNCellUndefined, LCSNCellIndex in Hcolumn.
        unfold LCSNCellUndefined, LCSNCellIndex.
        rewrite (Znth_replace_Znth_Diff None mixed
                   ((n + 1) * i) (row * (n + 1) + 0) (Some 0))
          by (try rewrite Hmixed; unfold LCSNCellIndex; nia).
        exact Hcolumn.
      * intros row col Hrow Hcol.
        specialize (Hother row col Hrow Hcol).
        unfold LCSNCellUndefined, LCSNCellIndex in Hother.
        unfold LCSNCellUndefined, LCSNCellIndex.
        assert (Hnew_index :
          0 <= (n + 1) * i < Zlength mixed) by (rewrite Hmixed; nia).
        assert (Hother_index :
          0 <= row * (n + 1) + col < Zlength mixed)
          by (rewrite Hmixed; nia).
        assert (Hdifferent :
          (n + 1) * i <> row * (n + 1) + col).
        { destruct (Z_lt_ge_dec row i); nia. }
        rewrite (Znth_replace_Znth_Diff None mixed
                   ((n + 1) * i) (row * (n + 1) + col) (Some 0))
          by auto.
        exact Hother.
Qed.
Lemma lcsn_column_complete_boundary_start__boundary_phase :
  forall mixed table n,
    0 <= n ->
    LCSNColumnProgressFacts mixed table n (n + 1) ->
    LCSNBoundaryProgressFacts mixed table n 1.
Proof.
  intros mixed table n Hn Hprogress.
  unfold LCSNColumnProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hfirst_column [Hfirst_column_undefined Hinterior_undefined]]].
  unfold LCSNBoundaryProgressFacts.
  split.
  - exact Hshape.
  - split.
    + intros row Hrow.
      apply Hfirst_column.
      lia.
    + split.
      * intros col Hcol.
        lia.
      * split.
        -- intros col Hcol.
           apply Hinterior_undefined; lia.
        -- intros row col Hrow Hcol.
           apply Hinterior_undefined; lia.
Qed.
Lemma lcsn_boundary_write_progress__boundary_phase :
  forall mixed table n j,
    1 <= j <= n ->
    LCSNBoundaryProgressFacts mixed table n j ->
    LCSNBoundaryProgressFacts
      (replace_Znth j (Some 0) mixed)
      (replace_Znth j 0 table) n (j + 1).
Proof.
  intros mixed table n j Hj Hprogress.
  destruct Hj as [Hj_low Hj_high].
  unfold LCSNBoundaryProgressFacts in *.
  destruct Hprogress as
      [Hshape [Hfirst_column [Hrow_prefix [Hrow_suffix Hinterior]]]].
  destruct Hshape as [Hmixed_length Htable_length].
  assert (Hj_mixed : 0 <= j < Zlength mixed) by
    (rewrite Hmixed_length; nia).
  assert (Hj_table : 0 <= j < Zlength table) by
    (rewrite Htable_length; nia).
  split.
  - unfold LCSNLogicalTableShape.
    split; rewrite Zlength_replace_Znth; assumption.
  - split.
    + intros row Hrow.
      destruct Hrow as [Hrow_low Hrow_high].
      assert (Hrow_bounds : 0 <= row <= n) by lia.
      specialize (Hfirst_column row Hrow_bounds).
      unfold LCSNBoundaryCell, LCSNCellInitialized in *.
      destruct Hfirst_column as [Hinitialized Hzero].
      assert (Hrow_index_mixed :
          0 <= row * (n + 1) + 0 < Zlength mixed) by
        (rewrite Hmixed_length; nia).
      assert (Hrow_index_table :
          0 <= row * (n + 1) + 0 < Zlength table) by
        (rewrite Htable_length; nia).
      assert (Hrow_index_distinct : j <> row * (n + 1) + 0) by
        (destruct (Z.eq_dec row 0) as [Heq | Hneq];
         [subst row; lia |
          assert (1 <= row) by lia;
          assert (n + 1 <= row * (n + 1)) by nia;
          lia]).
      split.
      * unfold LCSNCellIndex in *.
        rewrite Znth_replace_Znth_Diff by assumption.
        rewrite Znth_replace_Znth_Diff by assumption.
        exact Hinitialized.
      * unfold LCSNCellIndex in *.
        rewrite Znth_replace_Znth_Diff by assumption.
        exact Hzero.
    + split.
      * intros col Hcol.
        destruct Hcol as [Hcol_low Hcol_high].
        destruct (Z.eq_dec col j) as [Heq | Hneq].
        -- subst col.
           unfold LCSNBoundaryCell, LCSNCellInitialized, LCSNCellIndex.
           split.
           ++ rewrite Znth_replace_Znth_Same by exact Hj_mixed.
              rewrite Znth_replace_Znth_Same by exact Hj_table.
              reflexivity.
           ++ rewrite Znth_replace_Znth_Same by exact Hj_table.
              reflexivity.
        -- specialize (Hrow_prefix col ltac:(lia)).
           unfold LCSNBoundaryCell, LCSNCellInitialized in *.
           destruct Hrow_prefix as [Hinitialized Hzero].
           assert (Hcol_mixed : 0 <= col < Zlength mixed) by
             (rewrite Hmixed_length; nia).
           assert (Hcol_table : 0 <= col < Zlength table) by
             (rewrite Htable_length; nia).
           assert (Hj_col_distinct : j <> col) by
             (intro Heq; lia).
           split.
           ++ unfold LCSNCellIndex in *.
              rewrite Znth_replace_Znth_Diff by assumption.
              rewrite Znth_replace_Znth_Diff by assumption.
              exact Hinitialized.
           ++ unfold LCSNCellIndex in *.
              rewrite Znth_replace_Znth_Diff by assumption.
              exact Hzero.
      * split.
        -- intros col Hcol.
           destruct Hcol as [Hcol_low Hcol_high].
           specialize (Hrow_suffix col ltac:(lia)).
           assert (Hcol_mixed : 0 <= col < Zlength mixed) by
             (rewrite Hmixed_length; nia).
           assert (Hj_col_distinct : j <> col) by
             (intro Heq; lia).
           unfold LCSNCellUndefined, LCSNCellIndex in *.
           rewrite Znth_replace_Znth_Diff by assumption.
           exact Hrow_suffix.
        -- intros row col Hrow Hcol.
           destruct Hrow as [Hrow_low Hrow_high].
           destruct Hcol as [Hcol_low Hcol_high].
           specialize (Hinterior row col ltac:(lia) ltac:(lia)).
           assert (Hcell_mixed :
               0 <= row * (n + 1) + col < Zlength mixed) by
             (rewrite Hmixed_length; nia).
           assert (Hj_cell_distinct : j <> row * (n + 1) + col) by
             (intro Heq; nia).
           unfold LCSNCellUndefined, LCSNCellIndex in *.
           rewrite Znth_replace_Znth_Diff by assumption.
           exact Hinterior.
Qed.
Lemma lcsn_boundaries_complete_rows_start__row_phase_entry :
  forall xs ys mixed table n,
    LCSNBoundaryProgressFacts mixed table n (n + 1) ->
    LCSNRowsProgressFacts xs ys mixed table n 1.
Proof.
  intros xs ys mixed table n Hprogress.
  unfold LCSNBoundaryProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hcolumn [Hrow [Hrow_undefined Hinterior_undefined]]]].
  unfold LCSNRowsProgressFacts.
  split; [exact Hshape |].
  split.
  - unfold LCSNBoundariesReady.
    split; [exact Hcolumn |].
    intros col Hcol.
    destruct (Z.eq_dec col 0) as [-> | Hcol_nonzero].
    + apply Hcolumn. lia.
    + apply Hrow. lia.
  - split.
    + unfold LCSNCompletedInteriorRowsFacts.
      intros row col Hrow_bounds Hcol_bounds. lia.
    + exact Hinterior_undefined.
Qed.
Lemma lcsn_rows_start_row__row_phase_entry :
  forall xs ys mixed table n row,
    row <= n ->
    LCSNRowsProgressFacts xs ys mixed table n row ->
    LCSNRowProgressFacts xs ys mixed table n row 1.
Proof.
  intros xs ys mixed table n row Hrow_upper Hprogress.
  unfold LCSNRowsProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hboundaries [Hcompleted Hundefined]]].
  unfold LCSNRowProgressFacts.
  split; [exact Hshape |].
  split; [exact Hboundaries |].
  split; [exact Hcompleted |].
  split.
  - intros col Hcol_bounds. lia.
  - split.
    + intros col Hcol_bounds.
      apply Hundefined; lia.
    + unfold LCSNInteriorRowsUndefinedFromFacts in *.
      intros later_row col Hlater_bounds Hcol_bounds.
      apply Hundefined; lia.
Qed.
Lemma lcsn_replace_Znth_as_sublist__equal_write_and_row_exit :
  forall {A : Type} (d : A) (l : list A) k v,
    0 <= k < Zlength l ->
    replace_Znth k v l =
      sublist 0 k l ++ v :: sublist (k + 1) (Zlength l) l.
Proof.
  intros A d l k v Hk.
  assert (Hsplit :
    l = sublist 0 k l ++ sublist k (Zlength l) l).
  {
    pose proof (sublist_split 0 (Zlength l) k l) as H.
    specialize (H ltac:(lia) ltac:(lia)).
    rewrite sublist_self in H by reflexivity.
    exact H.
  }
  assert (Htail :
    sublist k (Zlength l) l =
      Znth k l d :: sublist (k + 1) (Zlength l) l).
  {
    rewrite (sublist_split k (Zlength l) (k + 1) l) by lia.
    rewrite (sublist_single d k l) by lia.
    reflexivity.
  }
  rewrite Htail in Hsplit.
  rewrite Hsplit at 1.
  rewrite replace_Znth_app_r by
    (rewrite Zlength_sublist0; lia).
  rewrite replace_Znth_nothing by
    (rewrite Zlength_sublist0; lia).
  rewrite Zlength_sublist0 by lia.
  replace (k - k) with 0 by lia.
  reflexivity.
Qed.
Lemma lcsn_cell_index_injective__equal_write_and_row_exit :
  forall n r1 c1 r2 c2,
    0 <= n ->
    0 <= r1 <= n ->
    0 <= c1 <= n ->
    0 <= r2 <= n ->
    0 <= c2 <= n ->
    LCSNCellIndex n r1 c1 = LCSNCellIndex n r2 c2 ->
    r1 = r2 /\ c1 = c2.
Proof.
  intros n r1 c1 r2 c2 Hn Hr1 Hc1 Hr2 Hc2 Heq.
  unfold LCSNCellIndex in Heq.
  destruct (Z.lt_trichotomy r1 r2) as [Hlt | [Heqr | Hgt]].
  - exfalso; nia.
  - subst r2. split; nia.
  - exfalso; nia.
Qed.
Lemma lcsn_Znth_replace_other_cell__equal_write_and_row_exit :
  forall {A : Type} (d : A) l n ur uc qr qc (v : A),
    0 <= n ->
    0 <= ur <= n ->
    0 <= uc <= n ->
    0 <= qr <= n ->
    0 <= qc <= n ->
    Zlength l = (n + 1) * (n + 1) ->
    (ur <> qr \/ uc <> qc) ->
    Znth (LCSNCellIndex n qr qc)
      (replace_Znth (LCSNCellIndex n ur uc) v l) d =
    Znth (LCSNCellIndex n qr qc) l d.
Proof.
  intros A d l n ur uc qr qc v Hn Hur Huc Hqr Hqc Hlen Hdifferent.
  apply Znth_replace_Znth_Diff.
  - rewrite Hlen. unfold LCSNCellIndex. nia.
  - rewrite Hlen. unfold LCSNCellIndex. nia.
  - intro Heq.
    pose proof
      (lcsn_cell_index_injective__equal_write_and_row_exit
        n ur uc qr qc Hn Hur Huc Hqr Hqc Heq) as [Hr Hc].
    destruct Hdifferent; contradiction.
Qed.
Lemma lcsn_boundary_cell_replace_other__equal_write_and_row_exit :
  forall mixed table n ur uc qr qc v,
    0 <= n ->
    0 <= ur <= n ->
    0 <= uc <= n ->
    0 <= qr <= n ->
    0 <= qc <= n ->
    Zlength mixed = (n + 1) * (n + 1) ->
    Zlength table = (n + 1) * (n + 1) ->
    (ur <> qr \/ uc <> qc) ->
    LCSNBoundaryCell mixed table n qr qc ->
    LCSNBoundaryCell
      (replace_Znth (LCSNCellIndex n ur uc) (Some v) mixed)
      (replace_Znth (LCSNCellIndex n ur uc) v table)
      n qr qc.
Proof.
  intros mixed table n ur uc qr qc v Hn Hur Huc Hqr Hqc
    Hmixedlen Htablelen Hdifferent Hcell.
  unfold LCSNBoundaryCell, LCSNCellInitialized in *.
  destruct Hcell as [Hinitialized Hzero].
  split.
  - rewrite
      (lcsn_Znth_replace_other_cell__equal_write_and_row_exit
        None mixed n ur uc qr qc (Some v)); try assumption.
    rewrite
      (lcsn_Znth_replace_other_cell__equal_write_and_row_exit
        0 table n ur uc qr qc v); try assumption.
  - rewrite
      (lcsn_Znth_replace_other_cell__equal_write_and_row_exit
        0 table n ur uc qr qc v); try assumption.
Qed.
Lemma lcsn_interior_cell_replace_before__equal_write_and_row_exit :
  forall xs ys mixed table n ur uc qr qc v,
    0 <= n ->
    1 <= ur <= n ->
    1 <= uc <= n ->
    1 <= qr <= n ->
    1 <= qc <= n ->
    Zlength mixed = (n + 1) * (n + 1) ->
    Zlength table = (n + 1) * (n + 1) ->
    (qr < ur \/ (qr = ur /\ qc < uc)) ->
    LCSNInteriorCellFacts xs ys mixed table n qr qc ->
    LCSNInteriorCellFacts xs ys
      (replace_Znth (LCSNCellIndex n ur uc) (Some v) mixed)
      (replace_Znth (LCSNCellIndex n ur uc) v table)
      n qr qc.
Proof.
  intros xs ys mixed table n ur uc qr qc v Hn Hur Huc Hqr Hqc
    Hmixedlen Htablelen Hbefore Hcell.
  assert (Hmain_diff : ur <> qr \/ uc <> qc) by
    (destruct Hbefore as [Hlt | [Heq Hlt]]; [left | right]; lia).
  assert (Hdiag_diff : ur <> qr - 1 \/ uc <> qc - 1) by
    (left; destruct Hbefore as [Hlt | [Heq Hlt]]; lia).
  assert (Habove_diff : ur <> qr - 1 \/ uc <> qc) by
    (left; destruct Hbefore as [Hlt | [Heq Hlt]]; lia).
  assert (Hleft_diff : ur <> qr \/ uc <> qc - 1) by
    (destruct Hbefore as [Hlt | [Heq Hlt]]; [left | right]; lia).
  assert (Hmixed_main :
    Znth (LCSNCellIndex n qr qc)
      (replace_Znth (LCSNCellIndex n ur uc) (Some v) mixed) None =
    Znth (LCSNCellIndex n qr qc) mixed None).
  {
    eapply lcsn_Znth_replace_other_cell__equal_write_and_row_exit;
      try eassumption; lia.
  }
  assert (Htable_main :
    Znth (LCSNCellIndex n qr qc)
      (replace_Znth (LCSNCellIndex n ur uc) v table) 0 =
    Znth (LCSNCellIndex n qr qc) table 0).
  {
    eapply lcsn_Znth_replace_other_cell__equal_write_and_row_exit;
      try eassumption; lia.
  }
  assert (Htable_diag :
    Znth (LCSNCellIndex n (qr - 1) (qc - 1))
      (replace_Znth (LCSNCellIndex n ur uc) v table) 0 =
    Znth (LCSNCellIndex n (qr - 1) (qc - 1)) table 0).
  {
    eapply lcsn_Znth_replace_other_cell__equal_write_and_row_exit;
      try eassumption; lia.
  }
  assert (Htable_above :
    Znth (LCSNCellIndex n (qr - 1) qc)
      (replace_Znth (LCSNCellIndex n ur uc) v table) 0 =
    Znth (LCSNCellIndex n (qr - 1) qc) table 0).
  {
    eapply lcsn_Znth_replace_other_cell__equal_write_and_row_exit;
      try eassumption; lia.
  }
  assert (Htable_left :
    Znth (LCSNCellIndex n qr (qc - 1))
      (replace_Znth (LCSNCellIndex n ur uc) v table) 0 =
    Znth (LCSNCellIndex n qr (qc - 1)) table 0).
  {
    eapply lcsn_Znth_replace_other_cell__equal_write_and_row_exit;
      try eassumption; lia.
  }
  unfold LCSNInteriorCellFacts in *.
  destruct Hcell as [Hinitialized [Hrecurrence Hvalue]].
  split.
  - unfold LCSNCellInitialized in *.
    rewrite Hmixed_main, Htable_main.
    exact Hinitialized.
  - split.
    + unfold LCSNCellRecurrence in *.
      rewrite Htable_main, Htable_diag, Htable_above, Htable_left.
      exact Hrecurrence.
    + rewrite Htable_main.
      exact Hvalue.
Qed.
Lemma lcsn_diagonal_successor_bound__equal_write_and_row_exit :
  forall xs ys mixed table n row col,
    0 <= n ->
    1 <= row <= n ->
    1 <= col <= n ->
    LCSNRowProgressFacts xs ys mixed table n row col ->
    0 <= Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1 <=
      Z.min row col.
Proof.
  intros xs ys mixed table n row col Hn Hrow Hcol Hprogress.
  unfold LCSNRowProgressFacts in Hprogress.
  destruct Hprogress as
      [_ [Hboundaries [Hcompleted [_ [_ _]]]]].
  destruct Hboundaries as [Hfirst_col Hrow_zero].
  destruct (Z.eq_dec row 1) as [Hrow_one | Hrow_not_one].
  - subst row.
    specialize (Hrow_zero (col - 1)).
    assert (0 <= col - 1 <= n) by lia.
    specialize (Hrow_zero H).
    unfold LCSNBoundaryCell, LCSNCellInitialized in Hrow_zero.
    destruct Hrow_zero as [_ Hzero].
    replace (1 - 1) with 0 in * by lia.
    rewrite Hzero.
    destruct (Z_le_gt_dec 1 col).
    + rewrite Z.min_l by lia. lia.
    + lia.
  - destruct (Z.eq_dec col 1) as [Hcol_one | Hcol_not_one].
    + subst col.
      specialize (Hfirst_col (row - 1)).
      assert (0 <= row - 1 <= n) by lia.
      specialize (Hfirst_col H).
      unfold LCSNBoundaryCell, LCSNCellInitialized in Hfirst_col.
      destruct Hfirst_col as [_ Hzero].
      replace (1 - 1) with 0 in * by lia.
      rewrite Hzero.
      destruct (Z_le_gt_dec row 1).
      * rewrite Z.min_l by lia. lia.
      * rewrite Z.min_r by lia. lia.
    + specialize (Hcompleted (row - 1) (col - 1)).
      assert (1 <= row - 1 < row) by lia.
      assert (1 <= col - 1 <= n) by lia.
      specialize (Hcompleted H H0).
      unfold LCSNInteriorCellFacts in Hcompleted.
      destruct Hcompleted as [_ [_ Hdiag]].
      destruct (Z_le_gt_dec row col).
      * rewrite Z.min_l in Hdiag by lia.
        rewrite Z.min_l by lia.
        lia.
      * rewrite Z.min_r in Hdiag by lia.
        rewrite Z.min_r by lia.
        lia.
Qed.
Lemma lcsn_equal_write_progress__equal_write_and_row_exit :
  forall xs ys mixed table n row col,
    0 <= n ->
    1 <= row <= n ->
    1 <= col <= n ->
    Znth (row - 1) xs 0 = Znth (col - 1) ys 0 ->
    LCSNRowProgressFacts xs ys mixed table n row col ->
    LCSNRowProgressFacts xs ys
      (replace_Znth (LCSNCellIndex n row col)
        (Some (Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1))
        mixed)
      (replace_Znth (LCSNCellIndex n row col)
        (Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1)
        table)
      n row (col + 1).
Proof.
  intros xs ys mixed table n row col Hn Hrow Hcol Hequal Hprogress.
  pose proof
    (lcsn_diagonal_successor_bound__equal_write_and_row_exit
      xs ys mixed table n row col Hn Hrow Hcol Hprogress) as Hdiag_bound.
  unfold LCSNRowProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hboundaries [Hcompleted [Hprefix [Hsuffix Hfuture]]]]].
  destruct Hshape as [Hmixedlen Htablelen].
  unfold LCSNRowProgressFacts.
  split.
  - unfold LCSNLogicalTableShape.
    split; rewrite Zlength_replace_Znth; assumption.
  - split.
    + unfold LCSNBoundariesReady in *.
      destruct Hboundaries as [Hfirst_col Hrow_zero].
      split.
      * intros r Hr.
        eapply lcsn_boundary_cell_replace_other__equal_write_and_row_exit;
          try eassumption; try lia.
        apply Hfirst_col; exact Hr.
      * intros c Hc.
        eapply lcsn_boundary_cell_replace_other__equal_write_and_row_exit;
          try eassumption; try lia.
        apply Hrow_zero; exact Hc.
    + split.
      * unfold LCSNCompletedInteriorRowsFacts in *.
        intros r c Hr Hc.
        eapply lcsn_interior_cell_replace_before__equal_write_and_row_exit;
          try eassumption; try lia.
        apply Hcompleted; assumption.
      * split.
        -- intros c Hc.
           destruct (Z_lt_ge_dec c col) as [Hlt | Hge].
           ++ eapply lcsn_interior_cell_replace_before__equal_write_and_row_exit;
                try eassumption; try lia.
              apply Hprefix; lia.
           ++ assert (c = col) by lia.
              subst c.
              unfold LCSNInteriorCellFacts.
              split.
              ** unfold LCSNCellInitialized.
                 rewrite Znth_replace_Znth_Same.
                 --- rewrite Znth_replace_Znth_Same.
                     +++ reflexivity.
                     +++ rewrite Htablelen.
                         unfold LCSNCellIndex. nia.
                 --- rewrite Hmixedlen.
                     unfold LCSNCellIndex. nia.
              ** split.
                 --- unfold LCSNCellRecurrence.
                     right.
                     split; [lia |].
                     split; [lia |].
                     left.
                     split; [exact Hequal |].
                     rewrite Znth_replace_Znth_Same.
                     +++ rewrite
                           (lcsn_Znth_replace_other_cell__equal_write_and_row_exit
                             0 table n row col (row - 1) (col - 1)
                             (Znth (LCSNCellIndex n (row - 1) (col - 1))
                               table 0 + 1));
                           try assumption; try lia.
                     +++ rewrite Htablelen.
                         unfold LCSNCellIndex. nia.
                 --- rewrite Znth_replace_Znth_Same.
                     +++ exact Hdiag_bound.
                     +++ rewrite Htablelen.
                         unfold LCSNCellIndex. nia.
        -- unfold LCSNInteriorRowsUndefinedFromFacts in *.
           split.
           ++ intros c Hc.
              unfold LCSNCellUndefined in *.
              rewrite
                (lcsn_Znth_replace_other_cell__equal_write_and_row_exit
                  None mixed n row col row c
                  (Some (Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1)));
                try assumption; try lia.
              ** apply Hsuffix; lia.
           ++ intros r c Hr Hc.
              unfold LCSNCellUndefined in *.
              rewrite
                (lcsn_Znth_replace_other_cell__equal_write_and_row_exit
                  None mixed n row col r c
                  (Some (Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1)));
                try assumption; try lia.
              ** apply Hfuture; lia.
Qed.
Lemma lcsn_row_finish_progress__equal_write_and_row_exit :
  forall xs ys mixed table n row next_col,
    0 <= n ->
    1 <= row <= n ->
    n < next_col <= n + 1 ->
    LCSNRowProgressFacts xs ys mixed table n row next_col ->
    LCSNRowsProgressFacts xs ys mixed table n (row + 1).
Proof.
  intros xs ys mixed table n row next_col Hn Hrow Hnext Hprogress.
  assert (next_col = n + 1) by lia.
  subst next_col.
  unfold LCSNRowProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hboundaries [Hcompleted [Hprefix [_ Hfuture]]]]].
  unfold LCSNRowsProgressFacts.
  split; [exact Hshape |].
  split; [exact Hboundaries |].
  split.
  - unfold LCSNCompletedInteriorRowsFacts in *.
    intros r c Hr Hc.
    destruct (Z_lt_ge_dec r row) as [Hlt | Hge].
    + apply Hcompleted; lia.
    + assert (r = row) by lia.
      subst r.
      apply Hprefix; lia.
  - exact Hfuture.
Qed.
Lemma replace_Znth_sublist__max_write :
  forall {A : Type} (l : list A) (i : Z) (v : A),
    0 <= i < Zlength l ->
    replace_Znth i v l =
      sublist 0 i l ++ v :: sublist (i + 1) (Zlength l) l.
Proof.
  intros A l i v Hi.
  assert (Hdecompose :
    l = sublist 0 i l ++ Znth i l v ::
        sublist (i + 1) (Zlength l) l).
  {
    change (l = sublist 0 i l ++
      ([Znth i l v] ++ sublist (i + 1) (Zlength l) l)).
    rewrite app_assoc.
    rewrite <- (sublist_single v i l) by lia.
    rewrite <- (sublist_split 0 (i + 1) i l) by lia.
    rewrite <- (sublist_split 0 (Zlength l) (i + 1) l) by lia.
    symmetry. apply sublist_self. reflexivity.
  }
  rewrite Hdecompose at 1.
  rewrite replace_Znth_app_r with
      (l1 := sublist 0 i l)
      (l2 := [Znth i l v] ++ sublist (i + 1) (Zlength l) l).
  2: { rewrite Zlength_sublist0 by lia. lia. }
  rewrite replace_Znth_nothing.
  2: { rewrite Zlength_sublist0 by lia. lia. }
  rewrite Zlength_sublist0 by lia.
  replace (i - i) with 0 by lia.
  reflexivity.
Qed.
Lemma lcsn_max_write_progress__max_write :
  forall (xs ys : list Z) (mixed : list (option Z)) (table : list Z)
         (n row col : Z),
    1 <= row <= n ->
    1 <= col <= n ->
    LCSNRowProgressFacts xs ys mixed table n row col ->
    Znth (row - 1) xs 0 <> Znth (col - 1) ys 0 ->
    LCSNRowProgressFacts xs ys
      (replace_Znth (LCSNCellIndex n row col)
         (Some (Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0))) mixed)
      (replace_Znth (LCSNCellIndex n row col)
         (Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0)) table)
      n row (col + 1).
Proof.
  intros xs ys mixed table n row col Hrow Hcol Hprogress Hneq.
  unfold LCSNRowProgressFacts in Hprogress |- *.
  destruct Hprogress as
      [Hshape [Hboundaries [Hcompleted [Hcurrent [Hcurrent_undefined Hundefined_future]]]]].
  destruct Hshape as [Hmixed_len Htable_len].
  destruct Hboundaries as [Hfirst_col Hrow_zero].

  assert (Hcurrent_index :
    0 <= LCSNCellIndex n row col < (n + 1) * (n + 1)).
  { unfold LCSNCellIndex. nia. }

  assert (Hmixed_before_row : forall r c,
    0 <= r < row -> 0 <= c <= n ->
    Znth (LCSNCellIndex n r c)
      (replace_Znth (LCSNCellIndex n row col)
         (Some (Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0))) mixed) None =
    Znth (LCSNCellIndex n r c) mixed None).
  {
    intros r c Hr Hc.
    rewrite Znth_replace_Znth_Diff.
    - reflexivity.
    - rewrite Hmixed_len. exact Hcurrent_index.
    - rewrite Hmixed_len. unfold LCSNCellIndex. nia.
    - unfold LCSNCellIndex. nia.
  }
  assert (Htable_before_row : forall r c,
    0 <= r < row -> 0 <= c <= n ->
    Znth (LCSNCellIndex n r c)
      (replace_Znth (LCSNCellIndex n row col)
         (Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0)) table) 0 =
    Znth (LCSNCellIndex n r c) table 0).
  {
    intros r c Hr Hc.
    rewrite Znth_replace_Znth_Diff.
    - reflexivity.
    - rewrite Htable_len. exact Hcurrent_index.
    - rewrite Htable_len. unfold LCSNCellIndex. nia.
    - unfold LCSNCellIndex. nia.
  }
  assert (Hmixed_current_prefix : forall c,
    0 <= c < col ->
    Znth (LCSNCellIndex n row c)
      (replace_Znth (LCSNCellIndex n row col)
         (Some (Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0))) mixed) None =
    Znth (LCSNCellIndex n row c) mixed None).
  {
    intros c Hc.
    rewrite Znth_replace_Znth_Diff.
    - reflexivity.
    - rewrite Hmixed_len. exact Hcurrent_index.
    - rewrite Hmixed_len. unfold LCSNCellIndex. nia.
    - unfold LCSNCellIndex. nia.
  }
  assert (Htable_current_prefix : forall c,
    0 <= c < col ->
    Znth (LCSNCellIndex n row c)
      (replace_Znth (LCSNCellIndex n row col)
         (Z.max
           (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0)) table) 0 =
    Znth (LCSNCellIndex n row c) table 0).
  {
    intros c Hc.
    rewrite Znth_replace_Znth_Diff.
    - reflexivity.
    - rewrite Htable_len. exact Hcurrent_index.
    - rewrite Htable_len. unfold LCSNCellIndex. nia.
    - unfold LCSNCellIndex. nia.
  }

  assert (Habove_bound :
    0 <= Znth (LCSNCellIndex n (row - 1) col) table 0 /\
    Znth (LCSNCellIndex n (row - 1) col) table 0 <= row /\
    Znth (LCSNCellIndex n (row - 1) col) table 0 <= col).
  {
    destruct (Z.eq_dec row 1) as [-> | Hrow_ne].
    - specialize (Hrow_zero col ltac:(lia)).
      unfold LCSNBoundaryCell in Hrow_zero.
      destruct Hrow_zero as [_ Hz].
      replace (1 - 1) with 0 by lia.
      rewrite Hz. repeat split; lia.
    - specialize (Hcompleted (row - 1) col ltac:(lia) ltac:(lia)).
      unfold LCSNInteriorCellFacts in Hcompleted.
      destruct Hcompleted as [_ [_ Hmin]].
      destruct Hmin as [Hnonneg Hmin].
      repeat split; try exact Hnonneg.
      + eapply Z.le_trans; [exact Hmin |].
        eapply Z.le_trans; [apply Z.le_min_l | lia].
      + eapply Z.le_trans; [exact Hmin |].
        eapply Z.le_trans; [apply Z.le_min_r | lia].
  }
  assert (Hleft_bound :
    0 <= Znth (LCSNCellIndex n row (col - 1)) table 0 /\
    Znth (LCSNCellIndex n row (col - 1)) table 0 <= row /\
    Znth (LCSNCellIndex n row (col - 1)) table 0 <= col).
  {
    destruct (Z.eq_dec col 1) as [-> | Hcol_ne].
    - specialize (Hfirst_col row ltac:(lia)).
      unfold LCSNBoundaryCell in Hfirst_col.
      destruct Hfirst_col as [_ Hz].
      replace (1 - 1) with 0 by lia.
      rewrite Hz. repeat split; lia.
    - specialize (Hcurrent (col - 1) ltac:(lia)).
      unfold LCSNInteriorCellFacts in Hcurrent.
      destruct Hcurrent as [_ [_ Hmin]].
      destruct Hmin as [Hnonneg Hmin].
      repeat split; try exact Hnonneg.
      + eapply Z.le_trans; [exact Hmin | apply Z.le_min_l].
      + eapply Z.le_trans; [exact Hmin |].
        eapply Z.le_trans; [apply Z.le_min_r | lia].
  }
  destruct Habove_bound as [Habove_nonneg [Habove_row Habove_col]].
  destruct Hleft_bound as [Hleft_nonneg [Hleft_row Hleft_col]].

  split.
  - unfold LCSNLogicalTableShape.
    split.
    + repeat rewrite Zlength_replace_Znth.
      exact Hmixed_len.
    + repeat rewrite Zlength_replace_Znth.
      exact Htable_len.
  - split.
    + unfold LCSNBoundariesReady.
      split.
      * intros r Hr.
        specialize (Hfirst_col r Hr).
        unfold LCSNBoundaryCell in Hfirst_col |- *.
        destruct Hfirst_col as [Hinit Hz].
        split.
        -- unfold LCSNCellInitialized in Hinit |- *.
           rewrite Znth_replace_Znth_Diff.
           2: { rewrite Hmixed_len. exact Hcurrent_index. }
           2: { rewrite Hmixed_len. unfold LCSNCellIndex. nia. }
           2: { destruct (Z_le_gt_dec r row); unfold LCSNCellIndex; nia. }
           rewrite Znth_replace_Znth_Diff.
           2: { rewrite Htable_len. exact Hcurrent_index. }
           2: { rewrite Htable_len. unfold LCSNCellIndex. nia. }
           2: { destruct (Z_le_gt_dec r row); unfold LCSNCellIndex; nia. }
           exact Hinit.
        -- rewrite Znth_replace_Znth_Diff.
           2: { rewrite Htable_len. exact Hcurrent_index. }
           2: { rewrite Htable_len. unfold LCSNCellIndex. nia. }
           2: { destruct (Z_le_gt_dec r row); unfold LCSNCellIndex; nia. }
           exact Hz.
      * intros c Hc.
        specialize (Hrow_zero c Hc).
        unfold LCSNBoundaryCell in Hrow_zero |- *.
        destruct Hrow_zero as [Hinit Hz].
        split.
        -- unfold LCSNCellInitialized in Hinit |- *.
           rewrite Hmixed_before_row by lia.
           rewrite Htable_before_row by lia.
           exact Hinit.
        -- rewrite Htable_before_row by lia.
           exact Hz.
    + split.
      * unfold LCSNCompletedInteriorRowsFacts.
        intros r c Hr Hc.
        specialize (Hcompleted r c Hr Hc).
        unfold LCSNInteriorCellFacts in Hcompleted |- *.
        destruct Hcompleted as [Hinit [Hrec Hmin]].
        split.
        -- unfold LCSNCellInitialized in Hinit |- *.
           rewrite Hmixed_before_row by lia.
           rewrite Htable_before_row by lia.
           exact Hinit.
        -- split.
           ++ unfold LCSNCellRecurrence in Hrec |- *.
              rewrite Htable_before_row by lia.
              rewrite Htable_before_row by lia.
              rewrite Htable_before_row by lia.
              rewrite Htable_before_row by lia.
              exact Hrec.
           ++ rewrite Htable_before_row by lia.
              exact Hmin.
      * split.
        -- intros c Hc.
           destruct (Z.eq_dec c col) as [-> | Hc_ne].
           ++ unfold LCSNInteriorCellFacts, LCSNCellInitialized, LCSNCellRecurrence.
              split.
              ** rewrite Znth_replace_Znth_Same by (rewrite Hmixed_len; exact Hcurrent_index).
                 rewrite Znth_replace_Znth_Same by (rewrite Htable_len; exact Hcurrent_index).
                 reflexivity.
              ** split.
                 --- right. split; [lia |]. split; [lia |]. right. split; [exact Hneq |].
                     rewrite Znth_replace_Znth_Same by (rewrite Htable_len; exact Hcurrent_index).
                     rewrite Htable_before_row by lia.
                     rewrite Htable_current_prefix by lia.
                     reflexivity.
                 --- rewrite Znth_replace_Znth_Same by (rewrite Htable_len; exact Hcurrent_index).
                     split.
                     +++ eapply Z.le_trans; [exact Habove_nonneg | apply Z.le_max_l].
                     +++ apply Z.min_glb.
                         *** apply Z.max_lub; assumption.
                         *** apply Z.max_lub; assumption.
           ++ assert (Hc_old : 1 <= c < col) by lia.
              specialize (Hcurrent c Hc_old).
              unfold LCSNInteriorCellFacts in Hcurrent |- *.
              destruct Hcurrent as [Hinit [Hrec Hmin]].
              split.
              ** unfold LCSNCellInitialized in Hinit |- *.
                 rewrite Hmixed_current_prefix by lia.
                 rewrite Htable_current_prefix by lia.
                 exact Hinit.
              ** split.
                 --- unfold LCSNCellRecurrence in Hrec |- *.
                     rewrite Htable_current_prefix by lia.
                     rewrite Htable_before_row by lia.
                     rewrite Htable_before_row by lia.
                     rewrite Htable_current_prefix by lia.
                     exact Hrec.
                 --- rewrite Htable_current_prefix by lia.
                     exact Hmin.
        -- split.
           ++ intros c Hc.
              specialize (Hcurrent_undefined c ltac:(lia)).
              unfold LCSNCellUndefined in Hcurrent_undefined |- *.
              rewrite Znth_replace_Znth_Diff.
              ** exact Hcurrent_undefined.
              ** rewrite Hmixed_len. exact Hcurrent_index.
              ** rewrite Hmixed_len. unfold LCSNCellIndex. nia.
              ** unfold LCSNCellIndex. nia.
           ++ unfold LCSNInteriorRowsUndefinedFromFacts in Hundefined_future |- *.
              intros r c Hr Hc.
              specialize (Hundefined_future r c ltac:(lia) Hc).
              unfold LCSNCellUndefined in Hundefined_future |- *.
              rewrite Znth_replace_Znth_Diff.
              ** exact Hundefined_future.
              ** rewrite Hmixed_len. exact Hcurrent_index.
              ** rewrite Hmixed_len. unfold LCSNCellIndex. nia.
              ** unfold LCSNCellIndex. nia.
Qed.
Lemma lcsn_completed_rows_result__finalize_and_return_index :
  forall xs ys mixed table n,
    0 <= n ->
    LCSNRowsProgressFacts xs ys mixed table n (n + 1) ->
    LCSNTableResultFacts xs ys n table.
Proof.
  intros xs ys mixed table n Hn Hprogress.
  destruct Hprogress as
      ((Hmixed_length & Htable_length) &
       (Hcolumn_boundary & Hrow_boundary) &
       Hcompleted & Hundefined).
  split.
  - exact Htable_length.
  - intros row col Hrow Hcol.
    destruct (Z.eq_dec row 0) as [-> | Hrow_nonzero].
    + left. split.
      * left. reflexivity.
      * exact (proj2 (Hrow_boundary col Hcol)).
    + destruct (Z.eq_dec col 0) as [-> | Hcol_nonzero].
      * left. split.
        -- right. reflexivity.
        -- exact (proj2 (Hcolumn_boundary row Hrow)).
      * destruct (Hcompleted row col ltac:(lia) ltac:(lia))
          as (Hinitialized & Hrecurrence & Hvalue_bound).
        exact Hrecurrence.
Qed.
Lemma lcsn_initialized_mixed_full_to_full__finalize_and_return_index :
  forall xs ys mixed table n,
    0 <= n ->
    LCSNRowsProgressFacts xs ys mixed table n (n + 1) ->
    mixed = map (@Some Z) table.
Proof.
  intros xs ys mixed table n Hn Hprogress.
  destruct Hprogress as
      ((Hmixed_length & Htable_length) &
       (Hcolumn_boundary & Hrow_boundary) &
       Hcompleted & Hundefined).
  eapply List.nth_ext with (d := None) (d' := None).
  - rewrite length_map.
    apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    lia.
  - intros index_nat Hindex_bound.
    set (index := Z.of_nat index_nat).
    assert (Hindex_nonnegative : 0 <= index) by (unfold index; lia).
    assert (Hindex_square : index < (n + 1) * (n + 1)).
    {
      rewrite Zlength_correct in Hmixed_length.
      unfold index.
      apply Nat2Z.inj_lt in Hindex_bound.
      lia.
    }
    pose proof (Z.mod_pos_bound index (n + 1) ltac:(lia)) as Hmod.
    pose proof (Z.div_mod index (n + 1) ltac:(lia)) as Hdivmod.
    assert (Hrow : 0 <= index / (n + 1) <= n) by nia.
    assert (Hcol : 0 <= index mod (n + 1) <= n) by nia.
    assert (Hinitialized :
      LCSNCellInitialized mixed table n
        (index / (n + 1)) (index mod (n + 1))).
    {
      destruct (Z.eq_dec (index / (n + 1)) 0) as [Hrow_zero | Hrow_nonzero].
      - rewrite Hrow_zero.
        exact (proj1 (Hrow_boundary (index mod (n + 1)) Hcol)).
      - destruct (Z.eq_dec (index mod (n + 1)) 0)
          as [Hcol_zero | Hcol_nonzero].
        + rewrite Hcol_zero.
          exact (proj1 (Hcolumn_boundary (index / (n + 1)) Hrow)).
        + exact (proj1
            (Hcompleted (index / (n + 1)) (index mod (n + 1))
              ltac:(lia) ltac:(lia))).
    }
    unfold LCSNCellInitialized, LCSNCellIndex in Hinitialized.
    replace
      (index / (n + 1) * (n + 1) + index mod (n + 1))
      with index in Hinitialized by nia.
    unfold Znth in Hinitialized.
    destruct (index <? 0) eqn:Hnegative.
    + apply Z.ltb_lt in Hnegative. lia.
    + unfold index in Hinitialized.
      rewrite Nat2Z.id in Hinitialized.
      rewrite Hinitialized.
      rewrite (nth_indep (map (@Some Z) table) (n := index_nat)
        None (Some 0)).
      * rewrite map_nth. reflexivity.
      * rewrite length_map.
        apply Nat2Z.inj_lt.
        rewrite <- Zlength_correct, Htable_length.
        exact Hindex_square.
Qed.
Lemma lcsn_diagonal_observation__read_exposure :
  forall xs ys mixed table n i j,
    1 <= i -> i <= n -> 1 <= j -> j <= n ->
    LCSNRowProgressFacts xs ys mixed table n i j ->
    LCSNCellUndefined mixed n i j /\
    LCSNCellInitialized mixed table n (i - 1) (j - 1) /\
    0 <= Znth (LCSNCellIndex n (i - 1) (j - 1)) table 0 <= n.
Proof.
  intros xs ys mixed table n i j Hi Hin Hj Hjn Hprogress.
  unfold LCSNRowProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hboundaries [Hcompleted [Hprefix [Hsuffix Hfuture]]]]].
  split.
  - apply Hsuffix. lia.
  - destruct (Z.eq_dec i 1) as [Hi1 | Hi1].
    + subst i.
      specialize (proj2 Hboundaries (j - 1) ltac:(lia)) as Hcell.
      unfold LCSNBoundaryCell in Hcell.
      destruct Hcell as [Hinit Hzero].
      replace (1 - 1) with 0 by lia.
      split; [exact Hinit |].
      rewrite Hzero. lia.
    + destruct (Z.eq_dec j 1) as [Hj1 | Hj1].
      * subst j.
        specialize (proj1 Hboundaries (i - 1) ltac:(lia)) as Hcell.
        unfold LCSNBoundaryCell in Hcell.
        destruct Hcell as [Hinit Hzero].
        replace (1 - 1) with 0 by lia.
        split; [exact Hinit |].
        rewrite Hzero. lia.
      * specialize (Hcompleted (i - 1) (j - 1) ltac:(lia) ltac:(lia))
          as Hcell.
        unfold LCSNInteriorCellFacts in Hcell.
        destruct Hcell as [Hinit [Hrec [Hlo Hhi]]].
        split; [exact Hinit |].
        split; [exact Hlo |].
        eapply Z.le_trans; [exact Hhi |].
        eapply Z.le_trans; [apply Z.le_min_l | lia].
Qed.
Lemma lcsn_neighbor_observations__read_exposure :
  forall xs ys mixed table n i j,
    1 <= i -> i <= n -> 1 <= j -> j <= n ->
    LCSNRowProgressFacts xs ys mixed table n i j ->
    LCSNCellUndefined mixed n i j /\
    LCSNCellInitialized mixed table n (i - 1) j /\
    LCSNCellInitialized mixed table n i (j - 1).
Proof.
  intros xs ys mixed table n i j Hi Hin Hj Hjn Hprogress.
  unfold LCSNRowProgressFacts in Hprogress.
  destruct Hprogress as
      [Hshape [Hboundaries [Hcompleted [Hprefix [Hsuffix Hfuture]]]]].
  split.
  - apply Hsuffix. lia.
  - split.
    + destruct (Z.eq_dec i 1) as [Hi1 | Hi1].
      * subst i.
        specialize (proj2 Hboundaries j ltac:(lia)) as Hcell.
        exact (proj1 Hcell).
      * specialize (Hcompleted (i - 1) j ltac:(lia) ltac:(lia))
          as Hcell.
        exact (proj1 Hcell).
    + destruct (Z.eq_dec j 1) as [Hj1 | Hj1].
      * subst j.
        specialize (proj1 Hboundaries i ltac:(lia)) as Hcell.
        exact (proj1 Hcell).
      * specialize (Hprefix (j - 1) ltac:(lia)) as Hcell.
        exact (proj1 Hcell).
Qed.

From MaxMinLib Require Import MaxMin Interface.
From Coq Require Import Sorting.Sorted.

(** A common subsequence is a sequence of matching positions, strictly
    increasing in both inputs. These are mathematical candidate domains. *)
Definition LCSNPositionOrder (p q : Z * Z) : Prop :=
  fst p < fst q /\ snd p < snd q.
Definition LCSNMatching (xs ys : list Z) (rows cols : Z)
    (pairs : list (Z * Z)) : Prop :=
  Forall (fun p => 0 <= fst p < rows /\ 0 <= snd p < cols /\
    Znth (fst p) xs 0 = Znth (snd p) ys 0) pairs /\
  StronglySorted LCSNPositionOrder pairs.
Definition LCSNLength (xs ys : list Z) (answer : Z) : Prop :=
  max_value_of_subset Z.le
    (LCSNMatching xs ys (Zlength xs) (Zlength ys)) (fun pairs => Zlength pairs) answer.

Lemma lcsn_sorted_snoc : forall pairs p,
  StronglySorted LCSNPositionOrder (pairs ++ [p]) <->
  StronglySorted LCSNPositionOrder pairs /\
  Forall (fun q => LCSNPositionOrder q p) pairs.
Proof.
  induction pairs as [|a pairs IH]; intro p; simpl.
  - split; intros; repeat constructor.
  - split.
    + intro H. inversion H as [|? ? Htail Hall]; subst.
      apply IH in Htail as [Hs Hp].
      rewrite Forall_app in Hall. destruct Hall as [Ha Hlast].
      inversion Hlast; subst. split; constructor; assumption.
    + intros [Hs Hp]. inversion Hs; subst. inversion Hp; subst.
      constructor.
      * apply IH; auto.
      * apply Forall_app; split; auto.
Qed.
Lemma lcsn_matching_mono : forall xs ys r c r' c' pairs,
  r <= r' -> c <= c' -> LCSNMatching xs ys r c pairs ->
  LCSNMatching xs ys r' c' pairs.
Proof.
  intros xs ys r c r' c' pairs Hr Hc [Hp Hsort].
  split; [|exact Hsort].
  eapply Forall_impl; [|exact Hp]. intros [a b]; simpl; intuition lia.
Qed.
Lemma lcsn_matching_snoc_inv : forall xs ys r c pairs a b,
  LCSNMatching xs ys r c (pairs ++ [(a,b)]) ->
  0 <= a < r /\ 0 <= b < c /\ Znth a xs 0 = Znth b ys 0 /\
  LCSNMatching xs ys a b pairs /\
  Forall (fun p => fst p <= a /\ snd p <= b) (pairs ++ [(a,b)]).
Proof.
  intros xs ys r c pairs a b [Hall Hsort].
  rewrite Forall_app in Hall. destruct Hall as [Hp Hlast].
  inversion Hlast as [|? ? Hvalue Hnil]; subst; simpl in Hvalue.
  apply lcsn_sorted_snoc in Hsort as [Hs Hbefore].
  destruct Hvalue as [Ha [Hb Heq]].
  split; [exact Ha |]. split; [exact Hb |]. split; [exact Heq |].
  split.
  - split; [|exact Hs].
    rewrite Forall_forall in Hp, Hbefore |- *.
    intros p Hin. specialize (Hp p Hin); specialize (Hbefore p Hin).
    unfold LCSNPositionOrder in Hbefore; simpl in Hbefore. intuition lia.
  - apply Forall_app; split.
    + eapply Forall_impl; [|exact Hbefore].
      intros p H; unfold LCSNPositionOrder in H; simpl in H; intuition lia.
    + constructor; [simpl; lia | constructor].
Qed.
Lemma lcsn_matching_snoc : forall xs ys r c pairs,
  0 <= r -> 0 <= c -> Znth r xs 0 = Znth c ys 0 ->
  LCSNMatching xs ys r c pairs ->
  LCSNMatching xs ys (r + 1) (c + 1) (pairs ++ [(r,c)]).
Proof.
  intros xs ys r c pairs Hr Hc Heq [Hp Hsort].
  split.
  - apply Forall_app; split.
    + eapply Forall_impl; [|exact Hp]. intros p H; intuition lia.
    + constructor; [simpl; intuition lia | constructor].
  - apply lcsn_sorted_snoc; split; [exact Hsort |].
    eapply Forall_impl; [|exact Hp].
    intros p H; unfold LCSNPositionOrder; simpl; intuition lia.
Qed.
Lemma lcsn_matching_empty_axis : forall xs ys r c pairs,
  (r = 0 \/ c = 0) -> LCSNMatching xs ys r c pairs -> pairs = [].
Proof.
  intros xs ys r c pairs Hzero [Hp _].
  destruct pairs as [|[a b] pairs]; auto.
  inversion Hp; subst; simpl in *; destruct Hzero; intuition lia.
Qed.
Lemma lcsn_matching_last_axis : forall xs ys r c pairs a b,
  LCSNMatching xs ys r c (pairs ++ [(a,b)]) ->
  a < r - 1 \/ b < c - 1 ->
  LCSNMatching xs ys (r - 1) c (pairs ++ [(a,b)]) \/
  LCSNMatching xs ys r (c - 1) (pairs ++ [(a,b)]).
Proof.
  intros xs ys r c pairs a b Hm Haxis.
  pose proof (lcsn_matching_snoc_inv _ _ _ _ _ _ _ Hm) as [_ [_ [_ [_ Hlast]]]].
  destruct Hm as [Hp Hsort].
  rewrite Forall_forall in Hp, Hlast.
  destruct Haxis as [Ha | Hb].
  - left; split; [|exact Hsort]. rewrite Forall_forall.
    intros p Hin; specialize (Hp p Hin); specialize (Hlast p Hin); intuition lia.
  - right; split; [|exact Hsort]. rewrite Forall_forall.
    intros p Hin; specialize (Hp p Hin); specialize (Hlast p Hin); intuition lia.
Qed.
Lemma lcsn_mismatch_cover : forall xs ys r c pairs,
  Znth (r - 1) xs 0 <> Znth (c - 1) ys 0 ->
  LCSNMatching xs ys r c pairs ->
  LCSNMatching xs ys (r - 1) c pairs \/
  LCSNMatching xs ys r (c - 1) pairs.
Proof.
  intros xs ys r c pairs Hneq Hm.
  destruct (list_eq_dec (prod_eq_dec Z.eq_dec Z.eq_dec) pairs []) as [-> | Hnonempty].
  - left; split; constructor.
  - destruct (@exists_last _ _ Hnonempty) as [prefix [[a b] Heq]]; subst pairs.
    pose proof (lcsn_matching_snoc_inv _ _ _ _ _ _ _ Hm) as [Ha [Hb [Hmatch _]]].
    apply lcsn_matching_last_axis; [exact Hm |].
    destruct (Z.eq_dec a (r - 1)); destruct (Z.eq_dec b (c - 1)); subst; try tauto; lia.
Qed.
Lemma lcsn_table_cell_optimal : forall xs ys n table,
  LCSNTableResultFacts xs ys n table ->
  forall r c, 0 <= r <= n -> 0 <= c <= n ->
  max_value_of_subset Z.le (LCSNMatching xs ys r c) (fun pairs => Zlength pairs)
    (Znth (LCSNCellIndex n r c) table 0).
Proof.
  intros xs ys n table [_ Hrec].
  assert (Hmain : forall s, 0 <= s -> forall r c,
    r + c = s -> 0 <= r <= n -> 0 <= c <= n ->
    max_value_of_subset Z.le (LCSNMatching xs ys r c) (fun pairs => Zlength pairs)
      (Znth (LCSNCellIndex n r c) table 0)).
  { apply (Z_lt_induction (fun s => forall r c,
      r + c = s -> 0 <= r <= n -> 0 <= c <= n ->
      max_value_of_subset Z.le (LCSNMatching xs ys r c) (fun pairs => Zlength pairs)
        (Znth (LCSNCellIndex n r c) table 0))).
    intros s IH r c Hsum Hr Hc.
    pose proof (Hrec r c Hr Hc) as Hcell.
    destruct Hcell as [[Hzero Hvalue] | [Hrpos [Hcpos [[Hsame Hvalue] | [Hdiff Hvalue]]]]].
    - rewrite Hvalue. exists []. split; [split | reflexivity].
      + split; constructor.
      + intros pairs Hm. rewrite (lcsn_matching_empty_axis _ _ _ _ _ Hzero Hm).
        reflexivity.
    - pose proof (IH ((r - 1) + (c - 1)) ltac:(lia)
        (r - 1) (c - 1) eq_refl ltac:(lia) ltac:(lia)) as Hdiag.
      destruct Hdiag as [best [[Hbest Hupper] Hbestval]].
      exists (best ++ [(r - 1,c - 1)]). split; [split |].
      + change (LCSNMatching xs ys r c (best ++ [(r - 1, c - 1)])).
        replace r with ((r - 1) + 1) at 1 by lia.
        replace c with ((c - 1) + 1) at 1 by lia.
        apply lcsn_matching_snoc; try lia; assumption.
      + intros pairs Hm.
        destruct (list_eq_dec (prod_eq_dec Z.eq_dec Z.eq_dec) pairs []) as [-> | Hnonempty].
        * rewrite Zlength_app_cons. pose proof (Zlength_nonneg best). change (0 <= Zlength best + 1); lia.
        * destruct (@exists_last _ _ Hnonempty) as [prefix [[a b] Heq]]; subst pairs.
          pose proof (lcsn_matching_snoc_inv _ _ _ _ _ _ _ Hm) as [Ha [Hb [_ [Hp _]]]].
          assert (Hprefix : LCSNMatching xs ys (r - 1) (c - 1) prefix).
          { eapply lcsn_matching_mono; [| |exact Hp]; lia. }
          specialize (Hupper prefix Hprefix).
          rewrite !Zlength_app_cons. lia.
      + rewrite Zlength_app_cons. rewrite Hvalue. lia.
    - pose proof (IH ((r - 1) + c) ltac:(lia)
        (r - 1) c eq_refl ltac:(lia) Hc) as Habove.
      pose proof (IH (r + (c - 1)) ltac:(lia)
        r (c - 1) eq_refl Hr ltac:(lia)) as Hleft.
      destruct Habove as [a [[Ha Haupper] Havalue]].
      destruct Hleft as [b [[Hb Hbupper] Hbvalue]].
      destruct (Z_le_dec (Zlength a) (Zlength b)) as [Hab | Hab].
      + exists b. split; [split |].
        * eapply lcsn_matching_mono; [| |exact Hb]; lia.
        * intros pairs Hm.
          destruct (lcsn_mismatch_cover _ _ _ _ _ Hdiff Hm) as [Hm' | Hm'].
          -- specialize (Haupper pairs Hm'); lia.
          -- exact (Hbupper pairs Hm').
        * rewrite Hvalue, Z.max_r; lia.
      + exists a. split; [split |].
        * eapply lcsn_matching_mono; [| |exact Ha]; lia.
        * intros pairs Hm.
          destruct (lcsn_mismatch_cover _ _ _ _ _ Hdiff Hm) as [Hm' | Hm'].
          -- exact (Haupper pairs Hm').
          -- specialize (Hbupper pairs Hm'); lia.
        * rewrite Hvalue, Z.max_l; lia.
  }
  intros r c Hr Hc. apply (Hmain (r + c)); lia.
Qed.
Lemma lcsn_table_length_result : forall xs ys n table,
  0 <= n -> Zlength xs = n -> Zlength ys = n ->
  LCSNTableResultFacts xs ys n table ->
  LCSNLength xs ys (Znth ((n + 1) * n + n) table 0).
Proof.
  intros xs ys n table Hn Hxs Hys Htable.
  unfold LCSNLength. rewrite Hxs, Hys.
  replace ((n + 1) * n + n) with (LCSNCellIndex n n n) by (unfold LCSNCellIndex; lia).
  apply lcsn_table_cell_optimal; auto; lia.
Qed.

(** Intrinsic mathematical length bounds follow from the recurrence; they
    need not be stored as fields of loop progress predicates. *)
Lemma lcsn_recurrence_rectangle_bound : forall xs ys table n r c,
  0 <= r -> 0 <= c ->
  (forall a b, 0 <= a <= r -> 0 <= b <= c ->
    LCSNCellRecurrence xs ys table n a b) ->
  0 <= Znth (LCSNCellIndex n r c) table 0 <= Z.min r c.
Proof.
  intros xs ys table n.
  assert (Hmain : forall s, 0 <= s -> forall r c,
    r + c = s -> 0 <= r -> 0 <= c ->
    (forall a b, 0 <= a <= r -> 0 <= b <= c ->
      LCSNCellRecurrence xs ys table n a b) ->
    0 <= Znth (LCSNCellIndex n r c) table 0 <= Z.min r c).
  { apply (Z_lt_induction (fun s => forall r c,
      r + c = s -> 0 <= r -> 0 <= c ->
      (forall a b, 0 <= a <= r -> 0 <= b <= c ->
        LCSNCellRecurrence xs ys table n a b) ->
      0 <= Znth (LCSNCellIndex n r c) table 0 <= Z.min r c)).
    intros s IH r c Hsum Hr Hc Hrec.
    destruct (Hrec r c ltac:(lia) ltac:(lia)) as
      [[Hz Heq] | [Hrp [Hcp [[Hm Heq] | [Hm Heq]]]]].
    - rewrite Heq. split; [lia | apply Z.min_glb; lia].
    - assert (Hd : 0 <= Znth (LCSNCellIndex n (r - 1) (c - 1)) table 0 <= Z.min (r - 1) (c - 1)).
      { apply (IH ((r - 1) + (c - 1)) ltac:(lia)); try lia.
        intros a b Ha0 Hb0; apply Hrec; lia. }
      rewrite Heq. pose proof (Z.le_min_l (r - 1) (c - 1)).
      pose proof (Z.le_min_r (r - 1) (c - 1)).
      split; [lia | apply Z.min_glb; lia].
    - assert (Ha : 0 <= Znth (LCSNCellIndex n (r - 1) c) table 0 <= Z.min (r - 1) c).
      { apply (IH ((r - 1) + c) ltac:(lia)); try lia.
        intros a b Ha0 Hb0; apply Hrec; lia. }
      assert (Hb : 0 <= Znth (LCSNCellIndex n r (c - 1)) table 0 <= Z.min r (c - 1)).
      { apply (IH (r + (c - 1)) ltac:(lia)); try lia.
        intros a b Ha0 Hb0; apply Hrec; lia. }
      rewrite Heq.
      pose proof (Z.le_min_l (r - 1) c); pose proof (Z.le_min_r (r - 1) c).
      pose proof (Z.le_min_l r (c - 1)); pose proof (Z.le_min_r r (c - 1)).
      split.
      + eapply Z.le_trans; [exact (proj1 Ha) | apply Z.le_max_l].
      + apply Z.max_lub; apply Z.min_glb; lia.
  }
  intros r c Hr Hc Hrec. apply (Hmain (r + c)); auto; lia.
Qed.

Lemma lcsn_none_row_segment mixed n row first :
  0 <= n -> 0 <= row <= n -> 0 <= first <= n + 1 ->
  Zlength mixed = (n + 1) * (n + 1) ->
  (Forall (eq (@None Z))
     (sublist (LCSNCellIndex n row first) (LCSNCellIndex n row (n + 1)) mixed) <->
   forall col, first <= col <= n -> LCSNCellUndefined mixed n row col).
Proof.
  intros Hn Hr Hfirst Hlen.
  unfold LCSNCellUndefined, LCSNCellIndex.
  rewrite Forall_Znth with (d := @None Z).
  rewrite Zlength_sublist by nia.
  split.
  - intros H col Hcol. specialize (H (col - first) ltac:(lia)).
    rewrite Znth_sublist in H by nia.
    replace (col - first + (row * (n + 1) + first)) with (row * (n + 1) + col) in H by lia.
    symmetry; exact H.
  - intros H index Hindex. rewrite Znth_sublist by nia.
    replace (index + (row * (n + 1) + first)) with (row * (n + 1) + (first + index)) by lia.
    symmetry; apply H; lia.
Qed.

Definition LCSNInteriorRowsUndefinedFrom
    (mixed : list (option Z)) (n rows_from : Z) : Prop :=
  forall row, rows_from <= row <= n ->
    Forall (eq (@None Z))
      (sublist (LCSNCellIndex n row 1) (LCSNCellIndex n row (n + 1)) mixed).
Lemma lcsn_undefined_rows_facts mixed n first :
  0 <= n -> 0 <= first -> Zlength mixed = (n + 1) * (n + 1) ->
  (LCSNInteriorRowsUndefinedFrom mixed n first <->
   LCSNInteriorRowsUndefinedFromFacts mixed n first).
Proof.
  intros Hn Hfirst Hlen.
  unfold LCSNInteriorRowsUndefinedFrom, LCSNInteriorRowsUndefinedFromFacts.
  split.
  - intros H row col Hr Hcol.
    exact (proj1 (lcsn_none_row_segment mixed n row 1 Hn ltac:(lia) ltac:(lia) Hlen) (H row Hr) col Hcol).
  - intros H row Hr.
    apply (proj2 (lcsn_none_row_segment mixed n row 1 Hn ltac:(lia) ltac:(lia) Hlen)).
    intros col Hcol; exact (H row col Hr Hcol).
Qed.

(** Public progress separates mathematical table meaning from shape. *)
Definition LCSNTableResult (xs ys : list Z) (n : Z) (table : list Z) : Prop :=
  forall row col, 0 <= row <= n -> 0 <= col <= n ->
    LCSNCellRecurrence xs ys table n row col.
Definition LCSNInteriorCell (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n row col : Z) : Prop :=
  LCSNCellInitialized mixed table n row col /\
  LCSNCellRecurrence xs ys table n row col.
Definition LCSNCompletedInteriorRows (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n rows_done : Z) : Prop :=
  forall row col, 1 <= row < rows_done -> 1 <= col <= n ->
    LCSNInteriorCell xs ys mixed table n row col.
Definition LCSNColumnProgress (mixed : list (option Z)) (table : list Z)
    (n rows_done : Z) : Prop :=
  (forall row, 0 <= row < rows_done -> LCSNBoundaryCell mixed table n row 0) /\
  (forall row, rows_done <= row <= n -> LCSNCellUndefined mixed n row 0) /\
  LCSNInteriorRowsUndefinedFrom mixed n 0.
Definition LCSNBoundaryProgress (mixed : list (option Z)) (table : list Z)
    (n cols_done : Z) : Prop :=
  (forall row, 0 <= row <= n -> LCSNBoundaryCell mixed table n row 0) /\
  (forall col, 1 <= col < cols_done -> LCSNBoundaryCell mixed table n 0 col) /\
  Forall (eq (@None Z)) (sublist cols_done (n + 1) mixed) /\
  LCSNInteriorRowsUndefinedFrom mixed n 1.
Definition LCSNRowsProgress (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n rows_done : Z) : Prop :=
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRows xs ys mixed table n rows_done /\
  LCSNInteriorRowsUndefinedFrom mixed n rows_done.
Definition LCSNRowProgress (xs ys : list Z) (mixed : list (option Z))
    (table : list Z) (n row next_col : Z) : Prop :=
  LCSNBoundariesReady mixed table n /\
  LCSNCompletedInteriorRows xs ys mixed table n row /\
  (forall col, 1 <= col < next_col -> LCSNInteriorCell xs ys mixed table n row col) /\
  Forall (eq (@None Z))
    (sublist (LCSNCellIndex n row next_col) (LCSNCellIndex n row (n + 1)) mixed) /\
  LCSNInteriorRowsUndefinedFrom mixed n (row + 1).
Lemma lcsn_column_facts : forall mixed table n i,
  0 <= n ->
  Zlength mixed = (n+1)*(n+1) -> Zlength table = (n+1)*(n+1) ->
  LCSNColumnProgress mixed table n i -> LCSNColumnProgressFacts mixed table n i.
Proof.
  intros mixed table n i Hn Hm Ht [Hb [Hu Hi]].
  unfold LCSNColumnProgressFacts, LCSNLogicalTableShape.
  split; [split; assumption |]. split; [exact Hb |]. split; [exact Hu |].
  apply (proj1 (lcsn_undefined_rows_facts mixed n 0 Hn ltac:(lia) Hm)); exact Hi.
Qed.
Lemma lcsn_column_public : forall mixed table n i,
  0 <= n -> LCSNColumnProgressFacts mixed table n i ->
  Zlength mixed = (n+1)*(n+1) /\ Zlength table = (n+1)*(n+1) /\ LCSNColumnProgress mixed table n i.
Proof.
  intros mixed table n i Hn [[Hm Ht] [Hb [Hu Hi]]].
  split; [exact Hm |]. split; [exact Ht |].
  unfold LCSNColumnProgress. split; [exact Hb |]. split; [exact Hu |].
  apply (proj2 (lcsn_undefined_rows_facts mixed n 0 Hn ltac:(lia) Hm)); exact Hi.
Qed.
Lemma lcsn_boundary_facts : forall mixed table n j,
  0 <= n -> 0 <= j <= n + 1 ->
  Zlength mixed = (n+1)*(n+1) -> Zlength table = (n+1)*(n+1) ->
  LCSNBoundaryProgress mixed table n j -> LCSNBoundaryProgressFacts mixed table n j.
Proof.
  intros mixed table n j Hn Hj Hm Ht [Hb [Hp [Hs Hu]]].
  unfold LCSNBoundaryProgressFacts. split; [split; assumption |].
  split; [exact Hb |]. split; [exact Hp |]. split.
  - apply (proj1 (lcsn_none_row_segment mixed n 0 j Hn ltac:(lia) Hj Hm)).
    unfold LCSNCellIndex; rewrite Z.mul_0_l, !Z.add_0_l; exact Hs.
  - apply (proj1 (lcsn_undefined_rows_facts mixed n 1 Hn ltac:(lia) Hm)); exact Hu.
Qed.
Lemma lcsn_boundary_public : forall mixed table n j,
  0 <= n -> 0 <= j <= n + 1 -> LCSNBoundaryProgressFacts mixed table n j ->
  Zlength mixed = (n+1)*(n+1) /\ Zlength table = (n+1)*(n+1) /\ LCSNBoundaryProgress mixed table n j.
Proof.
  intros mixed table n j Hn Hj [[Hm Ht] [Hb [Hp [Hs Hu]]]].
  split; [exact Hm |]. split; [exact Ht |].
  unfold LCSNBoundaryProgress. split; [exact Hb |]. split; [exact Hp |]. split.
  - pose proof (proj2 (lcsn_none_row_segment mixed n 0 j Hn ltac:(lia) Hj Hm) Hs) as H.
    unfold LCSNCellIndex in H; rewrite Z.mul_0_l, !Z.add_0_l in H; exact H.
  - apply (proj2 (lcsn_undefined_rows_facts mixed n 1 Hn ltac:(lia) Hm)); exact Hu.
Qed.

Lemma lcsn_completed_intrinsic_bounds : forall xs ys mixed table n rows,
  rows <= n+1 -> LCSNBoundariesReady mixed table n ->
  LCSNCompletedInteriorRows xs ys mixed table n rows ->
  LCSNCompletedInteriorRowsFacts xs ys mixed table n rows.
Proof.
  intros xs ys mixed table n rows Hrows [Hcol Hrow] Hdone r c Hr Hc.
  destruct (Hdone r c Hr Hc) as [Hinit Hrec].
  split; [exact Hinit |]. split; [exact Hrec |].
  apply (lcsn_recurrence_rectangle_bound xs ys table n); try lia.
  intros a b Ha Hb.
  destruct (Z.eq_dec a 0) as [-> | Ha0].
  - left; split; [auto | exact (proj2 (Hrow b ltac:(lia)))].
  - destruct (Z.eq_dec b 0) as [-> | Hb0].
    + left; split; [auto | exact (proj2 (Hcol a ltac:(lia)))].
    + exact (proj2 (Hdone a b ltac:(lia) ltac:(lia))).
Qed.
Lemma lcsn_rows_facts : forall xs ys mixed table n i,
  0 <= n -> 0 <= i <= n+1 -> Zlength mixed = (n+1)*(n+1) -> Zlength table = (n+1)*(n+1) ->
  LCSNRowsProgress xs ys mixed table n i -> LCSNRowsProgressFacts xs ys mixed table n i.
Proof.
  intros xs ys mixed table n i Hn Hi Hm Ht [Hb [Hd Hu]].
  split; [split; assumption |]. split; [exact Hb |].
  split; [eapply lcsn_completed_intrinsic_bounds; eauto; lia |].
  apply (proj1 (lcsn_undefined_rows_facts mixed n i Hn ltac:(lia) Hm)); exact Hu.
Qed.
Lemma lcsn_rows_public : forall xs ys mixed table n i,
  0 <= n -> 0 <= i -> LCSNRowsProgressFacts xs ys mixed table n i ->
  Zlength mixed = (n+1)*(n+1) /\ Zlength table = (n+1)*(n+1) /\ LCSNRowsProgress xs ys mixed table n i.
Proof.
  intros xs ys mixed table n i Hn Hi [[Hm Ht] [Hb [Hd Hu]]].
  split; [exact Hm |]. split; [exact Ht |].
  split; [exact Hb |]. split; [|apply (proj2 (lcsn_undefined_rows_facts mixed n i Hn Hi Hm)); exact Hu].
  intros r c Hr Hc. destruct (Hd r c Hr Hc) as [Hinit [Hrec _]]; split; assumption.
Qed.
Lemma lcsn_row_facts : forall xs ys mixed table n i j,
  1 <= i <= n -> 0 <= j <= n+1 ->
  Zlength mixed = (n+1)*(n+1) -> Zlength table = (n+1)*(n+1) ->
  LCSNRowProgress xs ys mixed table n i j -> LCSNRowProgressFacts xs ys mixed table n i j.
Proof.
  intros xs ys mixed table n i j Hi Hj Hm Ht [Hb [Hd [Hp [Hs Hu]]]].
  split; [split; assumption |]. split; [exact Hb |].
  split; [eapply lcsn_completed_intrinsic_bounds; eauto; lia |].
  split.
  2: { split.
       - apply (proj1 (lcsn_none_row_segment mixed n i j ltac:(lia) ltac:(lia) Hj Hm)); exact Hs.
       - apply (proj1 (lcsn_undefined_rows_facts mixed n (i+1) ltac:(lia) ltac:(lia) Hm)); exact Hu. }
  intros c Hc. destruct (Hp c Hc) as [Hinit Hrec].
  split; [exact Hinit |]. split; [exact Hrec |].
  apply (lcsn_recurrence_rectangle_bound xs ys table n); try lia.
  intros a b Ha Hb'. destruct Hb as [Hcol Hrow].
  destruct (Z.eq_dec a 0) as [-> | Ha0].
  - left; split; [auto | exact (proj2 (Hrow b ltac:(lia)))].
  - destruct (Z.eq_dec b 0) as [-> | Hb0].
    + left; split; [auto | exact (proj2 (Hcol a ltac:(lia)))].
    + destruct (Z.eq_dec a i) as [-> | Hai].
      * exact (proj2 (Hp b ltac:(lia))).
      * exact (proj2 (Hd a b ltac:(lia) ltac:(lia))).
Qed.
Lemma lcsn_row_public : forall xs ys mixed table n i j,
  1 <= i <= n -> 0 <= j <= n+1 -> LCSNRowProgressFacts xs ys mixed table n i j ->
  Zlength mixed = (n+1)*(n+1) /\ Zlength table = (n+1)*(n+1) /\ LCSNRowProgress xs ys mixed table n i j.
Proof.
  intros xs ys mixed table n i j Hi Hj [[Hm Ht] [Hb [Hd [Hp [Hs Hu]]]]].
  split; [exact Hm |]. split; [exact Ht |].
  split; [exact Hb |]. split.
  - intros r c Hr Hc. destruct (Hd r c Hr Hc) as [Hinit [Hrec _]]; split; assumption.
  - split.
    + intros c Hc. destruct (Hp c Hc) as [Hinit [Hrec _]]; split; assumption.
    + split.
      * apply (proj2 (lcsn_none_row_segment mixed n i j ltac:(lia) ltac:(lia) Hj Hm)); exact Hs.
      * apply (proj2 (lcsn_undefined_rows_facts mixed n (i+1) ltac:(lia) ltac:(lia) Hm)); exact Hu.
Qed.
Lemma lcsn_column_pure : forall m t n i,
  0 <= n -> LCSNColumnProgressFacts m t n i -> LCSNColumnProgress m t n i.
Proof. intros m t n i Hn H; exact (proj2 (proj2 (lcsn_column_public _ _ _ _ Hn H))). Qed.
Lemma lcsn_boundary_pure : forall m t n j,
  0 <= n -> 0 <= j <= n+1 -> LCSNBoundaryProgressFacts m t n j -> LCSNBoundaryProgress m t n j.
Proof. intros m t n j Hn Hj H; exact (proj2 (proj2 (lcsn_boundary_public _ _ _ _ Hn Hj H))). Qed.
Lemma lcsn_rows_pure : forall xs ys m t n i,
  0 <= n -> 0 <= i -> LCSNRowsProgressFacts xs ys m t n i -> LCSNRowsProgress xs ys m t n i.
Proof. intros xs ys m t n i Hn Hi H; exact (proj2 (proj2 (lcsn_rows_public _ _ _ _ _ _ Hn Hi H))). Qed.
Lemma lcsn_row_pure : forall xs ys m t n i j,
  1 <= i <= n -> 0 <= j <= n+1 -> LCSNRowProgressFacts xs ys m t n i j -> LCSNRowProgress xs ys m t n i j.
Proof. intros xs ys m t n i j Hi Hj H; exact (proj2 (proj2 (lcsn_row_public _ _ _ _ _ _ _ Hi Hj H))). Qed.
