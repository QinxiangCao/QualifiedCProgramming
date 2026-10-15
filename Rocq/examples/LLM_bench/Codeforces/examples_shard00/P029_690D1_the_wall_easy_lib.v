Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition NonemptyWallColumn (grid : list (list Z)) (col : Z) : Prop :=
  exists row, 0 <= row < Zlength grid /\ Znth col (Znth row grid nil) 0 = 66.

Definition StartsWallSegment (grid : list (list Z)) (col : Z) : Prop :=
  0 <= col < Zlength (Znth 0 grid nil) /\
  NonemptyWallColumn grid col /\
  (col = 0 \/ ~ NonemptyWallColumn grid (col - 1)).

Definition Pre (r c : Z) (grid : list (list Z)) : Prop :=
  1 <= r <= 100 /\ 1 <= c <= 100 /\ Zlength grid = r /\
  Forall (fun row => Zlength row = c /\
    Forall (fun cell => cell = 66 \/ cell = 46) row) grid.

Definition Spec (r c : Z) (grid : list (list Z)) (out : Z) : Prop :=
  out = #(fun col : Z =>
    0 <= col < Zlength (Znth 0 grid nil) /\ StartsWallSegment grid col).

Definition NonemptyWallColumnBefore
    (grid : list (list Z)) (rows col : Z) : Prop :=
  exists row, 0 <= row < rows /\ Znth col (Znth row grid nil) 0 = 66.

Definition OccupancyValue (occupied : Z) (present : Prop) : Prop :=
  (occupied = 1 /\ present) \/ (occupied = 0 /\ ~ present).

Definition WallColumnsAfterRows
    (grid : list (list Z)) (rows : Z) (occupied : list Z) : Prop :=
  Zlength occupied = 100 /\
  forall col, 0 <= col < 100 ->
    OccupancyValue (Znth col occupied 0)
      (NonemptyWallColumnBefore grid rows col).

Definition WallColumnsDuringRow
    (grid : list (list Z)) (row next_col : Z) (occupied : list Z) : Prop :=
  Zlength occupied = 100 /\
  forall col, 0 <= col < 100 ->
    OccupancyValue (Znth col occupied 0)
      ((col < next_col /\ NonemptyWallColumnBefore grid (row + 1) col) \/
       (next_col <= col /\ NonemptyWallColumnBefore grid row col)).

Definition SegmentCountPrefix
    (grid : list (list Z)) (next_col segments : Z) : Prop :=
  segments = #(fun col : Z =>
    0 <= col < next_col /\ StartsWallSegment grid col).

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Lemma wall_columns_during_row_zero__row_boundaries : forall grid row occupied,
  WallColumnsAfterRows grid row occupied ->
  WallColumnsDuringRow grid row 0 occupied.
Proof.
  intros grid row occupied [Hlen Hcols].
  split; [exact Hlen |].
  intros col Hcol.
  specialize (Hcols col Hcol).
  unfold OccupancyValue in *.
  destruct Hcols as [[Hone Hpresent] | [Hzero Habsent]].
  - left. split; [exact Hone |].
    right. split; [lia | exact Hpresent].
  - right. split; [exact Hzero |].
    intros [[Hlt _] | [_ Hpresent]]; [lia |].
    apply Habsent. exact Hpresent.
Qed.
Lemma wall_columns_during_row_complete__row_boundaries :
  forall r c grid row occupied,
    Pre r c grid ->
    0 <= row < r ->
    WallColumnsDuringRow grid row c occupied ->
    WallColumnsAfterRows grid (row + 1) occupied.
Proof.
  intros r c grid row occupied Hpre Hrow [Hlen Hcols].
  unfold Pre in Hpre.
  destruct Hpre as [[Hrlo Hrhi] [[Hclo Hchi] [Hgrid Hrows]]].
  split; [exact Hlen |].
  intros col Hcol.
  specialize (Hcols col Hcol).
  assert (Hrow_shape : Zlength (Znth row grid nil) = c).
  { pose proof (proj1
      (Forall_Znth
        (fun xs : list Z => Zlength xs = c /\
          Forall (fun cell => cell = 66 \/ cell = 46) xs)
        nil grid) Hrows row) as Hshape.
    specialize (Hshape ltac:(rewrite Hgrid; exact Hrow)).
    exact (proj1 Hshape). }
  assert (Hpresent_iff :
      ((col < c /\ NonemptyWallColumnBefore grid (row + 1) col) \/
       (c <= col /\ NonemptyWallColumnBefore grid row col)) <->
      NonemptyWallColumnBefore grid (row + 1) col).
  { split.
    - intros [[_ Hpresent] | [_ [witness [[Hw0 Hwlt] Hwcell]]]].
      + exact Hpresent.
      + exists witness. split; [lia | exact Hwcell].
    - intros Hpresent.
      destruct (Z_lt_ge_dec col c) as [Hcolc | Hccol].
      + left. split; assumption.
      + right. split; [lia |].
        destruct Hpresent as [witness [[Hw0 Hwlt] Hwcell]].
        exists witness. split; [| exact Hwcell].
        split; [exact Hw0 |].
        destruct (Z_lt_ge_dec witness row) as [Hwrow | Hroww];
          [exact Hwrow |].
        assert (witness = row) by lia. subst witness.
        change (nth (Z.to_nat col) (Znth row grid nil) 0 = 66) in Hwcell.
        rewrite nth_overflow in Hwcell.
        * discriminate.
        * assert (Hlen_nat :
              length (Znth row grid nil) = Z.to_nat c).
          { apply Nat2Z.inj.
            rewrite Z2Nat.id by lia.
            rewrite <- Zlength_correct.
            exact Hrow_shape. }
          rewrite Hlen_nat.
          apply (proj1 (Z2Nat.inj_le c col ltac:(lia) ltac:(lia))).
          lia. }
  unfold OccupancyValue in *.
  destruct Hcols as [[Hone Hpresent] | [Hzero Habsent]].
  - left. split; [exact Hone |].
    apply (proj1 Hpresent_iff). exact Hpresent.
  - right. split; [exact Hzero |].
    intro Hpresent.
    apply Habsent.
    apply (proj2 Hpresent_iff). exact Hpresent.
Qed.
Lemma segment_count_prefix_zero__row_boundaries : forall grid,
  SegmentCountPrefix grid 0 0.
Proof.
  intros grid.
  unfold SegmentCountPrefix.
  cbv [set_card SumLib.Sum.sum enum finite_Z_range Zrange Zrange_aux].
  reflexivity.
Qed.
Lemma pre_from_quantified_rows__row_boundaries :
  forall r c grid default_row,
    1 <= r <= 100 ->
    1 <= c <= 100 ->
    Zlength grid = r ->
    (forall row, 0 <= row < r ->
      Zlength (Znth row grid default_row) = c) ->
    (forall row col,
      (0 <= row < r /\ 0 <= col) /\ col < c ->
      Znth col (Znth row grid nil) 0 = 66 \/
      Znth col (Znth row grid nil) 0 = 46) ->
    Pre r c grid.
Proof.
  intros r c grid default_row Hr Hc Hgrid Hrow_length Hcells.
  unfold Pre.
  repeat split; try lia.
  apply (proj2
    (Forall_Znth
      (fun row : list Z =>
        Zlength row = c /\
        Forall (fun cell : Z => cell = 66 \/ cell = 46) row)
      nil grid)).
  intros row Hrow.
  assert (Hrow_pre : 0 <= row < r) by lia.
  assert (Hlength : Zlength (Znth row grid nil) = c).
  { rewrite (Znth_indep grid row nil default_row) by lia.
    apply Hrow_length.
    exact Hrow_pre. }
  split; [exact Hlength |].
  apply (proj2
    (Forall_Znth
      (fun cell : Z => cell = 66 \/ cell = 46)
      0 (Znth row grid nil))).
  intros col Hcol.
  apply Hcells.
  lia.
Qed.
Lemma replace_Znth_same_inbounds__cell_updates :
  forall (A : Type) (i : Z) (l : list A) (d : A),
    0 <= i < Zlength l ->
    replace_Znth i (Znth i l d) l = l.
Proof.
  intros A i l d _.
  apply replace_Znth_Znth.
Qed.
Lemma wall_columns_mark_current__cell_updates :
  forall grid row j occupied,
    0 <= row ->
    0 <= j < 100 ->
    Znth j (Znth row grid nil) 0 = 66 ->
    WallColumnsDuringRow grid row j occupied ->
    WallColumnsDuringRow grid row (j + 1) (replace_Znth j 1 occupied).
Proof.
  intros grid row j occupied Hrow Hj Hwall [Hlen Hcols].
  split.
  - assert (Hreplace_len : forall (A : Type) (n : nat) (xs : list A) (v : A),
        length (replace_nth n xs v) = length xs).
    { intros A n xs. revert n.
      induction xs as [|x xs IH]; intros [|n] v; simpl; auto. }
    unfold replace_Znth.
    rewrite !Zlength_correct, Hreplace_len.
    rewrite Zlength_correct in Hlen.
    exact Hlen.
  - intros col Hcol.
    destruct (Z.eq_dec col j) as [Heq | Hneq].
    + subst col.
      rewrite Znth_replace_Znth_Same by lia.
      unfold OccupancyValue.
      left. split; [reflexivity |].
      left. split; [lia |].
      exists row. split; [lia | exact Hwall].
    + rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
      specialize (Hcols col Hcol).
      unfold OccupancyValue in *.
      destruct Hcols as [[Hone Hpresent] | [Hzero Habsent]].
      * left. split; [exact Hone |].
        destruct Hpresent as [[Hlt Hbefore] | [Hge Hbefore]].
        -- left. split; [lia | exact Hbefore].
        -- right. split; [lia | exact Hbefore].
      * right. split; [exact Hzero |].
        intros [[Hlt Hbefore] | [Hge Hbefore]].
        -- apply Habsent. left. split; [lia | exact Hbefore].
        -- apply Habsent. right. split; [lia | exact Hbefore].
Qed.
Lemma wall_columns_skip_current__cell_updates :
  forall grid row j occupied,
    0 <= j < 100 ->
    Znth j (Znth row grid nil) 0 <> 66 ->
    WallColumnsDuringRow grid row j occupied ->
    WallColumnsDuringRow grid row (j + 1) occupied.
Proof.
  intros grid row j occupied Hj Hnot [Hlen Hcols].
  split; [exact Hlen |].
  intros col Hcol.
  specialize (Hcols col Hcol).
  unfold OccupancyValue in *.
  destruct Hcols as [[Hone Hpresent] | [Hzero Habsent]].
  - left. split; [exact Hone |].
    destruct Hpresent as [[Hlt Hbefore] | [Hge Hbefore]].
    + left. split; [lia | exact Hbefore].
    + destruct (Z.eq_dec col j) as [Heq | Hneq].
      * subst col. left. split; [lia |].
        destruct Hbefore as [witness [[Hw0 Hwlt] Hwcell]].
        exists witness. split; [lia | exact Hwcell].
      * right. split; [lia | exact Hbefore].
  - right. split; [exact Hzero |].
    intros [[Hlt Hbefore] | [Hge Hbefore]].
    + apply Habsent.
      destruct (Z_lt_ge_dec col j) as [Hcolj | Hjcol].
      * left. split; [exact Hcolj | exact Hbefore].
      * assert (col = j) by lia. subst col.
        destruct Hbefore as [witness [[Hw0 Hwlt] Hwcell]].
        destruct (Z_lt_ge_dec witness row) as [Hwrow | Hroww].
        -- right. split; [lia |].
           exists witness. split; [lia | exact Hwcell].
        -- assert (witness = row) by lia. subst witness.
           contradiction.
    + apply Habsent. right. split; [lia | exact Hbefore].
Qed.
Lemma occupancy_value_reflects_presence__segment_scan :
  forall occupied present,
    OccupancyValue occupied present ->
    (occupied = 0 <-> ~ present) /\
    (occupied <> 0 -> present).
Proof.
  intros occupied present Hoccupancy.
  unfold OccupancyValue in Hoccupancy.
  destruct Hoccupancy as [[Hone Hpresent] | [Hzero Habsent]].
  - split.
    + split.
      * intros Hzero. lia.
      * intros Hnot. contradiction.
    + intros _. exact Hpresent.
  - subst occupied.
    split.
    + split; [intros; exact Habsent | intros; reflexivity].
    + intros Hneq. contradiction.
Qed.
Lemma set_card_Z_as_sum__segment_scan :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma segment_count_prefix_add_start__segment_scan :
  forall grid j segments,
    0 <= j ->
    StartsWallSegment grid j ->
    SegmentCountPrefix grid j segments ->
    SegmentCountPrefix grid (j + 1) (segments + 1).
Proof.
  intros grid j segments Hj Hstart Hprefix.
  unfold SegmentCountPrefix in *.
  rewrite set_card_Z_as_sum__segment_scan in Hprefix |- *.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hj.
  destruct (prop_dec (StartsWallSegment grid j)) as [_ | Hnot].
  - lia.
  - contradiction.
Qed.
Lemma segment_count_prefix_skip_nonstart__segment_scan :
  forall grid j segments,
    0 <= j ->
    ~ StartsWallSegment grid j ->
    SegmentCountPrefix grid j segments ->
    SegmentCountPrefix grid (j + 1) segments.
Proof.
  intros grid j segments Hj Hnot Hprefix.
  unfold SegmentCountPrefix in *.
  rewrite set_card_Z_as_sum__segment_scan in Hprefix |- *.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hj.
  destruct (prop_dec (StartsWallSegment grid j)) as [Hstart | _].
  - contradiction.
  - lia.
Qed.
Lemma segment_count_prefix_full_to_spec__final_result :
  forall (r c : Z) (grid : list (list Z)) (segments : Z),
    Pre r c grid ->
    1 <= r ->
    SegmentCountPrefix grid c segments ->
    Spec r c grid segments.
Proof.
  intros r c grid segments Hpre Hr Hprefix.
  unfold Pre in Hpre.
  destruct Hpre as [_ [_ [Hgrid_length Hrows]]].
  pose proof
    (proj1
       (Forall_Znth
          (fun row =>
             Zlength row = c /\
             Forall (fun cell => cell = 66 \/ cell = 46) row)
          nil grid)
       Hrows 0 ltac:(lia)) as Hfirst_row.
  destruct Hfirst_row as [Hfirst_row_length _].
  unfold SegmentCountPrefix in Hprefix.
  unfold Spec.
  rewrite Hfirst_row_length.
  exact Hprefix.
Qed.

Lemma pre_first_row_length__segment_scan :
  forall (r c : Z) (grid : list (list Z)),
    Pre r c grid ->
    Zlength (Znth 0 grid nil) = c.
Proof.
  intros r c grid Hpre.
  unfold Pre in Hpre.
  destruct Hpre as [[Hrlo Hrhi] [[Hclo Hchi] [Hgrid Hrows]]].
  apply
    (proj1
       (Forall_Znth
          (fun row =>
             Zlength row = c /\
             Forall (fun cell => cell = 66 \/ cell = 46) row)
          nil grid)
       Hrows 0).
  rewrite Hgrid.
  lia.
Qed.
