Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition point : Type := (Z * Z)%type.

Definition mk_point (x y : Z) : point := (x, y).

Definition point_x (p : point) : Z := fst p.

Definition point_y (p : point) : Z := snd p.

Definition default_point : point := mk_point 0 0.

Definition CoordInBounds (z : Z) : Prop := -10000 <= z <= 10000.

Definition PointCoordsBound (l : list point) : Prop :=
  Forall (fun p => CoordInBounds (point_x p) /\ CoordInBounds (point_y p)) l.

Fixpoint flat_points_rec (flat : list Z) (pts : list point) : Prop :=
  match pts with
  | nil => flat = nil
  | p :: rest =>
      exists flat_rest,
        flat = point_x p :: point_y p :: flat_rest /\
        flat_points_rec flat_rest rest
  end.

Definition FlatPoints (flat : list Z) (pts : list point) : Prop :=
  Zlength flat = 2 * Zlength pts /\ flat_points_rec flat pts.

Definition PointPermutation : list point -> list point -> Prop := @Permutation point.

Definition polar_cross (gp a b : point) : Z :=
  (point_x a - point_x gp) * (point_y b - point_y gp) -
  (point_y a - point_y gp) * (point_x b - point_x gp).

Definition point_dist2 (gp a : point) : Z :=
  (point_x gp - point_x a) * (point_x gp - point_x a) +
  (point_y gp - point_y a) * (point_y gp - point_y a).

Definition polar_upper_half (gp a : point) : bool :=
  let dx := point_x a - point_x gp in
  let dy := point_y a - point_y gp in
  orb (Z.ltb 0 dy) (andb (Z.eqb dy 0) (Z.leb 0 dx)).

Definition PolarCmpResult (gp a b : point) (ret : Z) : Prop :=
  let ha := polar_upper_half gp a in
  let hb := polar_upper_half gp b in
  let cr := polar_cross gp a b in
  let da := point_dist2 gp a in
  let db := point_dist2 gp b in
  (ha = true /\ hb = false /\ ret = -1) \/
  (ha = false /\ hb = true /\ ret = 1) \/
  (ha = hb /\ cr > 0 /\ ret = -1) \/
  (ha = hb /\ cr < 0 /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da < db /\ ret = -1) \/
  (ha = hb /\ cr = 0 /\ da > db /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a < point_x b /\ ret = -1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a > point_x b /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a = point_x b /\ point_y a < point_y b /\ ret = -1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a = point_x b /\ point_y a > point_y b /\ ret = 1) \/
  (ha = hb /\ cr = 0 /\ da = db /\ point_x a = point_x b /\ point_y a = point_y b /\ ret = 0).

Definition PolarLt (gp a b : point) : Prop :=
  PolarCmpResult gp a b (-1).

Definition PolarLe (gp a b : point) : Prop :=
  PolarCmpResult gp a b (-1) \/ PolarCmpResult gp a b 0.

Definition PolarSorted (gp : point) (l : list point) : Prop :=
  forall i j,
    0 <= i ->
    i <= j ->
    j < Zlength l ->
    PolarLe gp (Znth i l default_point) (Znth j l default_point).

Definition PointSortedRange (gp : point) (l : list point) (left right : Z) : Prop :=
  forall i j,
    left <= i ->
    i <= j ->
    j <= right ->
    PolarLe gp (Znth i l default_point) (Znth j l default_point).

Definition PointSameOutsideRange (l l1 : list point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

Definition PointMemoryModel (gp : point) (flat : list Z) (n : Z) : Prop :=
  exists pts,
    Zlength pts = n /\
    FlatPoints flat pts /\
    PointCoordsBound (cons gp pts).

Definition PointRangeSortResult
  (gp : point) (flat_in : list Z) (pts_out : list point)
  (left right : Z) : Prop :=
  forall pts_in,
    FlatPoints flat_in pts_in ->
    PointCoordsBound (cons gp pts_in) ->
    PointPermutation pts_in pts_out /\
    PointSameOutsideRange pts_in pts_out left right /\
    PointSortedRange gp pts_out left right.

Definition PointPartitionedAt
  (gp : point) (l : list point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => PolarLe gp x (Znth p l default_point)) (sublist low p l) /\
  Forall (fun x => PolarLt gp (Znth p l default_point) x)
         (sublist (p + 1) (high + 1) l).

Definition PointPartitionScanInv
  (gp : point) (before cur : list point)
  (low high : Z) (pivot : point) (i j : Z) : Prop :=
  PointPermutation before cur /\
  PointSameOutsideRange before cur low high /\
  Znth high cur default_point = pivot /\
  (forall k, low <= k <= i -> PolarLe gp (Znth k cur default_point) pivot) /\
  (forall k, i < k < j -> PolarLt gp pivot (Znth k cur default_point)).

Definition point_swap_points (l : list point) (i j : Z) : list point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Definition point_swap_flat (flat : list Z) (i j : Z) : list Z :=
  let xi := Znth (2 * i) flat 0 in
  let yi := Znth (2 * i + 1) flat 0 in
  let xj := Znth (2 * j) flat 0 in
  let yj := Znth (2 * j + 1) flat 0 in
  replace_Znth (2 * j + 1) yi
    (replace_Znth (2 * j) xi
      (replace_Znth (2 * i + 1) yj
        (replace_Znth (2 * i) xj flat))).

(* Helper imports migrated from sort_point__vc_proving_subagent_tmp_proof_manual__merged_r4.v. *)
Require Import Coq.Strings.Ascii.

(* Helper lemmas migrated from sort_point__vc_proving_subagent_tmp_proof_manual__merged_r4.v. *)

Lemma polar_upper_half_true_of_pos_y :
  forall gx gy x y,
    y - gy > 0 ->
    polar_upper_half (mk_point gx gy) (mk_point x y) = true.
Proof.
  intros.
  unfold polar_upper_half, mk_point, point_x, point_y.
  cbn.
  replace (0 <? y - gy)%Z with true.
  reflexivity.
  symmetry.
  apply Z.ltb_lt.
  lia.
Qed.

Lemma polar_upper_half_true_of_zero_y_nonneg_x :
  forall gx gy x y,
    x - gx >= 0 ->
    y - gy = 0 ->
    polar_upper_half (mk_point gx gy) (mk_point x y) = true.
Proof.
  intros.
  unfold polar_upper_half, mk_point, point_x, point_y.
  cbn.
  replace (0 <? y - gy)%Z with false.
  2:{ symmetry. apply Z.ltb_ge. lia. }
  replace ((y - gy =? 0)%Z) with true.
  2:{ symmetry. apply Z.eqb_eq. lia. }
  replace ((0 <=? x - gx)%Z) with true.
  2:{ symmetry. apply Z.leb_le. lia. }
  reflexivity.
Qed.

Lemma polar_upper_half_false_of_nonpos_nonzero_y :
  forall gx gy x y,
    y - gy <> 0 ->
    y - gy <= 0 ->
    polar_upper_half (mk_point gx gy) (mk_point x y) = false.
Proof.
  intros.
  unfold polar_upper_half, mk_point, point_x, point_y.
  cbn.
  replace (0 <? y - gy)%Z with false.
  2:{ symmetry. apply Z.ltb_ge. lia. }
  replace ((y - gy =? 0)%Z) with false.
  2:{ symmetry. apply Z.eqb_neq. lia. }
  reflexivity.
Qed.

Lemma polar_upper_half_false_of_zero_y_neg_x :
  forall gx gy x y,
    x - gx < 0 ->
    y - gy = 0 ->
    polar_upper_half (mk_point gx gy) (mk_point x y) = false.
Proof.
  intros.
  unfold polar_upper_half, mk_point, point_x, point_y.
  cbn.
  replace (0 <? y - gy)%Z with false.
  2:{ symmetry. apply Z.ltb_ge. lia. }
  replace ((y - gy =? 0)%Z) with true.
  2:{ symmetry. apply Z.eqb_eq. lia. }
  replace ((0 <=? x - gx)%Z) with false.
  2:{ symmetry. apply Z.leb_gt. lia. }
  reflexivity.
Qed.

Lemma flat_points_lookup_point :
  forall flat pts i,
    0 <= i < Zlength pts ->
    FlatPoints flat pts ->
    mk_point (Znth (2 * i) flat 0) (Znth (2 * i + 1) flat 0) =
    Znth i pts default_point.
Proof.
  intros flat pts.
  revert flat.
  induction pts as [| p pts IH]; intros flat i Hi Hflat.
  - rewrite Zlength_nil in Hi. lia.
  - unfold FlatPoints in Hflat.
    destruct Hflat as [Hlen [flat_rest [Hflat Hrest]]].
    subst flat.
    destruct (Z.eq_dec i 0) as [-> | Hneq].
    + rewrite Znth0_cons.
      rewrite Znth_cons by lia.
      rewrite Znth0_cons.
      rewrite Znth0_cons.
      destruct p.
      reflexivity.
    + assert (0 < i) by lia.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      replace (2 * i - 1 - 1) with (2 * (i - 1)) by lia.
      replace (2 * i + 1 - 1 - 1) with (2 * (i - 1) + 1) by lia.
      apply IH.
      * rewrite Zlength_cons in Hi. lia.
      * split.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- exact Hrest.
Qed.

Lemma point_coords_bound_lookup :
  forall pts i,
    0 <= i < Zlength pts ->
    PointCoordsBound pts ->
    CoordInBounds (point_x (Znth i pts default_point)) /\
    CoordInBounds (point_y (Znth i pts default_point)).
Proof.
  intros pts.
  induction pts as [| p pts IH]; intros i Hi Hbound.
  - rewrite Zlength_nil in Hi. lia.
  - unfold PointCoordsBound in Hbound.
    inversion Hbound as [| p' pts' Hp Htail]; subst.
    destruct (Z.eq_dec i 0) as [-> | Hneq].
    + rewrite Znth0_cons. exact Hp.
    + assert (0 < i) by lia.
      rewrite Znth_cons by lia.
      apply IH.
      * rewrite Zlength_cons in Hi. lia.
      * exact Htail.
Qed.

Lemma PolarCmpResult_nonpos_le :
  forall gp a b ret,
    PolarCmpResult gp a b ret ->
    ret <= 0 ->
    PolarLe gp a b.
Proof.
  intros gp a b ret Hcmp Hret.
  assert (ret = -1 \/ ret = 0) as Hcases.
  {
    unfold PolarCmpResult in Hcmp.
    repeat (destruct Hcmp as [Hcmp | Hcmp]);
      repeat match type of Hcmp with
             | _ /\ _ => destruct Hcmp
             end;
      lia.
  }
  unfold PolarLe.
  destruct Hcases as [-> | ->]; auto.
Qed.

Lemma flat_points_rec_Znth_point :
  forall flat pts j,
    flat_points_rec flat pts ->
    0 <= j < Zlength pts ->
    Znth j pts default_point =
      mk_point (Znth (2 * j) flat 0) (Znth (2 * j + 1) flat 0).
Proof.
  intros flat pts.
  revert flat.
  induction pts as [| [x y] pts IH]; intros flat j Hflat Hj.
  - simpl in Hflat.
    subst flat.
    rewrite Zlength_nil in Hj.
    lia.
  - rewrite Zlength_cons in Hj.
    simpl in Hflat.
    destruct Hflat as [flat_rest [-> Hflat_rest]].
    destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite Znth0_cons.
      change (Znth (2 * 0 + 1) (x :: y :: flat_rest) 0)
        with (Znth 1 (x :: y :: flat_rest) 0).
      rewrite (Znth_cons 0 1 x (y :: flat_rest)) by lia.
      rewrite Znth0_cons.
      reflexivity.
    + assert (j > 0) by lia.
      rewrite Znth_cons by lia.
      assert (
        Hx :
          Znth (2 * j) (x :: y :: flat_rest) 0 =
          Znth (2 * (j - 1)) flat_rest 0
      ).
      {
        rewrite Znth_cons by lia.
        rewrite Znth_cons by lia.
        replace (2 * j - 1 - 1) with (2 * (j - 1)) by lia.
        reflexivity.
      }
      assert (
        Hy :
          Znth (2 * j + 1) (x :: y :: flat_rest) 0 =
          Znth (2 * (j - 1) + 1) flat_rest 0
      ).
      {
        rewrite Znth_cons by lia.
        rewrite Znth_cons by lia.
        replace (2 * j + 1 - 1 - 1) with (2 * (j - 1) + 1) by lia.
        reflexivity.
      }
      rewrite Hx, Hy.
      apply IH; auto; lia.
Qed.

Lemma FlatPoints_Znth_point :
  forall flat pts j,
    FlatPoints flat pts ->
    0 <= j < Zlength pts ->
    Znth j pts default_point =
      mk_point (Znth (2 * j) flat 0) (Znth (2 * j + 1) flat 0).
Proof.
  intros flat pts j [_ Hflat] Hj.
  eapply flat_points_rec_Znth_point; eauto.
Qed.

Lemma Zlength_point_swap_points :
  forall l i j,
    Zlength (point_swap_points l i j) = Zlength l.
Proof.
  intros.
  unfold point_swap_points.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma Znth_point_swap_points_left :
  forall l i j d,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Znth i (point_swap_points l i j) d = Znth j l d.
Proof.
  intros l i j d Hi Hj.
  unfold point_swap_points.
  destruct (Z.eq_dec i j) as [-> | Hij].
  - repeat rewrite replace_Znth_Znth with (a0 := default_point).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
      (v := Znth i l default_point).
    + rewrite Znth_replace_Znth_Same by exact Hi.
      apply Znth_indep; exact Hj.
    + rewrite Zlength_replace_Znth. exact Hj.
    + rewrite Zlength_replace_Znth. exact Hi.
    + congruence.
Qed.

Lemma Znth_point_swap_points_right :
  forall l i j d,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Znth j (point_swap_points l i j) d = Znth i l d.
Proof.
  intros l i j d Hi Hj.
  unfold point_swap_points.
  destruct (Z.eq_dec i j) as [-> | _].
  - repeat rewrite replace_Znth_Znth with (a0 := default_point).
    reflexivity.
  - rewrite Znth_replace_Znth_Same.
    + apply Znth_indep; exact Hi.
    + rewrite Zlength_replace_Znth. exact Hj.
Qed.

Lemma Znth_point_swap_points_other :
  forall l i j k d,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    0 <= k < Zlength l ->
    k <> i ->
    k <> j ->
    Znth k (point_swap_points l i j) d = Znth k l d.
Proof.
  intros l i j k d Hi Hj Hk Hki Hkj.
  unfold point_swap_points.
  rewrite Znth_replace_Znth_Diff with (i := j) (j := k)
    (v := Znth i l default_point).
  2: {
    rewrite Zlength_replace_Znth.
    exact Hj.
  }
  2: {
    rewrite Zlength_replace_Znth.
    exact Hk.
  }
  2: {
    congruence.
  }
  rewrite Znth_replace_Znth_Diff with (i := i) (j := k)
    (v := Znth j l default_point).
  - reflexivity.
  - exact Hi.
  - exact Hk.
  - congruence.
Qed.

Lemma PolarCmpResult_one_implies_PolarLt_flip :
  forall gp a b,
    PolarCmpResult gp a b 1 ->
    PolarLt gp b a.
Proof.
  intros [gx gy] [ax ay] [bx by0] Hcmp.
  unfold PolarLt, PolarCmpResult in *.
  cbn in *.
  repeat (destruct Hcmp as [Hcmp | Hcmp]);
    repeat match type of Hcmp with
           | _ /\ _ => destruct Hcmp
           end;
    subst; try lia.
  - destruct H0 as [Hb Hr].
    subst.
    left. repeat split; auto.
  - destruct H0 as [Hcr Hr].
    subst.
    right. right. left.
    repeat split; try (symmetry; exact H); auto.
    unfold polar_cross in Hcr |- *.
    cbn in *.
    nia.
  - destruct H0 as [Hcr [Hdist Hr]].
    subst.
    do 4 right. left.
    split.
    + symmetry. exact H.
    + split.
      * unfold polar_cross in Hcr |- *.
        cbn in *.
        nia.
      * split.
        -- unfold point_dist2 in Hdist |- *.
           cbn in *.
           nia.
        -- reflexivity.
  - destruct H0 as [Hcr [Hdist [Hbx Hr]]].
    subst.
    do 6 right. left.
    split.
    + symmetry. exact H.
    + split.
      * unfold polar_cross in Hcr |- *.
        cbn in *.
        nia.
      * split.
        -- unfold point_dist2 in Hdist |- *.
           cbn in *.
           nia.
        -- split.
           ++ nia.
           ++ reflexivity.
  - destruct H0 as [Hcr [Hdist [Hab [Hay Hr]]]].
    subst.
    do 8 right. left.
    split.
    + symmetry. exact H.
    + split.
      * unfold polar_cross in Hcr |- *.
        cbn in *.
        nia.
      * split.
        -- unfold point_dist2 in Hdist |- *.
           cbn in *.
           nia.
        -- split.
           ++ reflexivity.
           ++ split.
              ** nia.
              ** reflexivity.
Qed.

Lemma flat_points_rec_functional :
  forall flat pts1 pts2,
    flat_points_rec flat pts1 ->
    flat_points_rec flat pts2 ->
    pts1 = pts2.
Proof.
  intros flat pts1.
  revert flat.
  induction pts1 as [| [x1 y1] rest1 IH]; intros flat pts2 Hrec1 Hrec2.
  - simpl in Hrec1. subst flat.
    destruct pts2 as [| [x2 y2] rest2].
    + reflexivity.
    + simpl in Hrec2. destruct Hrec2 as [flat2 [Heq _]]. discriminate Heq.
  - simpl in Hrec1. destruct Hrec1 as [flat1 [Heq1 Hrec1]].
    destruct pts2 as [| [x2 y2] rest2].
    + simpl in Hrec2. subst flat. discriminate.
    + simpl in Hrec2. destruct Hrec2 as [flat2 [Heq2 Hrec2]].
      rewrite Heq1 in Heq2. inversion Heq2. subst.
      f_equal.
      eapply IH; eauto.
Qed.

Lemma FlatPoints_functional :
  forall flat pts1 pts2,
    FlatPoints flat pts1 ->
    FlatPoints flat pts2 ->
    pts1 = pts2.
Proof.
  intros flat pts1 pts2 [_ Hrec1] [_ Hrec2].
  eapply flat_points_rec_functional; eauto.
Qed.

Lemma PolarLe_refl :
  forall gp p,
    PolarLe gp p p.
Proof.
  intros [gx gy] [x y].
  right.
  unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2,
    point_x, point_y, mk_point.
  simpl.
  repeat right.
  repeat split; try reflexivity; nia.
Qed.

Lemma PointSameOutsideRange_refl :
  forall l left right,
    PointSameOutsideRange l l left right.
Proof.
  intros l left right.
  split.
  - reflexivity.
  - intros k Hrange _.
    reflexivity.
Qed.

Lemma PointSortedRange_degenerate :
  forall gp l left right,
    left >= right ->
    PointSortedRange gp l left right.
Proof.
  intros gp l left right Hge i j Hleft Hij Hright.
  assert (i = j) by lia.
  subst j.
  apply PolarLe_refl.
Qed.

Lemma PolarLt_implies_PolarLe :
  forall gp a b,
    PolarLt gp a b ->
    PolarLe gp a b.
Proof.
  intros gp a b Hlt.
  unfold PolarLt, PolarLe in *.
  auto.
Qed.

Lemma polar_upper_half_true_iff :
  forall gp p,
    polar_upper_half gp p = true <->
    point_y p - point_y gp > 0 \/
    (point_y p - point_y gp = 0 /\ point_x p - point_x gp >= 0).
Proof.
  intros [gx gy] [x y].
  unfold polar_upper_half, point_x, point_y, mk_point.
  cbn.
  rewrite orb_true_iff, andb_true_iff.
  rewrite Z.ltb_lt, Z.eqb_eq, Z.leb_le.
  split; intros H.
  - nia.
  - nia.
Qed.

Lemma polar_upper_half_false_iff :
  forall gp p,
    polar_upper_half gp p = false <->
    point_y p - point_y gp < 0 \/
    (point_y p - point_y gp = 0 /\ point_x p - point_x gp < 0).
Proof.
  intros [gx gy] [x y].
  unfold polar_upper_half, point_x, point_y, mk_point.
  cbn.
  rewrite orb_false_iff, andb_false_iff.
  rewrite Z.ltb_ge, Z.eqb_neq, Z.leb_gt.
  split.
  - intros [Hy Hrest].
    destruct (Z.eq_dec (y - gy) 0) as [Heq | Hyneq].
    + right. split; [lia|].
      rewrite Heq in Hrest.
      destruct Hrest as [Hyfalse | Hxlt].
      * exfalso. apply Hyfalse. reflexivity.
      * exact Hxlt.
    + left. lia.
  - intros [Hylt | [Hy0 Hxlt]].
    + split; [lia|left; lia].
    + split; [lia|right; lia].
Qed.

Lemma same_norm_zero_cross_same_or_opposite :
  forall dx1 dy1 dx2 dy2,
    dx1 * dy2 - dy1 * dx2 = 0 ->
    dx1 * dx1 + dy1 * dy1 = dx2 * dx2 + dy2 * dy2 ->
    (dx1 = dx2 /\ dy1 = dy2) \/
    (dx1 = - dx2 /\ dy1 = - dy2).
Proof.
  intros dx1 dy1 dx2 dy2 Hcross Hnorm.
  assert
    (Hprod :
      (((dx1 - dx2) * (dx1 - dx2) + (dy1 - dy2) * (dy1 - dy2)) *
       ((dx1 + dx2) * (dx1 + dx2) + (dy1 + dy2) * (dy1 + dy2))) = 0) by nia.
  assert (Hnonneg1 :
    0 <= (dx1 - dx2) * (dx1 - dx2) + (dy1 - dy2) * (dy1 - dy2)) by nia.
  assert (Hnonneg2 :
    0 <= (dx1 + dx2) * (dx1 + dx2) + (dy1 + dy2) * (dy1 + dy2)) by nia.
  apply Z.mul_eq_0 in Hprod.
  destruct Hprod as [Hzero | Hzero].
  - left.
    set (A := (dx1 - dx2) * (dx1 - dx2)) in *.
    set (B := (dy1 - dy2) * (dy1 - dy2)) in *.
    assert (HA : 0 <= A).
    { subst A. rewrite <- Z.pow_2_r. apply Z.pow_even_nonneg. exists 1%Z. reflexivity. }
    assert (HB : 0 <= B).
    { subst B. rewrite <- Z.pow_2_r. apply Z.pow_even_nonneg. exists 1%Z. reflexivity. }
    assert (Hsum : A + B = 0) by (subst A B; exact Hzero).
    assert (A = 0 /\ B = 0) as [Hsq1 Hsq2] by lia.
    subst A B.
    nia.
  - right.
    set (A := (dx1 + dx2) * (dx1 + dx2)) in *.
    set (B := (dy1 + dy2) * (dy1 + dy2)) in *.
    assert (HA : 0 <= A).
    { subst A. rewrite <- Z.pow_2_r. apply Z.pow_even_nonneg. exists 1%Z. reflexivity. }
    assert (HB : 0 <= B).
    { subst B. rewrite <- Z.pow_2_r. apply Z.pow_even_nonneg. exists 1%Z. reflexivity. }
    assert (Hsum : A + B = 0) by (subst A B; exact Hzero).
    assert (A = 0 /\ B = 0) as [Hsq1 Hsq2] by lia.
    subst A B.
    nia.
Qed.

Lemma opposite_same_half_zero :
  forall gp a b,
    polar_upper_half gp a = polar_upper_half gp b ->
    point_x a - point_x gp = - (point_x b - point_x gp) ->
    point_y a - point_y gp = - (point_y b - point_y gp) ->
    a = gp /\ b = gp.
Proof.
  intros gp a b Hhalf Hx Hy.
  destruct (polar_upper_half gp a) eqn:Ha.
  - assert (Hb : polar_upper_half gp b = true).
    { symmetry. exact Hhalf. }
    apply polar_upper_half_true_iff in Ha.
    apply polar_upper_half_true_iff in Hb.
    destruct Ha as [Hay | [Hay Hax]].
    + destruct Hb as [Hby | [Hby Hbx]].
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
    + destruct Hb as [Hby | [Hby Hbx]].
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
  - assert (Hb : polar_upper_half gp b = false).
    { symmetry. exact Hhalf. }
    apply polar_upper_half_false_iff in Ha.
    apply polar_upper_half_false_iff in Hb.
    destruct Ha as [Hay | [Hay Hax]].
    + destruct Hb as [Hby | [Hby Hbx]].
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
    + destruct Hb as [Hby | [Hby Hbx]].
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
      * destruct gp. destruct a. destruct b. simpl in *. repeat split; f_equal; lia.
Qed.

Lemma polar_cross_eq_dist_eq_same_half_eq :
  forall gp a b,
    polar_upper_half gp a = polar_upper_half gp b ->
    polar_cross gp a b = 0 ->
    point_dist2 gp a = point_dist2 gp b ->
    a = b.
Proof.
  intros gp a b Hhalf Hcross Hdist.
  unfold polar_cross, point_dist2, point_x, point_y, mk_point in Hcross, Hdist.
  cbn in Hcross, Hdist.
  assert (Hdist' :
    (fst a - fst gp) * (fst a - fst gp) +
    (snd a - snd gp) * (snd a - snd gp) =
    (fst b - fst gp) * (fst b - fst gp) +
    (snd b - snd gp) * (snd b - snd gp)) by nia.
  pose proof (same_norm_zero_cross_same_or_opposite
    (fst a - fst gp)
    (snd a - snd gp)
    (fst b - fst gp)
    (snd b - snd gp)
    Hcross Hdist') as Hcases.
  destruct Hcases as [[Hx Hy] | [Hx Hy]].
  - destruct a. destruct b. simpl in *. f_equal; lia.
  - pose proof (opposite_same_half_zero
      gp a b) as Htmp.
    specialize (Htmp Hhalf Hx Hy).
    destruct Htmp as [Ha Hb].
    now rewrite Ha, Hb.
Qed.

Lemma PolarCmpResult_zero_eq :
  forall gp a b,
    PolarCmpResult gp a b 0 ->
    a = b.
Proof.
  intros gp a b Hcmp.
  unfold PolarCmpResult in Hcmp.
  repeat (destruct Hcmp as [Hcmp | Hcmp]);
    repeat match type of Hcmp with
           | _ /\ _ => destruct Hcmp
           end;
    try lia.
  destruct a. destruct b. simpl in *. subst. f_equal; lia.
Qed.

Lemma upper_half_cross_trans_test :
  forall ax ay bx byv cx cy,
    (ay > 0 \/ (ay = 0 /\ ax >= 0)) ->
    (byv > 0 \/ (byv = 0 /\ bx >= 0)) ->
    (cy > 0 \/ (cy = 0 /\ cx >= 0)) ->
    ax * byv - ay * bx > 0 ->
    bx * cy - byv * cx > 0 ->
    ax * cy - ay * cx > 0.
Proof.
  nia.
Qed.

Lemma upper_half_cross_ray_right_test :
  forall ax ay bx byv cx cy,
    (ay > 0 \/ (ay = 0 /\ ax >= 0)) ->
    (byv > 0 \/ (byv = 0 /\ bx >= 0)) ->
    (cy > 0 \/ (cy = 0 /\ cx >= 0)) ->
    ax * byv - ay * bx > 0 ->
    bx * cy - byv * cx = 0 ->
    bx * bx + byv * byv < cx * cx + cy * cy ->
    ax * cy - ay * cx > 0.
Proof.
  nia.
Qed.

Lemma upper_half_cross_ray_left_test :
  forall ax ay bx byv cx cy,
    (ay > 0 \/ (ay = 0 /\ ax >= 0)) ->
    (byv > 0 \/ (byv = 0 /\ bx >= 0)) ->
    (cy > 0 \/ (cy = 0 /\ cx >= 0)) ->
    ax * byv - ay * bx = 0 ->
    ax * ax + ay * ay < bx * bx + byv * byv ->
    bx * cy - byv * cx > 0 ->
    ax * cy - ay * cx > 0 \/
    (ax * cy - ay * cx = 0 /\ ax * ax + ay * ay < cx * cx + cy * cy).
Proof.
  nia.
Qed.

Lemma upper_half_ray_dist_trans_test :
  forall ax ay bx byv cx cy,
    (ay > 0 \/ (ay = 0 /\ ax >= 0)) ->
    (byv > 0 \/ (byv = 0 /\ bx >= 0)) ->
    (cy > 0 \/ (cy = 0 /\ cx >= 0)) ->
    ax * byv - ay * bx = 0 ->
    ax * ax + ay * ay < bx * bx + byv * byv ->
    bx * cy - byv * cx = 0 ->
    bx * bx + byv * byv < cx * cx + cy * cy ->
    ax * cy - ay * cx = 0 /\
    ax * ax + ay * ay < cx * cx + cy * cy.
Proof.
  nia.
Qed.

Lemma lower_half_cross_trans_test :
  forall ax ay bx byv cx cy,
    (ay < 0 \/ (ay = 0 /\ ax < 0)) ->
    (byv < 0 \/ (byv = 0 /\ bx < 0)) ->
    (cy < 0 \/ (cy = 0 /\ cx < 0)) ->
    ax * byv - ay * bx > 0 ->
    bx * cy - byv * cx > 0 ->
    ax * cy - ay * cx > 0.
Proof.
  intros ax ay bx byv cx cy Ha Hb Hc Hab Hbc.
  pose proof (upper_half_cross_trans_test
      (- ax) (- ay) (- bx) (- byv) (- cx) (- cy)) as H.
  specialize (H ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia)).
  nia.
Qed.

Lemma lower_half_cross_ray_right_test :
  forall ax ay bx byv cx cy,
    (ay < 0 \/ (ay = 0 /\ ax < 0)) ->
    (byv < 0 \/ (byv = 0 /\ bx < 0)) ->
    (cy < 0 \/ (cy = 0 /\ cx < 0)) ->
    ax * byv - ay * bx > 0 ->
    bx * cy - byv * cx = 0 ->
    bx * bx + byv * byv < cx * cx + cy * cy ->
    ax * cy - ay * cx > 0.
Proof.
  intros ax ay bx byv cx cy Ha Hb Hc Hab Hbc Hdist.
  pose proof (upper_half_cross_ray_right_test
      (- ax) (- ay) (- bx) (- byv) (- cx) (- cy)) as H.
  specialize (H ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia)).
  nia.
Qed.

Lemma lower_half_cross_ray_left_test :
  forall ax ay bx byv cx cy,
    (ay < 0 \/ (ay = 0 /\ ax < 0)) ->
    (byv < 0 \/ (byv = 0 /\ bx < 0)) ->
    (cy < 0 \/ (cy = 0 /\ cx < 0)) ->
    ax * byv - ay * bx = 0 ->
    ax * ax + ay * ay < bx * bx + byv * byv ->
    bx * cy - byv * cx > 0 ->
    ax * cy - ay * cx > 0 \/
    (ax * cy - ay * cx = 0 /\ ax * ax + ay * ay < cx * cx + cy * cy).
Proof.
  intros ax ay bx byv cx cy Ha Hb Hc Hab Hdist Hbc.
  pose proof (upper_half_cross_ray_left_test
      (- ax) (- ay) (- bx) (- byv) (- cx) (- cy)) as H.
  specialize (H ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia)).
  nia.
Qed.

Lemma lower_half_ray_dist_trans_test :
  forall ax ay bx byv cx cy,
    (ay < 0 \/ (ay = 0 /\ ax < 0)) ->
    (byv < 0 \/ (byv = 0 /\ bx < 0)) ->
    (cy < 0 \/ (cy = 0 /\ cx < 0)) ->
    ax * byv - ay * bx = 0 ->
    ax * ax + ay * ay < bx * bx + byv * byv ->
    bx * cy - byv * cx = 0 ->
    bx * bx + byv * byv < cx * cx + cy * cy ->
    ax * cy - ay * cx = 0 /\
    ax * ax + ay * ay < cx * cx + cy * cy.
Proof.
  intros ax ay bx byv cx cy Ha Hb Hc Hab Habd Hbc Hbcd.
  pose proof (upper_half_ray_dist_trans_test
      (- ax) (- ay) (- bx) (- byv) (- cx) (- cy)) as H.
  specialize (H ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia) ltac:(nia)).
  nia.
Qed.

Lemma PolarLt_simplified_test :
  forall gp a b,
    PolarLt gp a b ->
    (polar_upper_half gp a = true /\ polar_upper_half gp b = false) \/
    (polar_upper_half gp a = polar_upper_half gp b /\ polar_cross gp a b > 0) \/
    (polar_upper_half gp a = polar_upper_half gp b /\ polar_cross gp a b = 0 /\ point_dist2 gp a < point_dist2 gp b).
Proof.
  intros [gx gy] [ax ay] [bx byv] Hlt.
  unfold PolarLt, PolarCmpResult in Hlt.
  cbn in Hlt.
  repeat (destruct Hlt as [Hlt | Hlt]);
    repeat match type of Hlt with
           | _ /\ _ => destruct Hlt
           end;
    try lia.
  - now left.
  - now right; left.
  - now right; right.
  - exfalso.
    destruct H0 as [H0 [H1 [H2 H3]]].
    pose proof (polar_cross_eq_dist_eq_same_half_eq (gx, gy) (ax, ay) (bx, byv) H H0 H1) as Heq.
    inversion Heq. lia.
  - exfalso.
    destruct H0 as [H0 [H1 [H2 [H3 H4]]]].
    pose proof (polar_cross_eq_dist_eq_same_half_eq (gx, gy) (ax, ay) (bx, byv) H H0 H1) as Heq.
    inversion Heq. lia.
Qed.

Lemma PolarLe_lt_or_eq_test :
  forall gp a b,
    PolarLe gp a b ->
    PolarLt gp a b \/ a = b.
Proof.
  intros gp a b Hle.
  destruct Hle as [Hlt | Heq].
  - now left.
  - right. eapply PolarCmpResult_zero_eq. exact Heq.
Qed.

Lemma PolarLt_trans_test :
  forall gp a b c,
    PolarLt gp a b ->
    PolarLt gp b c ->
    PolarLt gp a c.
Proof.
  intros gp a b c Hab Hbc.
  pose proof (PolarLt_simplified_test _ _ _ Hab) as Hab'.
  pose proof (PolarLt_simplified_test _ _ _ Hbc) as Hbc'.
  destruct gp as [gx gy], a as [ax ay], b as [bx byv], c as [cx cy].
  cbn in *.
  unfold polar_cross, point_dist2, point_x, point_y, mk_point in *.
  cbn in *.
  destruct Hab' as [[Hab_tf Hab_bf] | [[Hab_half Hab_cross] | [Hab_half [Hab_zero Hab_dist]]]].
  - destruct Hbc' as [[Hbc_bt Hbc_cf] | [[Hbc_half Hbc_cross] | [Hbc_half [Hbc_zero Hbc_dist]]]].
    + congruence.
    + unfold PolarLt, PolarCmpResult. cbn.
      assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
      left. repeat split; try assumption; try exact Hc; reflexivity.
    + unfold PolarLt, PolarCmpResult. cbn.
      assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
      left. repeat split; try assumption; try exact Hc; reflexivity.
  - destruct Hbc' as [[Hbc_bt Hbc_cf] | [[Hbc_half' Hbc_cross] | [Hbc_half' [Hbc_zero Hbc_dist]]]].
    + unfold PolarLt, PolarCmpResult. cbn.
      assert (Ha : polar_upper_half (gx, gy) (ax, ay) = true) by congruence.
      left. repeat split; try exact Ha; try assumption; reflexivity.
    + unfold PolarLt, PolarCmpResult. cbn.
      right. right. left.
      split.
      * congruence.
      * split.
        -- destruct (polar_upper_half (gx, gy) (ax, ay)) eqn:Ha.
           ++ assert (Hb : polar_upper_half (gx, gy) (bx, byv) = true) by congruence.
              assert (Hc : polar_upper_half (gx, gy) (cx, cy) = true) by congruence.
              apply polar_upper_half_true_iff in Ha.
              apply polar_upper_half_true_iff in Hb.
              apply polar_upper_half_true_iff in Hc.
              eapply upper_half_cross_trans_test with
                  (ax := ax - gx) (ay := ay - gy)
                  (bx := bx - gx) (byv := byv - gy)
                  (cx := cx - gx) (cy := cy - gy);
                [exact Ha | exact Hb | exact Hc | exact Hab_cross | exact Hbc_cross].
           ++ assert (Hb : polar_upper_half (gx, gy) (bx, byv) = false) by congruence.
              assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
              apply polar_upper_half_false_iff in Ha.
              apply polar_upper_half_false_iff in Hb.
              apply polar_upper_half_false_iff in Hc.
              eapply lower_half_cross_trans_test with
                  (ax := ax - gx) (ay := ay - gy)
                  (bx := bx - gx) (byv := byv - gy)
                  (cx := cx - gx) (cy := cy - gy);
                [exact Ha | exact Hb | exact Hc | exact Hab_cross | exact Hbc_cross].
        -- reflexivity.
    + unfold PolarLt, PolarCmpResult. cbn.
      right. right. left.
      split.
      * congruence.
      * split.
        -- destruct (polar_upper_half (gx, gy) (ax, ay)) eqn:Ha.
           ++ assert (Hb : polar_upper_half (gx, gy) (bx, byv) = true) by congruence.
              assert (Hc : polar_upper_half (gx, gy) (cx, cy) = true) by congruence.
              assert (Hbc_dist' :
                (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy) <
                (cx - gx) * (cx - gx) + (cy - gy) * (cy - gy)) by nia.
              apply polar_upper_half_true_iff in Ha.
              apply polar_upper_half_true_iff in Hb.
              apply polar_upper_half_true_iff in Hc.
              eapply upper_half_cross_ray_right_test with
                  (ax := ax - gx) (ay := ay - gy)
                  (bx := bx - gx) (byv := byv - gy)
                  (cx := cx - gx) (cy := cy - gy);
                [exact Ha | exact Hb | exact Hc | exact Hab_cross | exact Hbc_zero | exact Hbc_dist'].
           ++ assert (Hb : polar_upper_half (gx, gy) (bx, byv) = false) by congruence.
              assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
              assert (Hbc_dist' :
                (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy) <
                (cx - gx) * (cx - gx) + (cy - gy) * (cy - gy)) by nia.
              apply polar_upper_half_false_iff in Ha.
              apply polar_upper_half_false_iff in Hb.
              apply polar_upper_half_false_iff in Hc.
              eapply lower_half_cross_ray_right_test with
                  (ax := ax - gx) (ay := ay - gy)
                  (bx := bx - gx) (byv := byv - gy)
                  (cx := cx - gx) (cy := cy - gy);
                [exact Ha | exact Hb | exact Hc | exact Hab_cross | exact Hbc_zero | exact Hbc_dist'].
        -- reflexivity.
  - destruct Hbc' as [[Hbc_bt Hbc_cf] | [[Hbc_half' Hbc_cross] | [Hbc_half' [Hbc_zero Hbc_dist]]]].
    + unfold PolarLt, PolarCmpResult. cbn.
      assert (Ha : polar_upper_half (gx, gy) (ax, ay) = true) by congruence.
      left. repeat split; try exact Ha; try assumption; reflexivity.
    + unfold PolarLt, PolarCmpResult. cbn.
      destruct (polar_upper_half (gx, gy) (ax, ay)) eqn:Ha.
      * assert (Hb : polar_upper_half (gx, gy) (bx, byv) = true) by congruence.
        assert (Hc : polar_upper_half (gx, gy) (cx, cy) = true) by congruence.
        assert (Hab_dist' :
          (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy) <
          (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy)) by nia.
        apply polar_upper_half_true_iff in Ha.
        apply polar_upper_half_true_iff in Hb.
        apply polar_upper_half_true_iff in Hc.
        pose proof (upper_half_cross_ray_left_test
          (ax - gx) (ay - gy) (bx - gx) (byv - gy) (cx - gx) (cy - gy)
          Ha Hb Hc Hab_zero Hab_dist' Hbc_cross) as Hac.
        destruct Hac as [Hcross | [Hzero Hdist]].
        -- right. right. left. repeat split; try congruence; try exact Hcross; reflexivity.
        -- do 4 right. left.
           split; [congruence|].
           split; [exact Hzero|].
           split.
           ++ unfold point_dist2, point_x, point_y, mk_point in *; cbn in *; nia.
           ++ reflexivity.
      * assert (Hb : polar_upper_half (gx, gy) (bx, byv) = false) by congruence.
        assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
        assert (Hab_dist' :
          (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy) <
          (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy)) by nia.
        apply polar_upper_half_false_iff in Ha.
        apply polar_upper_half_false_iff in Hb.
        apply polar_upper_half_false_iff in Hc.
        pose proof (lower_half_cross_ray_left_test
          (ax - gx) (ay - gy) (bx - gx) (byv - gy) (cx - gx) (cy - gy)
          Ha Hb Hc Hab_zero Hab_dist' Hbc_cross) as Hac.
        destruct Hac as [Hcross | [Hzero Hdist]].
        -- right. right. left. repeat split; try congruence; try exact Hcross; reflexivity.
        -- do 4 right. left.
           split; [congruence|].
           split; [exact Hzero|].
           split.
           ++ unfold point_dist2, point_x, point_y, mk_point in *; cbn in *; nia.
           ++ reflexivity.
    + unfold PolarLt, PolarCmpResult. cbn.
      do 4 right. left.
      split.
      * congruence.
      * split.
        -- destruct (polar_upper_half (gx, gy) (ax, ay)) eqn:Ha.
           ++ assert (Hb : polar_upper_half (gx, gy) (bx, byv) = true) by congruence.
              assert (Hc : polar_upper_half (gx, gy) (cx, cy) = true) by congruence.
              assert (Hab_dist' :
                (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy) <
                (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy)) by nia.
              assert (Hbc_dist' :
                (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy) <
                (cx - gx) * (cx - gx) + (cy - gy) * (cy - gy)) by nia.
              apply polar_upper_half_true_iff in Ha.
              apply polar_upper_half_true_iff in Hb.
              apply polar_upper_half_true_iff in Hc.
              pose proof (upper_half_ray_dist_trans_test
                (ax - gx) (ay - gy) (bx - gx) (byv - gy) (cx - gx) (cy - gy)
                Ha Hb Hc Hab_zero Hab_dist' Hbc_zero Hbc_dist') as Hac.
              destruct Hac as [Hzero Hdist]. exact Hzero.
           ++ assert (Hb : polar_upper_half (gx, gy) (bx, byv) = false) by congruence.
              assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
              assert (Hab_dist' :
                (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy) <
                (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy)) by nia.
              assert (Hbc_dist' :
                (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy) <
                (cx - gx) * (cx - gx) + (cy - gy) * (cy - gy)) by nia.
              apply polar_upper_half_false_iff in Ha.
              apply polar_upper_half_false_iff in Hb.
              apply polar_upper_half_false_iff in Hc.
              pose proof (lower_half_ray_dist_trans_test
                (ax - gx) (ay - gy) (bx - gx) (byv - gy) (cx - gx) (cy - gy)
                Ha Hb Hc Hab_zero Hab_dist' Hbc_zero Hbc_dist') as Hac.
              destruct Hac as [Hzero Hdist]. exact Hzero.
        -- split.
           ++ destruct (polar_upper_half (gx, gy) (ax, ay)) eqn:Ha.
              ** assert (Hb : polar_upper_half (gx, gy) (bx, byv) = true) by congruence.
                 assert (Hc : polar_upper_half (gx, gy) (cx, cy) = true) by congruence.
                 assert (Hab_dist' :
                   (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy) <
                   (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy)) by nia.
                 assert (Hbc_dist' :
                   (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy) <
                   (cx - gx) * (cx - gx) + (cy - gy) * (cy - gy)) by nia.
                 apply polar_upper_half_true_iff in Ha.
                 apply polar_upper_half_true_iff in Hb.
                 apply polar_upper_half_true_iff in Hc.
                 pose proof (upper_half_ray_dist_trans_test
                   (ax - gx) (ay - gy) (bx - gx) (byv - gy) (cx - gx) (cy - gy)
                   Ha Hb Hc Hab_zero Hab_dist' Hbc_zero Hbc_dist') as Hac.
                 destruct Hac as [Hzero Hdist].
                 unfold point_dist2, point_x, point_y, mk_point in *; cbn in *; nia.
              ** assert (Hb : polar_upper_half (gx, gy) (bx, byv) = false) by congruence.
                 assert (Hc : polar_upper_half (gx, gy) (cx, cy) = false) by congruence.
                 assert (Hab_dist' :
                   (ax - gx) * (ax - gx) + (ay - gy) * (ay - gy) <
                   (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy)) by nia.
                 assert (Hbc_dist' :
                   (bx - gx) * (bx - gx) + (byv - gy) * (byv - gy) <
                   (cx - gx) * (cx - gx) + (cy - gy) * (cy - gy)) by nia.
                 apply polar_upper_half_false_iff in Ha.
                 apply polar_upper_half_false_iff in Hb.
                 apply polar_upper_half_false_iff in Hc.
                 pose proof (lower_half_ray_dist_trans_test
                   (ax - gx) (ay - gy) (bx - gx) (byv - gy) (cx - gx) (cy - gy)
                   Ha Hb Hc Hab_zero Hab_dist' Hbc_zero Hbc_dist') as Hac.
                 destruct Hac as [Hzero Hdist].
                 unfold point_dist2, point_x, point_y, mk_point in *; cbn in *; nia.
           ++ reflexivity.
Qed.

Lemma PolarLe_PolarLt_trans_structured :
  forall gp a b c,
    PolarLe gp a b ->
    PolarLt gp b c ->
    PolarLe gp a c.
Proof.
  intros gp a b c Hab Hbc.
  destruct (PolarLe_lt_or_eq_test _ _ _ Hab) as [Hlt | ->].
  - left. eapply PolarLt_trans_test; eauto.
  - left. exact Hbc.
Qed.

Lemma PointSameOutsideRange_trans :
  forall l l1 l2 left right,
    PointSameOutsideRange l l1 left right ->
    PointSameOutsideRange l1 l2 left right ->
    PointSameOutsideRange l l2 left right.
Proof.
  intros l l1 l2 left right [Hlen1 Heq1] [Hlen2 Heq2].
  split.
  - rewrite Hlen1. exact Hlen2.
  - intros k Hk Hout.
    assert (Hk1 : 0 <= k < Zlength l1) by (rewrite <- Hlen1; exact Hk).
    rewrite (Heq2 k Hk1 Hout).
    apply Heq1; assumption.
Qed.

Lemma PointSameOutsideRange_weaken :
  forall l l1 left1 right1 left2 right2,
    left2 <= left1 ->
    right1 <= right2 ->
    PointSameOutsideRange l l1 left1 right1 ->
    PointSameOutsideRange l l1 left2 right2.
Proof.
  intros l l1 left1 right1 left2 right2 Hleft Hright [Hlen Heq].
  split.
  - exact Hlen.
  - intros k Hk Hout.
    apply Heq; try assumption.
    destruct Hout as [Hout | Hout].
    + left. lia.
    + right. lia.
Qed.

Lemma PointCoordsBound_permutation :
  forall l1 l2,
    PointPermutation l1 l2 ->
    PointCoordsBound l1 ->
    PointCoordsBound l2.
Proof.
  intros l1 l2 Hperm Hbound.
  unfold PointCoordsBound in *.
  eapply Permutation_Forall; eauto.
Qed.

Lemma Forall_permutation_point :
  forall (P : point -> Prop) l1 l2,
    PointPermutation l1 l2 ->
    Forall P l1 ->
    Forall P l2.
Proof.
  intros P l1 l2 Hperm.
  induction Hperm; intros HForall.
  - exact HForall.
  - inversion HForall; subst.
    constructor; auto.
  - repeat match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end.
    constructor; auto.
  - apply IHHperm2.
    apply IHHperm1.
    exact HForall.
Qed.

Lemma Forall_Znth_point :
  forall (P : point -> Prop) (l : list point) i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l default_point).
Proof.
  intros P l i HForall Hrange.
  apply Forall_forall with (x := Znth i l default_point) in HForall.
  - exact HForall.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.

Lemma sublist_eq_from_Znth_point :
  forall l1 l2 lo hi,
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi -> Znth k l1 default_point = Znth k l2 default_point) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlen Hlohi Hhilen Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2) default_point)).
  split.
  - rewrite Zlength_sublist by (split; [exact Hlohi | exact Hhilen]).
    rewrite Zlength_sublist by (split; [exact Hlohi | rewrite <- Hlen; exact Hhilen]).
    lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    {
      rewrite Zlength_sublist in Hi by lia.
      exact Hi.
    }
    rewrite (@Znth_sublist_lt point default_point lo hi l1 i).
    2: exact Hlohi.
    2: exact Hhilen.
    2: exact Hi'.
    rewrite (@Znth_sublist_lt point default_point lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhilen. }
    2: exact Hi'.
    apply Hpoint.
    lia.
Qed.

Lemma list_decompose_sublist_point :
  forall l lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    l = @sublist point 0 lo l ++ @sublist point lo hi l ++ @sublist point hi (Zlength l) l.
Proof.
  intros l lo hi Hlohi Hhilen.
  rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) lo l).
  2: lia.
  2: {
    split.
    - transitivity hi; lia.
    - lia.
  }
  rewrite (sublist_split lo (Zlength l) hi l).
  2: lia.
  2: {
    split.
    - exact Hhilen.
    - lia.
  }
  reflexivity.
Qed.

Lemma PointSameOutsideRange_prefix :
  forall l l1 left right,
    PointSameOutsideRange l l1 left right ->
    0 <= left <= Zlength l ->
    sublist 0 left l1 = sublist 0 left l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  apply sublist_eq_from_Znth_point.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + lia.
    + left. lia.
Qed.

Lemma PointSameOutsideRange_suffix :
  forall l l1 left right,
    PointSameOutsideRange l l1 left right ->
    0 <= right + 1 <= Zlength l ->
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l.
Proof.
  intros l l1 left right Hsame Hrange.
  destruct Hsame as [Hlen Heq].
  rewrite <- Hlen.
  apply sublist_eq_from_Znth_point.
  - symmetry. exact Hlen.
  - lia.
  - lia.
  - intros k Hk.
    apply Heq.
    + rewrite Hlen. lia.
    + right. lia.
Qed.

Lemma PointPermutation_middle_of_same_outside :
  forall l l1 left right,
    PointPermutation l l1 ->
    PointSameOutsideRange l l1 left right ->
    0 <= left <= right + 1 ->
    right + 1 <= Zlength l ->
    PointPermutation (sublist left (right + 1) l) (sublist left (right + 1) l1).
Proof.
  intros l l1 left right Hperm Hsame Hlr Hlenr.
  pose proof Hsame as Hsame0.
  destruct Hsame as [Hlen _].
  pose proof (PointSameOutsideRange_prefix _ _ _ _ Hsame0) as Hpre.
  pose proof (PointSameOutsideRange_suffix _ _ _ _ Hsame0) as Hsuf.
  rewrite (list_decompose_sublist_point l left (right + 1)) in Hperm by lia.
  assert (Hlenr1 : right + 1 <= Zlength l1) by (rewrite <- Hlen; exact Hlenr).
  rewrite (list_decompose_sublist_point l1 left (right + 1)) in Hperm by lia.
  specialize (Hpre ltac:(lia)).
  specialize (Hsuf ltac:(lia)).
  rewrite Hpre, Hsuf in Hperm.
  apply Permutation_app_inv_l in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.

Lemma Forall_sublist_by_Znth_point :
  forall (P : point -> Prop) (l : list point) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall k, lo <= k < hi -> P (Znth k l default_point)) ->
    Forall P (sublist lo hi l).
Proof.
  intros P l lo hi Hlohi Hhilen Hpoint.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo hi Hlohi Hhilen Hpoint Hn.
  induction n; intros lo hi Hlohi Hhilen Hpoint Hn.
  - assert (hi = lo) by lia.
    subst hi.
    rewrite (@Zsublist_nil point l lo lo) by lia.
    constructor.
  - assert (lo < hi) by lia.
    rewrite (sublist_split lo hi (lo + 1) l).
    2: lia.
    2: {
      split.
      - lia.
      - exact Hhilen.
    }
    rewrite (@sublist_single point default_point lo l) by lia.
    constructor.
    + simpl. apply Hpoint. lia.
    + apply IHn with (lo := lo + 1) (hi := hi).
      * lia.
      * exact Hhilen.
      * intros k Hk. apply Hpoint. lia.
      * assert (Hn' : Z.to_nat (hi - (lo + 1)) = n) by lia.
        symmetry. exact Hn'.
Qed.

Lemma Forall_sublist_lookup_point :
  forall (P : point -> Prop) (l : list point) lo hi k,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    Forall P (sublist lo hi l) ->
    lo <= k < hi ->
    P (Znth k l default_point).
Proof.
  intros P l lo hi k Hlohi Hhilen Hforall Hk.
  pose proof (Forall_Znth_point P (sublist lo hi l) (k - lo) Hforall) as Hz.
  assert (Hrange : 0 <= k - lo < Zlength (sublist lo hi l)).
  {
    rewrite Zlength_sublist by (destruct Hlohi; lia).
    lia.
  }
  specialize (Hz Hrange).
  rewrite (@Znth_sublist_lt point default_point lo hi l (k - lo)) in Hz.
  2: destruct Hlohi; lia.
  2: exact Hhilen.
  2: {
    rewrite Zlength_sublist in Hrange by (destruct Hlohi; lia).
    exact Hrange.
  }
  replace (lo + (k - lo)) with k in Hz by lia.
  exact Hz.
Qed.

Lemma PointSameOutsideRange_swap_inside :
  forall l low high i j,
    0 <= low ->
    low <= i <= high ->
    low <= j <= high ->
    high < Zlength l ->
    PointSameOutsideRange l (point_swap_points l i j) low high.
Proof.
  intros l low high i j Hlow Hi Hj Hhigh.
  unfold PointSameOutsideRange.
  split.
  - rewrite Zlength_point_swap_points. reflexivity.
  - intros k Hk Hout.
    assert (Hkj : k <> j).
    { intro Heq. subst k. destruct Hout as [Hout | Hout]; lia. }
    assert (Hki : k <> i).
    { intro Heq. subst k. destruct Hout as [Hout | Hout]; lia. }
    apply Znth_point_swap_points_other; try lia.
Qed.

Lemma replace_Znth_swap_form_point :
  forall (l1 l2 l3 : list point) (xi xj : point),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3)) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := point) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) = xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3)) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := point) (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := point) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1.
  reflexivity.
Qed.

Lemma PointPermutation_swap_points :
  forall l i j,
    0 <= i /\ i < j /\ j < Zlength l ->
    PointPermutation l (point_swap_points l i j).
Proof.
  intros l i j Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l default_point) as xi0.
  remember (Znth j l default_point) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l default_point) at 1.
    2: { rewrite Zlength_correct in Hj. lia. }
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
    rewrite (list_split_nth _ nj lr default_point) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr default_point).
    2: {
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat : (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2: {
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2: {
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  unfold point_swap_points.
  assert (HZi :
    Znth (Zlength l1) (l1 ++ xi0 :: l2 ++ xj0 :: l3) default_point = xi0).
  {
    rewrite (@app_Znth2 point default_point l1 (xi0 :: l2 ++ xj0 :: l3) (Zlength l1)) by lia.
    replace (Zlength l1 - Zlength l1) with 0 by lia.
    simpl.
    reflexivity.
  }
  assert (HZj :
    Znth (Zlength l1 + 1 + Zlength l2) (l1 ++ xi0 :: l2 ++ xj0 :: l3) default_point = xj0).
  {
    pose proof (Zlength_nonneg l2) as Hlen2.
    rewrite (@app_Znth2 point default_point l1 (xi0 :: l2 ++ xj0 :: l3) (Zlength l1 + 1 + Zlength l2)) by lia.
    replace (Zlength l1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2) by lia.
    rewrite Znth_cons by lia.
    replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
    rewrite (@app_Znth2 point default_point l2 (xj0 :: l3) (Zlength l2)) by lia.
    replace (Zlength l2 - Zlength l2) with 0 by lia.
    simpl.
    reflexivity.
  }
  rewrite HZi, HZj.
  rewrite replace_Znth_swap_form_point.
  eapply Permutation_trans.
  2: { reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.

Lemma point_swap_points_comm :
  forall l i j,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    point_swap_points l i j = point_swap_points l j i.
Proof.
  intros l i j Hi Hj.
  apply (proj2 (list_eq_ext (point_swap_points l i j) (point_swap_points l j i) default_point)).
  split.
  - repeat rewrite Zlength_point_swap_points.
    reflexivity.
  - intros k Hk.
    assert (Hcase : k = i \/ k = j \/ (k <> i /\ k <> j)) by lia.
    destruct Hcase as [-> | [-> | [Hki Hkj]]].
    + rewrite Znth_point_swap_points_left.
      * rewrite Znth_point_swap_points_right with (i := j) (j := i).
        -- reflexivity.
        -- exact Hj.
        -- exact Hi.
      * exact Hi.
      * exact Hj.
    + rewrite Znth_point_swap_points_right.
      rewrite Znth_point_swap_points_left with (i := j) (j := i).
      * reflexivity.
      * exact Hj.
      * exact Hi.
      * exact Hi.
      * exact Hj.
    + rewrite Znth_point_swap_points_other with (i := i) (j := j).
      * rewrite Znth_point_swap_points_other with (i := j) (j := i).
        -- reflexivity.
        -- exact Hj.
        -- exact Hi.
        -- rewrite Zlength_point_swap_points in Hk.
           exact Hk.
        -- exact Hkj.
        -- exact Hki.
      * exact Hi.
      * exact Hj.
      * rewrite Zlength_point_swap_points in Hk.
        exact Hk.
      * exact Hki.
      * exact Hkj.
Qed.

Lemma PointPermutation_swap_points_any :
  forall l i j,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    PointPermutation l (point_swap_points l i j).
Proof.
  intros l i j Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hnji].
  - apply PointPermutation_swap_points.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hnji'].
    + rewrite point_swap_points_comm by assumption.
      apply PointPermutation_swap_points.
      lia.
    + assert (i = j) by lia.
      subst j.
      unfold point_swap_points.
      repeat rewrite replace_Znth_Znth with (a0 := default_point).
      apply Permutation_refl.
Qed.

Lemma PointPartitionedAt_preserved_by_left :
  forall gp l l1 left right p,
    PointPermutation l l1 ->
    0 <= left ->
    PointSameOutsideRange l l1 left (p - 1) ->
    right < Zlength l ->
    PointPartitionedAt gp l left right p ->
    PointPartitionedAt gp l1 left right p.
Proof.
  intros gp l l1 left right p Hperm Hleft0 Hsame Hlen Hpart.
  destruct Hsame as [Hlen' Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 default_point = Znth p l default_point).
  {
    assert (Hp : 0 <= p < Zlength l) by lia.
    apply Heq.
    - exact Hp.
    - right. lia.
  }
  split.
  - lia.
  - split.
    + rewrite Hpiv.
      eapply (Forall_permutation_point
                (fun x => PolarLe gp x (Znth p l default_point))
                (sublist left p l)
                (sublist left p l1)).
      * assert (Hmid :
            PointPermutation (sublist left (p - 1 + 1) l)
                             (sublist left (p - 1 + 1) l1)).
        {
          eapply PointPermutation_middle_of_same_outside
            with (left := left) (right := p - 1).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        replace (p - 1 + 1) with p in Hmid by lia.
        exact Hmid.
      * exact Hleft.
    + rewrite Hpiv.
      apply Forall_sublist_by_Znth_point; try lia.
      intros k Hk.
      rewrite Heq by (try lia; right; lia).
      assert (Hk' : 0 <= k - (p + 1) < Zlength (sublist (p + 1) (right + 1) l)) by
        (rewrite Zlength_sublist by lia; lia).
      pose proof (Forall_Znth_point _ _ (k - (p + 1)) Hright Hk') as Hz.
      rewrite (@Znth_sublist_lt point default_point (p + 1) (right + 1) l (k - (p + 1))) in Hz.
      2: lia.
      2: lia.
      2: {
        rewrite Zlength_sublist in Hk' by lia.
        exact Hk'.
      }
      replace (p + 1 + (k - (p + 1))) with k in Hz by lia.
      exact Hz.
Qed.

Lemma PointPartitionedAt_preserved_by_right :
  forall gp l l1 left right p,
    PointPermutation l l1 ->
    0 <= left ->
    PointSameOutsideRange l l1 (p + 1) right ->
    right < Zlength l ->
    PointPartitionedAt gp l left right p ->
    PointPartitionedAt gp l1 left right p.
Proof.
  intros gp l l1 left right p Hperm Hleft0 Hsame Hlen Hpart.
  destruct Hsame as [Hlen' Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 default_point = Znth p l default_point).
  {
    assert (Hp : 0 <= p < Zlength l) by lia.
    apply Heq.
    - exact Hp.
    - left. lia.
  }
  split.
  - lia.
  - split.
    + rewrite Hpiv.
      assert (Hsub : sublist left p l1 = sublist left p l).
      {
        apply sublist_eq_from_Znth_point.
        - symmetry. exact Hlen'.
        - lia.
        - lia.
        - intros k Hk.
          apply Heq.
          * lia.
          * left. lia.
      }
      rewrite Hsub.
      exact Hleft.
    + rewrite Hpiv.
      eapply (Forall_permutation_point
                (fun x => PolarLt gp (Znth p l default_point) x)
                (sublist (p + 1) (right + 1) l)
                (sublist (p + 1) (right + 1) l1)).
      * assert (Hmid :
            PointPermutation (sublist (p + 1) (right + 1) l)
                             (sublist (p + 1) (right + 1) l1)).
        {
          eapply PointPermutation_middle_of_same_outside
            with (left := p + 1) (right := right).
          - exact Hperm.
          - exact (conj Hlen' Heq).
          - lia.
          - lia.
        }
        exact Hmid.
      * exact Hright.
Qed.

Lemma PointPartitionedAt_after_final_swap :
  forall gp l l1 low high pivot i,
    0 <= low ->
    high < Zlength l1 ->
    low - 1 <= i ->
    i < high ->
    PointPartitionScanInv gp l l1 low high pivot i high ->
    PointPartitionedAt gp (point_swap_points l1 (i + 1) high) low high (i + 1).
Proof.
  intros gp l l1 low high pivot i Hlow Hhigh Hile Hihigh
         [_ [_ [Hpivot [Hle Hgt]]]].
  set (l2 := point_swap_points l1 (i + 1) high).
  assert (Hi1 : 0 <= i + 1 < Zlength l1) by lia.
  assert (Hhighrange : 0 <= high < Zlength l1) by lia.
  assert (Hpiv : Znth (i + 1) l2 default_point = pivot).
  {
    subst l2.
    rewrite Znth_point_swap_points_left; auto.
  }
  split.
  - lia.
  - split.
    + apply Forall_sublist_by_Znth_point.
      * lia.
      * subst l2. rewrite Zlength_point_swap_points. lia.
      * intros k Hk.
        rewrite Hpiv.
        assert (Hklen : 0 <= k < Zlength l1) by lia.
        assert (Hkhigh : k <> high) by lia.
        assert (Hki1 : k <> i + 1) by lia.
        subst l2.
        rewrite Znth_point_swap_points_other; auto.
        apply Hle. lia.
    + apply Forall_sublist_by_Znth_point.
      * lia.
      * subst l2. rewrite Zlength_point_swap_points. lia.
      * intros k Hk.
        rewrite Hpiv.
        assert (Hklen : 0 <= k < Zlength l1) by lia.
        destruct (Z.eq_dec k high) as [Hkhigh | Hkhigh].
        -- subst k.
           subst l2.
           rewrite Znth_point_swap_points_right; auto.
           apply Hgt. lia.
        -- assert (Hki1 : k <> i + 1) by lia.
           subst l2.
           rewrite Znth_point_swap_points_other; auto.
           apply Hgt. lia.
Qed.

Lemma PointSortedRange_from_left_boundary :
  forall gp l left right p,
    0 <= left ->
    p >= right ->
    right < Zlength l ->
    PointPartitionedAt gp l left right p ->
    PointSortedRange gp l left (p - 1) ->
    PointSortedRange gp l left right.
Proof.
  intros gp l left right p Hleft0 Hp Hrightlen Hpart Hsorted i j Hi Hij Hj.
  destruct Hpart as [Hbounds [Hleftpart _]].
  assert (p = right) by lia.
  subst p.
  destruct (Z.eq_dec j right) as [-> | Hjneq].
  - destruct (Z.eq_dec i right) as [-> | Hineq].
    + apply PolarLe_refl.
    + pose proof (Forall_Znth_point
                    (fun x => PolarLe gp x (Znth right l default_point))
                    (sublist left right l)
                    (i - left) Hleftpart) as Hz.
      assert (Hrange : 0 <= i - left < Zlength (sublist left right l)).
      {
        rewrite Zlength_sublist by lia.
        lia.
      }
      specialize (Hz Hrange).
      rewrite (@Znth_sublist_lt point default_point left right l (i - left)) in Hz.
      2: lia.
      2: lia.
      2: {
        rewrite Zlength_sublist in Hrange by lia.
        exact Hrange.
      }
      replace (left + (i - left)) with i in Hz by lia.
      exact Hz.
  - apply Hsorted; lia.
Qed.

Lemma PointSortedRange_from_right_boundary :
  forall gp l left right p,
    0 <= left ->
    p <= left ->
    right < Zlength l ->
    PointPartitionedAt gp l left right p ->
    PointSortedRange gp l (p + 1) right ->
    PointSortedRange gp l left right.
Proof.
  intros gp l left right p Hleft0 Hp Hrightlen Hpart Hsorted i j Hi Hij Hj.
  destruct Hpart as [Hbounds [_ Hrightpart]].
  assert (p = left) by lia.
  subst p.
  destruct (Z.eq_dec i left) as [-> | Hineq].
  - destruct (Z.eq_dec j left) as [-> | Hjneq].
    + apply PolarLe_refl.
    + apply PolarLt_implies_PolarLe.
      pose proof (Forall_Znth_point
                    (fun x => PolarLt gp (Znth left l default_point) x)
                    (sublist (left + 1) (right + 1) l)
                    (j - (left + 1)) Hrightpart) as Hz.
      assert (Hrange : 0 <= j - (left + 1) < Zlength (sublist (left + 1) (right + 1) l)).
      {
        rewrite Zlength_sublist by lia.
        lia.
      }
      specialize (Hz Hrange).
      rewrite (@Znth_sublist_lt point default_point (left + 1) (right + 1) l (j - (left + 1))) in Hz.
      2: lia.
      2: lia.
      2: {
        rewrite Zlength_sublist in Hrange by lia.
        exact Hrange.
      }
      replace (left + 1 + (j - (left + 1))) with j in Hz by lia.
      exact Hz.
  - apply Hsorted; lia.
Qed.

Lemma PointSortedRange_from_middle_partition :
  forall gp l left right p,
    0 <= left ->
    left < p ->
    p < right ->
    right < Zlength l ->
    PointPartitionedAt gp l left right p ->
    PointSortedRange gp l left (p - 1) ->
    PointSortedRange gp l (p + 1) right ->
    PointSortedRange gp l left right.
Proof.
  intros gp l left right p Hleft0 Hlp Hpr Hrightlen Hpart Hsorted_left Hsorted_right.
  intros i j Hi Hij Hj.
  destruct Hpart as [_ [Hleftpart Hrightpart]].
  assert (Hleft_pivot :
    forall k,
      left <= k < p ->
      PolarLe gp (Znth k l default_point) (Znth p l default_point)).
  {
    intros k Hk.
    eapply (Forall_sublist_lookup_point
              (fun x => PolarLe gp x (Znth p l default_point))
              l left p k).
    - lia.
    - lia.
    - exact Hleftpart.
    - exact Hk.
  }
  assert (Hpivot_right :
    forall k,
      p < k <= right ->
      PolarLt gp (Znth p l default_point) (Znth k l default_point)).
  {
    intros k Hk.
    eapply (Forall_sublist_lookup_point
              (fun x => PolarLt gp (Znth p l default_point) x)
              l (p + 1) (right + 1) k).
    - lia.
    - lia.
    - exact Hrightpart.
    - lia.
  }
  destruct (Z_lt_ge_dec j p) as [Hjlt | Hjge].
  - apply Hsorted_left; lia.
  - destruct (Z.eq_dec i p) as [-> | Hineq].
    + destruct (Z.eq_dec j p) as [-> | Hjneq].
      * apply PolarLe_refl.
      * apply PolarLt_implies_PolarLe.
        apply Hpivot_right.
        lia.
    + destruct (Z_lt_ge_dec i p) as [Hilt | Hige].
      * destruct (Z.eq_dec j p) as [-> | Hjneq].
        -- apply Hleft_pivot. lia.
        -- eapply PolarLe_PolarLt_trans_structured.
           ++ apply Hleft_pivot. lia.
           ++ apply Hpivot_right. lia.
      * apply Hsorted_right; lia.
Qed.

Lemma PointSortedRange_ext :
  forall gp l l1 left right,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right -> Znth k l1 default_point = Znth k l default_point) ->
    PointSortedRange gp l left right ->
    PointSortedRange gp l1 left right.
Proof.
  intros gp l l1 left right Hleft0 Hrightlen Hlen Heq Hsorted i j Hi Hij Hj.
  rewrite (Heq i) by lia.
  rewrite (Heq j) by lia.
  apply Hsorted; lia.
Qed.

Lemma Zlength_point_swap_flat :
  forall flat i j,
    Zlength (point_swap_flat flat i j) = Zlength flat.
Proof.
  intros.
  unfold point_swap_flat.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma point_swap_flat_preprocess_form :
  forall flat n i j,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    replace_Znth (2 * j + 1) (Znth (2 * i + 1) flat 0)
      (replace_Znth (2 * j) (Znth (2 * i) flat 0)
        (replace_Znth (2 * i + 1)
          (Znth (2 * j + 1)
            (replace_Znth (2 * i) (Znth (2 * j) flat 0) flat) 0)
          (replace_Znth (2 * i) (Znth (2 * j) flat 0) flat))) =
    point_swap_flat flat i j.
Proof.
  intros flat n i j Hlen Hi Hj.
  unfold point_swap_flat.
  rewrite Znth_replace_Znth_Diff with (i := 2 * i) (j := 2 * j + 1).
  - reflexivity.
  - lia.
  - repeat rewrite Zlength_replace_Znth.
    lia.
  - lia.
Qed.

Lemma flat_points_rec_from_lookup :
  forall flat pts,
    Zlength flat = 2 * Zlength pts ->
    (forall j,
        0 <= j < Zlength pts ->
        Znth j pts default_point =
        mk_point (Znth (2 * j) flat 0) (Znth (2 * j + 1) flat 0)) ->
    flat_points_rec flat pts.
Proof.
  intros flat pts.
  revert flat.
  induction pts as [| [x y] pts IH]; intros flat Hlen Hlookup.
  - destruct flat as [| a flat'].
    + reflexivity.
    + destruct flat' as [| b flat''].
      * exfalso.
        rewrite Zlength_cons, Zlength_nil in Hlen.
        lia.
      * exfalso.
        rewrite !Zlength_correct in Hlen.
        simpl in Hlen.
        lia.
  - destruct flat as [| a flat'].
    + exfalso.
      rewrite !Zlength_correct in Hlen.
      simpl in Hlen.
      lia.
    + destruct flat' as [| b flat_rest].
      * exfalso.
        rewrite !Zlength_correct in Hlen.
        simpl in Hlen.
        lia.
      * rewrite !Zlength_cons in Hlen.
    assert (Hxy :
      mk_point x y =
      mk_point (Znth 0 (a :: b :: flat_rest) 0)
               (Znth (2 * 0 + 1) (a :: b :: flat_rest) 0)).
    {
      specialize (Hlookup 0).
      assert (Hk0 : 0 < Zlength ((x, y) :: pts)).
      { rewrite Zlength_correct.
        simpl.
        lia. }
      specialize (Hlookup (conj (Z.le_refl 0) Hk0)).
      rewrite Znth0_cons in Hlookup.
      change (Znth (2 * 0 + 1) (a :: b :: flat_rest) 0)
        with (Znth 1 (a :: b :: flat_rest) 0) in Hlookup.
      rewrite (Znth_cons 0 1 a (b :: flat_rest)) in Hlookup by lia.
      rewrite Znth0_cons in Hlookup.
      exact Hlookup.
    }
    assert (Hxa : x = a).
    { apply (f_equal fst) in Hxy.
      exact Hxy. }
    assert (Hyb : y = b).
    { apply (f_equal snd) in Hxy.
      exact Hxy. }
    subst a b.
    exists flat_rest.
    split; [reflexivity|].
    apply IH.
    { lia. }
    { intros j Hj.
      specialize (Hlookup (j + 1)).
      rewrite Zlength_cons in Hlookup.
      assert (Hk1_upper : j + 1 < Z.succ (Zlength pts)) by lia.
      assert (Hk1_lower : 0 <= j + 1) by lia.
      specialize (Hlookup (conj Hk1_lower Hk1_upper)).
      rewrite Znth_cons in Hlookup by lia.
      replace (j + 1 - 1) with j in Hlookup by lia.
      rewrite Znth_cons in Hlookup by lia.
      rewrite Znth_cons in Hlookup by lia.
      replace (2 * (j + 1) - 1 - 1) with (2 * j) in Hlookup by lia.
      rewrite Znth_cons in Hlookup by lia.
      rewrite Znth_cons in Hlookup by lia.
      replace (2 * (j + 1) + 1 - 1 - 1) with (2 * j + 1) in Hlookup by lia.
      exact Hlookup. }
Qed.

Lemma FlatPoints_from_lookup :
  forall flat pts,
    Zlength flat = 2 * Zlength pts ->
    (forall j,
        0 <= j < Zlength pts ->
        Znth j pts default_point =
        mk_point (Znth (2 * j) flat 0) (Znth (2 * j + 1) flat 0)) ->
    FlatPoints flat pts.
Proof.
  intros.
  split; [exact H|].
  eapply flat_points_rec_from_lookup; eauto.
Qed.

Lemma Znth_point_swap_flat_x_left :
  forall flat n i j,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    Znth (2 * i) (point_swap_flat flat i j) 0 = Znth (2 * j) flat 0.
Proof.
  intros flat n i j Hlen Hi Hj.
  unfold point_swap_flat.
  rewrite Znth_replace_Znth_Diff with (i := 2 * j + 1) (j := 2 * i)
    by (repeat rewrite Zlength_replace_Znth; lia).
  destruct (Z.eq_dec i j) as [-> | Hij].
  - rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := 2 * j) (j := 2 * i)
      by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff with (i := 2 * i + 1) (j := 2 * i)
      by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
Qed.

Lemma Znth_point_swap_flat_y_left :
  forall flat n i j,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    Znth (2 * i + 1) (point_swap_flat flat i j) 0 = Znth (2 * j + 1) flat 0.
Proof.
  intros flat n i j Hlen Hi Hj.
  unfold point_swap_flat.
  destruct (Z.eq_dec i j) as [-> | Hij].
  - rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := 2 * j + 1) (j := 2 * i + 1)
      by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff with (i := 2 * j) (j := 2 * i + 1)
      by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
Qed.

Lemma Znth_point_swap_flat_x_right :
  forall flat n i j,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    Znth (2 * j) (point_swap_flat flat i j) 0 = Znth (2 * i) flat 0.
Proof.
  intros flat n i j Hlen Hi Hj.
  unfold point_swap_flat.
  rewrite Znth_replace_Znth_Diff with (i := 2 * j + 1) (j := 2 * j)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
  reflexivity.
Qed.

Lemma Znth_point_swap_flat_y_right :
  forall flat n i j,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    Znth (2 * j + 1) (point_swap_flat flat i j) 0 = Znth (2 * i + 1) flat 0.
Proof.
  intros flat n i j Hlen Hi Hj.
  unfold point_swap_flat.
  rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
  reflexivity.
Qed.

Lemma Znth_point_swap_flat_x_other :
  forall flat n i j k,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    0 <= k < n ->
    k <> i ->
    k <> j ->
    Znth (2 * k) (point_swap_flat flat i j) 0 = Znth (2 * k) flat 0.
Proof.
  intros flat n i j k Hlen Hi Hj Hk Hki Hkj.
  unfold point_swap_flat.
  rewrite Znth_replace_Znth_Diff with (i := 2 * j + 1) (j := 2 * k)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := 2 * j) (j := 2 * k)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := 2 * i + 1) (j := 2 * k)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := 2 * i) (j := 2 * k)
    by lia.
  reflexivity.
Qed.

Lemma Znth_point_swap_flat_y_other :
  forall flat n i j k,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    0 <= k < n ->
    k <> i ->
    k <> j ->
    Znth (2 * k + 1) (point_swap_flat flat i j) 0 = Znth (2 * k + 1) flat 0.
Proof.
  intros flat n i j k Hlen Hi Hj Hk Hki Hkj.
  unfold point_swap_flat.
  rewrite Znth_replace_Znth_Diff with (i := 2 * j + 1) (j := 2 * k + 1)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := 2 * j) (j := 2 * k + 1)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := 2 * i + 1) (j := 2 * k + 1)
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := 2 * i) (j := 2 * k + 1)
    by lia.
  reflexivity.
Qed.

Lemma FlatPoints_swap_points :
  forall flat pts i j,
    FlatPoints flat pts ->
    0 <= i < Zlength pts ->
    0 <= j < Zlength pts ->
    FlatPoints (point_swap_flat flat i j) (point_swap_points pts i j).
Proof.
  intros flat pts i j Hflat Hi Hj.
  destruct Hflat as [Hlen Hrec].
  apply FlatPoints_from_lookup.
  - rewrite Zlength_point_swap_flat.
    rewrite Zlength_point_swap_points.
    exact Hlen.
  - intros k Hk.
    assert (Hcase : k = i \/ k = j \/ (k <> i /\ k <> j)) by lia.
    destruct Hcase as [-> | [-> | [Hki Hkj]]];
      [ rewrite Znth_point_swap_points_left; [| exact Hi | exact Hj];
        pose proof (FlatPoints_Znth_point flat pts j (conj Hlen Hrec) Hj) as Hptj;
        rewrite Hptj;
        rewrite Znth_point_swap_flat_x_left with (n := Zlength pts); auto;
        rewrite Znth_point_swap_flat_y_left with (n := Zlength pts); auto;
        reflexivity
      | rewrite Znth_point_swap_points_right; [| exact Hi | exact Hj];
        pose proof (FlatPoints_Znth_point flat pts i (conj Hlen Hrec) Hi) as Hpti;
        rewrite Hpti;
        rewrite Znth_point_swap_flat_x_right with (n := Zlength pts); auto;
        rewrite Znth_point_swap_flat_y_right with (n := Zlength pts); auto;
        reflexivity
      | assert (Hk_pts : 0 <= k < Zlength pts);
        [ rewrite Zlength_point_swap_points in Hk; exact Hk
        | rewrite Znth_point_swap_points_other; [| exact Hi | exact Hj | exact Hk_pts | exact Hki | exact Hkj];
          pose proof (FlatPoints_Znth_point flat pts k (conj Hlen Hrec) Hk_pts) as Hptk;
          rewrite Hptk;
          rewrite Znth_point_swap_flat_x_other with (n := Zlength pts); auto;
          rewrite Znth_point_swap_flat_y_other with (n := Zlength pts); auto;
          reflexivity ] ].
Qed.
