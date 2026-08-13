Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive PrefixSplitState
    (l : list Z) (cap : Z) : Z -> Z -> Z -> Prop :=
  | PrefixSplitState_zero :
      0 <= cap ->
      PrefixSplitState l cap 0 1 0
  | PrefixSplitState_new_segment :
      forall i cnt cur,
        0 <= i < Zlength l ->
        0 <= Znth i l 0 <= cap ->
        cur + Znth i l 0 > cap ->
        PrefixSplitState l cap i cnt cur ->
        PrefixSplitState l cap (i + 1) (cnt + 1) (Znth i l 0)
  | PrefixSplitState_extend :
      forall i cnt cur,
        0 <= i < Zlength l ->
        0 <= Znth i l 0 <= cap ->
        cur + Znth i l 0 <= cap ->
        PrefixSplitState l cap i cnt cur ->
        PrefixSplitState l cap (i + 1) cnt (cur + Znth i l 0).

Definition CanSplit (l : list Z) (m cap : Z) : Prop :=
  exists cnt cur,
    PrefixSplitState l cap (Zlength l) cnt cur /\ cnt <= m.

Definition CannotSplit (l : list Z) (m cap : Z) : Prop :=
  forall cnt cur,
    PrefixSplitState l cap (Zlength l) cnt cur -> m < cnt.

Definition SegmentPartition (l : list Z) (parts : list (list Z)) : Prop :=
  parts <> [] /\
  concat parts = l /\
  Forall (fun seg => seg <> []) parts.

Definition MaxSegmentSum (parts : list (list Z)) (max_sum : Z) : Prop :=
  max_value_of_subset Z.le
    (fun seg => In seg parts)
    (fun seg => sum seg)
    max_sum.

Definition PartitionMaxSegmentSum (l : list Z) (m max_sum : Z) : Prop :=
  exists parts,
    SegmentPartition l parts /\
    Zlength parts = m /\
    MaxSegmentSum parts max_sum.

Definition NotPartitionMaxSegmentSum (l : list Z) (m max_sum : Z) : Prop :=
  ~ PartitionMaxSegmentSum l m max_sum.

Definition MinimizedMaxSegmentSum (l : list Z) (m answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun max_sum => PartitionMaxSegmentSum l m max_sum)
    (fun max_sum => max_sum)
    answer.

Lemma minimized_partition_witness:
  forall l m answer,
    MinimizedMaxSegmentSum l m answer ->
    PartitionMaxSegmentSum l m answer.
Proof.
  intros l m answer Hmin.
  unfold min_value_of_subset, min_object_of_subset in Hmin.
  destruct Hmin as [best [[Hpart _] Heq]].
  simpl in Heq.
  subst.
  exact Hpart.
Qed.

Lemma minimized_lower_bound:
  forall l m answer max_sum,
    MinimizedMaxSegmentSum l m answer ->
    PartitionMaxSegmentSum l m max_sum ->
    answer <= max_sum.
Proof.
  intros l m answer max_sum Hmin Hpart.
  unfold min_value_of_subset, min_object_of_subset in Hmin.
  destruct Hmin as [best [[_ Hlower] Heq]].
  simpl in Heq.
  subst.
  apply Hlower.
  exact Hpart.
Qed.

Lemma minmax_not_partition_below:
  forall l m answer cap,
    MinimizedMaxSegmentSum l m answer ->
    cap < answer ->
    NotPartitionMaxSegmentSum l m cap.
Proof.
  intros l m answer cap Hmin Hlt Hpart.
  pose proof (minimized_lower_bound _ _ _ _ Hmin Hpart).
  lia.
Qed.

Lemma can_split_cannot_contradiction:
  forall l m cap,
    CanSplit l m cap ->
    CannotSplit l m cap ->
    False.
Proof.
  intros l m cap Hcan Hcannot.
  unfold CanSplit in Hcan.
  unfold CannotSplit in Hcannot.
  destruct Hcan as [cnt [cur [Hstate Hle]]].
  specialize (Hcannot cnt cur Hstate).
  lia.
Qed.

Lemma mid_quot_bounds:
  forall left right,
    0 <= left ->
    left < right ->
    right <= 1000000000 ->
    0 <= left + (right - left) ÷ 2 <= 1000000000.
Proof.
  intros.
  assert (0 <= (right - left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right - left) ÷ 2 <= right - left) by
    (apply (Z.quot_le_upper_bound (right - left) 2 (right - left)); lia).
  lia.
Qed.

Lemma prefix_split_state_zero:
  forall l cap,
    0 <= cap ->
    PrefixSplitState l cap 0 1 0.
Proof.
  intros.
  constructor; lia.
Qed.

Lemma prefix_split_state_step_over_cap:
  forall l cap n i cnt cur,
    Zlength l = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k l 0 < 100000000) ->
    0 <= i ->
    i < n ->
    Znth i l 0 <= cap ->
    cur + Znth i l 0 > cap ->
    PrefixSplitState l cap i cnt cur ->
    PrefixSplitState l cap (i + 1) (cnt + 1) (Znth i l 0).
Proof.
  intros l cap n i cnt cur Hlen Hbound Hlow Hi Hle Hover Hprefix.
  eapply PrefixSplitState_new_segment; try eassumption; try lia.
  pose proof (Hbound i ltac:(lia)); lia.
Qed.

Lemma prefix_split_state_extend_no_split:
  forall (l : list Z) (cap i cnt cur : Z),
    (forall k : Z, 0 <= k < Zlength l -> 0 <= Znth k l 0) ->
    0 <= i ->
    Znth i l 0 <= cap ->
    cur + Znth i l 0 <= cap ->
    i < Zlength l ->
    PrefixSplitState l cap i cnt cur ->
    PrefixSplitState l cap (i + 1) cnt (cur + Znth i l 0).
Proof.
  intros l cap i cnt cur Hnonneg Hlow Hzcap Hsum Hi Hpre.
  eapply PrefixSplitState_extend; try eassumption; try lia.
  split; [apply Hnonneg; lia | exact Hzcap].
Qed.

Lemma PrefixSplitState_items_bound:
  forall l cap i cnt cur,
    PrefixSplitState l cap i cnt cur ->
    forall k, 0 <= k < i -> 0 <= Znth k l 0 <= cap.
Proof.
  intros l cap i cnt cur Hstate.
  induction Hstate; intros k Hk.
  - lia.
  - destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + apply IHHstate; lia.
    + assert (k = i) by lia.
      subst k; lia.
  - destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + apply IHHstate; lia.
    + assert (k = i) by lia.
      subst k; lia.
Qed.

Lemma PrefixSplitState_unique:
  forall l cap i cnt1 cur1 cnt2 cur2,
    PrefixSplitState l cap i cnt1 cur1 ->
    PrefixSplitState l cap i cnt2 cur2 ->
    cnt1 = cnt2 /\ cur1 = cur2.
Proof.
  intros l cap i cnt1 cur1 cnt2 cur2 Hleft.
  revert cnt2 cur2.
  induction Hleft; intros cnt2 cur2 Hright.
  - inversion Hright; subst.
    + split; reflexivity.
    + lia.
    + lia.
  - inversion Hright; subst.
    + lia.
    + assert (i0 = i) by lia.
      subst i0.
      clear Hleft.
      match goal with
      | Hprev : PrefixSplitState l cap i ?cnt_prev ?cur_prev |- _ =>
          destruct (IHHleft _ _ Hprev) as [Hcnt Hcur];
          subst cnt_prev cur_prev
      end.
      split; reflexivity.
    + assert (i0 = i) by lia.
      subst i0.
      clear Hleft.
      match goal with
      | Hprev : PrefixSplitState l cap i ?cnt_prev ?cur_prev |- _ =>
          destruct (IHHleft _ _ Hprev) as [Hcnt Hcur];
          subst cnt_prev cur_prev
      end.
      lia.
  - inversion Hright; subst.
    + lia.
    + assert (i0 = i) by lia.
      subst i0.
      clear Hleft.
      match goal with
      | Hprev : PrefixSplitState l cap i ?cnt_prev ?cur_prev |- _ =>
          destruct (IHHleft _ _ Hprev) as [Hcnt Hcur];
          subst cnt_prev cur_prev
      end.
      lia.
    + assert (i0 = i) by lia.
      subst i0.
      clear Hleft.
      match goal with
      | Hprev : PrefixSplitState l cap i ?cnt_prev ?cur_prev |- _ =>
          destruct (IHHleft _ _ Hprev) as [Hcnt Hcur];
          subst cnt_prev cur_prev
      end.
      split; reflexivity.
Qed.

(* Facts connecting the greedy splitter state with partition semantics. *)
Local Open Scope list_scope.

Lemma sum_snoc :
  forall l x, sum (l ++ x :: nil) = sum l + x.
Proof.
  intros.
  rewrite sum_app.
  simpl.
  lia.
Qed.

Lemma sublist_snoc_Znth :
  forall {A : Type} (d : A) (l : list A) i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A d l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single d i l) by lia.
  reflexivity.
Qed.

Lemma prefix_state_partition :
  forall l cap i cnt cur,
    PrefixSplitState l cap i cnt cur ->
    exists done curseg,
      sublist 0 i l = concat (done ++ curseg :: nil) /\
      Zlength done + 1 = cnt /\
      sum curseg = cur /\
      Forall
        (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
        done /\
      sum curseg <= cap /\
      (forall x, In x curseg -> 0 <= x) /\
      ((i = 0 /\ curseg = nil) \/ (0 < i /\ curseg <> nil)).
Proof.
  intros l cap i cnt cur Hstate.
  induction Hstate.
  - exists nil, nil.
    split.
    + unfold sublist. simpl. reflexivity.
    + split; [simpl; lia |].
      split; [reflexivity |].
      split; [constructor |].
      split; [simpl; lia |].
      split; [intros x [] |].
      left; split; reflexivity.
  - destruct IHHstate as
      [done [curseg [Hconcat [Hcnt [Hsum [Hdone [Hcur_le [Hcur_nonneg Hcur_shape]]]]]]]].
    assert (Hcurseg_nonempty : curseg <> nil).
    {
      destruct Hcur_shape as [[Hi0 Hnil] | [_ Hneq]]; [| exact Hneq].
      subst i curseg.
      simpl in Hsum.
      subst cur.
      lia.
    }
    exists (done ++ curseg :: nil), (Znth i l 0 :: nil).
    repeat split.
    + rewrite (sublist_snoc_Znth 0 l i) by lia.
      rewrite Hconcat.
      change (concat (done ++ [curseg]) ++ concat [[Znth i l 0]] =
        concat ((done ++ [curseg]) ++ [[Znth i l 0]])).
      rewrite <- concat_app.
      reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + simpl; lia.
    + rewrite Forall_app.
      split; [exact Hdone |].
      constructor; [| constructor].
      repeat split; try assumption.
    + simpl; lia.
    + intros x [Hx | []].
      subst x; lia.
    + right; split; [lia | discriminate].
  - destruct IHHstate as
      [done [curseg [Hconcat [Hcnt [Hsum [Hdone [Hcur_le [Hcur_nonneg Hcur_shape]]]]]]]].
    exists done, (curseg ++ Znth i l 0 :: nil).
    repeat split.
    + rewrite (sublist_snoc_Znth 0 l i) by lia.
      rewrite Hconcat.
      rewrite concat_app.
      simpl.
      rewrite concat_app.
      simpl.
      repeat rewrite app_nil_r.
      rewrite app_assoc.
      reflexivity.
    + exact Hcnt.
    + rewrite sum_snoc.
      lia.
    + exact Hdone.
    + rewrite sum_snoc.
      lia.
    + intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hin | [Hx | []]].
      * apply Hcur_nonneg; exact Hin.
      * subst x; lia.
    + right.
      split; [lia |].
      destruct curseg; simpl; discriminate.
Qed.

Lemma can_split_bounded_partition_at_most :
  forall l m cap,
    0 < Zlength l ->
    CanSplit l m cap ->
    exists parts,
      concat parts = l /\
      Zlength parts <= m /\
      Forall
        (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
        parts.
Proof.
  intros l m cap Hl_nonempty Hcan.
  unfold CanSplit in Hcan.
  destruct Hcan as [cnt [cur [Hstate Hcnt]]].
  pose proof (prefix_state_partition l cap (Zlength l) cnt cur Hstate) as
    [done [curseg [Hconcat [Hcnt_eq [Hsum [Hdone [Hcur_le [Hcur_nonneg Hshape]]]]]]]].
  assert (Hcurseg_nonempty : curseg <> nil).
  {
    destruct Hshape as [[Hi Hnil] | [_ Hneq]]; [| exact Hneq].
    rewrite Hi in Hl_nonempty.
    lia.
  }
  exists (done ++ curseg :: nil).
  split.
  - rewrite <- Hconcat.
    apply sublist_self.
    reflexivity.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + rewrite Forall_app.
      split; [exact Hdone |].
      constructor; [| constructor].
      repeat split; try assumption.
Qed.

Lemma max_segment_sum_exists :
  forall parts,
    parts <> nil ->
    exists max_sum, MaxSegmentSum parts max_sum.
Proof.
  induction parts as [| seg rest IH]; intros Hne.
  - contradiction Hne; reflexivity.
  - destruct rest as [| seg' rest'].
    + exists (sum seg).
      unfold MaxSegmentSum, max_value_of_subset, max_object_of_subset.
      exists seg.
      split.
      * split.
        -- left; reflexivity.
        -- intros b Hb.
           simpl in Hb.
           destruct Hb as [Hb | []]; subst; lia.
      * reflexivity.
    + assert (Hrest_ne : seg' :: rest' <> nil) by discriminate.
      destruct (IH Hrest_ne) as [max_rest Hmax_rest].
      unfold MaxSegmentSum, max_value_of_subset, max_object_of_subset in Hmax_rest.
      destruct Hmax_rest as [best [[Hbest_in Hbest_max] Hbest_sum]].
      destruct (Z_le_dec (sum seg) max_rest) as [Hseg_le | Hseg_gt].
      * exists max_rest.
        unfold MaxSegmentSum, max_value_of_subset, max_object_of_subset.
        exists best.
        split.
        -- split.
           ++ right; exact Hbest_in.
           ++ intros b Hb.
              simpl in Hb.
              destruct Hb as [Hb | Hb].
              ** subst b; lia.
              ** apply Hbest_max; exact Hb.
        -- exact Hbest_sum.
      * exists (sum seg).
        unfold MaxSegmentSum, max_value_of_subset, max_object_of_subset.
        exists seg.
        split.
        -- split.
           ++ left; reflexivity.
           ++ intros b Hb.
              simpl in Hb.
              destruct Hb as [Hb | Hb].
              ** subst b; lia.
              ** pose proof (Hbest_max b Hb).
                 lia.
        -- reflexivity.
Qed.

Lemma sum_nonnegative :
  forall seg,
    (forall x, In x seg -> 0 <= x) ->
    0 <= sum seg.
Proof.
  induction seg as [| x xs IH]; intros Hnonneg.
  - simpl; lia.
  - simpl.
    assert (0 <= x) by (apply Hnonneg; left; reflexivity).
    assert (0 <= sum xs).
    {
      apply IH.
      intros y Hy.
      apply Hnonneg.
      right; exact Hy.
    }
    lia.
Qed.

Lemma sublist_cons_tail :
  forall {A : Type} (d : A) (l : list A) i x xs,
    0 <= i ->
    i + 1 + Zlength xs <= Zlength l ->
    sublist i (i + 1 + Zlength xs) l = x :: xs ->
    Znth i l d = x /\
    sublist (i + 1) (i + 1 + Zlength xs) l = xs.
Proof.
  intros A d l i x xs Hi Hbound Hsub.
  pose proof (Zlength_nonneg xs) as Hxs_len.
  rewrite (sublist_split i (i + 1 + Zlength xs) (i + 1) l) in Hsub by lia.
  rewrite (sublist_single d i l) in Hsub by lia.
  simpl in Hsub.
  injection Hsub as Hhead Htail.
  split; assumption.
Qed.

Lemma prefix_state_cur_bounds :
  forall l cap i cnt cur,
    PrefixSplitState l cap i cnt cur ->
    0 <= cur <= cap.
Proof.
  intros l cap i cnt cur Hstate.
  pose proof (prefix_state_partition l cap i cnt cur Hstate) as
    [done [curseg [_ [_ [Hsum [_ [Hcur_le [Hcur_nonneg _]]]]]]]].
  subst cur.
  split.
  - apply sum_nonnegative.
    exact Hcur_nonneg.
  - exact Hcur_le.
Qed.

Lemma process_segment_no_new :
  forall l cap i cnt cur seg,
    PrefixSplitState l cap i cnt cur ->
    0 <= i ->
    i + Zlength seg <= Zlength l ->
    sublist i (i + Zlength seg) l = seg ->
    cur + sum seg <= cap ->
    (forall x, In x seg -> 0 <= x) ->
    exists cur',
      PrefixSplitState l cap (i + Zlength seg) cnt cur' /\
      cur' = cur + sum seg.
Proof.
  intros l cap i cnt cur seg.
  revert i cnt cur.
  induction seg as [| x xs IH]; intros i cnt cur Hstate Hi Hbound Hsub Hsum_le Hnonneg.
  - exists cur.
    rewrite Zlength_nil.
    simpl in Hsum_le.
    split.
    + replace (i + 0) with i by lia.
      exact Hstate.
    + simpl; lia.
  - rewrite Zlength_cons in Hbound.
    pose proof (Zlength_nonneg xs) as Hxs_len.
    assert (Htail_bound : i + 1 + Zlength xs <= Zlength l) by lia.
    replace (i + Zlength (x :: xs)) with (i + 1 + Zlength xs) in Hsub by
      (rewrite Zlength_cons; lia).
    destruct (sublist_cons_tail 0 l i x xs Hi Htail_bound Hsub) as [Hx Htail].
    change (sum (x :: xs)) with (x + sum xs) in Hsum_le.
    assert (Htail_nonneg_sum : 0 <= sum xs).
    {
      apply sum_nonnegative.
      intros z Hz.
      apply Hnonneg.
      right; exact Hz.
    }
    assert (Hcur_bounds : 0 <= cur <= cap) by
      (apply prefix_state_cur_bounds with (l := l) (i := i) (cnt := cnt); exact Hstate).
    assert (Hx_nonneg : 0 <= x) by (apply Hnonneg; left; reflexivity).
    assert (Hx_cap : x <= cap) by lia.
    assert (Hextend_sum : cur + x <= cap) by lia.
    assert (Hstep :
      PrefixSplitState l cap (i + 1) cnt (cur + Znth i l 0)).
    {
      eapply PrefixSplitState_extend.
      - lia.
      - rewrite Hx; lia.
      - rewrite Hx; lia.
      - exact Hstate.
    }
    rewrite Hx in Hstep.
    destruct (IH (i + 1) cnt (cur + x) Hstep) as [cur' [Hfinal Hcur']].
    + lia.
    + lia.
    + exact Htail.
    + lia.
    + intros z Hz.
      apply Hnonneg.
      right; exact Hz.
    + exists cur'.
      split.
      * replace (i + Zlength (x :: xs)) with (i + 1 + Zlength xs) by
          (rewrite Zlength_cons; lia).
        exact Hfinal.
      * rewrite Hcur'.
        change (sum (x :: xs)) with (x + sum xs).
        lia.
Qed.

Lemma process_segment_one_new :
  forall l cap i cnt cur seg,
    PrefixSplitState l cap i cnt cur ->
    0 <= i ->
    i + Zlength seg <= Zlength l ->
    sublist i (i + Zlength seg) l = seg ->
    sum seg <= cap ->
    (forall x, In x seg -> 0 <= x) ->
    exists cnt' cur',
      PrefixSplitState l cap (i + Zlength seg) cnt' cur' /\
      cnt' <= cnt + 1.
Proof.
  intros l cap i cnt cur seg.
  revert i cnt cur.
  induction seg as [| x xs IH]; intros i cnt cur Hstate Hi Hbound Hsub Hsum_le Hnonneg.
  - exists cnt, cur.
    rewrite Zlength_nil.
    split.
    + replace (i + 0) with i by lia.
      exact Hstate.
    + lia.
  - rewrite Zlength_cons in Hbound.
    pose proof (Zlength_nonneg xs) as Hxs_len.
    assert (Htail_bound : i + 1 + Zlength xs <= Zlength l) by lia.
    replace (i + Zlength (x :: xs)) with (i + 1 + Zlength xs) in Hsub by
      (rewrite Zlength_cons; lia).
    destruct (sublist_cons_tail 0 l i x xs Hi Htail_bound Hsub) as [Hx Htail].
    change (sum (x :: xs)) with (x + sum xs) in Hsum_le.
    assert (Htail_nonneg_sum : 0 <= sum xs).
    {
      apply sum_nonnegative.
      intros z Hz.
      apply Hnonneg.
      right; exact Hz.
    }
    assert (Hx_nonneg : 0 <= x) by (apply Hnonneg; left; reflexivity).
    assert (Hx_cap : x <= cap) by lia.
    destruct (Z_le_dec (cur + x) cap) as [Hfits | Hover].
    + assert (Hstep :
        PrefixSplitState l cap (i + 1) cnt (cur + Znth i l 0)).
      {
        eapply PrefixSplitState_extend.
        - lia.
        - rewrite Hx; lia.
        - rewrite Hx; lia.
        - exact Hstate.
      }
      rewrite Hx in Hstep.
      destruct (IH (i + 1) cnt (cur + x) Hstep) as [cnt' [cur' [Hfinal Hcnt]]].
      * lia.
      * lia.
      * exact Htail.
      * lia.
      * intros z Hz.
        apply Hnonneg.
        right; exact Hz.
      * exists cnt', cur'.
        split.
        -- replace (i + Zlength (x :: xs)) with (i + 1 + Zlength xs) by
             (rewrite Zlength_cons; lia).
           exact Hfinal.
        -- exact Hcnt.
    + assert (Hstep :
        PrefixSplitState l cap (i + 1) (cnt + 1) (Znth i l 0)).
      {
        eapply PrefixSplitState_new_segment.
        - lia.
        - rewrite Hx; lia.
        - rewrite Hx.
          apply Znot_le_gt.
          exact Hover.
        - exact Hstate.
      }
      rewrite Hx in Hstep.
      destruct (process_segment_no_new l cap (i + 1) (cnt + 1) x xs Hstep)
        as [cur' [Hfinal Hcur']].
      * lia.
      * lia.
      * exact Htail.
      * lia.
      * intros z Hz.
        apply Hnonneg.
        right; exact Hz.
      * exists (cnt + 1), cur'.
        split.
        -- replace (i + Zlength (x :: xs)) with (i + 1 + Zlength xs) by
             (rewrite Zlength_cons; lia).
           exact Hfinal.
        -- lia.
Qed.

Lemma app_eq_same_zlength :
  forall {A : Type} (a b c d : list A),
    a ++ b = c ++ d ->
    Zlength a = Zlength c ->
    a = c /\ b = d.
Proof.
  intros A a.
  induction a as [| x xs IH]; intros b c d Happ Hlen.
  - destruct c as [| y ys].
    + split; [reflexivity | exact Happ].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg ys).
      lia.
  - destruct c as [| y ys].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg xs).
      lia.
    + simpl in Happ.
      inversion Happ; subst.
      destruct (IH b ys d H1) as [Hxs Hb].
      * repeat rewrite Zlength_cons in Hlen.
        lia.
      * subst xs.
        split; [reflexivity | exact Hb].
Qed.

Lemma split_sublist_at_prefix :
  forall {A : Type} (d : A) (l prefix rest : list A) i,
    0 <= i ->
    i + Zlength (prefix ++ rest) <= Zlength l ->
    sublist i (i + Zlength (prefix ++ rest)) l = prefix ++ rest ->
    sublist i (i + Zlength prefix) l = prefix /\
    sublist (i + Zlength prefix) (i + Zlength (prefix ++ rest)) l = rest.
Proof.
  intros A d l prefix rest i Hi Hbound Hsub.
  pose proof (Zlength_nonneg prefix) as Hprefix_len.
  pose proof (Zlength_nonneg rest) as Hrest_len.
  rewrite Zlength_app in Hbound.
  rewrite (sublist_split i (i + Zlength (prefix ++ rest)) (i + Zlength prefix) l) in Hsub.
  - apply app_eq_same_zlength in Hsub.
    + exact Hsub.
    + rewrite Zlength_sublist by lia.
      lia.
  - lia.
  - rewrite Zlength_app.
    lia.
Qed.

Lemma process_parts_one_new_each :
  forall l cap i cnt cur parts,
    PrefixSplitState l cap i cnt cur ->
    0 <= i ->
    i + Zlength (concat parts) <= Zlength l ->
    sublist i (i + Zlength (concat parts)) l = concat parts ->
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    exists cnt' cur',
      PrefixSplitState l cap (i + Zlength (concat parts)) cnt' cur' /\
      cnt' <= cnt + Zlength parts.
Proof.
  intros l cap i cnt cur parts Hstate Hi Hbound Hsub Hgood.
  revert i cnt cur Hstate Hi Hbound Hsub.
  induction Hgood as [| seg rest Hseg Hrest IH]; intros i cnt cur Hstate Hi Hbound Hsub.
  - exists cnt, cur.
    simpl.
    rewrite Zlength_nil.
    split.
    + replace (i + 0) with i by lia.
      exact Hstate.
    + rewrite Zlength_nil.
      lia.
  - destruct Hseg as [_ [Hseg_sum Hseg_nonneg]].
    simpl concat in Hsub.
    simpl concat in Hbound.
    assert (Hsplit := split_sublist_at_prefix 0 l seg (concat rest) i Hi Hbound Hsub).
    destruct Hsplit as [Hseg_sub Hrest_sub].
    pose proof (Zlength_nonneg seg) as Hseg_len.
    pose proof (Zlength_nonneg (concat rest)) as Hrest_concat_len.
    assert (Hbound_app : i + Zlength seg + Zlength (concat rest) <= Zlength l).
    {
      rewrite Zlength_app in Hbound.
      lia.
    }
    destruct (process_segment_one_new l cap i cnt cur seg Hstate) as
      [cnt1 [cur1 [Hstate1 Hcnt1]]].
    + exact Hi.
    + lia.
    + exact Hseg_sub.
    + exact Hseg_sum.
    + exact Hseg_nonneg.
    + destruct (IH (i + Zlength seg) cnt1 cur1 Hstate1) as
        [cnt' [cur' [Hstate' Hcnt']]].
      * lia.
      * exact Hbound_app.
      * replace (i + Zlength seg + Zlength (concat rest)) with
          (i + Zlength (seg ++ concat rest)) by (rewrite Zlength_app; lia).
        exact Hrest_sub.
      * exists cnt', cur'.
        split.
        -- replace (i + Zlength (concat (seg :: rest))) with
             (i + Zlength seg + Zlength (concat rest)) by
             (simpl; rewrite Zlength_app; lia).
           exact Hstate'.
        -- rewrite Zlength_cons.
           lia.
Qed.

Lemma bounded_partition_to_can_split :
  forall l m cap parts,
    0 <= cap ->
    parts <> nil ->
    concat parts = l ->
    Zlength parts = m ->
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    CanSplit l m cap.
Proof.
  intros l m cap parts Hcap Hparts_ne Hconcat Hparts_len Hgood.
  destruct parts as [| first rest].
  - contradiction Hparts_ne; reflexivity.
  - simpl concat in Hconcat.
    inversion Hgood as [| ? ? Hfirst Hrest].
    destruct Hfirst as [_ [Hfirst_sum Hfirst_nonneg]].
    assert (Hwhole :
      sublist 0 (0 + Zlength (first ++ concat rest)) l = first ++ concat rest).
    {
      replace (0 + Zlength (first ++ concat rest)) with (Zlength l).
      - rewrite sublist_self by reflexivity.
        symmetry; exact Hconcat.
      - rewrite <- Hconcat.
        lia.
    }
    pose proof (split_sublist_at_prefix 0 l first (concat rest) 0 ltac:(lia)
      ltac:(rewrite <- Hconcat; lia) Hwhole) as [Hfirst_sub Hrest_sub].
    assert (Hzero : PrefixSplitState l cap 0 1 0) by (constructor; lia).
    pose proof (Zlength_nonneg first) as Hfirst_len.
    pose proof (Zlength_nonneg (concat rest)) as Hrest_concat_len.
    destruct (process_segment_no_new l cap 0 1 0 first Hzero) as
      [cur1 [Hstate1 Hcur1]].
    + lia.
    + rewrite <- Hconcat.
      rewrite Zlength_app.
      lia.
    + exact Hfirst_sub.
    + simpl.
      lia.
    + exact Hfirst_nonneg.
    + destruct (process_parts_one_new_each l cap (Zlength first) 1 cur1 rest Hstate1)
        as [cnt' [cur' [Hstate' Hcnt']]].
      * lia.
      * rewrite <- Hconcat.
        rewrite Zlength_app.
        lia.
      * replace (Zlength first + Zlength (concat rest)) with
          (0 + Zlength (first ++ concat rest)) by (rewrite Zlength_app; lia).
        exact Hrest_sub.
      * exact Hrest.
      * unfold CanSplit.
        exists cnt', cur'.
        split.
        -- replace (Zlength l) with (Zlength first + Zlength (concat rest)).
           ++ exact Hstate'.
           ++ rewrite <- Hconcat.
              rewrite Zlength_app.
              lia.
        -- rewrite Zlength_cons in Hparts_len.
           lia.
Qed.

Lemma in_list_nonnegative :
  forall l x,
    In x l ->
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    0 <= x.
Proof.
  induction l as [| a rest IH]; intros x Hin Hnonneg.
  - contradiction Hin.
  - simpl in Hin.
    destruct Hin as [Hx | Hin].
    + subst x.
      specialize (Hnonneg 0).
      rewrite Znth0_cons in Hnonneg.
      apply Hnonneg.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest).
      lia.
    + apply IH; [exact Hin |].
      intros i Hi.
      specialize (Hnonneg (i + 1)).
      rewrite Znth_cons in Hnonneg by lia.
      replace (i + 1 - 1) with i in Hnonneg by lia.
      apply Hnonneg.
      rewrite Zlength_cons.
      lia.
Qed.

Lemma partition_max_segments_good :
  forall l parts max_sum cap,
    concat parts = l ->
    Forall (fun seg => seg <> nil) parts ->
    MaxSegmentSum parts max_sum ->
    max_sum <= cap ->
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts.
Proof.
  intros l parts max_sum cap Hconcat Hnonnil Hmax Hmax_cap Hnonneg.
  unfold MaxSegmentSum, max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmax as [best [[Hbest_in Hbest_max] Hbest_sum]].
  apply Forall_forall.
  intros seg Hseg_in.
  split.
  - apply Forall_forall with (x := seg) in Hnonnil; [exact Hnonnil | exact Hseg_in].
  - split.
    + pose proof (Hbest_max seg Hseg_in) as Hseg_max.
      lia.
    + intros x Hx.
      eapply in_list_nonnegative.
      * rewrite <- Hconcat.
        apply in_concat.
        exists seg.
        split; [exact Hseg_in | exact Hx].
      * intros i Hi.
        rewrite Hconcat.
        apply Hnonneg.
        rewrite <- Hconcat.
        exact Hi.
Qed.

Lemma partition_max_to_can_split :
  forall l m max_sum cap,
    0 <= cap ->
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    PartitionMaxSegmentSum l m max_sum ->
    max_sum <= cap ->
    CanSplit l m cap.
Proof.
  intros l m max_sum cap Hcap Hnonneg Hpart Hmax_cap.
  unfold PartitionMaxSegmentSum in Hpart.
  destruct Hpart as [parts [Hsegment [Hlen Hmax]]].
  unfold SegmentPartition in Hsegment.
  destruct Hsegment as [Hparts_ne [Hconcat Hnonnil]].
  eapply bounded_partition_to_can_split; try eassumption.
  eapply partition_max_segments_good; eassumption.
Qed.

Lemma refine_partition_once :
  forall cap parts,
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    Zlength parts < Zlength (concat parts) ->
    exists parts',
      concat parts' = concat parts /\
      Zlength parts' = Zlength parts + 1 /\
      Forall
        (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
        parts'.
Proof.
  intros cap parts Hgood.
  induction Hgood as [| seg rest Hseg Hrest IH]; intros Hlen.
  - simpl in Hlen.
    repeat rewrite Zlength_nil in Hlen.
    lia.
  - destruct Hseg as [Hseg_ne [Hseg_sum Hseg_nonneg]].
    destruct seg as [| x xs].
    {
      contradiction Hseg_ne; reflexivity.
    }
    destruct xs as [| y ys].
    + assert (Zlength rest < Zlength (concat rest)).
      {
        rewrite Zlength_cons in Hlen.
        change (concat ((x :: nil) :: rest)) with ((x :: nil) ++ concat rest) in Hlen.
        rewrite Zlength_app in Hlen.
        rewrite Zlength_cons, Zlength_nil in Hlen.
        lia.
      }
      destruct (IH H) as [rest' [Hconcat [Hcount Hrest_good]]].
      exists ((x :: nil) :: rest').
      split.
      * simpl.
        rewrite Hconcat.
        reflexivity.
      * split.
        -- rewrite Zlength_cons, Hcount.
           rewrite Zlength_cons.
           lia.
        -- constructor; [| exact Hrest_good].
           repeat split.
           ++ discriminate.
           ++ simpl in Hseg_sum; exact Hseg_sum.
           ++ intros z [Hz | []].
              subst z.
              apply Hseg_nonneg.
              left; reflexivity.
    + exists ((x :: nil) :: (y :: ys) :: rest).
      split.
      * reflexivity.
      * split.
        -- repeat rewrite Zlength_cons.
           lia.
        -- constructor.
           ++ repeat split.
              ** discriminate.
              ** change (sum (x :: y :: ys)) with (x + sum (y :: ys)) in Hseg_sum.
                 pose proof (sum_nonnegative (y :: ys)) as Htail_nonneg.
                 assert (0 <= sum (y :: ys)).
                 {
                   apply Htail_nonneg.
                   intros z Hz.
                   apply Hseg_nonneg.
                   right; exact Hz.
                 }
                 assert (0 <= x) by (apply Hseg_nonneg; left; reflexivity).
                 change (sum (x :: nil)) with (x + 0).
                 lia.
              ** intros z [Hz | []].
                 subst z.
                 apply Hseg_nonneg.
                 left; reflexivity.
           ++ constructor; [| exact Hrest].
              repeat split.
              ** discriminate.
              ** change (sum (x :: y :: ys)) with (x + sum (y :: ys)) in Hseg_sum.
                 assert (0 <= x) by (apply Hseg_nonneg; left; reflexivity).
                 lia.
              ** intros z Hz.
                 apply Hseg_nonneg.
                 right; exact Hz.
Qed.

Lemma refine_partition_to_target_fuel :
  forall fuel cap parts target,
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    Zlength parts <= target <= Zlength (concat parts) ->
    target - Zlength parts <= Z.of_nat fuel ->
    exists parts',
      concat parts' = concat parts /\
      Zlength parts' = target /\
      Forall
        (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
        parts'.
Proof.
  induction fuel as [| fuel IH]; intros cap parts target Hgood Hrange Hfuel.
  - assert (target = Zlength parts) by lia.
    exists parts.
    split; [reflexivity |].
    split; [lia | exact Hgood].
  - destruct (Z.eq_dec target (Zlength parts)) as [Heq | Hneq].
    + exists parts.
      split; [reflexivity |].
      split; [lia | exact Hgood].
    + assert (Hlt_parts : Zlength parts < target) by lia.
      assert (Hlt_concat : Zlength parts < Zlength (concat parts)) by lia.
      destruct (refine_partition_once cap parts Hgood Hlt_concat) as
        [parts1 [Hconcat1 [Hlen1 Hgood1]]].
      destruct (IH cap parts1 target Hgood1) as [parts' [Hconcat' [Hlen' Hgood']]].
      * rewrite Hlen1.
        rewrite Hconcat1.
        lia.
      * rewrite Hlen1.
        lia.
      * exists parts'.
        split.
        -- rewrite Hconcat'.
           exact Hconcat1.
        -- split; assumption.
Qed.

Lemma refine_partition_to_target :
  forall cap parts target,
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    Zlength parts <= target <= Zlength (concat parts) ->
    exists parts',
      concat parts' = concat parts /\
      Zlength parts' = target /\
      Forall
        (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
        parts'.
Proof.
  intros cap parts target Hgood Hrange.
  eapply refine_partition_to_target_fuel with
    (fuel := Z.to_nat (target - Zlength parts)); try eassumption.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma max_segment_sum_bound :
  forall cap parts max_sum,
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    MaxSegmentSum parts max_sum ->
    max_sum <= cap.
Proof.
  intros cap parts max_sum Hgood Hmax.
  unfold MaxSegmentSum, max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmax as [seg [[Hseg_in _] Hsum]].
  change (In seg parts) in Hseg_in.
  apply Forall_forall with (x := seg) in Hgood; [| exact Hseg_in].
  destruct Hgood as [_ [Hseg_le _]].
  lia.
Qed.

Lemma good_segments_nonnil :
  forall cap parts,
    Forall
      (fun seg => seg <> nil /\ sum seg <= cap /\ forall x, In x seg -> 0 <= x)
      parts ->
    Forall (fun seg => seg <> nil) parts.
Proof.
  intros cap parts Hgood.
  induction Hgood as [| seg rest Hseg _ IH].
  - constructor.
  - constructor; [| exact IH].
    destruct Hseg as [Hne _].
    exact Hne.
Qed.

Lemma can_split_to_partition_max :
  forall l m cap,
    1 <= m ->
    m <= Zlength l ->
    0 < Zlength l ->
    CanSplit l m cap ->
    exists max_sum,
      PartitionMaxSegmentSum l m max_sum /\
      max_sum <= cap.
Proof.
  intros l m cap Hm_pos Hm_len Hl_nonempty Hcan.
  destruct (can_split_bounded_partition_at_most l m cap Hl_nonempty Hcan) as
    [parts [Hconcat [Hparts_le Hgood]]].
  destruct (refine_partition_to_target cap parts m Hgood) as
    [parts' [Hconcat' [Hlen' Hgood']]].
  - split.
    + exact Hparts_le.
    + rewrite Hconcat.
      exact Hm_len.
  - assert (Hparts'_ne : parts' <> nil).
    {
      intro Hnil.
      subst parts'.
      rewrite Zlength_nil in Hlen'.
      lia.
    }
    destruct (max_segment_sum_exists parts' Hparts'_ne) as [max_sum Hmax].
    exists max_sum.
    split.
    + unfold PartitionMaxSegmentSum.
      exists parts'.
      split.
      * unfold SegmentPartition.
        split; [exact Hparts'_ne |].
        split.
        -- rewrite Hconcat'.
           exact Hconcat.
        -- apply good_segments_nonnil with (cap := cap).
           exact Hgood'.
      * split; [exact Hlen' | exact Hmax].
    + eapply max_segment_sum_bound; eassumption.
Qed.

Lemma minmax_can_lower_bound:
  forall l m answer cap,
    1 <= m <= Zlength l ->
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    MinimizedMaxSegmentSum l m answer ->
    CanSplit l m cap ->
    answer <= cap.
Proof.
  intros l m answer cap Hm _ Hmin Hcan.
  destruct (can_split_to_partition_max l m cap) as
    [max_sum [Hpart Hmax_cap]]; try lia; try exact Hcan.
  pose proof (minimized_lower_bound _ _ _ _ Hmin Hpart).
  lia.
Qed.

Lemma minmax_cannot_upper_bound:
  forall l m answer cap,
    0 <= cap ->
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    MinimizedMaxSegmentSum l m answer ->
    CannotSplit l m cap ->
    cap < answer.
Proof.
  intros l m answer cap Hcap Hnonneg Hmin Hcannot.
  destruct (Z_lt_ge_dec cap answer) as [Hlt | Hge]; [exact Hlt |].
  assert (Hanswer_cap : answer <= cap) by lia.
  pose proof (minimized_partition_witness _ _ _ Hmin) as Hpart.
  pose proof (partition_max_to_can_split
    l m answer cap Hcap Hnonneg Hpart Hanswer_cap) as Hcan.
  exfalso.
  eapply can_split_cannot_contradiction; eassumption.
Qed.
