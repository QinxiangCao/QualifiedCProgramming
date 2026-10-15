Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition SegmentMex (a : list Z) (l r w : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z =>
      0 <= candidate /\
      forall i, l <= i <= r -> Znth i a 0 <> candidate)
    (fun candidate => candidate) w.

Definition OneSnap (before after : list Z) : Prop :=
  exists l r w,
    0 <= l <= r /\ r < Zlength before /\
    SegmentMex before l r w /\
    Zlength after = Zlength before /\
    forall i, 0 <= i < Zlength before ->
      Znth i after 0 =
        if andb (l <=? i) (i <=? r) then w else Znth i before 0.

Definition SnapTrace (initial : list Z) (states : list (list Z)) : Prop :=
  0 < Zlength states /\
  Znth 0 states [] = initial /\
  (forall k, 0 <= k < Zlength states - 1 ->
     OneSnap (Znth k states []) (Znth (k + 1) states [])) /\
  Forall (fun x => x = 0) (Znth (Zlength states - 1) states []).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 100000 /\
  Forall (fun x => 0 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (SnapTrace a)
    (fun states => Zlength states - 1) out.

Definition NonzeroStartAt (a : list Z) (i : Z) : Prop :=
  0 <= i < Zlength a /\
  Znth i a 0 <> 0 /\
  (i = 0 \/ Znth (i - 1) a 0 = 0).

Definition PrefixRunCount (a : list Z) (upto runs : Z) : Prop :=
  exists starts : list Z,
    Zlength starts = runs /\
    NoDup starts /\
    forall i,
      In i starts <->
      0 <= i < upto /\ NonzeroStartAt a i.

Definition PrefixTailState (a : list Z) (upto inside : Z) : Prop :=
  (upto = 0 /\ inside = 0) \/
  (0 < upto <= Zlength a /\
   ((inside = 0 /\ Znth (upto - 1) a 0 = 0) \/
    (inside = 1 /\ Znth (upto - 1) a 0 <> 0))).

Definition ScanState (a : list Z) (upto runs inside : Z) : Prop :=
  PrefixRunCount a upto runs /\ PrefixTailState a upto inside.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Lemma scan_state_step_zero__scan_state_transitions :
  forall (a : list Z) i runs inside,
    0 <= i < Zlength a ->
    Znth i a 0 = 0 ->
    ScanState a i runs inside ->
    ScanState a (i + 1) runs 0.
Proof.
  intros a i runs inside Hi Hzero [Hcount Htail].
  split.
  - unfold PrefixRunCount in Hcount |- *.
    destruct Hcount as [starts [Hlen [Hnodup Hmem]]].
    exists starts.
    split; [exact Hlen |].
    split; [exact Hnodup |].
    intro j.
    specialize (Hmem j).
    rewrite Hmem.
    split.
    + intros [Hj Hstart].
      split; [lia | exact Hstart].
    + intros [[Hj0 Hjnext] Hstart].
      assert (j <> i).
      { intros ->. destruct Hstart as [_ [Hnz _]]. contradiction. }
      split; [lia | exact Hstart].
  - unfold PrefixTailState.
    right.
    split; [lia |].
    left.
    split; [reflexivity |].
    replace (i + 1 - 1) with i by lia.
    exact Hzero.
Qed.
Lemma scan_state_step_new_run__scan_state_transitions :
  forall (a : list Z) i runs,
    0 <= i < Zlength a ->
    Znth i a 0 <> 0 ->
    ScanState a i runs 0 ->
    ScanState a (i + 1) (runs + 1) 1.
Proof.
  intros a i runs Hi Hnonzero [Hcount Htail].
  unfold PrefixTailState in Htail.
  assert (Hfresh : NonzeroStartAt a i).
  {
    unfold NonzeroStartAt.
    split; [exact Hi |].
    split; [exact Hnonzero |].
    destruct Htail as [[Hi0 _] | [[Hipos _] Hinside]].
    - left. exact Hi0.
    - destruct Hinside as [[_ Hprevzero] | [Hcontra _]].
      + right. exact Hprevzero.
      + discriminate.
  }
  split.
  - unfold PrefixRunCount in Hcount |- *.
    destruct Hcount as [starts [Hlen [Hnodup Hmem]]].
    exists (starts ++ [i]).
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + split.
      * apply NoDup_app.
        repeat split; try assumption.
        -- constructor; [intro H; inversion H | constructor].
        -- intros j Hj [Hji | []].
           subst j.
           apply Hmem in Hj.
           lia.
      * intro j.
        rewrite in_app_iff.
        simpl.
        specialize (Hmem j).
        rewrite Hmem.
        split.
        -- intros [[Hj Hstart] | [Hji | Hfalse]].
           ++ split; [lia | exact Hstart].
           ++ subst j. split; [lia | exact Hfresh].
           ++ contradiction.
        -- intros [[Hj0 Hjnext] Hstart].
           destruct (Z.eq_dec j i) as [-> | Hji].
           ++ right. left. reflexivity.
           ++ left. split; [lia | exact Hstart].
  - unfold PrefixTailState.
    right.
    split; [lia |].
    right.
    split; [reflexivity |].
    replace (i + 1 - 1) with i by lia.
    exact Hnonzero.
Qed.
Lemma scan_state_step_inside_run__scan_state_transitions :
  forall (a : list Z) i runs inside,
    0 <= i < Zlength a ->
    0 <= inside <= 1 ->
    inside <> 0 ->
    Znth i a 0 <> 0 ->
    ScanState a i runs inside ->
    ScanState a (i + 1) runs inside.
Proof.
  intros a i runs inside Hi Hinside_bounds Hinside_nonzero Hnonzero
    [Hcount Htail].
  unfold PrefixTailState in Htail.
  assert (Hinside : inside = 1) by lia.
  assert (Hipos : 0 < i).
  {
    destruct Htail as [[_ Hzero] | [[Hipos _] _]]; [contradiction | lia].
  }
  assert (Hprev_nonzero : Znth (i - 1) a 0 <> 0).
  {
    destruct Htail as [[_ Hzero] | [[_ _] Htail]].
    - exfalso. apply Hinside_nonzero. exact Hzero.
    - destruct Htail as [[Hzero _] | [_ Hprev]];
        [contradiction | exact Hprev].
  }
  split.
  - unfold PrefixRunCount in Hcount |- *.
    destruct Hcount as [starts [Hlen [Hnodup Hmem]]].
    exists starts.
    split; [exact Hlen |].
    split; [exact Hnodup |].
    intro j.
    specialize (Hmem j).
    rewrite Hmem.
    split.
    + intros [Hj Hstart]. split; [lia | exact Hstart].
    + intros [[Hj0 Hjnext] Hstart].
      assert (j <> i).
      {
        intros ->.
        destruct Hstart as [_ [_ [Hi0 | Hprevzero]]]; lia.
      }
      split; [lia | exact Hstart].
  - unfold PrefixTailState.
    right.
    split; [lia |].
    right.
    split; [exact Hinside |].
    replace (i + 1 - 1) with i by lia.
    exact Hnonzero.
Qed.
Lemma Znth_repeat_exact__final_spec : forall (a d : Z) n i,
  0 <= i < Z.of_nat n ->
  Znth i (repeat a n) d = a.
Proof.
  intros a d n i Hi.
  apply Znth_repeat_lt.
  lia.
Qed.
Lemma Forall_zero_Znth__final_spec : forall (a : list Z) i,
  Forall (fun x => x = 0) a ->
  0 <= i < Zlength a ->
  Znth i a 0 = 0.
Proof.
  intros a i Hall Hi.
  unfold Znth.
  apply (proj1 (Forall_nth (fun x : Z => x = 0) a) Hall).
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma pointwise_zero_eq_repeat__final_spec : forall (a : list Z),
  (forall i, 0 <= i < Zlength a -> Znth i a 0 = 0) ->
  a = repeat 0 (length a).
Proof.
  intros a Hz.
  apply (proj2 (list_eq_ext a (repeat 0 (length a)) 0)).
  split.
  - rewrite !Zlength_correct. f_equal. symmetry. apply repeat_length.
  - intros i Hi.
    rewrite Hz by exact Hi.
    symmetry. apply Znth_repeat_exact__final_spec.
    rewrite Zlength_correct in Hi.
    exact Hi.
Qed.
Lemma Forall_zero_repeat__final_spec : forall n,
  Forall (fun x : Z => x = 0) (repeat 0 n).
Proof.
  induction n; simpl; constructor; auto.
Qed.
Lemma nonzero_has_start__final_spec : forall (a : list Z) i,
  0 <= i < Zlength a ->
  Znth i a 0 <> 0 ->
  exists s, 0 <= s <= i /\ NonzeroStartAt a s.
Proof.
  intros a i Hi Hnz.
  assert (Hi0 : 0 <= i) by lia.
  assert (Hex : exists n, 0 <= n <= i /\ Znth n a 0 <> 0).
  { exists i. split; [lia|exact Hnz]. }
  destruct (min_n_in_range (fun j => Znth j a 0 <> 0) i Hi0 Hex)
    as [s [Hsnz [[Hs0 Hsi] Hmin]]].
  exists s. split; [lia|].
  unfold NonzeroStartAt.
  repeat split; try lia; auto.
  destruct (Z.eq_dec s 0) as [->|Hsne].
  - auto.
  - right.
    destruct (Z.eq_dec (Znth (s - 1) a 0) 0) as [Hz|Hnzprev]; auto.
    exfalso.
    specialize (Hmin (s - 1) ltac:(lia) Hnzprev).
    lia.
Qed.
Lemma zero_then_nonzero_has_later_start__final_spec : forall (a : list Z) z j,
  0 <= z /\ z < j /\ j < Zlength a ->
  Znth z a 0 = 0 ->
  Znth j a 0 <> 0 ->
  exists s, z < s <= j /\ NonzeroStartAt a s.
Proof.
  intros a z j Hbounds Hz Hjnz.
  assert (HK : 0 <= j - z - 1) by lia.
  assert (Hex : exists n, 0 <= n <= j - z - 1 /\
      Znth (z + 1 + n) a 0 <> 0).
  { exists (j - z - 1). split; [lia|].
    replace (z + 1 + (j - z - 1)) with j by lia. exact Hjnz. }
  destruct (min_n_in_range
    (fun off => Znth (z + 1 + off) a 0 <> 0) (j - z - 1) HK Hex)
    as [off [Hoffnz [[Hoff0 Hoffhi] Hmin]]].
  exists (z + 1 + off). split; [lia|].
  unfold NonzeroStartAt.
  repeat split; try lia; auto.
  right.
  destruct (Z.eq_dec off 0) as [->|Hoffne].
  - replace (z + 1 + 0 - 1) with z by lia. exact Hz.
  - destruct (Z.eq_dec (Znth (z + 1 + off - 1) a 0) 0)
      as [Hprev|Hprevnz]; auto.
    exfalso.
    specialize (Hmin (off - 1) ltac:(lia)).
    replace (z + 1 + (off - 1)) with (z + 1 + off - 1) in Hmin by lia.
    specialize (Hmin Hprevnz).
    lia.
Qed.
Lemma segment_mex_zero__final_spec : forall a l r,
  0 <= l <= r ->
  (forall i, l <= i <= r -> Znth i a 0 <> 0) ->
  SegmentMex a l r 0.
Proof.
  intros a l r Hlr Hnz.
  unfold SegmentMex, min_value_of_subset, min_object_of_subset.
  exists 0. split; [split|]; simpl; auto.
  - split; [lia|exact Hnz].
  - intros b [Hb _]. lia.
Qed.
Lemma segment_mex_exists__final_spec : forall a l r,
  0 <= l <= r ->
  r < Zlength a ->
  (forall i, 0 <= i < Zlength a -> Znth i a 0 <= 1000000000) ->
  exists w, SegmentMex a l r w.
Proof.
  intros a l r Hlr Hr Hupper.
  set (Q := fun w : Z => forall i, l <= i <= r -> Znth i a 0 <> w).
  assert (HK : 0 <= 1000000001) by lia.
  assert (Hex : exists w, 0 <= w <= 1000000001 /\ Q w).
  { exists 1000000001. split; [lia|].
    intros i Hi Heq.
    specialize (Hupper i ltac:(lia)). lia. }
  destruct (min_n_in_range Q 1000000001 HK Hex)
    as [w [HQ [[Hw0 HwK] Hmin]]].
  exists w.
  unfold SegmentMex, min_value_of_subset, min_object_of_subset.
  exists w. split; [split|]; simpl; auto.
  - split; auto.
  - intros b [Hb HQb].
    destruct (Z_le_gt_dec b 1000000001).
    + apply Hmin; [lia|exact HQb].
    + lia.
Qed.
Lemma prefix_zero_all__final_spec : forall a n,
  PrefixRunCount a n 0 ->
  n = Zlength a ->
  forall i, 0 <= i < Zlength a -> Znth i a 0 = 0.
Proof.
  intros a n [starts [Hlen [Hnodup Hchar]]] -> i Hi.
  destruct starts as [|s starts].
  - destruct (Z.eq_dec (Znth i a 0) 0) as [Hz|Hnz].
    + exact Hz.
    + destruct (nonzero_has_start__final_spec a i Hi Hnz) as [t [_ Hstart]].
      assert (Htbound : 0 <= t < Zlength a).
      { unfold NonzeroStartAt in Hstart. tauto. }
      specialize (proj2 (Hchar t) (conj Htbound Hstart)) as Hin. contradiction.
  - rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg starts). lia.
Qed.
Lemma prefix_one_run_shape__final_spec : forall a n,
  0 < n ->
  n = Zlength a ->
  PrefixRunCount a n 1 ->
  exists s r,
    0 <= s <= r /\ r < Zlength a /\
    (forall i, s <= i <= r -> Znth i a 0 <> 0) /\
    (forall i, 0 <= i < Zlength a ->
       i < s \/ r < i -> Znth i a 0 = 0).
Proof.
  intros a n Hn Hna [starts [Hlen [Hnodup Hchar]]].
  destruct starts as [|s tail].
  { rewrite Zlength_nil in Hlen. lia. }
  destruct tail as [|t tail].
  2:{ rewrite !Zlength_cons in Hlen. pose proof (Zlength_nonneg tail). lia. }
  assert (Hsstart : NonzeroStartAt a s).
  { pose proof (proj1 (Hchar s) ltac:(simpl; auto)) as Hfacts. tauto. }
  destruct Hsstart as [[Hs0 Hsn] [Hsnz Hsprev]].
  assert (Hunique : forall x, NonzeroStartAt a x -> x = s).
  { intros x Hx.
    assert (Hxb : 0 <= x < Zlength a).
    { unfold NonzeroStartAt in Hx. tauto. }
    assert (Hin : In x [s]).
    { apply (proj2 (Hchar x)). split; [rewrite Hna; exact Hxb|exact Hx]. }
    simpl in Hin. destruct Hin as [Heq|[]]. symmetry. exact Heq. }
  assert (HK : 0 <= n - 1) by lia.
  assert (Hex : exists x, 0 <= x <= n - 1 /\ Znth x a 0 <> 0).
  { exists s. split; [rewrite Hna; lia|exact Hsnz]. }
  destruct (max_n_in_range (fun x => Znth x a 0 <> 0) (n - 1) HK Hex)
    as [r [Hrnz [[Hr0 Hrn] Hmax]]].
  assert (Hsr : s <= r).
  { apply Hmax; [rewrite Hna; lia|exact Hsnz]. }
  exists s, r.
  split; [lia|]. split; [rewrite <- Hna; lia|]. split.
  - intros i [Hsi Hir].
    destruct (Z.eq_dec (Znth i a 0) 0) as [Hz|Hnz]; auto.
    destruct (Z.eq_dec i r) as [->|Hirne]; [contradiction|].
    destruct (zero_then_nonzero_has_later_start__final_spec a i r)
      as [x [[Hix Hxr] Hxstart]]; try lia.
    rewrite (Hunique x Hxstart) in Hix. lia.
  - intros i Hi [His|Hri].
    + destruct (Z.eq_dec (Znth i a 0) 0) as [Hz|Hnz]; auto.
      destruct (nonzero_has_start__final_spec a i Hi Hnz)
        as [x [[Hx0 Hxi] Hxstart]].
      rewrite (Hunique x Hxstart) in Hxi. lia.
    + destruct (Z.eq_dec (Znth i a 0) 0) as [Hz|Hnz]; auto.
      specialize (Hmax i ltac:(rewrite Hna; lia) Hnz). lia.
Qed.
Lemma prefix_two_starts__final_spec : forall a n runs,
  2 <= runs ->
  n = Zlength a ->
  PrefixRunCount a n runs ->
  exists p q, p < q /\ NonzeroStartAt a p /\ NonzeroStartAt a q.
Proof.
  intros a n runs Hruns Hna [starts [Hlen [Hnodup Hchar]]].
  destruct starts as [|x starts].
  { rewrite Zlength_nil in Hlen. lia. }
  destruct starts as [|y starts].
  { rewrite Zlength_cons, Zlength_nil in Hlen. lia. }
  assert (Hx : NonzeroStartAt a x).
  { pose proof (proj1 (Hchar x) ltac:(simpl; auto)) as Hfacts. tauto. }
  assert (Hy : NonzeroStartAt a y).
  { pose proof (proj1 (Hchar y) ltac:(simpl; auto)) as Hfacts. tauto. }
  inversion Hnodup as [|? ? Hxnot Htailnodup]; subst.
  assert (Hxy : x <> y) by (intro; subst; apply Hxnot; simpl; auto).
  destruct (Z_lt_ge_dec x y) as [Hlt|Hge].
  - exists x, y. split; [exact Hlt|]. split; assumption.
  - exists y, x. split; [lia|]. split; assumption.
Qed.
Lemma zero_trace__final_spec : forall a,
  (forall i, 0 <= i < Zlength a -> Znth i a 0 = 0) ->
  SnapTrace a [a].
Proof.
  intros a Hz.
  assert (Ha : a = repeat 0 (length a)).
  { apply pointwise_zero_eq_repeat__final_spec. exact Hz. }
  unfold SnapTrace.
  split. { rewrite Zlength_cons, Zlength_nil. lia. }
  split. { apply Znth0_cons. }
  split.
  - intros k Hk. rewrite Zlength_cons, Zlength_nil in Hk. lia.
  - replace (Znth (Zlength [a] - 1) [a] []) with a.
    + rewrite Ha. apply Forall_zero_repeat__final_spec.
    + rewrite Zlength_cons, Zlength_nil. simpl. reflexivity.
Qed.
Lemma one_trace__final_spec : forall a s r,
  0 <= s <= r ->
  r < Zlength a ->
  (forall i, s <= i <= r -> Znth i a 0 <> 0) ->
  (forall i, 0 <= i < Zlength a ->
     i < s \/ r < i -> Znth i a 0 = 0) ->
  SnapTrace a [a; repeat 0 (length a)].
Proof.
  intros a s r Hsr Hr Hinside Houtside.
  assert (Hsnap : OneSnap a (repeat 0 (length a))).
  { unfold OneSnap. exists s, r, 0.
    split; [exact Hsr|]. split; [exact Hr|].
    split; [apply segment_mex_zero__final_spec; assumption|].
    split.
    - rewrite !Zlength_correct. f_equal. apply repeat_length.
    - intros i Hi.
      rewrite Znth_repeat_exact__final_spec by
        (rewrite Zlength_correct in Hi; exact Hi).
      destruct (andb (s <=? i) (i <=? r)) eqn:E; auto.
      apply andb_false_iff in E. destruct E as [E|E].
      + apply Z.leb_gt in E. symmetry. apply Houtside; auto.
      + apply Z.leb_gt in E. symmetry. apply Houtside; auto. }
  unfold SnapTrace.
  split. { repeat rewrite Zlength_cons. rewrite Zlength_nil. lia. }
  split. { apply Znth0_cons. }
  split.
  - intros k Hk. repeat rewrite Zlength_cons in Hk. rewrite Zlength_nil in Hk.
    assert (k = 0) by lia. subst.
    rewrite Znth0_cons. replace (0 + 1) with 1 by lia.
    rewrite Znth_cons by lia. rewrite Znth0_cons. exact Hsnap.
  - repeat rewrite Zlength_cons. rewrite Zlength_nil.
    replace (2 - 1) with 1 by lia. rewrite Znth_cons by lia. rewrite Znth0_cons.
    apply Forall_zero_repeat__final_spec.
Qed.
Lemma two_trace__final_spec : forall a p q,
  0 < Zlength a ->
  p < q ->
  NonzeroStartAt a p ->
  NonzeroStartAt a q ->
  (forall i, 0 <= i < Zlength a -> Znth i a 0 <= 1000000000) ->
  exists mid, SnapTrace a [a; mid; repeat 0 (length a)].
Proof.
  intros a p q Hlen Hpq Hp Hq Hupper.
  assert (Hwhole : 0 <= 0 <= Zlength a - 1) by lia.
  destruct (segment_mex_exists__final_spec a 0 (Zlength a - 1))
    as [w Hmex]; try lia; auto.
  assert (Hp0 : 0 <= p) by (unfold NonzeroStartAt in Hp; tauto).
  assert (Hsep : Znth (q - 1) a 0 = 0).
  { unfold NonzeroStartAt in Hq. destruct Hq as [_ [_ [Hq0|Hqprev]]]; [lia|exact Hqprev]. }
  assert (Hw : w <> 0).
  { unfold SegmentMex, min_value_of_subset, min_object_of_subset in Hmex.
    destruct Hmex as [x [[[Hx0 Hmissing] Hleast] Hxw]].
    simpl in Hxw. subst x.
    specialize (Hmissing (q - 1) ltac:(unfold NonzeroStartAt in Hq; lia)).
    intro. subst w. contradiction. }
  set (mid := repeat w (length a)).
  assert (Hsnap1 : OneSnap a mid).
  { unfold OneSnap. exists 0, (Zlength a - 1), w.
    split; [exact Hwhole|]. split; [lia|]. split; [exact Hmex|]. split.
    - unfold mid. rewrite !Zlength_correct. f_equal. apply repeat_length.
    - intros i Hi. unfold mid.
      rewrite Znth_repeat_exact__final_spec by
        (rewrite Zlength_correct in Hi; exact Hi).
      assert (E : andb (0 <=? i) (i <=? Zlength a - 1) = true).
      { apply andb_true_iff. split; apply Z.leb_le; lia. }
      rewrite E. reflexivity. }
  assert (Hsnap2 : OneSnap mid (repeat 0 (length a))).
  { unfold OneSnap. exists 0, (Zlength a - 1), 0.
    split; [exact Hwhole|].
    assert (Hmidlen : Zlength mid = Zlength a).
    { unfold mid. rewrite !Zlength_correct. f_equal. apply repeat_length. }
    split; [rewrite Hmidlen; lia|]. split.
    - apply segment_mex_zero__final_spec; [exact Hwhole|].
      intros i Hi. unfold mid.
      rewrite Znth_repeat_exact__final_spec; [exact Hw|].
      rewrite <- Zlength_correct. lia.
    - split.
      + rewrite Hmidlen. rewrite !Zlength_correct. f_equal. apply repeat_length.
      + intros i Hi. rewrite Hmidlen in Hi. unfold mid.
        rewrite !Znth_repeat_exact__final_spec by
          (rewrite Zlength_correct in Hi; exact Hi).
        assert (E : andb (0 <=? i) (i <=? Zlength a - 1) = true).
        { apply andb_true_iff. split; apply Z.leb_le; lia. }
        rewrite E. reflexivity. }
  exists mid. unfold SnapTrace.
  split. { repeat rewrite Zlength_cons. rewrite Zlength_nil. lia. }
  split. { apply Znth0_cons. }
  split.
  - intros k Hk.
    repeat rewrite Zlength_cons in Hk. rewrite Zlength_nil in Hk.
    destruct (Z.eq_dec k 0) as [->|Hk0]; [exact Hsnap1|].
    assert (k = 1) by lia. subst.
    repeat rewrite Znth_cons by lia. rewrite !Znth0_cons. exact Hsnap2.
  - repeat rewrite Zlength_cons. rewrite Zlength_nil.
    replace (3 - 1) with 2 by lia. repeat rewrite Znth_cons by lia. rewrite Znth0_cons.
    apply Forall_zero_repeat__final_spec.
Qed.
Lemma trace_cost_ge_one__final_spec : forall a s states,
  NonzeroStartAt a s ->
  SnapTrace a states ->
  1 <= Zlength states - 1.
Proof.
  intros a s states Hs Htrace.
  destruct Htrace as [Hpos [Hinit [Hsteps Hfinal]]].
  destruct states as [|x tail].
  { rewrite Zlength_nil in Hpos. lia. }
  destruct tail as [|y tail].
  - rewrite Znth0_cons in Hinit. subst x.
    rewrite Zlength_cons, Zlength_nil in Hfinal. simpl in Hfinal.
    unfold NonzeroStartAt in Hs.
    destruct Hs as [Hsb [Hsnz _]].
    pose proof (Forall_zero_Znth__final_spec a s Hfinal Hsb). contradiction.
  - rewrite !Zlength_cons. pose proof (Zlength_nonneg tail). lia.
Qed.
Lemma onesnap_two_starts_impossible__final_spec : forall a after p q,
  p < q ->
  NonzeroStartAt a p ->
  NonzeroStartAt a q ->
  OneSnap a after ->
  Forall (fun x => x = 0) after ->
  False.
Proof.
  intros a after p q Hpq Hp Hq Hsnap Hzero.
  destruct Hsnap as [l [r [w [Hlr [Hr [Hmex [Halen Heq]]]]]]].
  assert (Hpb : 0 <= p < Zlength a) by (unfold NonzeroStartAt in Hp; tauto).
  assert (Hqb : 0 <= q < Zlength a) by (unfold NonzeroStartAt in Hq; tauto).
  assert (Hpa : Znth p after 0 = 0).
  { apply Forall_zero_Znth__final_spec; [exact Hzero|rewrite Halen; exact Hpb]. }
  assert (Hqa : Znth q after 0 = 0).
  { apply Forall_zero_Znth__final_spec; [exact Hzero|rewrite Halen; exact Hqb]. }
  specialize (Heq p Hpb) as Hep.
  destruct (andb (l <=? p) (p <=? r)) eqn:Ep.
  2:{ rewrite Hpa in Hep.
      unfold NonzeroStartAt in Hp. destruct Hp as [_ [Hpnz _]].
      apply Hpnz. symmetry. exact Hep. }
  assert (Hw0 : w = 0) by (rewrite Hpa in Hep; exact (eq_sym Hep)).
  apply andb_true_iff in Ep. destruct Ep as [Elp Epr].
  apply Z.leb_le in Elp. apply Z.leb_le in Epr.
  specialize (Heq q Hqb) as Heq'.
  destruct (andb (l <=? q) (q <=? r)) eqn:Eq.
  2:{ rewrite Hqa in Heq'.
      unfold NonzeroStartAt in Hq. destruct Hq as [_ [Hqnz _]].
      apply Hqnz. symmetry. exact Heq'. }
  apply andb_true_iff in Eq. destruct Eq as [Elq Eqr].
  apply Z.leb_le in Elq. apply Z.leb_le in Eqr.
  unfold SegmentMex, min_value_of_subset, min_object_of_subset in Hmex.
  destruct Hmex as [x [[[Hx0 Hmissing] Hleast] Hxw]].
  simpl in Hxw. subst x. rewrite Hw0 in Hmissing.
  assert (Hprev : Znth (q - 1) a 0 = 0).
  { unfold NonzeroStartAt in Hq. destruct Hq as [_ [_ [Hq0|Hqprev]]]; [lia|exact Hqprev]. }
  specialize (Hmissing (q - 1) ltac:(lia)). contradiction.
Qed.
Lemma trace_cost_ge_two__final_spec : forall a p q states,
  p < q ->
  NonzeroStartAt a p ->
  NonzeroStartAt a q ->
  SnapTrace a states ->
  2 <= Zlength states - 1.
Proof.
  intros a p q states Hpq Hp Hq Htrace.
  pose proof (trace_cost_ge_one__final_spec a p states Hp Htrace) as Hone.
  destruct Htrace as [Hpos [Hinit [Hsteps Hfinal]]].
  destruct states as [|x tail].
  { rewrite Zlength_nil in Hpos. lia. }
  destruct tail as [|y tail].
  { rewrite Zlength_cons, Zlength_nil in Hone. lia. }
  destruct tail as [|z tail].
  - rewrite Znth0_cons in Hinit. subst x.
    specialize (Hsteps 0 ltac:(repeat rewrite Zlength_cons; rewrite Zlength_nil; lia)).
    rewrite Znth0_cons in Hsteps. replace (0 + 1) with 1 in Hsteps by lia.
    rewrite Znth_cons in Hsteps by lia. rewrite Znth0_cons in Hsteps.
    repeat rewrite Zlength_cons in Hfinal. rewrite Zlength_nil in Hfinal.
    replace (2 - 1) with 1 in Hfinal by lia.
    rewrite Znth_cons in Hfinal by lia. rewrite Znth0_cons in Hfinal.
    exfalso.
    exact (onesnap_two_starts_impossible__final_spec
      a y p q Hpq Hp Hq Hsteps Hfinal).
  - rewrite !Zlength_cons. pose proof (Zlength_nonneg tail). lia.
Qed.
Lemma scan_state_complete_spec__final_spec : forall a runs inside,
  0 < Zlength a ->
  (forall i, 0 <= i < Zlength a -> Znth i a 0 <= 1000000000) ->
  ScanState a (Zlength a) runs inside ->
  Spec a (Z.min runs 2).
Proof.
  intros a runs inside Hlen Hupper [Hcount Htail].
  assert (Hruns0 : 0 <= runs).
  { destruct Hcount as [starts [Hstarts _]].
    rewrite <- Hstarts. apply Zlength_nonneg. }
  unfold Spec, min_value_of_subset, min_object_of_subset.
  destruct (Z.eq_dec runs 0) as [Hr0|Hr0].
  - subst runs. rewrite Z.min_l by lia.
    assert (Hz : forall i, 0 <= i < Zlength a -> Znth i a 0 = 0).
    { eapply prefix_zero_all__final_spec; eauto. }
    exists [a]. split; [split|].
    + apply zero_trace__final_spec. exact Hz.
    + intros states Htrace. rewrite Zlength_cons, Zlength_nil.
      unfold SnapTrace in Htrace.
      destruct Htrace as [Hpos _]. lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (Z.eq_dec runs 1) as [Hr1|Hr1].
    + subst runs. rewrite Z.min_l by lia.
      destruct (prefix_one_run_shape__final_spec a (Zlength a))
        as [s [r [Hsr [Hr [Hinside Houtside]]]]]; auto.
      assert (Hsb : 0 <= s < Zlength a) by lia.
      assert (Hsnz : Znth s a 0 <> 0) by (apply Hinside; lia).
      destruct (nonzero_has_start__final_spec a s Hsb Hsnz)
        as [t [_ Htstart]].
      exists [a; repeat 0 (length a)]. split; [split|].
      * apply one_trace__final_spec with (s := s) (r := r); assumption.
      * intros states Htrace.
        apply trace_cost_ge_one__final_spec with (a := a) (s := t); assumption.
      * repeat rewrite Zlength_cons. rewrite Zlength_nil. lia.
    + assert (Hr2 : 2 <= runs) by lia.
      rewrite Z.min_r by lia.
      destruct (prefix_two_starts__final_spec a (Zlength a) runs Hr2 eq_refl Hcount)
        as [p [q [Hpq [Hp Hq]]]].
      destruct (two_trace__final_spec a p q Hlen Hpq Hp Hq Hupper)
        as [mid Htrace].
      exists [a; mid; repeat 0 (length a)]. split; [split|].
      * exact Htrace.
      * intros states Hstates.
        apply trace_cost_ge_two__final_spec with (a := a) (p := p) (q := q);
          assumption.
      * repeat rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.
