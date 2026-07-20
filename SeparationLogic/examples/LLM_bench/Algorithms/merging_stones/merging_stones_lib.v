Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StoneMassesBounded (stones : list Z) (n : Z) : Prop :=
  Zlength stones = n /\
  forall i, 0 <= i < n -> 1 <= Znth i stones 0 <= 1000.

Inductive StoneMergePlan (stones : list Z) : Z -> Z -> Z -> Prop :=
  | StoneMergePlan_single :
      forall left,
        0 <= left < Zlength stones ->
        StoneMergePlan stones left left 0
  | StoneMergePlan_join :
      forall left split right left_cost right_cost,
        0 <= left ->
        left <= split < right ->
        right < Zlength stones ->
        StoneMergePlan stones left split left_cost ->
        StoneMergePlan stones (split + 1) right right_cost ->
        StoneMergePlan stones left right
          (left_cost + right_cost + sum (sublist left (right + 1) stones)).

Definition StoneIntervalMin
    (stones : list Z) (left right answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost => StoneMergePlan stones left right cost)
    (fun cost => cost)
    answer.

Definition StoneMinimumCost
    (stones : list Z) (n answer : Z) : Prop :=
  Zlength stones = n /\ StoneIntervalMin stones 0 (n - 1) answer.

Definition StonePrefixProgress
    (stones prefix : list Z) (n done : Z) : Prop :=
  Zlength stones = n /\
  Zlength prefix = done + 1 /\
  0 <= done <= n /\
  forall k, 0 <= k <= done ->
    Znth k prefix 0 = sum (sublist 0 k stones).

Definition StonePrefixDone
    (stones prefix : list Z) (n : Z) : Prop :=
  StonePrefixProgress stones prefix n n.

Definition StoneTableShape (table : list (list Z)) (n : Z) : Prop :=
  Zlength table = n /\
  forall row, 0 <= row < n -> Zlength (Znth row table []) = n.

Definition StoneZeroRows
    (table : list (list Z)) (n row : Z) : Prop :=
  StoneTableShape table n /\
  0 <= row <= n /\
  forall r c, 0 <= r < row -> 0 <= c < n ->
    Znth c (Znth r table []) 0 = 0.

Definition StoneZeroProgress
    (table : list (list Z)) (n row col : Z) : Prop :=
  StoneTableShape table n /\
  0 <= row < n /\
  0 <= col <= n /\
  (forall r c, 0 <= r < row -> 0 <= c < n ->
     Znth c (Znth r table []) 0 = 0) /\
  (forall c, 0 <= c < col ->
     Znth c (Znth row table []) 0 = 0).

Definition StoneLenDone
    (stones : list Z) (table : list (list Z)) (n len : Z) : Prop :=
  Zlength stones = n /\
  StoneTableShape table n /\
  1 <= len /\
  forall l left right,
    1 <= l < len ->
    right = left + l - 1 ->
    0 <= left ->
    left + l <= n ->
    StoneIntervalMin stones left right
      (Znth right (Znth left table []) 0).

Definition StoneLeftProgress
    (stones : list Z) (table : list (list Z))
    (n len left : Z) : Prop :=
  StoneLenDone stones table n len /\
  2 <= len <= n /\
  0 <= left <= n - len + 1 /\
  forall done_left right,
    0 <= done_left < left ->
    right = done_left + len - 1 ->
    done_left + len <= n ->
    StoneIntervalMin stones done_left right
      (Znth right (Znth done_left table []) 0).

Definition StoneSplitCandidate
    (stones : list Z) (table : list (list Z))
    (left right split candidate : Z) : Prop :=
  left <= split < right /\
  right < Zlength stones /\
  candidate =
    Znth split (Znth left table []) 0 +
    Znth right (Znth (split + 1) table []) 0 +
    sum (sublist left (right + 1) stones).

Definition StoneSplitProgress
    (stones : list Z) (table : list (list Z))
    (n len left split best : Z) : Prop :=
  StoneLeftProgress stones table n len left /\
  let right := left + len - 1 in
  left <= split <= right /\
  0 <= best <= 1000000 /\
  ((split = left /\ best = 1000000) \/
   (left < split /\
    min_value_of_subset Z.le
      (fun candidate =>
         exists k,
           left <= k < split /\
           StoneSplitCandidate stones table left right k candidate)
      (fun candidate => candidate)
      best)).

Definition StoneUpdatedCell
    (stones : list Z) (old_table new_table : list (list Z))
    (left right value : Z) : Prop :=
  0 <= left < Zlength old_table /\
  0 <= right < Zlength (Znth left old_table []) /\
  new_table =
    replace_Znth left
      (replace_Znth right value (Znth left old_table []))
      old_table /\
  StoneIntervalMin stones left right value.

Lemma list_sum_bounds__arithmetic_safety :
  forall (l : list Z),
    (forall i, 0 <= i < Zlength l -> 1 <= Znth i l 0 <= 1000) ->
    Zlength l <= sum l <= Zlength l * 1000.
Proof.
  induction l as [| a l IH]; intros Hbound.
  - simpl. change (Zlength (@nil Z)) with 0. lia.
  - simpl.
    rewrite Zlength_cons.
    assert (Ha : 1 <= a <= 1000).
    {
      specialize (Hbound 0).
      rewrite Znth0_cons in Hbound.
      apply Hbound.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l); lia.
    }
    assert (Htail :
      forall i, 0 <= i < Zlength l -> 1 <= Znth i l 0 <= 1000).
    {
      intros i Hi.
      specialize (Hbound (i + 1)).
      rewrite Znth_cons in Hbound by lia.
      replace (i + 1 - 1) with i in Hbound by lia.
      apply Hbound.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l); lia.
    }
    specialize (IH Htail).
    nia.
Qed.
Lemma stone_interval_sum_bounds__arithmetic_safety :
  forall stones n left right,
    n <= 8 ->
    0 <= left ->
    left < right ->
    right < n ->
    StoneMassesBounded stones n ->
    2 <= sum (sublist left (right + 1) stones) <= 8000.
Proof.
  intros stones n left right Hn Hleft Hright Hrightn Hmasses.
  destruct Hmasses as [Hlength Hbound].
  assert (Hsub :
    forall i,
      0 <= i < Zlength (sublist left (right + 1) stones) ->
      1 <= Znth i (sublist left (right + 1) stones) 0 <= 1000).
  {
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hbound.
    lia.
  }
  pose proof
    (list_sum_bounds__arithmetic_safety
       (sublist left (right + 1) stones) Hsub) as Hsum.
  rewrite Zlength_sublist in Hsum by lia.
  nia.
Qed.
Lemma sum_lower_bound__prefix_math :
  forall l : list Z,
    (forall i, 0 <= i < Zlength l -> 1 <= Znth i l 0) ->
    Zlength l <= sum l.
Proof.
  induction l as [| x xs IH]; intros Hbound.
  - reflexivity.
  - assert (Hx : 1 <= x).
    {
      specialize (Hbound 0).
      rewrite Znth0_cons in Hbound.
      apply Hbound.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg xs).
      lia.
    }
    assert (Hxs : forall i, 0 <= i < Zlength xs -> 1 <= Znth i xs 0).
    {
      intros i Hi.
      specialize (Hbound (i + 1)).
      rewrite Znth_cons in Hbound by lia.
      replace (i + 1 - 1) with i in Hbound by lia.
      apply Hbound.
      rewrite Zlength_cons.
      lia.
    }
    specialize (IH Hxs).
    simpl.
    rewrite Zlength_cons.
    lia.
Qed.
Lemma StoneMassesBounded_Znth__prefix_math :
  forall stones n i,
    StoneMassesBounded stones n ->
    0 <= i < n ->
    1 <= Znth i stones 0 <= 1000.
Proof.
  intros stones n i [_ Hbound] Hi.
  apply Hbound; exact Hi.
Qed.
Lemma StoneMassesBounded_sublist_sum_bounds__prefix_math :
  forall stones n lo hi,
    StoneMassesBounded stones n ->
    0 <= lo <= hi ->
    hi <= n ->
    hi - lo <= sum (sublist lo hi stones) <= (hi - lo) * 1000.
Proof.
  intros stones n lo hi [Hlen Hbound] Hlo Hhi.
  assert (Hsub_lower : Zlength (sublist lo hi stones) <=
                         sum (sublist lo hi stones)).
  {
    apply sum_lower_bound__prefix_math.
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hbound.
    lia.
  }
  assert (Hsub_upper : 0 <= sum (sublist lo hi stones) <=
                         Z.of_nat (length (sublist lo hi stones)) * 1000).
  {
    apply sum_bound.
    intros i Hi.
    destruct (Z_lt_ge_dec i (hi - lo)) as [Hin | Hout].
    - rewrite Znth_sublist by lia.
      replace (i + lo) with (lo + i) by lia.
      pose proof (Hbound (lo + i) ltac:(lia)) as Hb.
      destruct Hb as [Hb_low Hb_high].
      split; [lia | exact Hb_high].
    - rewrite Znth_sublist_ge by lia.
      lia.
  }
  rewrite Zlength_sublist in Hsub_lower by lia.
  rewrite sublist_length in Hsub_upper by lia.
  rewrite Z2Nat.id in Hsub_upper by lia.
  lia.
Qed.
Lemma StonePrefixProgress_value_bounds__prefix_math :
  forall stones prefix n done k,
    StoneMassesBounded stones n ->
    n <= 8 ->
    StonePrefixProgress stones prefix n done ->
    0 <= k <= done ->
    0 <= Znth k prefix 0 <= 8000.
Proof.
  intros stones prefix n done k Hmass Hn
    [_ [_ [Hdone Hprefix]]] Hk.
  rewrite Hprefix by lia.
  pose proof
    (StoneMassesBounded_sublist_sum_bounds__prefix_math
       stones n 0 k Hmass ltac:(lia) ltac:(lia)) as Hsum.
  lia.
Qed.
Lemma StonePrefixProgress_extend__prefix_math :
  forall stones prefix n i,
    StonePrefixProgress stones prefix n i ->
    0 <= i < n ->
    StonePrefixProgress stones
      (prefix ++ [Znth i prefix 0 + Znth i stones 0]) n (i + 1).
Proof.
  intros stones prefix n i
    [Hstones [Hprefix_len [Hi Hprefix]]] Hi_lt.
  unfold StonePrefixProgress.
  split; [exact Hstones |].
  split.
  - rewrite Zlength_app, Hprefix_len, Zlength_cons, Zlength_nil.
    lia.
  - split; [lia |].
    intros k Hk.
    destruct (Z.eq_dec k (i + 1)) as [Hlast | Hbefore].
    + subst k.
      rewrite app_Znth2 by lia.
      replace (i + 1 - Zlength prefix) with 0 by lia.
      rewrite Znth0_cons.
      rewrite Hprefix by lia.
      rewrite (sublist_split 0 (i + 1) i stones) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i stones) by lia.
      simpl. lia.
    + assert (0 <= k < Zlength prefix) by lia.
      rewrite app_Znth1 by exact H.
      apply Hprefix.
      lia.
Qed.
Lemma StonePrefixDone_interval_sum__prefix_math :
  forall stones prefix n lo hi,
    StonePrefixDone stones prefix n ->
    0 <= lo <= hi ->
    hi <= n ->
    Znth hi prefix 0 - Znth lo prefix 0 =
      sum (sublist lo hi stones).
Proof.
  intros stones prefix n lo hi
    [Hstones [_ [_ Hprefix]]] Hlo Hhi.
  rewrite Hprefix by lia.
  rewrite Hprefix by lia.
  rewrite (sublist_split 0 hi lo stones) by lia.
  rewrite sum_app.
  lia.
Qed.
Lemma StonePrefixDone_interval_bounds__prefix_math :
  forall stones prefix n lo hi,
    StoneMassesBounded stones n ->
    StonePrefixDone stones prefix n ->
    0 <= lo <= hi ->
    hi <= n ->
    hi - lo <= Znth hi prefix 0 - Znth lo prefix 0 <=
      (hi - lo) * 1000.
Proof.
  intros stones prefix n lo hi Hmass Hprefix Hlo Hhi.
  rewrite (StonePrefixDone_interval_sum__prefix_math
             stones prefix n lo hi Hprefix Hlo Hhi).
  apply StoneMassesBounded_sublist_sum_bounds__prefix_math with (n := n);
    assumption.
Qed.
Lemma StoneSplitProgress_initial__prefix_math :
  forall stones table n len left,
    StoneLeftProgress stones table n len left ->
    2 <= len ->
    StoneSplitProgress stones table n len left left 1000000.
Proof.
  intros stones table n len left Hleft Hlen.
  unfold StoneSplitProgress.
  simpl.
  split; [exact Hleft |].
  split; [lia |].
  split; [lia |].
  left; split; reflexivity.
Qed.
Lemma StoneZeroProgress_store__zero_table :
  forall table n row col d,
    StoneZeroProgress table n row col ->
    col < n ->
    StoneZeroProgress
      (replace_Znth row
        (replace_Znth col 0 (Znth row table d)) table)
      n row (col + 1).
Proof.
  intros table n row col d Hprogress Hcol_lt.
  unfold StoneZeroProgress in Hprogress |- *.
  destruct Hprogress as
    [Hshape [Hrow [Hcol [Hzero_rows Hzero_current]]]].
  destruct Hshape as [Htable_len Hrow_len].
  assert (Hrow_default : Znth row table d = Znth row table []).
  { apply Znth_indep. rewrite Htable_len. exact Hrow. }
  assert (Hrow_len_d : Zlength (Znth row table d) = n).
  { rewrite Hrow_default. apply Hrow_len. exact Hrow. }
  split.
  - unfold StoneTableShape.
    split.
    + rewrite Zlength_replace_Znth. exact Htable_len.
    + intros r Hr.
      destruct (Z.eq_dec r row) as [Heq | Hneq].
      * subst r.
        rewrite Znth_replace_Znth_Same by
          (rewrite Htable_len; exact Hrow).
        rewrite Zlength_replace_Znth. exact Hrow_len_d.
      * rewrite Znth_replace_Znth_Diff by
          (try rewrite Htable_len; lia).
        apply Hrow_len. exact Hr.
  - split.
    + exact Hrow.
    + split.
      * lia.
      * split.
        -- intros r c Hr Hc.
           rewrite Znth_replace_Znth_Diff by
             (try rewrite Htable_len; lia).
           apply Hzero_rows; assumption.
        -- intros c Hc.
           rewrite Znth_replace_Znth_Same by
             (rewrite Htable_len; exact Hrow).
           destruct (Z.eq_dec c col) as [Heq | Hneq].
           ++ subst c.
              rewrite Znth_replace_Znth_Same by
                (rewrite Hrow_len_d; lia).
              reflexivity.
           ++ rewrite Znth_replace_Znth_Diff by
                (try rewrite Hrow_len_d; lia).
              rewrite Hrow_default.
              apply Hzero_current. lia.
Qed.
Lemma StoneIntervalMin_singleton__zero_table :
  forall stones left,
    0 <= left < Zlength stones ->
    StoneIntervalMin stones left left 0.
Proof.
  intros stones left Hleft.
  unfold StoneIntervalMin, min_value_of_subset, min_object_of_subset.
  exists 0.
  split.
  - split.
    + apply StoneMergePlan_single. exact Hleft.
    + intros cost Hplan.
      inversion Hplan; subst; lia.
  - reflexivity.
Qed.
Lemma StoneLenDone_two_of_zero__zero_table :
  forall stones table n,
    Zlength stones = n ->
    1 <= n ->
    StoneZeroRows table n n ->
    StoneLenDone stones table n 2.
Proof.
  intros stones table n Hstones_len Hn Hzero.
  unfold StoneZeroRows in Hzero.
  destruct Hzero as [Hshape [_ Hzero]].
  unfold StoneLenDone.
  split; [exact Hstones_len |].
  split; [exact Hshape |].
  split; [lia |].
  intros len left right Hlen Hright Hleft Hwithin.
  assert (len = 1) by lia.
  subst len.
  assert (right = left) by lia.
  subst right.
  assert (Hindex : 0 <= left < n) by lia.
  unfold StoneIntervalMin.
  replace (left + 1 - 1) with left by lia.
  rewrite (Hzero left left Hindex Hindex).
  apply StoneIntervalMin_singleton__zero_table.
  rewrite Hstones_len. exact Hindex.
Qed.
Lemma StoneIntervalSum_bounds__interval_min_core :
  forall stones n left right,
    StoneMassesBounded stones n ->
    n <= 8 ->
    0 <= left <= right ->
    right < n ->
    0 <= sum (sublist left (right + 1) stones) <= 8000.
Proof.
  intros stones n left right [Hlen Hmass] Hn Hlr Hright.
  pose proof (sum_bound 1000 (sublist left (right + 1) stones)) as Hsum.
  specialize (Hsum ltac:(
    intros i Hi;
    destruct (Z_lt_ge_dec i (Zlength (sublist left (right + 1) stones)))
      as [Hin | Hout];
    [ rewrite Zlength_sublist in Hin by lia;
      rewrite Znth_sublist by lia;
      specialize (Hmass (i + left) ltac:(lia));
      lia
    | unfold Znth;
      rewrite nth_overflow by (rewrite Zlength_correct in Hout; lia);
      lia ])).
  rewrite <- Zlength_correct in Hsum.
  rewrite Zlength_sublist in Hsum by lia.
  lia.
Qed.
Lemma StoneMergePlan_bounds__interval_min_core :
  forall stones left right cost,
    StoneMergePlan stones left right cost ->
    forall n,
      StoneMassesBounded stones n ->
      n <= 8 ->
      0 <= cost <= (right - left) * 8000.
Proof.
  intros stones left right cost Hplan.
  induction Hplan as
      [left Hleft
      |left split right left_cost right_cost Hleft Hsplit Hright
       Hleft_plan IHleft Hright_plan IHright];
    intros n Hbounded Hn.
  - lia.
  - pose proof (IHleft n Hbounded Hn) as Hleft_cost.
    pose proof (IHright n Hbounded Hn) as Hright_cost.
    destruct Hbounded as [Hlen Hmass].
    pose proof
      (StoneIntervalSum_bounds__interval_min_core
         stones n left right (conj Hlen Hmass) Hn ltac:(lia) ltac:(lia))
      as Hinterval.
    lia.
Qed.
Lemma StoneIntervalMin_precise_bounds__interval_min_core :
  forall stones n left right answer,
    StoneMassesBounded stones n ->
    n <= 8 ->
    0 <= left <= right ->
    right < n ->
    StoneIntervalMin stones left right answer ->
    0 <= answer <= (right - left) * 8000.
Proof.
  intros stones n left right answer Hbounded Hn Hlr Hright Hmin.
  unfold StoneIntervalMin, min_value_of_subset, min_object_of_subset in Hmin.
  destruct Hmin as [cost [[Hplan Hleast] Hanswer]].
  subst answer.
  pose proof
    (StoneMergePlan_bounds__interval_min_core
       stones left right cost Hplan n Hbounded Hn) as Hcost.
  exact Hcost.
Qed.
Lemma StoneIntervalMin_bounds__interval_min_core :
  forall stones n left right answer,
    StoneMassesBounded stones n ->
    n <= 8 ->
    0 <= left <= right ->
    right < n ->
    StoneIntervalMin stones left right answer ->
    0 <= answer <= 56000.
Proof.
  intros stones n left right answer Hbounded Hn Hlr Hright Hmin.
  pose proof
    (StoneIntervalMin_precise_bounds__interval_min_core
       stones n left right answer Hbounded Hn Hlr Hright Hmin) as Hbounds.
  lia.
Qed.
Lemma StoneLenDone_entry_bounds__interval_min_core :
  forall stones table n len left right,
    StoneMassesBounded stones n ->
    n <= 8 ->
    StoneLenDone stones table n len ->
    0 <= left <= right ->
    right < n ->
    right - left + 1 < len ->
    0 <= Znth right (Znth left table []) 0 <= 56000.
Proof.
  intros stones table n len left right Hbounded Hn Hdone Hlr Hright Hshort.
  destruct Hdone as [Hstones [Hshape [Hlen Hinterval]]].
  assert (Hmin :
    StoneIntervalMin stones left right
      (Znth right (Znth left table []) 0)).
  {
    apply (Hinterval (right - left + 1) left right); lia.
  }
  eapply StoneIntervalMin_bounds__interval_min_core; eauto.
Qed.
Lemma StoneLenDone_entry_precise_bounds__interval_min_core :
  forall stones table n len left right,
    StoneMassesBounded stones n ->
    n <= 8 ->
    StoneLenDone stones table n len ->
    0 <= left <= right ->
    right < n ->
    right - left + 1 < len ->
    0 <= Znth right (Znth left table []) 0 <= (right - left) * 8000.
Proof.
  intros stones table n len left right Hbounded Hn Hdone Hlr Hright Hshort.
  destruct Hdone as [Hstones [Hshape [Hlen Hinterval]]].
  assert (Hmin :
    StoneIntervalMin stones left right
      (Znth right (Znth left table []) 0)).
  {
    apply (Hinterval (right - left + 1) left right); lia.
  }
  eapply StoneIntervalMin_precise_bounds__interval_min_core; eauto.
Qed.
Lemma StoneSplitProgress_child_bounds__interval_min_core :
  forall stones table n len left split right best default_row,
    StoneMassesBounded stones n ->
    n <= 8 ->
    StoneSplitProgress stones table n len left split best ->
    right = left + len - 1 ->
    left <= split < right ->
    right < n ->
    (0 <= Znth split (Znth left table default_row) 0 <= 56000) /\
    (0 <= Znth right (Znth (split + 1) table default_row) 0 <= 56000).
Proof.
  intros stones table n len left split right best default_row
    Hbounded Hn Hprogress Hright Hsplit Hright_bound.
  unfold StoneSplitProgress in Hprogress.
  cbn in Hprogress.
  destruct Hprogress as [Hleft_progress Hrest].
  destruct Hleft_progress as [Hdone [Hlen [Hleft Hcompleted]]].
  pose proof Hdone as Hdone_shape.
  destruct Hdone_shape as [Hstones [Hshape [Hlen_done Hinterval]]].
  destruct Hshape as [Htable_len Hrows].
  split.
  - pose proof
      (StoneLenDone_entry_bounds__interval_min_core
         stones table n len left split
         Hbounded Hn Hdone ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
    rewrite
      (Znth_indep table left [] default_row ltac:(lia))
      in Hbounds.
    exact Hbounds.
  - pose proof
      (StoneLenDone_entry_bounds__interval_min_core
         stones table n len (split + 1) right
         Hbounded Hn Hdone ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds.
    rewrite
      (Znth_indep table (split + 1) [] default_row ltac:(lia))
      in Hbounds.
    exact Hbounds.
Qed.
Lemma StoneSplitProgress_candidate_facts__interval_min_core :
  forall stones table n len left split right best interval_sum default_row,
    StoneMassesBounded stones n ->
    n <= 8 ->
    StoneSplitProgress stones table n len left split best ->
    right = left + len - 1 ->
    left <= split < right ->
    right < n ->
    interval_sum = sum (sublist left (right + 1) stones) ->
    let candidate :=
      Znth split (Znth left table default_row) 0 +
      Znth right (Znth (split + 1) table default_row) 0 +
      interval_sum in
    (0 <= candidate <= 56000) /\
    StoneSplitCandidate stones table left right split candidate.
Proof.
  intros stones table n len left split right best interval_sum default_row
    Hbounded Hn Hprogress Hright Hsplit Hright_bound Hsum.
  cbn.
  unfold StoneSplitProgress in Hprogress.
  cbn in Hprogress.
  destruct Hprogress as [Hleft_progress Hrest].
  destruct Hleft_progress as [Hdone [Hlen [Hleft Hcompleted]]].
  pose proof Hdone as Hdone_shape.
  destruct Hdone_shape as [Hstones [Hshape [Hlen_done Hinterval]]].
  destruct Hshape as [Htable_len Hrows].
  pose proof
    (StoneLenDone_entry_precise_bounds__interval_min_core
       stones table n len left split
       Hbounded Hn Hdone ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft_bounds.
  pose proof
    (StoneLenDone_entry_precise_bounds__interval_min_core
       stones table n len (split + 1) right
       Hbounded Hn Hdone ltac:(lia) ltac:(lia) ltac:(lia)) as Hright_bounds.
  rewrite
    (Znth_indep table left [] default_row ltac:(lia))
    in Hleft_bounds.
  rewrite
    (Znth_indep table (split + 1) [] default_row ltac:(lia))
    in Hright_bounds.
  pose proof
    (StoneIntervalSum_bounds__interval_min_core
       stones n left right Hbounded Hn ltac:(lia) Hright_bound) as Hsum_bounds.
  split.
  - lia.
  - unfold StoneSplitCandidate.
    repeat split; try lia.
    rewrite
      <- (Znth_indep table left [] default_row ltac:(lia)),
      <- (Znth_indep table (split + 1) [] default_row ltac:(lia)).
    lia.
Qed.
Lemma StoneSplitProgress_table_shape__interval_min_core :
  forall stones table n len left split best,
    StoneSplitProgress stones table n len left split best ->
    StoneTableShape table n.
Proof.
  intros stones table n len left split best Hprogress.
  unfold StoneSplitProgress, StoneLeftProgress, StoneLenDone in Hprogress.
  cbn in Hprogress.
  tauto.
Qed.
Lemma StoneSplitProgress_complete__interval_min_core :
  forall stones table n len left right best,
    right = left + len - 1 ->
    left < right ->
    right < n ->
    StoneSplitProgress stones table n len left right best ->
    StoneIntervalMin stones left right best.
Proof.
  intros stones table n len left right best Hright Hleft_right Hright_n
    Hprogress.
  unfold StoneSplitProgress in Hprogress.
  cbn in Hprogress.
  destruct Hprogress as
    [Hleft_progress [Hsplit_bounds [Hbest_bounds Hstate]]].
  destruct Hleft_progress as
    [Hdone [Hlen_bounds [Hleft_bounds Hcompleted]]].
  destruct Hdone as [Hstones_len [Hshape [Hlen_lower Hinterval]]].
  destruct Hstate as [[Hinitial _] | [Hnoninitial Hcandidate_min]].
  - lia.
  - rewrite <- Hright in Hcandidate_min.
    unfold min_value_of_subset, min_object_of_subset in Hcandidate_min.
    destruct Hcandidate_min as [chosen Hchosen].
    destruct Hchosen as [Hchosen_object Hchosen_eq].
    destruct Hchosen_object as [Hchosen_set Hchosen_least].
    destruct Hchosen_set as [k [Hk Hchosen_candidate]].
    unfold StoneSplitCandidate in Hchosen_candidate.
    destruct Hchosen_candidate as
      [Hk_again [Hright_length Hchosen_formula]].
    assert (Hleft_min :
      StoneIntervalMin stones left k
        (Znth k (Znth left table []) 0)).
    {
      apply (Hinterval (k - left + 1) left k); lia.
    }
    assert (Hright_min :
      StoneIntervalMin stones (k + 1) right
        (Znth right (Znth (k + 1) table []) 0)).
    {
      apply (Hinterval (right - k) (k + 1) right); lia.
    }
    unfold StoneIntervalMin, min_value_of_subset, min_object_of_subset
      in Hleft_min, Hright_min.
    destruct Hleft_min as
      [left_answer [[Hleft_plan Hleft_least] Hleft_answer]].
    destruct Hright_min as
      [right_answer [[Hright_plan Hright_least] Hright_answer]].
    subst left_answer right_answer.
    unfold StoneIntervalMin, min_value_of_subset, min_object_of_subset.
    exists best.
    split.
    + split.
      * rewrite <- Hchosen_eq, Hchosen_formula.
        eapply StoneMergePlan_join; eauto; lia.
      * intros cost Hplan.
        inversion Hplan as
          [single_left Hsingle
          |join_left join_split join_right left_cost right_cost
           Hjoin_left Hjoin_split Hjoin_right Hleft_plan' Hright_plan'];
          subst.
        -- lia.
        -- assert (Hjoin_left_min :
             StoneIntervalMin stones left join_split
               (Znth join_split (Znth left table []) 0)).
           {
             apply (Hinterval (join_split - left + 1) left join_split);
               lia.
           }
           assert (Hjoin_right_min :
             StoneIntervalMin stones (join_split + 1) (left + len - 1)
               (Znth (left + len - 1)
                  (Znth (join_split + 1) table []) 0)).
           {
             apply
               (Hinterval ((left + len - 1) - join_split)
                  (join_split + 1) (left + len - 1));
               lia.
           }
           unfold StoneIntervalMin, min_value_of_subset,
             min_object_of_subset in Hjoin_left_min, Hjoin_right_min.
           destruct Hjoin_left_min as
             [left_min [[Hleft_min_plan Hleft_min_least] Hleft_min_eq]].
           destruct Hjoin_right_min as
             [right_min [[Hright_min_plan Hright_min_least] Hright_min_eq]].
           subst left_min right_min.
           specialize (Hleft_min_least left_cost Hleft_plan').
           specialize (Hright_min_least right_cost Hright_plan').
           set (candidate :=
             Znth join_split (Znth left table []) 0 +
             Znth (left + len - 1) (Znth (join_split + 1) table []) 0 +
             sum (sublist left (left + len - 1 + 1) stones)).
           assert (Hcandidate_set :
             exists split,
               left <= split < left + len - 1 /\
               StoneSplitCandidate stones table left (left + len - 1)
                 split candidate).
           {
             exists join_split.
             split; [lia |].
             unfold candidate, StoneSplitCandidate.
             repeat split; try lia.
           }
           specialize (Hchosen_least candidate Hcandidate_set).
           unfold candidate in Hchosen_least.
           lia.
    + reflexivity.
Qed.
Lemma StoneLenDone_final_facts__interval_min_core :
  forall stones table n len default_row,
    1 <= n ->
    n <= 8 ->
    StoneMassesBounded stones n ->
    len > n ->
    len <= n + 1 ->
    StoneLenDone stones table n len ->
    let answer := Znth (n - 1) (Znth 0 table default_row) 0 in
    StoneLenDone stones table n (n + 1) /\
    StoneMinimumCost stones n answer /\
    0 <= answer <= 56000.
Proof.
  intros stones table n len default_row Hn Hn_upper Hbounded
    Hlen_lower Hlen_upper Hdone.
  assert (Hlen : len = n + 1) by lia.
  subst len.
  cbn.
  pose proof Hdone as Hdone_parts.
  destruct Hdone_parts as
    [Hstones_len [Hshape [Hlen_done Hinterval]]].
  destruct Hshape as [Htable_len Hrow_lengths].
  assert (Hminimum :
    StoneIntervalMin stones 0 (n - 1)
      (Znth (n - 1) (Znth 0 table []) 0)).
  {
    apply (Hinterval n 0 (n - 1)); lia.
  }
  rewrite
    (Znth_indep table 0 [] default_row ltac:(lia))
    in Hminimum.
  pose proof
    (StoneIntervalMin_bounds__interval_min_core
       stones n 0 (n - 1)
       (Znth (n - 1) (Znth 0 table default_row) 0)
       Hbounded Hn_upper ltac:(lia) ltac:(lia) Hminimum) as Hbounds.
  destruct Hbounds as [Hanswer_low Hanswer_high].
  repeat split; try assumption.
Qed.
Lemma StoneSplitProgress_keep_best__split_loop_step :
  forall stones table n len left right split candidate best,
    right = left + len - 1 ->
    split < right ->
    candidate <= 56000 ->
    best <= candidate ->
    StoneSplitCandidate stones table left right split candidate ->
    StoneSplitProgress stones table n len left split best ->
    StoneSplitProgress stones table n len left (split + 1) best.
Proof.
  intros stones table n len left right split candidate best
    Hright Hsplit Hcandidate_bound Hbest_candidate Hcandidate Hprogress.
  unfold StoneSplitProgress in Hprogress |- *.
  cbn in Hprogress |- *.
  rewrite <- Hright in Hprogress |- *.
  destruct Hprogress as
    [Hleft_progress [[Hleft_split Hsplit_right]
      [[Hbest_nonneg Hbest_bound] Hminimum]]].
  split; [exact Hleft_progress |].
  split; [lia |].
  split; [lia |].
  right.
  split; [lia |].
  destruct Hminimum as
    [[Hsplit_left Hbest_default] | [Hleft_strict Hminimum]].
  - lia.
  - unfold min_value_of_subset in Hminimum |- *.
    destruct Hminimum as
      [old_best [[Hold_member Hold_least] Hold_value]].
    cbn in Hold_value.
    subst old_best.
    exists best.
    split.
    + unfold min_object_of_subset in *.
      split.
      * destruct Hold_member as [k [[Hleft_k Hk_split] Hk_candidate]].
        exists k.
        split; [lia | exact Hk_candidate].
      * intros value [k [[Hleft_k Hk_next] Hk_candidate]].
        assert (k < split \/ k = split) as [Hk_split | Hk_split] by lia.
        -- apply Hold_least.
           exists k.
           split; [lia | exact Hk_candidate].
        -- subst k.
           assert (candidate = value) as Hvalue.
           {
             unfold StoneSplitCandidate in Hcandidate, Hk_candidate.
             destruct Hcandidate as [_ [_ Hcandidate_value]].
             destruct Hk_candidate as [_ [_ Hk_value]].
             lia.
           }
           lia.
    + reflexivity.
Qed.
Lemma StoneSplitProgress_replace_best__split_loop_step :
  forall stones table n len left right split candidate best,
    right = left + len - 1 ->
    split < right ->
    0 <= candidate ->
    candidate <= 1000000 ->
    candidate < best ->
    StoneSplitCandidate stones table left right split candidate ->
    StoneSplitProgress stones table n len left split best ->
    StoneSplitProgress stones table n len left (split + 1) candidate.
Proof.
  intros stones table n len left right split candidate best
    Hright Hsplit Hcandidate_nonneg Hcandidate_bound Hcandidate_best
    Hcandidate Hprogress.
  unfold StoneSplitProgress in Hprogress |- *.
  cbn in Hprogress |- *.
  rewrite <- Hright in Hprogress |- *.
  destruct Hprogress as
    [Hleft_progress [[Hleft_split Hsplit_right]
      [[Hbest_nonneg Hbest_bound] Hminimum]]].
  split; [exact Hleft_progress |].
  split; [lia |].
  split; [lia |].
  right.
  split; [lia |].
  unfold min_value_of_subset.
  exists candidate.
  split.
  - unfold min_object_of_subset.
    split.
    + exists split.
      split; [lia | exact Hcandidate].
    + intros value [k [[Hleft_k Hk_next] Hk_candidate]].
      destruct Hminimum as
        [[Hsplit_left Hbest_default] | [Hleft_strict Hminimum]].
      * assert (k = split) by lia.
        subst k.
        unfold StoneSplitCandidate in Hcandidate, Hk_candidate.
        destruct Hcandidate as [_ [_ Hcandidate_value]].
        destruct Hk_candidate as [_ [_ Hk_value]].
        lia.
      * assert (k < split \/ k = split) as [Hk_split | Hk_split] by lia.
        -- unfold min_value_of_subset in Hminimum.
           destruct Hminimum as
             [old_best [[Hold_member Hold_least] Hold_value]].
           cbn in Hold_value.
           subst old_best.
           eapply Z.le_trans with (m := best); [lia |].
           apply Hold_least.
           exists k.
           split; [lia | exact Hk_candidate].
        -- subst k.
           unfold StoneSplitCandidate in Hcandidate, Hk_candidate.
           destruct Hcandidate as [_ [_ Hcandidate_value]].
           destruct Hk_candidate as [_ [_ Hk_value]].
           lia.
  - reflexivity.
Qed.
Lemma StoneLenDone_to_initial_left_progress__table_progress :
  forall stones table n len,
    StoneLenDone stones table n len ->
    2 <= len <= n ->
    StoneLeftProgress stones table n len 0.
Proof.
  intros stones table n len Hdone Hlen.
  unfold StoneLeftProgress.
  split; [exact Hdone |].
  split; [exact Hlen |].
  split; [lia |].
  intros done_left right Hdone_left. lia.
Qed.
Lemma StoneUpdatedCell_to_next_left_progress__table_progress :
  forall stones old_table new_table n len left right value,
    StoneLeftProgress stones old_table n len left ->
    right = left + len - 1 ->
    left + len <= n ->
    StoneUpdatedCell stones old_table new_table left right value ->
    StoneLeftProgress stones new_table n len (left + 1).
Proof.
  intros stones old_table new_table n len left right value
    Hprogress Hright Hfits Hupdated.
  unfold StoneUpdatedCell in Hupdated.
  destruct Hupdated as (Hleft_index & Hright_index & Hnew & Hminimum).
  subst new_table.
  unfold StoneLeftProgress in Hprogress |- *.
  destruct Hprogress as
    (Hdone & Hlen_bounds & Hleft_bounds & Hprevious).
  unfold StoneLenDone in Hdone.
  destruct Hdone as (Hstones_len & Hshape & Hlen_pos & Hshorter).
  unfold StoneTableShape in Hshape.
  destruct Hshape as (Htable_len & Hrow_len).
  split.
  - unfold StoneLenDone.
    split; [exact Hstones_len |].
    split.
    + unfold StoneTableShape.
      split.
      * rewrite Zlength_replace_Znth. exact Htable_len.
      * intros row Hrow.
        destruct (Z.eq_dec row left) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by exact Hleft_index.
           rewrite Zlength_replace_Znth.
           apply Hrow_len.
           rewrite Htable_len in Hleft_index. lia.
        -- rewrite Znth_replace_Znth_Diff by
               (try rewrite Htable_len; try lia; exact Hneq).
           apply Hrow_len. exact Hrow.
    + split; [exact Hlen_pos |].
      intros l done_left interval_right Hl Hinterval_right Hdone_left Hfit.
      destruct (Z.eq_dec done_left left) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by exact Hleft_index.
        assert (Hrow_old : Zlength (Znth left old_table []) = n).
        {
          apply Hrow_len.
          rewrite Htable_len in Hleft_index. lia.
        }
        rewrite Znth_replace_Znth_Diff by
            (rewrite ?Hrow_old; try lia).
        eapply Hshorter; eauto.
      * rewrite Znth_replace_Znth_Diff by
            (try rewrite Htable_len; try lia).
        eapply Hshorter; eauto.
  - split; [exact Hlen_bounds |].
    split; [lia |].
    intros done_left interval_right Hdone_left Hinterval_right Hfit.
    destruct (Z.eq_dec done_left left) as [Heq | Hneq].
    + subst done_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      assert (Heqright : interval_right = right) by lia.
      rewrite Heqright.
      rewrite Znth_replace_Znth_Same by exact Hright_index.
      exact Hminimum.
    + rewrite Znth_replace_Znth_Diff by
          (try rewrite Htable_len; try lia).
      eapply Hprevious; eauto; lia.
Qed.
Lemma StoneLeftProgress_to_next_len_done__table_progress :
  forall stones table n len left,
    StoneLeftProgress stones table n len left ->
    left + len > n ->
    StoneLenDone stones table n (len + 1).
Proof.
  intros stones table n len left Hprogress Hexhausted.
  unfold StoneLeftProgress in Hprogress.
  destruct Hprogress as
    (Hdone & Hlen_bounds & Hleft_bounds & Hcurrent).
  unfold StoneLenDone in Hdone |- *.
  destruct Hdone as (Hstones_len & Hshape & Hlen_pos & Hshorter).
  split; [exact Hstones_len |].
  split; [exact Hshape |].
  split; [lia |].
  intros l done_left right Hl Hright Hdone_left Hfits.
  destruct (Z_lt_ge_dec l len) as [Hlt | Hge].
  - eapply Hshorter; eauto; lia.
  - assert (l = len) by lia.
    subst l.
    eapply Hcurrent; eauto; lia.
Qed.
