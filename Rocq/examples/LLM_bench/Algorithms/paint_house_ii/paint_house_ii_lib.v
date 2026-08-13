Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.
From SumLib Require Import Sum ZRange FiniteExtra.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition PaintHouseIIInf : Z := 1000000000.

Definition PaintCostAt (costs : list (list Z)) (row color : Z) : Z :=
  Znth color (Znth row costs nil) 0.

Definition PaintHouseIIValidColoring (k n : Z) (colors : list Z) : Prop :=
  Zlength colors = n /\
  (forall i, 0 <= i < n -> 0 <= Znth i colors (-1) < k) /\
  (forall i, 0 <= i < n - 1 ->
     Znth i colors (-1) <> Znth (i + 1) colors (-1)).

Definition PaintHouseIIColoringCost
    (costs : list (list Z)) (n : Z) (colors : list Z) : Z :=
  sum
    (fun i : Z => 0 <= i < n)
    (fun i : Z => PaintCostAt costs i (Znth i colors (-1))).

Definition PaintHouseIIPrefixLastColor
    (row : Z) (colors : list Z) (color : Z) : Prop :=
  (row = 0 /\ color = -1) \/
  (1 <= row /\ color = Znth (row - 1) colors (-1)).

Definition PaintHouseIIValidPrefixColoring
    (k row : Z) (colors : list Z) : Prop :=
  Zlength colors = row /\
  0 <= row /\
  (forall i, 0 <= i < row -> 0 <= Znth i colors (-1) < k) /\
  (forall i, 0 <= i < row - 1 ->
     Znth i colors (-1) <> Znth (i + 1) colors (-1)).

Inductive PaintHouseIIPrefixCost
    (costs : list (list Z)) (n k : Z) : Z -> Z -> Z -> Prop :=
| PaintHouseIIPrefixCost_nil :
    0 <= n ->
    PaintHouseIIPrefixCost costs n k 0 (-1) 0
| PaintHouseIIPrefixCost_cons :
    forall row prev_color prev_value color value,
      0 <= row < n ->
      0 <= color < k ->
      prev_color <> color ->
      PaintHouseIIPrefixCost costs n k row prev_color prev_value ->
      value = prev_value + PaintCostAt costs row color ->
      PaintHouseIIPrefixCost costs n k (row + 1) color value.

Definition PaintHouseIIBestColor
    (costs : list (list Z)) (n k row color value : Z) : Prop :=
  PaintHouseIIPrefixCost costs n k row color value /\
  min_value_of_subset Z.le
    (fun p : Z * Z =>
       PaintHouseIIPrefixCost costs n k row (fst p) (snd p))
    (fun p : Z * Z => snd p)
    value.

Definition PaintHouseIISecondBestForColor
    (costs : list (list Z)) (n k row color value : Z) : Prop :=
  (row = 0 /\ color = -1 /\ value = 0) \/
  (1 <= row <= n /\
   min_value_of_subset Z.le
     (fun p : Z * Z =>
        fst p <> color /\
        PaintHouseIIPrefixCost costs n k row (fst p) (snd p))
     (fun p : Z * Z => snd p)
     value).

Definition PaintHouseIIDPState
    (costs : list (list Z)) (n k row min1 min2 min1_color : Z) : Prop :=
  (row = 0 /\ min1 = 0 /\ min2 = 0 /\ min1_color = -1) \/
  (1 <= row <= n /\
   0 <= min1_color < k /\
   PaintHouseIIBestColor costs n k row min1_color min1 /\
   PaintHouseIISecondBestForColor costs n k row min1_color min2).

Definition PaintHouseIIPrevCost
    (costs : list (list Z)) (k row old_min1 old_min2 old_color color : Z) : Z :=
  PaintCostAt costs row color +
  if Z.eq_dec color old_color then old_min2 else old_min1.

Definition PaintHouseIIPrevSelection
    (old_min1 old_min2 old_color color prev : Z) : Prop :=
  prev = if Z.eq_dec color old_color then old_min2 else old_min1.

Definition PaintHouseIIProcessedCandidate
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color
       processed color value : Z) : Prop :=
  0 <= color < processed /\
  PaintHouseIIPrefixCost costs n k (row + 1) color value.

Definition PaintHouseIIProcessedBestColor
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color processed color value : Z)
    : Prop :=
  PaintHouseIIProcessedCandidate
    costs n k row old_min1 old_min2 old_color processed color value /\
  min_value_of_subset Z.le
    (fun p : Z * Z =>
       PaintHouseIIProcessedCandidate
         costs n k row old_min1 old_min2 old_color processed (fst p) (snd p))
    (fun p : Z * Z => snd p)
    value.

Definition PaintHouseIIProcessedSecondBest
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color processed color value : Z)
    : Prop :=
  min_value_of_subset Z.le
    (fun p : Z * Z =>
       fst p <> color /\
       PaintHouseIIProcessedCandidate
         costs n k row old_min1 old_min2 old_color processed (fst p) (snd p))
    (fun p : Z * Z => snd p)
    value.

Definition PaintHouseIIInnerState
    (costs : list (list Z)) (n k row processed old_min1 old_min2 old_color
       new_min1 new_min2 new_color : Z) : Prop :=
  0 <= row < n /\
  0 <= processed <= k /\
  PaintHouseIIDPState costs n k row old_min1 old_min2 old_color /\
  ((processed = 0 /\
    new_min1 = PaintHouseIIInf /\
    new_min2 = PaintHouseIIInf /\
    new_color = -1) \/
   (1 <= processed <= k /\
    0 <= new_color < processed /\
    PaintHouseIIProcessedBestColor
      costs n k row old_min1 old_min2 old_color processed new_color new_min1 /\
    ((processed = 1 /\ new_min2 = PaintHouseIIInf) \/
     (2 <= processed /\
      PaintHouseIIProcessedSecondBest
        costs n k row old_min1 old_min2 old_color processed new_color new_min2)))).

Definition PaintHouseIICompletedRowState
    (costs : list (list Z)) (n k row old_min1 old_min2 old_color
       new_min1 new_min2 new_color : Z) : Prop :=
  PaintHouseIIInnerState
    costs n k row k old_min1 old_min2 old_color new_min1 new_min2 new_color /\
  PaintHouseIIDPState costs n k (row + 1) new_min1 new_min2 new_color.

Definition PaintHouseIIAnswer
    (costs : list (list Z)) (n k answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun colors : list Z =>
       PaintHouseIIValidColoring k n colors)
    (fun colors : list Z =>
       PaintHouseIIColoringCost costs n colors)
    answer.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Lemma PaintHouseIIPrefixCost_value_bound__loop_core :
  forall costs n k row color value,
    n <= 10000 ->
    (forall r c,
       0 <= r < n ->
       0 <= c < k ->
       0 <= PaintCostAt costs r c <= 10000) ->
    PaintHouseIIPrefixCost costs n k row color value ->
    0 <= row <= n /\ 0 <= value <= row * 10000.
Proof.
  intros costs n k row color value Hn Hcost Hprefix.
  induction Hprefix.
  - split; lia.
  - destruct IHHprefix as [Hrow_bound Hprev_bound].
    pose proof (Hcost row color H H0) as Hcost_bound.
    subst value.
    split; lia.
Qed.
Lemma PaintHouseIIDPState_values_bound__loop_core :
  forall costs n k row min1 min2 min1_color,
    n <= 10000 ->
    (forall r c,
       0 <= r < n ->
       0 <= c < k ->
       0 <= PaintCostAt costs r c <= 10000) ->
    PaintHouseIIDPState costs n k row min1 min2 min1_color ->
    0 <= min1 <= row * 10000 /\ 0 <= min2 <= row * 10000.
Proof.
  intros costs n k row min1 min2 min1_color Hn Hcost Hstate.
  unfold PaintHouseIIDPState in Hstate.
  destruct Hstate as [[Hrow [Hmin1 [Hmin2 _]]] |
                      [Hrow_range [_ [Hbest Hsecond]]]].
  - subst. split; lia.
  - unfold PaintHouseIIBestColor in Hbest.
    destruct Hbest as [Hbest_prefix _].
    pose proof (PaintHouseIIPrefixCost_value_bound__loop_core
                  costs n k row min1_color min1 Hn Hcost Hbest_prefix)
      as [_ Hmin1_bound].
    unfold PaintHouseIISecondBestForColor in Hsecond.
    destruct Hsecond as [[Hrow0 [_ Hmin2]] | [_ Hmin2_min]].
    + subst. lia.
    + unfold min_value_of_subset, min_object_of_subset in Hmin2_min.
      destruct Hmin2_min as [[second_color second_value]
          [[[ _ Hsecond_prefix] _] Hsecond_value]].
      simpl in Hsecond_value. subst second_value.
      pose proof (PaintHouseIIPrefixCost_value_bound__loop_core
                    costs n k row second_color min2 Hn Hcost Hsecond_prefix)
        as [_ Hmin2_bound].
      split; lia.
Qed.
Lemma PaintHouseIIInnerState_values_bound__loop_core :
  forall costs n k row processed old_min1 old_min2 old_color
         new_min1 new_min2 new_color,
    n <= 10000 ->
    (forall r c,
       0 <= r < n ->
       0 <= c < k ->
       0 <= PaintCostAt costs r c <= 10000) ->
    PaintHouseIIInnerState costs n k row processed old_min1 old_min2 old_color
      new_min1 new_min2 new_color ->
    0 <= new_min1 <= 1000000000 /\
    0 <= new_min2 <= 1000000000 /\
    -1 <= new_color < k.
Proof.
  intros costs n k row processed old_min1 old_min2 old_color
    new_min1 new_min2 new_color Hn Hcost Hinner.
  unfold PaintHouseIIInnerState in Hinner.
  destruct Hinner as [Hrow [Hprocessed [_ [Hzero | Hpos]]]].
  - destruct Hzero as [Hprocessed0 [Hnew1 [Hnew2 Hcolor]]].
    subst processed new_min1 new_min2 new_color.
    unfold PaintHouseIIInf.
    repeat split; lia.
  - destruct Hpos as [Hprocessed_pos [Hcolor_range [Hbest Hsecond]]].
    unfold PaintHouseIIProcessedBestColor in Hbest.
    destruct Hbest as [Hbest_candidate _].
    unfold PaintHouseIIProcessedCandidate in Hbest_candidate.
    destruct Hbest_candidate as [_ Hnew1_prefix].
    pose proof (PaintHouseIIPrefixCost_value_bound__loop_core
                  costs n k (row + 1) new_color new_min1
                  Hn Hcost Hnew1_prefix) as [_ Hnew1_bound].
    assert (Hnew2_bound: 0 <= new_min2 <= 1000000000).
    { destruct Hsecond as [[_ Hnew2] | [_ Hsecond_min]].
      - subst new_min2. unfold PaintHouseIIInf. lia.
      - unfold PaintHouseIIProcessedSecondBest in Hsecond_min.
        unfold min_value_of_subset, min_object_of_subset in Hsecond_min.
        destruct Hsecond_min as [[second_color second_value]
            [[[ _ Hsecond_candidate] _] Hsecond_value]].
        unfold PaintHouseIIProcessedCandidate in Hsecond_candidate.
        destruct Hsecond_candidate as [_ Hsecond_prefix].
        simpl in Hsecond_value. subst second_value.
        pose proof (PaintHouseIIPrefixCost_value_bound__loop_core
                      costs n k (row + 1) second_color new_min2
                      Hn Hcost Hsecond_prefix) as [_ Hnew2_prefix_bound].
        lia. }
    split; [lia | split; lia].
Qed.
Lemma PaintHouseIIPrefixCost_inv_cons__loop_core :
  forall costs n k row color value,
    0 <= row < n ->
    PaintHouseIIPrefixCost costs n k (row + 1) color value ->
    exists prev_color prev_value,
      prev_color <> color /\
      PaintHouseIIPrefixCost costs n k row prev_color prev_value /\
      value = prev_value + PaintCostAt costs row color.
Proof.
  intros costs n k row color value Hrow Hprefix.
  inversion Hprefix; subst.
  - lia.
  - assert (row0 = row) by lia.
    subst row0.
    exists prev_color, prev_value.
    repeat split; auto.
Qed.
Lemma PaintHouseIIPrefixCost_color_bound__loop_core :
  forall costs n k row color value,
    1 <= row ->
    PaintHouseIIPrefixCost costs n k row color value ->
    0 <= color < k.
Proof.
  intros costs n k row color value Hrow Hprefix.
  inversion Hprefix; subst; lia.
Qed.
Lemma PaintHouseIIPrevSelection_min_prefix__loop_core :
  forall costs n k row old_min1 old_min2 old_color color prev,
    0 <= row < n ->
    0 <= color < k ->
    PaintHouseIIDPState costs n k row old_min1 old_min2 old_color ->
    PaintHouseIIPrevSelection old_min1 old_min2 old_color color prev ->
    (exists prev_color,
       prev_color <> color /\
       PaintHouseIIPrefixCost costs n k row prev_color prev) /\
    (forall prev_color prev_value,
       prev_color <> color ->
       PaintHouseIIPrefixCost costs n k row prev_color prev_value ->
       prev <= prev_value).
Proof.
  intros costs n k row old_min1 old_min2 old_color color prev
    Hrow Hcolor Hdp Hsel.
  unfold PaintHouseIIDPState in Hdp.
  destruct Hdp as [[Hrow0 [Hold1 [Hold2 Hold_color]]] |
                   [Hrow_pos [Hold_color_range [Hbest Hsecond]]]].
  - subst.
    unfold PaintHouseIIPrevSelection in Hsel.
    destruct (Z.eq_dec color (-1)); [lia | subst prev].
    split.
    + exists (-1). split; [lia | constructor; lia].
    + intros prev_color prev_value Hne Hprefix.
      inversion Hprefix; subst; lia.
  - unfold PaintHouseIIPrevSelection in Hsel.
    destruct (Z.eq_dec color old_color) as [Heq | Hne].
    + subst color. subst prev.
      unfold PaintHouseIISecondBestForColor in Hsecond.
      destruct Hsecond as [[Hrow0 _] | [_ Hmin]]; [lia |].
      unfold min_value_of_subset, min_object_of_subset in Hmin.
      destruct Hmin as [[best_color best_value] [[Hobj Hleast] Heqv]].
      simpl in Heqv. subst best_value.
      simpl in Hobj. destruct Hobj as [Hbest_ne Hbest_prefix].
      split.
      * exists best_color. split; auto.
      * intros prev_color prev_value Hne Hprefix.
        pose proof (Hleast (prev_color, prev_value)) as Hle.
        simpl in Hle.
        apply Hle.
        simpl. split; auto.
    + subst prev.
      unfold PaintHouseIIBestColor in Hbest.
      destruct Hbest as [Hbest_prefix Hmin].
      unfold min_value_of_subset, min_object_of_subset in Hmin.
      destruct Hmin as [[best_color best_value] [[_ Hleast] Hbest_eq]].
      simpl in Hbest_eq. subst old_min1.
      split.
      * exists old_color. split; auto.
      * intros prev_color prev_value _ Hprefix.
        pose proof (Hleast (prev_color, prev_value)) as Hle.
        simpl in Hle.
        apply Hle.
        simpl. exact Hprefix.
Qed.
Lemma PaintHouseIIPrevSelection_prefix_candidate__loop_core :
  forall costs n k row old_min1 old_min2 old_color color prev total,
    0 <= row < n ->
    0 <= color < k ->
    PaintHouseIIDPState costs n k row old_min1 old_min2 old_color ->
    PaintHouseIIPrevSelection old_min1 old_min2 old_color color prev ->
    total = prev + PaintCostAt costs row color ->
    PaintHouseIIPrefixCost costs n k (row + 1) color total.
Proof.
  intros costs n k row old_min1 old_min2 old_color color prev total
    Hrow Hcolor Hdp Hsel Htotal.
  pose proof (PaintHouseIIPrevSelection_min_prefix__loop_core
                costs n k row old_min1 old_min2 old_color color prev
                Hrow Hcolor Hdp Hsel) as [[prev_color [Hne Hprefix]] _].
  subst total.
  eapply PaintHouseIIPrefixCost_cons; eauto.
Qed.
Lemma PaintHouseIIPrevSelection_prefix_min_next__loop_core :
  forall costs n k row old_min1 old_min2 old_color color prev total value,
    0 <= row < n ->
    0 <= color < k ->
    PaintHouseIIDPState costs n k row old_min1 old_min2 old_color ->
    PaintHouseIIPrevSelection old_min1 old_min2 old_color color prev ->
    total = prev + PaintCostAt costs row color ->
    PaintHouseIIPrefixCost costs n k (row + 1) color value ->
    total <= value.
Proof.
  intros costs n k row old_min1 old_min2 old_color color prev total value
    Hrow Hcolor Hdp Hsel Htotal Hprefix.
  pose proof (PaintHouseIIPrevSelection_min_prefix__loop_core
                costs n k row old_min1 old_min2 old_color color prev
                Hrow Hcolor Hdp Hsel) as [_ Hleast].
  pose proof (PaintHouseIIPrefixCost_inv_cons__loop_core
                costs n k row color value Hrow Hprefix)
    as [prev_color [prev_value [Hne [Hprev_prefix Hvalue]]]].
  specialize (Hleast prev_color prev_value Hne Hprev_prefix).
  subst total value.
  lia.
Qed.
Lemma PaintHouseIIInnerState_update_best__loop_core :
  forall costs n k row processed old_min1 old_min2 old_color
         new_min1 new_min2 new_color prev total,
    0 <= processed < k ->
    total < new_min1 ->
    PaintHouseIIPrevSelection old_min1 old_min2 old_color processed prev ->
    total = prev + PaintCostAt costs row processed ->
    PaintHouseIIInnerState costs n k row processed old_min1 old_min2 old_color
      new_min1 new_min2 new_color ->
    PaintHouseIIInnerState costs n k row (processed + 1)
      old_min1 old_min2 old_color total new_min1 processed.
Proof.
  intros costs n k row processed old_min1 old_min2 old_color
    new_min1 new_min2 new_color prev total Hprocessed Hlt Hsel Htotal Hinner.
  unfold PaintHouseIIInnerState in *.
  destruct Hinner as [Hrow [Hprocessed_old [Hdp Hcase]]].
  split; [lia|].
  split; [lia|].
  split; [exact Hdp|].
  right.
  split; [lia|].
  split; [lia|].
  split.
  - unfold PaintHouseIIProcessedBestColor.
    split.
    + unfold PaintHouseIIProcessedCandidate.
      split; [lia|].
      eapply PaintHouseIIPrevSelection_prefix_candidate__loop_core; eauto; lia.
    + unfold min_value_of_subset, min_object_of_subset.
      exists (processed, total). simpl.
      split.
      * split.
        -- unfold PaintHouseIIProcessedCandidate.
           unfold SetElement.SetsEle.In. simpl. split; [lia|].
           eapply PaintHouseIIPrevSelection_prefix_candidate__loop_core; eauto; lia.
        -- intros [color value] Hcand.
           simpl in *.
           unfold SetElement.SetsEle.In in Hcand.
           unfold PaintHouseIIProcessedCandidate in Hcand.
           destruct Hcand as [Hcolor_range Hprefix].
           simpl in Hcolor_range.
           destruct (Z.eq_dec color processed) as [Heq | Hne].
           ++ subst color.
              eapply (PaintHouseIIPrevSelection_prefix_min_next__loop_core
                costs n k row old_min1 old_min2 old_color processed
                prev total value); eauto; lia.
           ++ assert (Hcolor_old : 0 <= color < processed) by lia.
              destruct Hcase as [[Hprocessed0 _] |
                                 [Hprocessed_pos [Hnew_color_range [Hbest _]]]].
              ** lia.
              ** unfold PaintHouseIIProcessedBestColor in Hbest.
                 destruct Hbest as [_ Hbest_min].
                 unfold min_value_of_subset, min_object_of_subset in Hbest_min.
                 destruct Hbest_min as [[best_color best_value]
                    [[_ Hleast] Hbest_value]].
                 pose proof (Hleast (color, value)) as Hle.
                 simpl in Hle.
                 specialize (Hle ltac:(unfold SetElement.SetsEle.In; unfold PaintHouseIIProcessedCandidate;
                   simpl; split; auto)).
                 simpl in Hbest_value. subst new_min1.
                 lia.
      * reflexivity.
  - destruct (Z.eq_dec processed 0) as [Hprocessed0 | Hprocessed_nonzero].
    + left.
      destruct Hcase as [[_ [Hnew1 [_ _]]] | [Hpos _]]; [subst; auto | lia].
    + right.
      destruct Hcase as [[Hprocessed0_old _] |
                         [Hprocessed_pos [Hnew_color_range [Hbest _]]]]; [lia|].
      split; [lia|].
      unfold PaintHouseIIProcessedSecondBest.
      unfold min_value_of_subset, min_object_of_subset.
      exists (new_color, new_min1). simpl.
      split.
      * split.
        -- unfold SetElement.SetsEle.In. simpl. split; [lia|].
           unfold PaintHouseIIProcessedBestColor in Hbest.
           destruct Hbest as [Hbest_candidate _].
           unfold PaintHouseIIProcessedCandidate in *.
           destruct Hbest_candidate as [Hbest_range Hbest_prefix].
           simpl in Hbest_range.
           split; [lia|exact Hbest_prefix].
        -- intros [color value] Hcand.
           simpl in *.
           change (color <> processed /\
             PaintHouseIIProcessedCandidate costs n k row old_min1 old_min2
               old_color (processed + 1) color value) in Hcand.
           destruct Hcand as [Hne_color Hcandidate].
           unfold PaintHouseIIProcessedCandidate in Hcandidate.
           destruct Hcandidate as [Hcolor_range Hprefix].
           simpl in Hcolor_range.
           assert (Hcolor_old : 0 <= color < processed) by lia.
           unfold PaintHouseIIProcessedBestColor in Hbest.
           destruct Hbest as [_ Hbest_min].
           unfold min_value_of_subset, min_object_of_subset in Hbest_min.
           destruct Hbest_min as [[best_color best_value] [[_ Hleast] Hbest_value]].
           pose proof (Hleast (color, value)) as Hle.
           simpl in Hle.
           specialize (Hle ltac:(unfold SetElement.SetsEle.In; unfold PaintHouseIIProcessedCandidate;
             simpl; split; auto)).
           simpl in Hbest_value. subst new_min1.
           exact Hle.
      * reflexivity.
Qed.
Lemma PaintHouseIIInnerState_update_second__loop_core :
  forall costs n k row processed old_min1 old_min2 old_color
         new_min1 new_min2 new_color prev total,
    0 <= processed < k ->
    new_min1 <= total ->
    total < new_min2 ->
    PaintHouseIIPrevSelection old_min1 old_min2 old_color processed prev ->
    total = prev + PaintCostAt costs row processed ->
    PaintHouseIIInnerState costs n k row processed old_min1 old_min2 old_color
      new_min1 new_min2 new_color ->
    PaintHouseIIInnerState costs n k row (processed + 1)
      old_min1 old_min2 old_color new_min1 total new_color.
Proof.
  intros costs n k row processed old_min1 old_min2 old_color
    new_min1 new_min2 new_color prev total Hprocessed Hge Hlt Hsel Htotal Hinner.
  unfold PaintHouseIIInnerState in *.
  destruct Hinner as [Hrow [Hprocessed_old [Hdp Hcase]]].
  split; [lia|].
  split; [lia|].
  split; [exact Hdp|].
  destruct Hcase as [[Hprocessed0 [Hnew1 [Hnew2 Hcolor]]] |
                     [Hprocessed_pos [Hnew_color_range [Hbest Hsecond]]]].
  - subst. unfold PaintHouseIIInf in *. lia.
  - right.
    split; [lia|].
    split; [lia|].
    split.
    + unfold PaintHouseIIProcessedBestColor.
      unfold PaintHouseIIProcessedBestColor in Hbest.
      destruct Hbest as [Hbest_candidate Hbest_min].
      split.
      * unfold PaintHouseIIProcessedCandidate in *.
        destruct Hbest_candidate as [Hbest_range Hbest_prefix].
        simpl in *.
        split; [lia|exact Hbest_prefix].
      * unfold min_value_of_subset, min_object_of_subset in *.
        destruct Hbest_min as [[best_color best_value] [[_ Hleast] Hbest_eq]].
        simpl in Hbest_eq. subst best_value.
        exists (new_color, new_min1). simpl.
        split.
        -- split.
           ++ unfold SetElement.SetsEle.In. simpl.
              unfold PaintHouseIIProcessedCandidate in *.
              destruct Hbest_candidate as [Hbest_range Hbest_prefix].
              simpl in *.
              split; [lia|exact Hbest_prefix].
           ++ intros [color value] Hcand.
              simpl in *.
              unfold SetElement.SetsEle.In in Hcand.
              unfold PaintHouseIIProcessedCandidate in Hcand.
              destruct Hcand as [Hcolor_range Hprefix].
              simpl in Hcolor_range.
              destruct (Z.eq_dec color processed) as [Heq | Hne].
              ** subst color.
                 pose proof (PaintHouseIIPrevSelection_prefix_min_next__loop_core
                   costs n k row old_min1 old_min2 old_color processed
                   prev total value Hrow ltac:(lia) Hdp Hsel Htotal Hprefix).
                 lia.
              ** assert (Hcolor_old : 0 <= color < processed) by lia.
                 pose proof (Hleast (color, value)) as Hle.
                 simpl in Hle.
                 specialize (Hle ltac:(unfold SetElement.SetsEle.In;
                   unfold PaintHouseIIProcessedCandidate; simpl; split; auto)).
                 exact Hle.
        -- reflexivity.
    + right.
      split; [lia|].
      unfold PaintHouseIIProcessedSecondBest.
      unfold min_value_of_subset, min_object_of_subset.
      exists (processed, total). simpl.
      split.
      * split.
        -- unfold SetElement.SetsEle.In. simpl.
           split; [lia|].
           unfold PaintHouseIIProcessedCandidate.
           split; [lia|].
           eapply PaintHouseIIPrevSelection_prefix_candidate__loop_core; eauto; lia.
        -- intros [color value] Hcand.
           simpl in *.
           unfold SetElement.SetsEle.In in Hcand.
           destruct Hcand as [Hne_color Hcandidate].
           unfold PaintHouseIIProcessedCandidate in Hcandidate.
           destruct Hcandidate as [Hcolor_range Hprefix].
           simpl in Hcolor_range.
           destruct (Z.eq_dec color processed) as [Heq | Hne].
           ++ subst color.
              eapply (PaintHouseIIPrevSelection_prefix_min_next__loop_core
                costs n k row old_min1 old_min2 old_color processed
                prev total value); eauto; lia.
           ++ assert (Hcolor_old : 0 <= color < processed) by lia.
              destruct Hsecond as [[Hprocessed1 Hnew2] |
                                   [Hprocessed2 Hsecond_best]].
              ** assert (color = new_color) by lia. contradiction.
              ** unfold PaintHouseIIProcessedSecondBest in Hsecond_best.
                 unfold min_value_of_subset, min_object_of_subset in Hsecond_best.
                 destruct Hsecond_best as [[second_color second_value]
                   [[[Hold_ne Hold_candidate] Hold_le] Hold_eq]].
                 simpl in Hold_eq. subst second_value.
                 pose proof (Hold_le (color, value)) as Hle.
                 simpl in Hle.
                 specialize (Hle ltac:(unfold SetElement.SetsEle.In; simpl;
                   split; [exact Hne_color|];
                   unfold PaintHouseIIProcessedCandidate; simpl;
                   split; auto)).
                 lia.
      * reflexivity.
Qed.
Lemma PaintHouseIIInnerState_keep__loop_core :
  forall costs n k row processed old_min1 old_min2 old_color
         new_min1 new_min2 new_color prev total,
    0 <= processed < k ->
    new_min1 <= total ->
    new_min2 <= total ->
    total < PaintHouseIIInf ->
    PaintHouseIIPrevSelection old_min1 old_min2 old_color processed prev ->
    total = prev + PaintCostAt costs row processed ->
    PaintHouseIIInnerState costs n k row processed old_min1 old_min2 old_color
      new_min1 new_min2 new_color ->
    PaintHouseIIInnerState costs n k row (processed + 1)
      old_min1 old_min2 old_color new_min1 new_min2 new_color.
Proof.
  intros costs n k row processed old_min1 old_min2 old_color
    new_min1 new_min2 new_color prev total Hprocessed Hge1 Hge2 Htotal_bound
    Hsel Htotal Hinner.
  unfold PaintHouseIIInnerState in *.
  destruct Hinner as [Hrow [Hprocessed_old [Hdp Hcase]]].
  split; [lia|].
  split; [lia|].
  split; [exact Hdp|].
  destruct Hcase as [[Hprocessed0 [Hnew1 [Hnew2 Hcolor]]] |
                     [Hprocessed_pos [Hnew_color_range [Hbest Hsecond]]]].
  - subst. unfold PaintHouseIIInf in *. lia.
  - right.
    unfold PaintHouseIIProcessedBestColor in Hbest.
    destruct Hbest as [Hbest_candidate Hbest_min].
    split; [lia|].
    split; [lia|].
    split.
    + unfold PaintHouseIIProcessedBestColor.
      split.
      * unfold PaintHouseIIProcessedCandidate in *.
        destruct Hbest_candidate as [Hbest_range Hbest_prefix].
        simpl in *.
        split; [lia|exact Hbest_prefix].
      * unfold min_value_of_subset, min_object_of_subset in *.
        destruct Hbest_min as [[best_color best_value] [[_ Hleast] Hbest_eq]].
        simpl in Hbest_eq. subst best_value.
        exists (new_color, new_min1). simpl.
        split.
        -- split.
           ++ unfold SetElement.SetsEle.In. simpl.
              unfold PaintHouseIIProcessedCandidate in *.
              destruct Hbest_candidate as [Hbest_range Hbest_prefix].
              simpl in *.
              split; [lia|exact Hbest_prefix].
           ++ intros [color value] Hcand.
              simpl in *.
              unfold SetElement.SetsEle.In in Hcand.
              unfold PaintHouseIIProcessedCandidate in Hcand.
              destruct Hcand as [Hcolor_range Hprefix].
              simpl in Hcolor_range.
              destruct (Z.eq_dec color processed) as [Heq | Hne].
              ** subst color.
                 pose proof (PaintHouseIIPrevSelection_prefix_min_next__loop_core
                   costs n k row old_min1 old_min2 old_color processed
                   prev total value Hrow ltac:(lia) Hdp Hsel Htotal Hprefix).
                 lia.
              ** assert (Hcolor_old : 0 <= color < processed) by lia.
                 pose proof (Hleast (color, value)) as Hle.
                 simpl in Hle.
                 specialize (Hle ltac:(unfold SetElement.SetsEle.In;
                   unfold PaintHouseIIProcessedCandidate; simpl; split; auto)).
                 exact Hle.
        -- reflexivity.
    + destruct Hsecond as [[Hprocessed1 Hnew2] |
                           [Hprocessed2 Hsecond_best]].
      * subst. unfold PaintHouseIIInf in *. lia.
      * right.
        split; [lia|].
        unfold PaintHouseIIProcessedSecondBest.
        unfold PaintHouseIIProcessedSecondBest in Hsecond_best.
        unfold min_value_of_subset, min_object_of_subset in *.
        destruct Hsecond_best as [[second_color second_value]
          [[[Hsecond_ne Hsecond_candidate] Hsecond_le] Hsecond_eq]].
        simpl in Hsecond_eq. subst second_value.
        exists (second_color, new_min2). simpl.
        split.
        -- split.
           ++ unfold SetElement.SetsEle.In. simpl.
              split; [exact Hsecond_ne|].
              unfold PaintHouseIIProcessedCandidate in *.
              destruct Hsecond_candidate as [Hsecond_range Hsecond_prefix].
              simpl in *.
              split; [lia|exact Hsecond_prefix].
           ++ intros [color value] Hcand.
              simpl in *.
              unfold SetElement.SetsEle.In in Hcand.
              destruct Hcand as [Hne_color Hcandidate].
              unfold PaintHouseIIProcessedCandidate in Hcandidate.
              destruct Hcandidate as [Hcolor_range Hprefix].
              simpl in Hcolor_range.
              destruct (Z.eq_dec color processed) as [Heq | Hne].
              ** subst color.
                 pose proof (PaintHouseIIPrevSelection_prefix_min_next__loop_core
                   costs n k row old_min1 old_min2 old_color processed
                   prev total value Hrow ltac:(lia) Hdp Hsel Htotal Hprefix).
                 lia.
              ** assert (Hcolor_old : 0 <= color < processed) by lia.
                 pose proof (Hsecond_le (color, value)) as Hle.
                 simpl in Hle.
                 specialize (Hle ltac:(unfold SetElement.SetsEle.In; simpl;
                   split; [exact Hne_color|];
                   unfold PaintHouseIIProcessedCandidate; simpl;
                   split; auto)).
                 exact Hle.
        -- reflexivity.
Qed.
Lemma PaintHouseIIInnerState_completed_row__loop_core :
  forall costs n k row old_min1 old_min2 old_color
         new_min1 new_min2 new_color,
    2 <= k ->
    PaintHouseIIInnerState costs n k row k old_min1 old_min2 old_color
      new_min1 new_min2 new_color ->
    PaintHouseIICompletedRowState costs n k row old_min1 old_min2 old_color
      new_min1 new_min2 new_color.
Proof.
  intros costs n k row old_min1 old_min2 old_color
    new_min1 new_min2 new_color Hk Hinner.
  unfold PaintHouseIICompletedRowState.
  split; [exact Hinner|].
  unfold PaintHouseIIInnerState in Hinner.
  destruct Hinner as [Hrow [Hprocessed [Hdp Hcase]]].
  unfold PaintHouseIIDPState.
  destruct Hcase as [[Hprocessed0 _] |
                     [Hprocessed_pos [Hnew_color_range [Hbest Hsecond]]]].
  - lia.
  - right.
    split; [lia|].
    split; [lia|].
    split.
    + unfold PaintHouseIIBestColor.
      unfold PaintHouseIIProcessedBestColor in Hbest.
      destruct Hbest as [Hbest_candidate Hbest_min].
      unfold PaintHouseIIProcessedCandidate in Hbest_candidate.
      destruct Hbest_candidate as [_ Hbest_prefix].
      split; [exact Hbest_prefix|].
      unfold min_value_of_subset, min_object_of_subset in *.
      destruct Hbest_min as [[best_color best_value] [[_ Hleast] Hbest_eq]].
      simpl in Hbest_eq. subst best_value.
      exists (new_color, new_min1). simpl.
      split.
      * split.
        -- unfold SetElement.SetsEle.In. simpl.
           exact Hbest_prefix.
        -- intros [color value] Hcand.
           simpl in *.
           unfold SetElement.SetsEle.In in Hcand.
           pose proof (PaintHouseIIPrefixCost_color_bound__loop_core
                         costs n k (row + 1) color value ltac:(lia) Hcand)
             as Hcolor_bound.
           pose proof (Hleast (color, value)) as Hle.
           simpl in Hle.
           specialize (Hle ltac:(unfold SetElement.SetsEle.In;
             unfold PaintHouseIIProcessedCandidate; simpl;
             split; auto)).
           exact Hle.
      * reflexivity.
    + unfold PaintHouseIISecondBestForColor.
      right.
      split; [lia|].
      destruct Hsecond as [[Hprocessed1 _] |
                           [Hprocessed2 Hsecond_best]]; [lia|].
      unfold PaintHouseIIProcessedSecondBest in Hsecond_best.
      unfold min_value_of_subset, min_object_of_subset in *.
      destruct Hsecond_best as [[second_color second_value]
        [[[Hsecond_ne Hsecond_candidate] Hsecond_le] Hsecond_eq]].
      simpl in Hsecond_eq. subst second_value.
      exists (second_color, new_min2). simpl.
      split.
      * split.
        -- unfold SetElement.SetsEle.In. simpl.
           split; [exact Hsecond_ne|].
           unfold PaintHouseIIProcessedCandidate in Hsecond_candidate.
           destruct Hsecond_candidate as [_ Hsecond_prefix].
           exact Hsecond_prefix.
        -- intros [color value] Hcand.
           simpl in *.
           unfold SetElement.SetsEle.In in Hcand.
           destruct Hcand as [Hne Hprefix].
           pose proof (PaintHouseIIPrefixCost_color_bound__loop_core
                         costs n k (row + 1) color value ltac:(lia) Hprefix)
             as Hcolor_bound.
           pose proof (Hsecond_le (color, value)) as Hle.
           simpl in Hle.
           specialize (Hle ltac:(unfold SetElement.SetsEle.In; simpl;
             split; [exact Hne|];
             unfold PaintHouseIIProcessedCandidate; simpl;
             split; auto)).
           exact Hle.
      * reflexivity.
Qed.
Lemma PaintHouseIIPrefixCost_row_bounds__answer :
  forall costs n k row color value,
    PaintHouseIIPrefixCost costs n k row color value ->
    0 <= row <= n.
Proof.
  intros costs n k row color value H.
  induction H; lia.
Qed.
Lemma PaintHouseIIPrefixCost_to_valid_prefix__answer :
  forall costs n k row color value,
    PaintHouseIIPrefixCost costs n k row color value ->
    exists colors,
      PaintHouseIIValidPrefixColoring k row colors /\
      PaintHouseIIPrefixLastColor row colors color /\
      value = PaintHouseIIColoringCost costs row colors.
Proof.
  intros costs n k row color value Hprefix.
  induction Hprefix.
  - exists nil.
    split.
    + unfold PaintHouseIIValidPrefixColoring.
      repeat split; try rewrite Zlength_nil; try lia; intros; lia.
    + split.
      * unfold PaintHouseIIPrefixLastColor.
        left; split; lia.
      * unfold PaintHouseIIColoringCost.
        rewrite sum_Z_range_empty by lia; reflexivity.
  - destruct IHHprefix as [colors [Hvalid [Hlast Hcost]]].
    exists (colors ++ color :: nil).
    assert (Hrow_nonneg : 0 <= row).
    { pose proof (PaintHouseIIPrefixCost_row_bounds__answer _ _ _ _ _ _ Hprefix); lia. }
    assert (Hlen : Zlength colors = row).
    { unfold PaintHouseIIValidPrefixColoring in Hvalid; tauto. }
    split.
    + unfold PaintHouseIIValidPrefixColoring in *.
      destruct Hvalid as [Hlen0 [Hrow0 [Hbounds Hadj]]].
      split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen0; lia.
      * split; [lia |].
        split.
        -- intros idx Hi.
           destruct (Z.eq_dec idx row) as [-> | Hneq].
           ++ rewrite app_Znth2 by lia.
              replace (row - Zlength colors) with 0 by lia.
              rewrite Znth0_cons; lia.
           ++ rewrite app_Znth1 by lia.
              apply Hbounds; lia.
        -- intros idx Hi.
           destruct (Z.eq_dec (idx + 1) row) as [Hsucc | Hsucc].
           ++ assert (idx = row - 1) by lia; subst idx.
              rewrite app_Znth1 by lia.
              rewrite app_Znth2 by lia.
              replace (row - 1 + 1 - Zlength colors) with 0 by lia.
              rewrite Znth0_cons.
              unfold PaintHouseIIPrefixLastColor in Hlast.
              destruct Hlast as [[Hrow0' _] | [_ Hlast]]; [lia |].
              congruence.
           ++ rewrite !app_Znth1 by lia.
              apply Hadj; lia.
    + split.
      * unfold PaintHouseIIPrefixLastColor.
        right.
        split; [lia |].
        rewrite app_Znth2 by lia.
        replace (row + 1 - 1 - Zlength colors) with 0 by lia.
        rewrite Znth0_cons.
        reflexivity.
      * subst value.
        unfold PaintHouseIIColoringCost in *.
        rewrite sum_Z_range_extend_right by lia.
        replace (Znth row (colors ++ color :: nil) (-1)) with color.
        -- replace
             (sum (fun i : Z => 0 <= i < row)
                (fun i : Z =>
                   PaintCostAt costs i (Znth i (colors ++ color :: nil) (-1))))
             with
             (sum (fun i : Z => 0 <= i < row)
                (fun i : Z => PaintCostAt costs i (Znth i colors (-1)))).
           ++ lia.
           ++ apply sum_ext. intros i Hi.
              rewrite app_Znth1 by lia.
              reflexivity.
        -- rewrite app_Znth2 by lia.
           replace (row - Zlength colors) with 0 by lia.
           rewrite Znth0_cons.
           reflexivity.
Qed.
Lemma PaintHouseIIValidColoring_to_PrefixCost__answer :
  forall costs total row k colors,
    0 <= row <= total ->
    PaintHouseIIValidColoring k row colors ->
    PaintHouseIIPrefixCost costs total k row
      (Znth (row - 1) colors (-1))
      (PaintHouseIIColoringCost costs row colors).
Proof.
  intros costs total row k colors Hrange Hvalid.
  remember (Z.to_nat row) as m eqn:Hm.
  assert (Hrow_eq : row = Z.of_nat m) by (subst m; lia).
  subst row.
  clear Hm.
  revert total colors Hrange Hvalid.
  induction m as [|m IH]; intros total colors Hrange Hvalid.
  - simpl.
    unfold PaintHouseIIValidColoring in Hvalid.
    destruct Hvalid as [Hlen _].
    destruct colors as [|x xs].
    2:{
      rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg xs).
      lia.
    }
    unfold PaintHouseIIColoringCost.
    rewrite sum_Z_range_empty by lia.
    simpl.
    constructor; lia.
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
    replace (Z.of_nat m + 1 - 1) with (Z.of_nat m) by lia.
    pose (prefix := sublist 0 (Z.of_nat m) colors).
    assert (Hvalid_prefix : PaintHouseIIValidColoring k (Z.of_nat m) prefix).
    {
      unfold prefix.
      unfold PaintHouseIIValidColoring in *.
      destruct Hvalid as [Hlen [Hbounds Hadj]].
      split.
      - rewrite Zlength_sublist by lia; lia.
      - split.
        + intros idx Hi.
          rewrite Znth_sublist0 by lia.
          apply Hbounds; lia.
        + intros idx Hi.
          rewrite !Znth_sublist0 by lia.
          apply Hadj; lia.
    }
    specialize (IH total prefix ltac:(lia) Hvalid_prefix).
    unfold PaintHouseIIValidColoring in Hvalid.
    destruct Hvalid as [Hlen [Hbounds Hadj]].
    eapply PaintHouseIIPrefixCost_cons with
      (prev_color := Znth (Z.of_nat m - 1) prefix (-1))
      (prev_value := PaintHouseIIColoringCost costs (Z.of_nat m) prefix).
    + lia.
    + apply Hbounds; lia.
    + 
      destruct (Z.eq_dec (Z.of_nat m) 0) as [Hrow0 | Hrowpos].
      * unfold prefix.
        rewrite Zsublist_nil by lia.
        rewrite Hrow0.
        change (Znth (0 - 1) (@nil Z) (-1)) with (-1).
        pose proof (Hbounds 0 ltac:(lia)).
        lia.
      * unfold prefix.
        rewrite Znth_sublist0 by lia.
        specialize (Hadj (Z.of_nat m - 1) ltac:(lia)).
        replace (Z.of_nat m - 1 + 1) with (Z.of_nat m) in Hadj by lia.
        exact Hadj.
    + exact IH.
    + unfold PaintHouseIIColoringCost.
      rewrite sum_Z_range_extend_right by lia.
      replace
        (sum (fun i : Z => 0 <= i < Z.of_nat m)
           (fun i : Z => PaintCostAt costs i (Znth i colors (-1))))
        with
        (PaintHouseIIColoringCost costs (Z.of_nat m) prefix).
      * reflexivity.
      * unfold PaintHouseIIColoringCost, prefix.
        apply sum_ext. intros i Hi.
        rewrite Znth_sublist0 by lia.
        reflexivity.
Qed.
Lemma PaintHouseIIDPState_answer__answer :
  forall costs n k min1 min2 min1_color,
    1 <= n ->
    PaintHouseIIDPState costs n k n min1 min2 min1_color ->
    PaintHouseIIAnswer costs n k min1.
Proof.
  intros costs n k min1 min2 min1_color Hn Hdp.
  unfold PaintHouseIIDPState in Hdp.
  destruct Hdp as [[Hrow _] | [_ [_ [Hbest _]]]]; [lia |].
  unfold PaintHouseIIBestColor in Hbest.
  destruct Hbest as [_ Hmin].
  unfold PaintHouseIIAnswer.
  unfold min_value_of_subset, min_object_of_subset in *.
  destruct Hmin as [[best_color best_value] [[Hbest_prefix Hbest_le] Hbest_value]].
  simpl in Hbest_value; subst best_value.
  simpl in Hbest_prefix, Hbest_le.
  pose proof
    (PaintHouseIIPrefixCost_to_valid_prefix__answer
       costs n k n best_color min1 Hbest_prefix)
    as [best_colors [Hbest_valid [_ Hbest_cost]]].
  exists best_colors.
  split.
  - split.
    + unfold PaintHouseIIValidPrefixColoring in Hbest_valid.
      unfold PaintHouseIIValidColoring.
      destruct Hbest_valid as [Hlen [_ [Hbounds Hadj]]].
      split; [exact Hlen | split; [exact Hbounds | exact Hadj]].
    + intros colors Hvalid.
      specialize
        (Hbest_le
           (Znth (n - 1) colors (-1),
            PaintHouseIIColoringCost costs n colors)).
      simpl in Hbest_le.
      rewrite <- Hbest_cost.
      apply Hbest_le.
      apply PaintHouseIIValidColoring_to_PrefixCost__answer; [lia | exact Hvalid].
  - symmetry; exact Hbest_cost.
Qed.
