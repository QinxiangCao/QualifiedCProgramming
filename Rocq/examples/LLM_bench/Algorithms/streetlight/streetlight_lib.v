From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive StreetlightPlan
    (positions powers : list Z) (start : Z) :
    Z -> Z -> Z -> Z -> Prop :=
  | StreetlightPlan_start :
      0 <= start < Zlength positions ->
      Zlength powers = Zlength positions ->
      StreetlightPlan positions powers start start start start 0
  | StreetlightPlan_extend_left :
      forall left right endpoint cost,
        0 <= left ->
        left < start <= right ->
        right < Zlength positions ->
        StreetlightPlan positions powers start
          (left + 1) right endpoint cost ->
        StreetlightPlan positions powers start left right left
          (cost +
           (Znth endpoint positions 0 - Znth left positions 0) *
           (sum powers - sum (sublist (left + 1) (right + 1) powers)))
  | StreetlightPlan_extend_right :
      forall left right endpoint cost,
        0 <= left ->
        left <= start < right ->
        right < Zlength positions ->
        StreetlightPlan positions powers start
          left (right - 1) endpoint cost ->
        StreetlightPlan positions powers start left right right
          (cost +
           (Znth right positions 0 - Znth endpoint positions 0) *
           (sum powers - sum (sublist left right powers))).

Definition StreetlightCompletePlan
    (positions powers : list Z) (start cost : Z) : Prop :=
  exists endpoint,
    StreetlightPlan positions powers start
      0 (Zlength positions - 1) endpoint cost.

Definition StreetlightMinimumEnergy
    (positions powers : list Z) (start answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost => StreetlightCompletePlan positions powers start cost)
    (fun cost => cost)
    answer.

Definition StreetlightTableShape
    (table : list (list Z)) (n : Z) : Prop :=
  Zlength table = n /\
  forall row, 0 <= row < n -> Zlength (Znth row table []) = n.

Definition StreetlightPrefixProgress
    (powers prefix : list Z) (done : Z) : Prop :=
  Zlength prefix = done + 1 /\
  forall k, 0 <= k <= done ->
    Znth k prefix 0 = sum (sublist 0 k powers).

Definition StreetlightInfRows
    (table : list (list Z)) (n rows_done : Z) : Prop :=
  StreetlightTableShape table n /\
  forall row col,
    0 <= row < rows_done ->
    0 <= col < n ->
    Znth col (Znth row table []) 0 = 2147483647.

Definition StreetlightInfProgress
    (table : list (list Z)) (n row next_col : Z) : Prop :=
  StreetlightInfRows table n row /\
  forall col,
    0 <= col < next_col ->
    Znth col (Znth row table []) 0 = 2147483647.

Definition StreetlightEndpointMinimum
    (positions powers : list Z) (start left right endpoint answer : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cost =>
       StreetlightPlan positions powers start left right endpoint cost)
    (fun cost => cost)
    answer.

Definition StreetlightLeftEntryCorrect
    (positions powers : list Z) (start left right value : Z) : Prop :=
  (left = start /\ right = start /\ value = 0) \/
  (left < start /\
   StreetlightEndpointMinimum
     positions powers start left right left value) \/
  (left = start /\ start < right /\ value = 2147483647).

Definition StreetlightRightEntryCorrect
    (positions powers : list Z) (start left right value : Z) : Prop :=
  (left = start /\ right = start /\ value = 0) \/
  (start < right /\
   StreetlightEndpointMinimum
     positions powers start left right right value) \/
  (left < start /\ right = start /\ value = 2147483647).

Definition StreetlightIntervalCorrect
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (start left right : Z) : Prop :=
  StreetlightLeftEntryCorrect positions powers start left right
    (Znth right (Znth left left_table []) 0) /\
  StreetlightRightEntryCorrect positions powers start left right
    (Znth right (Znth left right_table []) 0).

Definition StreetlightLengthsDone
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (n start next_len : Z) : Prop :=
  StreetlightTableShape left_table n /\
  StreetlightTableShape right_table n /\
  forall len left right,
    1 <= len < next_len ->
    right = left + len - 1 ->
    0 <= left ->
    right < n ->
    left <= start <= right ->
    StreetlightIntervalCorrect
      positions powers left_table right_table start left right.

Definition StreetlightLeftProgress
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (n start len next_left : Z) : Prop :=
  StreetlightLengthsDone
    positions powers left_table right_table n start len /\
  forall left right,
    0 <= left < next_left ->
    right = left + len - 1 ->
    right < n ->
    left <= start <= right ->
    StreetlightIntervalCorrect
      positions powers left_table right_table start left right.

Definition StreetlightLeftEndpointReady
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (n start len left : Z) : Prop :=
  StreetlightLeftProgress
    positions powers left_table right_table n start len left /\
  let right := left + len - 1 in
  StreetlightLeftEntryCorrect positions powers start left right
    (Znth right (Znth left left_table []) 0).

Definition StreetlightFinalCandidates
    (positions powers : list Z)
    (left_table right_table : list (list Z))
    (start left_answer right_answer : Z) : Prop :=
  let right := Zlength positions - 1 in
  StreetlightLeftEntryCorrect positions powers start 0 right left_answer /\
  StreetlightRightEntryCorrect positions powers start 0 right right_answer /\
  StreetlightMinimumEnergy
    positions powers start (Z.min left_answer right_answer).

From Coq Require Import Lia.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma streetlight_prefix_extend__prefix_setup :
  forall powers prefix i,
    0 <= i ->
    i < Zlength powers ->
    StreetlightPrefixProgress powers prefix i ->
    StreetlightPrefixProgress powers
      (prefix ++ [Znth i prefix 0 + Znth i powers 0]) (i + 1).
Proof.
  intros powers prefix i Hi Hipower Hprefix.
  unfold StreetlightPrefixProgress in *.
  destruct Hprefix as [Hlength Hvalues].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k (i + 1)) as [Hbefore | Hlast].
    + rewrite app_Znth1 by lia.
      apply Hvalues.
      lia.
    + assert (k = i + 1) by lia.
      subst k.
      rewrite app_Znth2 by lia.
      replace (i + 1 - Zlength prefix) with 0 by lia.
      simpl.
      rewrite (sublist_split 0 (i + 1) i powers) by lia.
      rewrite (sublist_single 0 i powers) by lia.
      rewrite sum_app.
      simpl.
      rewrite Hvalues by lia.
      rewrite Znth0_cons.
      lia.
Qed.
Lemma streetlight_prefix_zero_bounds__prefix_setup :
  forall k,
    0 <= k <= 0 ->
    0 <= Znth k [0] 0 <= 5000.
Proof.
  intros k Hk.
  assert (k = 0) by lia.
  subst k.
  rewrite Znth0_cons.
  lia.
Qed.
Lemma streetlight_prefix_zero_progress__prefix_setup :
  forall powers,
    StreetlightPrefixProgress powers [0] 0.
Proof.
  intros powers.
  unfold StreetlightPrefixProgress.
  split.
  - reflexivity.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    rewrite Znth0_cons.
    reflexivity.
Qed.
Lemma streetlight_table_shape_from_full__prefix_setup :
  forall table n,
    Zlength table = n ->
    (forall row,
      0 <= row < n ->
      Zlength (Znth row table nil) = n) ->
    StreetlightTableShape table n.
Proof.
  intros table n Hlength Hrows.
  unfold StreetlightTableShape.
  split.
  - exact Hlength.
  - exact Hrows.
Qed.
Lemma streetlight_inf_rows_zero__prefix_setup :
  forall table n,
    StreetlightTableShape table n ->
    StreetlightInfRows table n 0.
Proof.
  intros table n Hshape.
  unfold StreetlightInfRows.
  split.
  - exact Hshape.
  - intros row col Hrow.
    lia.
Qed.
Lemma streetlight_sum_positive__prefix_setup :
  forall values,
    values <> nil ->
    (forall k,
      0 <= k < Zlength values ->
      1 <= Znth k values 0) ->
    1 <= sum values.
Proof.
  induction values as [| value tail IH].
  - intros Hnonempty.
    contradiction.
  - intros _ Hvalues.
    assert (Hhead : 1 <= value).
    {
      specialize (Hvalues 0).
      rewrite Znth0_cons in Hvalues.
      apply Hvalues.
      rewrite Zlength_correct.
      simpl.
      lia.
    }
    destruct tail as [| next tail].
    + simpl.
      lia.
    + assert (Htail : 1 <= sum (next :: tail)).
      {
        apply IH.
        - discriminate.
        - intros k Hk.
          specialize (Hvalues (k + 1)).
          rewrite Znth_cons in Hvalues by lia.
          replace (k + 1 - 1) with k in Hvalues by lia.
          apply Hvalues.
          rewrite !Zlength_correct in *.
          simpl in *.
          lia.
      }
      simpl in Htail |- *.
      lia.
Qed.
Lemma streetlight_prefix_total_positive__prefix_setup :
  forall powers prefix n,
    1 <= n ->
    Zlength powers = n ->
    (forall k,
      0 <= k < n ->
      1 <= Znth k powers 0) ->
    StreetlightPrefixProgress powers prefix n ->
    1 <= Znth n prefix 0.
Proof.
  intros powers prefix n Hn Hlength Hpowers Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [_ Hprefix].
  rewrite Hprefix by lia.
  rewrite (sublist_self powers n) by lia.
  apply streetlight_sum_positive__prefix_setup.
  - intro Hnil.
    subst powers.
    unfold Zlength in Hlength.
    simpl in Hlength.
    lia.
  - intros k Hk.
    apply Hpowers.
    lia.
Qed.
Lemma streetlight_inf_progress_close_row__inf_tables :
  forall table n row next_col,
    n <= next_col ->
    StreetlightInfProgress table n row next_col ->
    StreetlightInfRows table n (row + 1).
Proof.
  intros table n row next_col Hnext
    [Hrows Hcurrent].
  destruct Hrows as [Hshape Hprevious].
  split; [exact Hshape |].
  intros r col Hr Hcol.
  destruct (Z_lt_ge_dec r row) as [Hbefore | Hcurrent_row].
  - apply Hprevious; lia.
  - assert (r = row) by lia.
    subst r.
    apply Hcurrent; lia.
Qed.
Lemma streetlight_inf_progress_store__inf_tables :
  forall table n row col d,
    0 <= row < n ->
    0 <= col < n ->
    StreetlightInfProgress table n row col ->
    StreetlightInfProgress
      (replace_Znth row
        (replace_Znth col 2147483647 (Znth row table d)) table)
      n row (col + 1).
Proof.
  intros table n row col d Hrow Hcol Hprogress.
  unfold StreetlightInfProgress in Hprogress |- *.
  destruct Hprogress as [[Hshape Hprevious] Hcurrent].
  destruct Hshape as [Htable_len Hrow_len].
  assert (Hrow_default : Znth row table d = Znth row table []).
  { apply Znth_indep. rewrite Htable_len. exact Hrow. }
  assert (Hrow_len_d : Zlength (Znth row table d) = n).
  { rewrite Hrow_default. apply Hrow_len. exact Hrow. }
  split.
  - split.
    + unfold StreetlightTableShape.
      split.
      * rewrite Zlength_replace_Znth. exact Htable_len.
      * intros r Hr.
        destruct (Z.eq_dec r row) as [Heq | Hneq].
        -- subst r.
           rewrite Znth_replace_Znth_Same by
             (rewrite Htable_len; exact Hrow).
           rewrite Zlength_replace_Znth. exact Hrow_len_d.
        -- rewrite Znth_replace_Znth_Diff by
             (try rewrite Htable_len; lia).
           apply Hrow_len. exact Hr.
    + intros r c Hr Hc.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_len; lia).
      apply Hprevious; assumption.
  - intros c Hc.
    rewrite Znth_replace_Znth_Same by
      (rewrite Htable_len; exact Hrow).
    destruct (Z.eq_dec c col) as [Heq | Hneq].
    + subst c.
      rewrite Znth_replace_Znth_Same by
        (rewrite Hrow_len_d; exact Hcol).
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrow_len_d; lia).
      rewrite Hrow_default.
      apply Hcurrent. lia.
Qed.
Lemma streetlight_diagonal_base__diagonal_base :
  forall positions powers left_table right_table n start d,
    0 <= start < n ->
    StreetlightInfRows left_table n n ->
    StreetlightInfRows right_table n n ->
    StreetlightLengthsDone positions powers
      (replace_Znth start
        (replace_Znth start 0 (Znth start left_table d)) left_table)
      (replace_Znth start
        (replace_Znth start 0 (Znth start right_table d)) right_table)
      n start 2 /\
    (forall pending_right,
      start < pending_right < n ->
      Znth pending_right
        (Znth start
          (replace_Znth start
            (replace_Znth start 0 (Znth start left_table d)) left_table)
          d) 0 = 2147483647) /\
    (forall pending_left,
      0 <= pending_left < start ->
      Znth start
        (Znth pending_left
          (replace_Znth start
            (replace_Znth start 0 (Znth start right_table d)) right_table)
          d) 0 = 2147483647).
Proof.
  intros positions powers left_table right_table n start d
    Hstart Hleft Hright.
  destruct Hleft as [[Hleft_len Hleft_row_len] Hleft_inf].
  destruct Hright as [[Hright_len Hright_row_len] Hright_inf].
  assert (Hleft_default :
    Znth start left_table d = Znth start left_table []).
  { apply Znth_indep. rewrite Hleft_len. exact Hstart. }
  assert (Hright_default :
    Znth start right_table d = Znth start right_table []).
  { apply Znth_indep. rewrite Hright_len. exact Hstart. }
  assert (Hleft_start_len : Zlength (Znth start left_table d) = n).
  { rewrite Hleft_default. apply Hleft_row_len. exact Hstart. }
  assert (Hright_start_len : Zlength (Znth start right_table d) = n).
  { rewrite Hright_default. apply Hright_row_len. exact Hstart. }
  assert (Hleft_shape :
    StreetlightTableShape
      (replace_Znth start
        (replace_Znth start 0 (Znth start left_table d)) left_table)
      n).
  {
    unfold StreetlightTableShape.
    split.
    - rewrite Zlength_replace_Znth. exact Hleft_len.
    - intros r Hr.
      destruct (Z.eq_dec r start) as [Heq | Hneq].
      + subst r.
        rewrite Znth_replace_Znth_Same by
          (rewrite Hleft_len; exact Hstart).
        rewrite Zlength_replace_Znth. exact Hleft_start_len.
      + rewrite Znth_replace_Znth_Diff by
          (try rewrite Hleft_len; lia).
        apply Hleft_row_len. exact Hr.
  }
  assert (Hright_shape :
    StreetlightTableShape
      (replace_Znth start
        (replace_Znth start 0 (Znth start right_table d)) right_table)
      n).
  {
    unfold StreetlightTableShape.
    split.
    - rewrite Zlength_replace_Znth. exact Hright_len.
    - intros r Hr.
      destruct (Z.eq_dec r start) as [Heq | Hneq].
      + subst r.
        rewrite Znth_replace_Znth_Same by
          (rewrite Hright_len; exact Hstart).
        rewrite Zlength_replace_Znth. exact Hright_start_len.
      + rewrite Znth_replace_Znth_Diff by
          (try rewrite Hright_len; lia).
        apply Hright_row_len. exact Hr.
  }
  split.
  - unfold StreetlightLengthsDone.
    split; [exact Hleft_shape |].
    split; [exact Hright_shape |].
    intros len l r Hlen Hr_eq Hl Hr Hcontains.
    assert (len = 1) by lia.
    subst len.
    assert (l = start) by lia.
    subst l.
    replace r with start in * by lia.
    unfold StreetlightIntervalCorrect.
    split.
    + unfold StreetlightLeftEntryCorrect.
      left.
      split; [reflexivity |].
      split; [reflexivity |].
      rewrite Znth_replace_Znth_Same by
        (rewrite Hleft_len; exact Hstart).
      rewrite Znth_replace_Znth_Same by
        (rewrite Hleft_start_len; exact Hstart).
      reflexivity.
    + unfold StreetlightRightEntryCorrect.
      left.
      split; [reflexivity |].
      split; [reflexivity |].
      rewrite Znth_replace_Znth_Same by
        (rewrite Hright_len; exact Hstart).
      rewrite Znth_replace_Znth_Same by
        (rewrite Hright_start_len; exact Hstart).
      reflexivity.
  - split.
    + intros pending_right Hpending.
      rewrite Znth_replace_Znth_Same by
        (rewrite Hleft_len; exact Hstart).
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hleft_start_len; lia).
      rewrite Hleft_default.
      apply Hleft_inf; lia.
    + intros pending_left Hpending.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_len; lia).
      rewrite (Znth_indep right_table pending_left d []) by
        (rewrite Hright_len; lia).
      apply Hright_inf; lia.
Qed.
Lemma streetlight_left_progress_zero__length_entry :
  forall positions powers left_table right_table n start entry len,
    start = entry ->
    StreetlightLengthsDone
      positions powers left_table right_table n start len ->
    StreetlightLeftProgress
      positions powers left_table right_table n entry len 0.
Proof.
  intros positions powers left_table right_table n start entry len
    Hentry Hdone.
  subst entry.
  unfold StreetlightLeftProgress.
  split.
  - exact Hdone.
  - intros left right Hleft.
    lia.
Qed.
Lemma streetlight_left_progress_initial__length_entry :
  forall positions powers left_table right_table n start len,
    StreetlightLengthsDone
      positions powers left_table right_table n start len ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len
      (start - len + 1).
Proof.
  intros positions powers left_table right_table n start len Hdone.
  unfold StreetlightLeftProgress.
  split.
  - exact Hdone.
  - intros left right Hleft Hright Hright_bound Hcontains_start.
    exfalso.
    lia.
Qed.
Lemma streetlight_sum_nonnegative_pointwise__left_remain :
  forall xs,
    (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0) ->
    0 <= sum xs.
Proof.
  induction xs as [| x xs IH]; intros Hnonnegative; simpl.
  - lia.
  - assert (Hx : 0 <= x).
    {
      specialize (Hnonnegative 0).
      unfold Znth in Hnonnegative.
      simpl in Hnonnegative.
      apply Hnonnegative.
      rewrite Zlength_correct.
      simpl.
      lia.
    }
    assert (Htail :
      forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0).
    {
      intros k Hk.
      specialize (Hnonnegative (k + 1)).
      rewrite Znth_cons in Hnonnegative by lia.
      replace (k + 1 - 1) with k in Hnonnegative by lia.
      apply Hnonnegative.
      rewrite Zlength_correct in *.
      simpl in *.
      lia.
    }
    specialize (IH Htail).
    lia.
Qed.
Lemma streetlight_remaining_bounds__left_remain :
  forall powers prefix n total left right,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    StreetlightPrefixProgress powers prefix n ->
    total = Znth n prefix 0 ->
    0 <= left ->
    left < right ->
    right < n ->
    1 <= total - (Znth (right + 1) prefix 0 -
                    Znth (left + 1) prefix 0) <= total.
Proof.
  intros powers prefix n total left right
    Hpowers Hpower_bounds Hprogress Htotal Hleft Hleft_right Hright.
  destruct Hprogress as [Hprefix_length Hprefix].
  pose proof (Hprefix n ltac:(lia)) as Hprefix_n.
  pose proof (Hprefix (right + 1) ltac:(lia)) as Hprefix_right.
  pose proof (Hprefix (left + 1) ltac:(lia)) as Hprefix_left.
  assert (Hwhole :
    sublist 0 n powers =
      sublist 0 (left + 1) powers ++
      sublist (left + 1) (right + 1) powers ++
      sublist (right + 1) n powers).
  {
    rewrite (sublist_split 0 n (left + 1) powers) by lia.
    rewrite (sublist_split (left + 1) n (right + 1) powers) by lia.
    reflexivity.
  }
  assert (Hthrough_right :
    sublist 0 (right + 1) powers =
      sublist 0 (left + 1) powers ++
      sublist (left + 1) (right + 1) powers).
  {
    rewrite (sublist_split 0 (right + 1) (left + 1) powers) by lia.
    reflexivity.
  }
  assert (Hmiddle_nonnegative :
    0 <= sum (sublist (left + 1) (right + 1) powers)).
  {
    apply streetlight_sum_nonnegative_pointwise__left_remain.
    intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    specialize (Hpower_bounds (k + (left + 1)) ltac:(lia)).
    lia.
  }
  assert (Hsuffix_nonnegative :
    0 <= sum (sublist (right + 1) n powers)).
  {
    apply streetlight_sum_nonnegative_pointwise__left_remain.
    intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    specialize (Hpower_bounds (k + (right + 1)) ltac:(lia)).
    lia.
  }
  assert (Hprefix_positive :
    1 <= sum (sublist 0 (left + 1) powers)).
  {
    rewrite (sublist_split 0 (left + 1) 1 powers) by lia.
    assert (Hsingle : sublist 0 1 powers = [Znth 0 powers 0]).
    {
      replace 1 with (0 + 1) by lia.
      apply sublist_single.
      lia.
    }
    rewrite Hsingle.
    rewrite sum_app.
    simpl.
    assert (Hhead : 1 <= Znth 0 powers 0).
    {
      specialize (Hpower_bounds 0 ltac:(lia)).
      lia.
    }
    assert (Htail_nonnegative :
      0 <= sum (sublist 1 (left + 1) powers)).
    {
      apply streetlight_sum_nonnegative_pointwise__left_remain.
      intros k Hk.
      rewrite Zlength_sublist in Hk by lia.
      rewrite Znth_sublist by lia.
      specialize (Hpower_bounds (k + 1) ltac:(lia)).
      lia.
    }
    lia.
  }
  pose proof (f_equal sum Hwhole) as Hsum_whole.
  pose proof (f_equal sum Hthrough_right) as Hsum_through_right.
  rewrite !sum_app in Hsum_whole.
  rewrite sum_app in Hsum_through_right.
  rewrite Htotal, Hprefix_n, Hprefix_right, Hprefix_left.
  lia.
Qed.
Lemma streetlight_sublist_sum_nonnegative__left_predecessor :
  forall (powers : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength powers ->
    (forall k, 0 <= k < Zlength powers ->
       1 <= Znth k powers 0 <= 100) ->
    0 <= sum (sublist lo hi powers).
Proof.
  intros powers lo hi Hlohi Hhi Hpowers.
  assert (Hentries :
    forall i, 0 <= i ->
      0 <= Znth i (sublist lo hi powers) 0 <= 100).
  {
    intros i Hi.
    destruct (Z_lt_ge_dec i (hi - lo)) as [Hin | Hout].
    - rewrite Znth_sublist by lia.
      specialize (Hpowers (i + lo) ltac:(lia)).
      lia.
    - rewrite Znth_sublist_ge by lia.
      lia.
  }
  pose proof (sum_bound 100 (sublist lo hi powers) Hentries) as Hsum.
  lia.
Qed.
Lemma streetlight_remaining_sum_bounds__left_predecessor :
  forall (powers : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength powers ->
    (forall k, 0 <= k < Zlength powers ->
       1 <= Znth k powers 0 <= 100) ->
    0 <= sum powers - sum (sublist lo hi powers) <= sum powers.
Proof.
  intros powers lo hi Hlohi Hhi Hpowers.
  assert (Hdecomp :
    powers =
      sublist 0 lo powers ++
      sublist lo hi powers ++
      sublist hi (Zlength powers) powers).
  {
    transitivity (sublist 0 (Zlength powers) powers).
    - symmetry. apply sublist_self. reflexivity.
    - rewrite (sublist_split 0 (Zlength powers) lo powers) by lia.
      rewrite (sublist_split lo (Zlength powers) hi powers) by lia.
      reflexivity.
  }
  pose proof
    (streetlight_sublist_sum_nonnegative__left_predecessor
       powers 0 lo ltac:(lia) ltac:(lia) Hpowers) as Hprefix.
  pose proof
    (streetlight_sublist_sum_nonnegative__left_predecessor
       powers lo hi Hlohi Hhi Hpowers) as Hmiddle.
  pose proof
    (streetlight_sublist_sum_nonnegative__left_predecessor
       powers hi (Zlength powers) ltac:(lia) ltac:(lia) Hpowers) as Hsuffix.
  pose proof (f_equal sum Hdecomp) as Hsumdecomp.
  rewrite !sum_app in Hsumdecomp.
  lia.
Qed.
Lemma streetlight_plan_endpoint_bounds__left_predecessor :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    left <= endpoint <= right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  induction Hplan; lia.
Qed.
Lemma streetlight_adjacent_nondecreasing_nat__left_predecessor :
  forall (positions : list Z) i (d : nat),
    (forall k, 0 <= k /\ k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    0 <= i ->
    i + Z.of_nat d < Zlength positions ->
    Znth i positions 0 <= Znth (i + Z.of_nat d) positions 0.
Proof.
  intros positions i d Hadj.
  induction d as [| d IH]; intros Hi Hbound.
  - replace (i + Z.of_nat 0) with i by lia.
    apply Z.le_refl.
  - rewrite Nat2Z.inj_succ in Hbound |- *.
    specialize (IH Hi ltac:(lia)).
    specialize (Hadj (i + Z.of_nat d) ltac:(lia)).
    replace (i + Z.succ (Z.of_nat d)) with (i + Z.of_nat d + 1) by lia.
    eapply Z.le_trans; [exact IH |].
    apply Z.lt_le_incl.
    exact Hadj.
Qed.
Lemma streetlight_adjacent_nondecreasing__left_predecessor :
  forall (positions : list Z) i j,
    (forall k, 0 <= k /\ k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    0 <= i ->
    i <= j ->
    j < Zlength positions ->
    Znth i positions 0 <= Znth j positions 0.
Proof.
  intros positions i j Hadj Hi Hij Hj.
  pose proof
    (streetlight_adjacent_nondecreasing_nat__left_predecessor
       positions i (Z.to_nat (j - i)) Hadj) as Hmono.
  rewrite Z2Nat.id in Hmono by lia.
  replace (i + (j - i)) with j in Hmono by lia.
  apply Hmono; lia.
Qed.
Lemma streetlight_plan_cost_bounds__left_predecessor :
  forall positions powers start left right endpoint cost,
    Zlength positions = Zlength powers ->
    (forall k, 0 <= k < Zlength positions ->
       0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < Zlength powers ->
       1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    StreetlightPlan positions powers start left right endpoint cost ->
    0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost
    Hlength Hpositions Hadj Hpowers Htotal Hplan.
  induction Hplan as
    [Hstart Hsame
    | l r ep c Hl Hstart_in Hr Hchild IH
    | l r ep c Hl Hstart_in Hr Hchild IH].
  - lia.
  - pose proof
      (streetlight_plan_endpoint_bounds__left_predecessor
         positions powers start (l + 1) r ep c Hchild) as Hep.
    pose proof (Hpositions l ltac:(lia)) as Hpos_l.
    pose proof (Hpositions ep ltac:(lia)) as Hpos_ep.
    pose proof
      (streetlight_adjacent_nondecreasing__left_predecessor
         positions l ep Hadj ltac:(lia) ltac:(lia) ltac:(lia)) as Horder.
    pose proof
      (streetlight_remaining_sum_bounds__left_predecessor
         powers (l + 1) (r + 1) ltac:(lia) ltac:(lia) Hpowers) as Hremain.
    nia.
  - pose proof
      (streetlight_plan_endpoint_bounds__left_predecessor
         positions powers start l (r - 1) ep c Hchild) as Hep.
    pose proof (Hpositions ep ltac:(lia)) as Hpos_ep.
    pose proof (Hpositions r ltac:(lia)) as Hpos_r.
    pose proof
      (streetlight_adjacent_nondecreasing__left_predecessor
         positions ep r Hadj ltac:(lia) ltac:(lia) ltac:(lia)) as Horder.
    pose proof
      (streetlight_remaining_sum_bounds__left_predecessor
         powers l r ltac:(lia) ltac:(lia) Hpowers) as Hremain.
    nia.
Qed.
Lemma streetlight_endpoint_minimum_bounds__left_predecessor :
  forall positions powers start left right endpoint answer,
    Zlength positions = Zlength powers ->
    (forall k, 0 <= k < Zlength positions ->
       0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < Zlength powers ->
       1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    StreetlightEndpointMinimum
      positions powers start left right endpoint answer ->
    0 <= answer <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint answer
    Hlength Hpositions Hadj Hpowers Htotal Hminimum.
  unfold StreetlightEndpointMinimum,
    min_value_of_subset, min_object_of_subset in Hminimum.
  destruct Hminimum as [candidate [[Hcandidate Hleast] Heq]].
  subst answer.
  change
    (StreetlightPlan positions powers start left right endpoint candidate)
    in Hcandidate.
  exact
    (streetlight_plan_cost_bounds__left_predecessor
       positions powers start left right endpoint candidate
       Hlength Hpositions Hadj Hpowers Htotal Hcandidate).
Qed.
Lemma streetlight_previous_left_entry_bounds__left_predecessor :
  forall positions powers prefix left_table right_table default_row
    n total start len left inf,
    Zlength positions = n ->
    Zlength powers = n ->
    total = Znth n prefix 0 ->
    total <= 5000 ->
    (forall k, 0 <= k < n ->
       0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n ->
       1 <= Znth k powers 0 <= 100) ->
    0 <= left ->
    left < start ->
    start <= left + len - 1 ->
    left + len - 1 < n ->
    2 <= len ->
    inf = 2147483647 ->
    StreetlightPrefixProgress powers prefix n ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len left ->
    Znth (left + len - 1)
      (Znth (left + 1) left_table default_row) 0 < inf ->
    0 <= Znth (left + len - 1)
           (Znth (left + 1) left_table default_row) 0 <=
      (len - 2) * 40000000.
Proof.
  intros positions powers prefix left_table right_table default_row
    n total start len left inf
    Hpositions_length Hpowers_length Htotal Htotal_bound
    Hpositions Hadj Hpowers Hleft Hleft_start Hstart_right Hright
    Hlen Hinf Hprefix Hprogress Hentry_inf.
  assert (Hsum_total : sum powers = total).
  {
    unfold StreetlightPrefixProgress in Hprefix.
    destruct Hprefix as [_ Hprefix_values].
    specialize (Hprefix_values n ltac:(lia)).
    rewrite (sublist_self powers n ltac:(lia)) in Hprefix_values.
    lia.
  }
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths_done _].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [_ Hintervals]].
  unfold StreetlightTableShape in Hleft_shape.
  destruct Hleft_shape as [Hleft_table_length _].
  assert (Hentry_indep :
    Znth (left + len - 1) (Znth (left + 1) left_table []) 0 =
    Znth (left + len - 1)
      (Znth (left + 1) left_table default_row) 0).
  {
    rewrite
      (Znth_indep left_table (left + 1) [] default_row ltac:(lia)).
    reflexivity.
  }
  assert (Hentry_inf_nil :
    Znth (left + len - 1) (Znth (left + 1) left_table []) 0 < inf).
  { rewrite Hentry_indep. exact Hentry_inf. }
  specialize
    (Hintervals (len - 1) (left + 1) (left + len - 1)
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold StreetlightIntervalCorrect in Hintervals.
  destruct Hintervals as [Hleft_correct _].
  unfold StreetlightLeftEntryCorrect in Hleft_correct.
  destruct Hleft_correct as
    [[Hsingle_left [Hsingle_right Hsingle_value]]
    | [[Hproper_left Hminimum]
      | [Hinf_left [Hinf_right Hinf_value]]]].
  - rewrite <- Hentry_indep, Hsingle_value. lia.
  - pose proof
      (streetlight_endpoint_minimum_bounds__left_predecessor
         positions powers start (left + 1) (left + len - 1) (left + 1)
         (Znth (left + len - 1)
            (Znth (left + 1) left_table []) 0)
         ltac:(lia)
         ltac:(intros; apply Hpositions; lia)
         ltac:(intros; apply Hadj; lia)
         ltac:(intros; apply Hpowers; lia)
         ltac:(lia)
         Hminimum) as Hminimum_bounds.
    replace (left + len - 1 - (left + 1)) with (len - 2)
      in Hminimum_bounds by lia.
    rewrite Hentry_indep in Hminimum_bounds.
    exact Hminimum_bounds.
  - rewrite Hinf_value in Hentry_inf_nil.
    lia.
Qed.
Lemma streetlight_sum_sublist_bounds__left_best_a :
  forall (l : list Z) n lo hi,
    Zlength l = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k l 0 <= 100) ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum (sublist lo hi l) <= sum l.
Proof.
  intros l n lo hi Hlen Hbounds Hlohi Hhin.
  assert (Hnonneg : forall a b,
      0 <= a <= b -> b <= n -> 0 <= sum (sublist a b l)).
  {
    intros a b Hab Hbn.
    assert (Hsegment : forall i,
        0 <= i -> 0 <= Znth i (sublist a b l) 0 <= 100).
    {
      intros i Hi.
      destruct (Z_lt_ge_dec i (b - a)) as [Hin | Hout].
      - rewrite Znth_sublist by lia.
        pose proof (Hbounds (i + a) ltac:(lia)) as Hvalue.
        lia.
      - rewrite Znth_sublist_ge by lia.
        lia.
    }
    pose proof (sum_bound 100 (sublist a b l) Hsegment) as Hsum.
    lia.
  }
  pose proof (Hnonneg lo hi Hlohi Hhin) as Hmiddle.
  pose proof (Hnonneg 0 lo ltac:(lia) ltac:(lia)) as Hprefix.
  pose proof (Hnonneg hi n ltac:(lia) ltac:(lia)) as Hsuffix.
  pose proof (sublist_split 0 n lo l ltac:(lia) ltac:(lia)) as Hsplit0.
  pose proof (sublist_split lo n hi l ltac:(lia) ltac:(lia)) as Hsplit1.
  rewrite Hsplit1 in Hsplit0.
  assert (Hfull : sublist 0 n l = l).
  {
    rewrite <- Hlen.
    pose proof (sublist_app_exact1 l []) as H.
    rewrite app_nil_r in H.
    exact H.
  }
  rewrite Hfull in Hsplit0.
  pose proof (f_equal sum Hsplit0) as Hsum.
  repeat rewrite sum_app in Hsum.
  lia.
Qed.
Lemma streetlight_adjacent_monotone__left_best_a :
  forall (l : list Z) n,
    Zlength l = n ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k l 0 < Znth (k + 1) l 0) ->
    forall i j,
      0 <= i -> i <= j -> j < n -> Znth i l 0 <= Znth j l 0.
Proof.
  intros l n Hlen Hadj i j Hi Hij Hj.
  assert (Hchain : forall d k,
      0 <= k -> k + Z.of_nat d < n ->
      Znth k l 0 <= Znth (k + Z.of_nat d) l 0).
  {
    induction d as [| d IH]; intros k Hk Hbound.
    - replace (k + Z.of_nat 0) with k by (simpl; lia).
      lia.
    - apply Z.le_trans with (Znth (k + Z.of_nat d) l 0).
      + apply IH; [lia |].
        rewrite Nat2Z.inj_succ in Hbound.
        lia.
      + apply Z.lt_le_incl.
        replace (k + Z.of_nat (S d)) with
          ((k + Z.of_nat d) + 1)
          by (rewrite Nat2Z.inj_succ; lia).
        apply Hadj.
        rewrite Nat2Z.inj_succ in Hbound.
        lia.
  }
  specialize (Hchain (Z.to_nat (j - i)) i Hi).
  rewrite Z2Nat.id in Hchain by lia.
  replace (i + (j - i)) with j in Hchain by lia.
  apply Hchain.
  lia.
Qed.
Lemma streetlight_plan_endpoint_bounds__left_best_a :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    left <= endpoint <= right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  destruct Hplan; lia.
Qed.
Lemma streetlight_plan_cost_bounds__left_best_a :
  forall positions powers n start left right endpoint cost,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    StreetlightPlan positions powers start left right endpoint cost ->
    0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers n start left right endpoint cost
    Hposlen Hpowlen Hposbounds Hposstep Hpowbounds Hsum Hplan.
  induction Hplan as
      [Hstart Hstartlen
      | left0 right0 endpoint0 cost0 Hleft Hcover Hright Hprev IH
      | left0 right0 endpoint0 cost0 Hleft Hcover Hright Hprev IH].
  - lia.
  - pose proof
      (streetlight_plan_endpoint_bounds__left_best_a
         positions powers start (left0 + 1) right0 endpoint0 cost0 Hprev)
      as Hendpoint.
    pose proof (Hposbounds left0 ltac:(lia)) as Hposleft.
    pose proof (Hposbounds endpoint0 ltac:(lia)) as Hposendpoint.
    pose proof
      (streetlight_adjacent_monotone__left_best_a
         positions n Hposlen Hposstep
         left0 endpoint0 ltac:(lia) ltac:(lia) ltac:(lia))
      as Hdelta.
    pose proof
      (streetlight_sum_sublist_bounds__left_best_a
         powers n (left0 + 1) (right0 + 1)
         Hpowlen Hpowbounds ltac:(lia) ltac:(lia))
      as Hremain.
    nia.
  - pose proof
      (streetlight_plan_endpoint_bounds__left_best_a
         positions powers start left0 (right0 - 1) endpoint0 cost0 Hprev)
      as Hendpoint.
    pose proof (Hposbounds right0 ltac:(lia)) as Hposright.
    pose proof (Hposbounds endpoint0 ltac:(lia)) as Hposendpoint.
    pose proof
      (streetlight_adjacent_monotone__left_best_a
         positions n Hposlen Hposstep
         endpoint0 right0 ltac:(lia) ltac:(lia) ltac:(lia))
      as Hdelta.
    pose proof
      (streetlight_sum_sublist_bounds__left_best_a
         powers n left0 right0
         Hpowlen Hpowbounds ltac:(lia) ltac:(lia))
      as Hremain.
    nia.
Qed.
Lemma streetlight_right_predecessor_bounds__left_best_a :
  forall positions powers prefix left_table right_table
         (default_row : list Z) n start len left total inf,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    total = Znth n prefix 0 ->
    total <= 5000 ->
    StreetlightPrefixProgress powers prefix n ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len left ->
    0 <= left ->
    left < start ->
    start <= left + len - 1 ->
    left + len - 1 < n ->
    inf = 2147483647 ->
    Znth (left + len - 1)
      (Znth (left + 1) right_table default_row) 0 < inf ->
    0 <= Znth (left + len - 1)
           (Znth (left + 1) right_table default_row) 0 <=
      (len - 2) * 40000000.
Proof.
  intros positions powers prefix left_table right_table default_row
    n start len left total inf
    Hposlen Hpowlen Hposbounds Hposstep Hpowbounds
    Htotal Htotalupper Hprefix Hprogress
    Hleft Hleftstart Hstartright Hrightn Hinf Hfinite.
  assert (Hfull : sublist 0 n powers = powers).
  {
    rewrite <- Hpowlen.
    pose proof (sublist_app_exact1 powers []) as H.
    rewrite app_nil_r in H.
    exact H.
  }
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [_ Hprefix].
  specialize (Hprefix n ltac:(lia)).
  rewrite Hfull in Hprefix.
  assert (Hsumpowers : sum powers <= 5000) by lia.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleftshape [Hrightshape Hdone]].
  pose proof
    (Hdone (len - 1) (left + 1) (left + len - 1)
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Hinter.
  unfold StreetlightTableShape in Hrightshape.
  destruct Hrightshape as [Hrightlen _].
  pose proof
    (Znth_indep right_table (left + 1) default_row [] ltac:(lia))
    as Hroweq.
  rewrite Hroweq in Hfinite |- *.
  unfold StreetlightIntervalCorrect in Hinter.
  destruct Hinter as [_ Hrightcorrect].
  unfold StreetlightRightEntryCorrect in Hrightcorrect.
  destruct Hrightcorrect as
      [[Hsameleft [Hsameright Hvalue]]
      | [[Hstartlt Hminimum]
        | [Hleftlt [Hrightstart Hvalue]]]].
  - rewrite Hvalue.
    lia.
  - unfold StreetlightEndpointMinimum in Hminimum.
    unfold min_value_of_subset, min_object_of_subset in Hminimum.
    destruct Hminimum as [candidate [[Hcandidate _] Hcandidate_value]].
    simpl in Hcandidate_value.
    subst candidate.
    pose proof
      (streetlight_plan_cost_bounds__left_best_a
         positions powers n start (left + 1) (left + len - 1)
         (left + len - 1)
         (Znth (left + len - 1)
            (Znth (left + 1) right_table []) 0)
         Hposlen Hpowlen Hposbounds Hposstep Hpowbounds
         Hsumpowers Hcandidate)
      as Hcost.
    lia.
  - rewrite Hvalue in Hfinite.
    lia.
Qed.
Lemma sum_total_bounds__left_best_b :
  forall (l : list Z),
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 100) ->
    0 <= sum l <= Zlength l * 100.
Proof.
  intros l Hbounds.
  pose proof (sum_bound 100 l) as Hsum.
  specialize (Hsum ltac:(
    intros i Hi;
    destruct (Z_lt_ge_dec i (Zlength l)) as [Hin | Hout];
    [ apply Hbounds; lia
    | unfold Znth;
      rewrite nth_overflow by (rewrite Zlength_correct in Hout; lia);
      lia ])).
  rewrite <- Zlength_correct in Hsum.
  exact Hsum.
Qed.
Lemma sum_sublist_bounds__left_best_b :
  forall (l : list Z) lo hi,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 100) ->
    0 <= sum (sublist lo hi l) <= sum l.
Proof.
  intros l lo hi Hlohi Hhi Hbounds.
  assert (Hnonneg :
    forall a b,
      0 <= a <= b ->
      b <= Zlength l ->
      0 <= sum (sublist a b l)).
  {
    intros a b Hab Hb.
    pose proof (sum_bound 100 (sublist a b l)) as Hsum.
    specialize (Hsum ltac:(
      intros i Hi;
      destruct (Z_lt_ge_dec i (b - a)) as [Hin | Hout];
      [ rewrite Znth_sublist by lia;
        apply Hbounds; lia
      | rewrite Znth_sublist_ge by lia;
        lia ])).
    lia.
  }
  pose proof (Hnonneg lo hi Hlohi Hhi) as Hmiddle.
  pose proof (Hnonneg 0 lo ltac:(lia) ltac:(lia)) as Hprefix.
  pose proof
    (Hnonneg hi (Zlength l) ltac:(lia) ltac:(lia)) as Hsuffix.
  pose proof
    (sublist_split 0 (Zlength l) lo l ltac:(lia) ltac:(lia)) as Hsplit1.
  pose proof
    (sublist_split lo (Zlength l) hi l ltac:(lia) ltac:(lia)) as Hsplit2.
  rewrite Hsplit2 in Hsplit1.
  rewrite (sublist_self l (Zlength l) eq_refl) in Hsplit1.
  pose proof (f_equal sum Hsplit1) as Hsum_decomp.
  repeat rewrite sum_app in Hsum_decomp.
  lia.
Qed.
Lemma adjacent_Znth_le_nat__left_best_b :
  forall (l : list Z) (d : nat) i,
    0 <= i ->
    i + Z.of_nat d < Zlength l ->
    (forall k,
      (0 <= k /\ k + 1 < Zlength l) ->
      Znth k l 0 < Znth (k + 1) l 0) ->
    Znth i l 0 <= Znth (i + Z.of_nat d) l 0.
Proof.
  intros l d.
  induction d as [| d IH]; intros i Hi Hlast Hadj.
  - replace (i + Z.of_nat 0) with i by lia.
    lia.
  - rewrite Nat2Z.inj_succ in *.
    pose proof (IH i Hi ltac:(lia) Hadj) as Hprefix.
    specialize (Hadj (i + Z.of_nat d) ltac:(lia)).
    replace (i + Z.succ (Z.of_nat d)) with (i + Z.of_nat d + 1) by lia.
    lia.
Qed.
Lemma adjacent_Znth_le__left_best_b :
  forall (l : list Z) i j,
    0 <= i ->
    i <= j ->
    j < Zlength l ->
    (forall k,
      (0 <= k /\ k + 1 < Zlength l) ->
      Znth k l 0 < Znth (k + 1) l 0) ->
    Znth i l 0 <= Znth j l 0.
Proof.
  intros l i j Hi Hij Hj Hadj.
  set (d := Z.to_nat (j - i)).
  assert (Hj_eq : j = i + Z.of_nat d).
  {
    unfold d.
    rewrite Z2Nat.id by lia.
    lia.
  }
  rewrite Hj_eq.
  eapply adjacent_Znth_le_nat__left_best_b; eauto.
  lia.
Qed.
Lemma StreetlightPlan_endpoint_bounds__left_best_b :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    left <= endpoint <= right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  induction Hplan; lia.
Qed.
Lemma StreetlightPlan_cost_bounds__left_best_b :
  forall positions powers start left right endpoint cost n,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k,
      (0 <= k /\ k + 1 < n) ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    StreetlightPlan positions powers start left right endpoint cost ->
    0 <= cost /\ cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost n
    Hpositions Hpowers Hn Hpos Hpos_adj Hpower Hplan.
  assert (Hpower_zlength :
    forall k,
      0 <= k < Zlength powers ->
      0 <= Znth k powers 0 <= 100).
  {
    intros k Hk.
    specialize (Hpower k ltac:(lia)).
    lia.
  }
  assert (Hpos_adj_zlength :
    forall k,
      (0 <= k /\ k + 1 < Zlength positions) ->
      Znth k positions 0 < Znth (k + 1) positions 0).
  {
    intros k Hk.
    apply Hpos_adj.
    lia.
  }
  pose proof
    (sum_total_bounds__left_best_b powers Hpower_zlength) as Htotal.
  induction Hplan as
      [Hstart Hsame_length
      |left right previous_endpoint previous_cost
       Hleft Hcontains Hright Hprevious IH
      |left right previous_endpoint previous_cost
       Hleft Hcontains Hright Hprevious IH].
  - lia.
  - pose proof
      (StreetlightPlan_endpoint_bounds__left_best_b
        positions powers start (left + 1) right
        previous_endpoint previous_cost Hprevious) as Hendpoint.
    pose proof (Hpos left ltac:(lia)) as Hpos_left.
    pose proof (Hpos previous_endpoint ltac:(lia)) as Hpos_endpoint.
    pose proof
      (adjacent_Znth_le__left_best_b
        positions left previous_endpoint ltac:(lia) ltac:(lia)
        ltac:(lia) Hpos_adj_zlength) as Hpos_order.
    pose proof
      (sum_sublist_bounds__left_best_b
        powers (left + 1) (right + 1)
        ltac:(lia) ltac:(lia) Hpower_zlength) as Hsublist.
    nia.
  - pose proof
      (StreetlightPlan_endpoint_bounds__left_best_b
        positions powers start left (right - 1)
        previous_endpoint previous_cost Hprevious) as Hendpoint.
    pose proof (Hpos right ltac:(lia)) as Hpos_right.
    pose proof (Hpos previous_endpoint ltac:(lia)) as Hpos_endpoint.
    pose proof
      (adjacent_Znth_le__left_best_b
        positions previous_endpoint right ltac:(lia) ltac:(lia)
        ltac:(lia) Hpos_adj_zlength) as Hpos_order.
    pose proof
      (sum_sublist_bounds__left_best_b
        powers left right ltac:(lia) ltac:(lia) Hpower_zlength) as Hsublist.
    nia.
Qed.
Lemma StreetlightEndpointMinimum_bounds__left_best_b :
  forall positions powers start left right endpoint value n,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k,
      (0 <= k /\ k + 1 < n) ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    StreetlightEndpointMinimum
      positions powers start left right endpoint value ->
    0 <= value /\ value <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint value n
    Hpositions Hpowers Hn Hpos Hpos_adj Hpower Hminimum.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  destruct Hminimum as [cost [[Hplan Hleast] Hcost]].
  simpl in Hcost.
  subst value.
  eapply (StreetlightPlan_cost_bounds__left_best_b
    positions powers start left right endpoint cost n); eauto.
Qed.
Lemma StreetlightLeftProgress_predecessor_right_bounds__left_best_b :
  forall positions powers left_table right_table n start len left
    (default_row : list Z),
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    2 <= len ->
    0 <= left ->
    left < start ->
    start <= left + len - 1 ->
    left + len - 1 < n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k,
      (0 <= k /\ k + 1 < n) ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len left ->
    Znth (left + len - 1)
      (Znth (left + 1) right_table default_row) 0 < 2147483647 ->
    0 <= Znth (left + len - 1)
      (Znth (left + 1) right_table default_row) 0 /\
    Znth (left + len - 1)
      (Znth (left + 1) right_table default_row) 0
      <= (len - 2) * 40000000.
Proof.
  intros positions powers left_table right_table n start len left default_row
    Hpositions Hpowers Hn Hlen Hleft Hleft_start Hstart_right Hright
    Hpos Hpos_adj Hpower Hprogress Hfinite.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths_done Hcurrent].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as
    [Hleft_shape [Hright_shape Hprevious_lengths]].
  specialize
    (Hprevious_lengths
      (len - 1) (left + 1) (left + len - 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold StreetlightIntervalCorrect in Hprevious_lengths.
  destruct Hprevious_lengths as [Hleft_correct Hright_correct].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Hright_length Hrow_lengths].
  assert (Hrow_default :
    Znth (left + 1) right_table default_row =
    Znth (left + 1) right_table []).
  {
    apply Znth_indep.
    rewrite Hright_length.
    lia.
  }
  rewrite Hrow_default in Hfinite |- *.
  unfold StreetlightRightEntryCorrect in Hright_correct.
  destruct Hright_correct as
    [[Hentry_left [Hentry_right Hvalue]]
    | [[Hentry_right Hminimum]
      | [Hentry_left [Hentry_right Hvalue]]]].
  - lia.
  - pose proof
      (StreetlightEndpointMinimum_bounds__left_best_b
        positions powers start (left + 1) (left + len - 1)
        (left + len - 1)
        (Znth (left + len - 1)
          (Znth (left + 1) right_table []) 0)
        n Hpositions Hpowers Hn Hpos Hpos_adj Hpower Hminimum) as Hbounds.
    lia.
  - lia.
Qed.
Lemma streetlight_adjacent_positions_strict__left_compare_a :
  forall (positions : list Z) (n : Z),
    (forall k,
       0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    forall i j,
      0 <= i ->
      i < j ->
      j < n ->
      Znth i positions 0 < Znth j positions 0.
Proof.
  intros positions n Hadj i j Hi Hij Hj.
  assert
    (forall d k,
       0 <= k ->
       k + Z.of_nat (S d) < n ->
       Znth k positions 0 < Znth (k + Z.of_nat (S d)) positions 0)
    as Hchain.
  {
    induction d as [| d IHd]; intros k Hk Hbound.
    - replace (k + Z.of_nat 1) with (k + 1) by (simpl; lia).
      apply Hadj.
      lia.
    - eapply Z.lt_trans.
      + apply IHd; [lia |].
        rewrite Nat2Z.inj_succ in Hbound.
        lia.
      + replace (k + Z.of_nat (S (S d)))
          with ((k + Z.of_nat (S d)) + 1)
          by (rewrite (Nat2Z.inj_succ (S d)); lia).
        apply Hadj.
        rewrite (Nat2Z.inj_succ (S d)) in Hbound.
        lia.
  }
  specialize (Hchain (Z.to_nat (j - i - 1)) i Hi).
  rewrite Nat2Z.inj_succ in Hchain.
  rewrite Z2Nat.id in Hchain by lia.
  replace (i + Z.succ (j - i - 1)) with j in Hchain by lia.
  apply Hchain.
  exact Hj.
Qed.
Lemma streetlight_left_candidate_bounds__left_compare_a :
  forall prev len left_position right_position remain,
    0 <= prev ->
    prev <= (len - 2) * 40000000 ->
    left_position <= right_position ->
    0 <= left_position ->
    right_position <= 8000 ->
    1 <= remain ->
    remain <= 5000 ->
    0 <= prev + (right_position - left_position) * remain /\
    prev + (right_position - left_position) * remain <=
      (len - 1) * 40000000.
Proof.
  intros.
  split; nia.
Qed.
Lemma streetlight_strict_positions_between__left_compare_b :
  forall (positions : list Z) (n i j : Z),
    Zlength positions = n ->
    (forall k,
       0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    0 <= i ->
    i < j ->
    j < n ->
    Znth i positions 0 < Znth j positions 0.
Proof.
  intros positions n i j _ Hadj Hi Hij Hj.
  assert (forall d k,
    0 <= k ->
    k + Z.of_nat (S d) < n ->
    Znth k positions 0 < Znth (k + Z.of_nat (S d)) positions 0)
    as Hchain.
  { induction d as [| d IHd]; intros k Hk Hbound.
    - replace (k + Z.of_nat 1) with (k + 1) by (simpl; lia).
      apply Hadj.
      lia.
    - eapply Z.lt_trans with
        (m := Znth (k + Z.of_nat (S d)) positions 0).
      + apply IHd; try lia.
      + replace (k + Z.of_nat (S (S d)))
          with ((k + Z.of_nat (S d)) + 1)
          by (rewrite (Nat2Z.inj_succ (S d)); lia).
        apply Hadj.
        lia. }
  specialize (Hchain (Z.to_nat (j - i - 1)) i Hi).
  rewrite Nat2Z.inj_succ in Hchain.
  rewrite Z2Nat.id in Hchain by lia.
  replace (i + Z.succ (j - i - 1)) with j in Hchain by lia.
  apply Hchain.
  lia.
Qed.
Lemma streetlight_adjacent_strict_order__left_commit_d :
  forall l,
    (forall k,
      0 <= k /\ k + 1 < Zlength l ->
      Znth k l 0 < Znth (k + 1) l 0) ->
    forall i j,
      0 <= i ->
      i <= j ->
      j < Zlength l ->
      Znth i l 0 <= Znth j l 0.
Proof.
  intros l Hadj i j Hi Hij Hj.
  assert
    (forall d k,
      0 <= k ->
      k + Z.of_nat d < Zlength l ->
      Znth k l 0 <= Znth (k + Z.of_nat d) l 0) as Hchain.
  {
    induction d as [| d IHd]; intros k Hk Hbound.
    - replace (k + Z.of_nat 0) with k by (simpl; lia).
      lia.
    - eapply Z.le_trans with (m := Znth (k + Z.of_nat d) l 0).
      + apply IHd; [lia |].
        rewrite Nat2Z.inj_succ in Hbound.
        lia.
      + replace (k + Z.of_nat (S d)) with
          ((k + Z.of_nat d) + 1) by
          (rewrite Nat2Z.inj_succ; lia).
        specialize (Hadj (k + Z.of_nat d) ltac:(split; lia)).
        lia.
  }
  specialize (Hchain (Z.to_nat (j - i)) i Hi).
  rewrite Z2Nat.id in Hchain by lia.
  replace (i + (j - i)) with j in Hchain by lia.
  apply Hchain.
  lia.
Qed.
Lemma StreetlightPrefixProgress_remainder__right_remain_a :
  forall powers prefix n total left right remain,
    Zlength powers = n ->
    StreetlightPrefixProgress powers prefix n ->
    total = Znth n prefix 0 ->
    remain = total - (Znth (right + 1) prefix 0 -
                      Znth (left + 1) prefix 0) ->
    0 <= left ->
    left < right ->
    right < n ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers).
Proof.
  intros powers prefix n total left right remain Hpowlen Hprefix
    Htotal Hremain Hleft Hlr Hright.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [_ Hprefix].
  pose proof (Hprefix n ltac:(lia)) as Hn.
  pose proof (Hprefix (left + 1) ltac:(lia)) as Hleft_prefix.
  pose proof (Hprefix (right + 1) ltac:(lia)) as Hright_prefix.
  assert (Hfull : sublist 0 n powers = powers).
  { apply sublist_self. lia. }
  assert (Hsplit :
    sublist 0 (right + 1) powers =
      sublist 0 (left + 1) powers ++
      sublist (left + 1) (right + 1) powers).
  { apply sublist_split; lia. }
  rewrite Hfull in Hn.
  rewrite Hsplit, sum_app in Hright_prefix.
  lia.
Qed.
Lemma StreetlightLeftProgress_update_cell__right_remain_a :
  forall positions powers left_table right_table n start len left right best,
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    1 <= len ->
    0 <= left ->
    right = left + len - 1 ->
    right < n ->
    StreetlightLeftProgress positions powers
      (replace_Znth left
        (replace_Znth right best (Znth left left_table []))
        left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table n start len left right best
    Hprogress Hlen Hleft Hright_eq Hright.
  unfold StreetlightLeftProgress in Hprogress |- *.
  destruct Hprogress as [Hdone Hcurrent].
  unfold StreetlightLengthsDone in Hdone |- *.
  destruct Hdone as [Hshape_left [Hshape_right Hshort]].
  destruct Hshape_left as [Htable_len Hrow_len].
  split.
  - split.
    + split.
      * rewrite Zlength_replace_Znth. exact Htable_len.
      * intros row Hrow.
        destruct (Z.eq_dec row left) as [-> | Hne].
        -- rewrite Znth_replace_Znth_Same by lia.
           rewrite Zlength_replace_Znth.
           apply Hrow_len; lia.
        -- rewrite Znth_replace_Znth_Diff by lia.
           apply Hrow_len; lia.
    + split; [exact Hshape_right |].
      intros short_len row col Hshort_len Hcol_eq Hrow_nonneg Hcol_bound
        Hcontains.
      specialize (Hshort short_len row col Hshort_len Hcol_eq Hrow_nonneg
        Hcol_bound Hcontains).
      unfold StreetlightIntervalCorrect in Hshort |- *.
      destruct Hshort as [Hleft_entry Hright_entry].
      split; [| exact Hright_entry].
      destruct (Z.eq_dec row left) as [Hsame | Hdiff].
      * subst row.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Znth_replace_Znth_Diff by
          (pose proof (Hrow_len left ltac:(lia)); lia).
        exact Hleft_entry.
      * rewrite Znth_replace_Znth_Diff by lia.
        exact Hleft_entry.
  - intros row col Hrow Hcol_eq Hcol_bound Hcontains.
    specialize (Hcurrent row col Hrow Hcol_eq Hcol_bound Hcontains).
    unfold StreetlightIntervalCorrect in Hcurrent |- *.
    destruct Hcurrent as [Hleft_entry Hright_entry].
    split; [| exact Hright_entry].
    rewrite Znth_replace_Znth_Diff by lia.
    exact Hleft_entry.
Qed.
Lemma StreetlightPlan_endpoint_boundary__right_remain_a :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; subst; auto.
Qed.
Lemma StreetlightPlan_right_start_endpoint__right_remain_a :
  forall positions powers start left endpoint cost,
    StreetlightPlan positions powers start left start endpoint cost ->
    endpoint = left.
Proof.
  intros positions powers start left endpoint cost Hplan.
  inversion Hplan; subst; lia.
Qed.
Lemma StreetlightEndpointMinimum_start__right_remain_a :
  forall positions powers start,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightEndpointMinimum positions powers start start start start 0.
Proof.
  intros positions powers start Hstart Hlength.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists 0.
  split.
  - split.
    + apply StreetlightPlan_start; assumption.
    + intros cost Hplan.
      inversion Hplan; subst; lia.
  - reflexivity.
Qed.
Lemma Streetlight_sublist_sum_nonnegative__right_remain_a :
  forall powers n lo hi,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum (sublist lo hi powers).
Proof.
  intros powers n lo hi Hlength Hbound Hlo Hhi.
  pose proof (sum_bound 100 (sublist lo hi powers)) as Hsum.
  specialize (Hsum ltac:(
    intros i Hi;
    destruct (Z_lt_ge_dec i (Zlength (sublist lo hi powers)))
      as [Hin | Hout];
    [ rewrite Zlength_sublist in Hin by lia;
      rewrite Znth_sublist by lia;
      specialize (Hbound (i + lo) ltac:(lia));
      lia
    | unfold Znth;
      rewrite nth_overflow by (rewrite Zlength_correct in Hout; lia);
      lia ])).
  lia.
Qed.
Lemma Streetlight_remaining_sum_bounds__right_remain_a :
  forall powers n lo hi,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum powers - sum (sublist lo hi powers) <= 5000.
Proof.
  intros powers n lo hi Hlength Hbound Hsum Hlo Hhi.
  pose proof
    (Streetlight_sublist_sum_nonnegative__right_remain_a
       powers n 0 lo Hlength Hbound ltac:(lia) ltac:(lia))
    as Hbefore.
  pose proof
    (Streetlight_sublist_sum_nonnegative__right_remain_a
       powers n hi n Hlength Hbound ltac:(lia) ltac:(lia))
    as Hafter.
  pose proof
    (Streetlight_sublist_sum_nonnegative__right_remain_a
       powers n lo hi Hlength Hbound Hlo Hhi)
    as Hduring.
  assert (Hdecomp :
    powers = sublist 0 lo powers ++ sublist lo hi powers ++
      sublist hi n powers).
  {
    transitivity (sublist 0 n powers).
    - symmetry. apply sublist_self. lia.
    - rewrite (sublist_split 0 n lo powers) by lia.
      rewrite (sublist_split lo n hi powers) by lia.
      rewrite app_assoc.
      reflexivity.
  }
  assert (Hsum_decomp :
    sum powers = sum (sublist 0 lo powers) +
      sum (sublist lo hi powers) + sum (sublist hi n powers)).
  { rewrite Hdecomp at 1. rewrite !sum_app. lia. }
  lia.
Qed.
Lemma Streetlight_positions_strict__right_remain_a :
  forall positions n,
    (forall k, 0 <= k /\ k + 1 < n ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    forall i j,
      0 <= i ->
      i < j ->
      j < n ->
      Znth i positions 0 < Znth j positions 0.
Proof.
  intros positions n Hadj i j Hi Hij Hj.
  assert (forall d k,
    0 <= k ->
    k + Z.of_nat (S d) < n ->
    Znth k positions 0 < Znth (k + Z.of_nat (S d)) positions 0)
    as KEY.
  {
    induction d as [| d IHd]; intros k Hk Hb.
    - replace (k + Z.of_nat 1) with (k + 1) by (simpl; lia).
      apply Hadj; lia.
    - eapply Z.lt_trans with
        (Znth (k + Z.of_nat (S d)) positions 0).
      + apply IHd; [lia |].
        rewrite (Nat2Z.inj_succ (S d)) in Hb.
        lia.
      + replace (k + Z.of_nat (S (S d))) with
          ((k + Z.of_nat (S d)) + 1)
          by (rewrite (Nat2Z.inj_succ (S d)); lia).
        apply Hadj.
        rewrite (Nat2Z.inj_succ (S d)) in Hb.
        lia.
  }
  specialize (KEY (Z.to_nat (j - i - 1)) i Hi).
  rewrite Nat2Z.inj_succ in KEY.
  rewrite Z2Nat.id in KEY by lia.
  replace (i + Z.succ (j - i - 1)) with j in KEY by lia.
  apply KEY; lia.
Qed.
Lemma StreetlightPlan_bounds__right_remain_a :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    forall n,
      Zlength positions = n ->
      Zlength powers = n ->
      (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
      (forall k, 0 <= k /\ k + 1 < n ->
        Znth k positions 0 < Znth (k + 1) positions 0) ->
      (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
      0 <= sum powers <= 5000 ->
      0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  induction Hplan as
      [Hstart Hsame_length
      |left right endpoint cost Hleft Hspan Hright Hchild IH
      |left right endpoint cost Hleft Hspan Hright Hchild IH];
    intros n Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum.
  - lia.
  - pose proof
      (IH n Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum)
      as Hcost.
    pose proof
      (Streetlight_remaining_sum_bounds__right_remain_a
         powers n (left + 1) (right + 1) Hpowlen Hpowerbound Hsum
         ltac:(lia) ltac:(lia)) as Hremain.
    pose proof
      (StreetlightPlan_endpoint_boundary__right_remain_a
         positions powers start (left + 1) right endpoint cost Hchild)
      as Hendpoint.
    assert (Hdistance :
      0 <= Znth endpoint positions 0 - Znth left positions 0 <= 8000).
    {
      destruct Hendpoint as [-> | ->].
      - pose proof
          (Streetlight_positions_strict__right_remain_a
             positions n Hposstep left (left + 1)
             ltac:(lia) ltac:(lia) ltac:(lia)).
        pose proof (Hposbound left ltac:(lia)).
        pose proof (Hposbound (left + 1) ltac:(lia)).
        lia.
      - pose proof
          (Streetlight_positions_strict__right_remain_a
             positions n Hposstep left right
             ltac:(lia) ltac:(lia) ltac:(lia)).
        pose proof (Hposbound left ltac:(lia)).
        pose proof (Hposbound right ltac:(lia)).
        lia.
    }
    nia.
  - pose proof
      (IH n Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum)
      as Hcost.
    pose proof
      (Streetlight_remaining_sum_bounds__right_remain_a
         powers n left right Hpowlen Hpowerbound Hsum
         ltac:(lia) ltac:(lia)) as Hremain.
    pose proof
      (StreetlightPlan_endpoint_boundary__right_remain_a
         positions powers start left (right - 1) endpoint cost Hchild)
      as Hendpoint.
    assert (Hdistance :
      0 <= Znth right positions 0 - Znth endpoint positions 0 <= 8000).
    {
      destruct Hendpoint as [-> | ->].
      - pose proof
          (Streetlight_positions_strict__right_remain_a
             positions n Hposstep left right
             ltac:(lia) ltac:(lia) ltac:(lia)).
        pose proof (Hposbound left ltac:(lia)).
        pose proof (Hposbound right ltac:(lia)).
        lia.
      - pose proof
          (Streetlight_positions_strict__right_remain_a
             positions n Hposstep (right - 1) right
             ltac:(lia) ltac:(lia) ltac:(lia)).
        pose proof (Hposbound (right - 1) ltac:(lia)).
        pose proof (Hposbound right ltac:(lia)).
        lia.
    }
    nia.
Qed.
Lemma StreetlightEndpointMinimum_bounds__right_remain_a :
  forall positions powers start left right endpoint answer n,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    StreetlightEndpointMinimum positions powers start left right endpoint answer ->
    0 <= answer <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint answer n Hposlen Hpowlen
    Hposbound Hposstep Hpowerbound Hsum Hminimum.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  destruct Hminimum as [cost [[Hplan _] Hanswer]].
  subst answer.
  exact
    (StreetlightPlan_bounds__right_remain_a
       positions powers start left right endpoint cost Hplan n
       Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum).
Qed.
Lemma StreetlightPrefixProgress_total_sum__right_remain_a :
  forall powers prefix n total,
    Zlength powers = n ->
    StreetlightPrefixProgress powers prefix n ->
    total = Znth n prefix 0 ->
    total = sum powers.
Proof.
  intros powers prefix n total Hlength Hprefix Htotal.
  pose proof (Zlength_nonneg powers) as Hnonneg.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [_ Hprefix].
  pose proof (Hprefix n ltac:(lia)) as Hn.
  rewrite (sublist_self powers n ltac:(lia)) in Hn.
  lia.
Qed.
Lemma StreetlightLeftProgress_predecessor_finite__right_remain_a :
  forall positions powers left_table right_table n start len left right
    (default_row : list Z),
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    n <= 50 ->
    2 <= len ->
    0 <= left ->
    left < start ->
    right = left + len - 1 ->
    start <= right ->
    right < n ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    Znth right (Znth (left + 1) left_table default_row) 0 < 2147483647 \/
    Znth right (Znth (left + 1) right_table default_row) 0 < 2147483647.
Proof.
  intros positions powers left_table right_table n start len left right default_row
    Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum Hn Hlen Hleft
    Hleft_start Hright_eq Hstart_right Hright Hprogress.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left [Hshape_right Hintervals]].
  destruct Hshape_left as [Hleft_table_len Hleft_row_len].
  destruct Hshape_right as [Hright_table_len Hright_row_len].
  assert (Hinterval :
    StreetlightIntervalCorrect positions powers left_table right_table start
      (left + 1) right).
  {
    apply (Hintervals (len - 1) (left + 1) right); lia.
  }
  unfold StreetlightIntervalCorrect in Hinterval.
  destruct Hinterval as [Hleft_entry Hright_entry].
  rewrite (Znth_indep left_table (left + 1) [] default_row) in Hleft_entry
    by lia.
  rewrite (Znth_indep right_table (left + 1) [] default_row) in Hright_entry
    by lia.
  assert (Hminimum_finite :
    forall endpoint answer,
      StreetlightEndpointMinimum positions powers start
        (left + 1) right endpoint answer ->
      answer < 2147483647).
  {
    intros endpoint answer Hminimum.
    pose proof
      (StreetlightEndpointMinimum_bounds__right_remain_a
         positions powers start (left + 1) right endpoint answer n
         Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum Hminimum)
      as Hbounds.
    nia.
  }
  unfold StreetlightLeftEntryCorrect in Hleft_entry.
  destruct Hleft_entry as
      [[Hleft_base [Hright_base Hvalue_base]]
      |[[Hleft_strict Hminimum_left]
        |[Hleft_start_eq [Hright_strict Hvalue_inf]]]].
  - left. lia.
  - left. apply (Hminimum_finite (left + 1)). exact Hminimum_left.
  - unfold StreetlightRightEntryCorrect in Hright_entry.
    destruct Hright_entry as
        [[Hleft_base [Hright_base Hvalue_base]]
        |[[Hright_strict' Hminimum_right]
          |[Hleft_strict [Hright_start Hvalue_inf']]]].
    + right. lia.
    + right. apply (Hminimum_finite right). exact Hminimum_right.
    + lia.
Qed.
Lemma StreetlightPlan_extend_left_inv__right_remain_a :
  forall positions powers start left right new_cost,
    left < start ->
    left < right ->
    StreetlightPlan positions powers start left right left new_cost ->
    exists endpoint old_cost,
      StreetlightPlan positions powers start (left + 1) right endpoint old_cost /\
      new_cost =
        old_cost +
        (Znth endpoint positions 0 - Znth left positions 0) *
        (sum powers - sum (sublist (left + 1) (right + 1) powers)).
Proof.
  intros positions powers start left right new_cost Hleft_start Hleft_right
    Hplan.
  inversion Hplan; subst; try lia.
  eauto.
Qed.
Lemma StreetlightLeftEntryCorrect_from_left_candidate__right_remain_a :
  forall positions powers prefix left_table right_table n total start len
    left right remain best (default_row : list Z),
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    StreetlightPrefixProgress powers prefix n ->
    total = Znth n prefix 0 ->
    1 <= total <= 5000 ->
    n <= 50 ->
    2 <= len ->
    0 <= left ->
    left < start ->
    right = left + len - 1 ->
    start <= right ->
    right < n ->
    remain = total -
      (Znth (right + 1) prefix 0 - Znth (left + 1) prefix 0) ->
    1 <= remain <= 5000 ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    Znth right (Znth (left + 1) left_table default_row) 0 < 2147483647 ->
    best =
      Znth right (Znth (left + 1) left_table default_row) 0 +
      (Znth (left + 1) positions 0 - Znth left positions 0) * remain ->
    (Znth right (Znth (left + 1) right_table default_row) 0 < 2147483647 ->
      best <=
        Znth right (Znth (left + 1) right_table default_row) 0 +
        (Znth right positions 0 - Znth left positions 0) * remain) ->
    StreetlightLeftEntryCorrect positions powers start left right best.
Proof.
  intros positions powers prefix left_table right_table n total start len
    left right remain best default_row Hposlen Hpowlen Hposbound Hposstep
    Hpowerbound Hprefix Htotal Htotal_bounds Hn Hlen Hleft Hleft_start
    Hright_eq Hstart_right Hright Hremain Hremain_bounds Hprogress
    Hleft_finite Hbest_left Hbest_right.
  pose proof
    (StreetlightPrefixProgress_total_sum__right_remain_a
       powers prefix n total Hpowlen Hprefix Htotal) as Htotal_sum.
  assert (Hsum : 0 <= sum powers <= 5000) by lia.
  pose proof
    (StreetlightPrefixProgress_remainder__right_remain_a
       powers prefix n total left right remain Hpowlen Hprefix Htotal Hremain
       Hleft ltac:(lia) Hright) as Hremain_sum.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left [Hshape_right Hintervals]].
  destruct Hshape_left as [Hleft_table_len Hleft_row_len].
  destruct Hshape_right as [Hright_table_len Hright_row_len].
  assert (Hinterval :
    StreetlightIntervalCorrect positions powers left_table right_table start
      (left + 1) right).
  {
    apply (Hintervals (len - 1) (left + 1) right); lia.
  }
  unfold StreetlightIntervalCorrect in Hinterval.
  destruct Hinterval as [Hleft_entry Hright_entry].
  rewrite (Znth_indep left_table (left + 1) [] default_row) in Hleft_entry
    by lia.
  rewrite (Znth_indep right_table (left + 1) [] default_row) in Hright_entry
    by lia.
  assert (Hminimum_left :
    StreetlightEndpointMinimum positions powers start (left + 1) right
      (left + 1)
      (Znth right (Znth (left + 1) left_table default_row) 0)).
  {
    unfold StreetlightLeftEntryCorrect in Hleft_entry.
    destruct Hleft_entry as
        [[Hleft_base [Hright_base Hvalue_base]]
        |[[Hleft_strict Hminimum]
          |[Hleft_start_eq [Hright_strict Hvalue_inf]]]].
    - rewrite Hvalue_base, Hleft_base, Hright_base.
      apply StreetlightEndpointMinimum_start__right_remain_a; lia.
    - exact Hminimum.
    - lia.
  }
  assert (Hminimum_right :
    start < right ->
    StreetlightEndpointMinimum positions powers start (left + 1) right
      right (Znth right (Znth (left + 1) right_table default_row) 0)).
  {
    intro Hstart_right_strict.
    unfold StreetlightRightEntryCorrect in Hright_entry.
    destruct Hright_entry as
        [[Hleft_base [Hright_base Hvalue_base]]
        |[[Hright_strict Hminimum]
          |[Hleft_strict [Hright_start Hvalue_inf]]]].
    - lia.
    - exact Hminimum.
    - lia.
  }
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum_left.
  destruct Hminimum_left as
    [left_cost [[Hleft_plan Hleft_least] Hleft_cost_eq]].
  unfold StreetlightLeftEntryCorrect.
  right; left.
  split; [exact Hleft_start |].
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists
    (left_cost +
      (Znth (left + 1) positions 0 - Znth left positions 0) *
      (sum powers - sum (sublist (left + 1) (right + 1) powers))).
  split.
  - split.
    + apply StreetlightPlan_extend_left.
      * exact Hleft.
      * lia.
      * rewrite Hposlen. exact Hright.
      * exact Hleft_plan.
    + intros candidate Hcandidate.
      destruct
        (StreetlightPlan_extend_left_inv__right_remain_a
           positions powers start left right candidate Hleft_start
           ltac:(lia) Hcandidate)
        as [endpoint [old_cost [Hold_plan Hcandidate_eq]]].
      pose proof
        (StreetlightPlan_endpoint_boundary__right_remain_a
           positions powers start (left + 1) right endpoint old_cost
           Hold_plan) as Hendpoint.
      destruct Hendpoint as [Hendpoint_left | Hendpoint_right].
      * subst endpoint.
        specialize (Hleft_least old_cost Hold_plan).
        lia.
      * subst endpoint.
        destruct (Z.eq_dec right start) as [Hright_start | Hright_ne_start].
        -- pose proof Hold_plan as Hold_plan_original.
           rewrite Hright_start in Hold_plan.
           pose proof
             (StreetlightPlan_right_start_endpoint__right_remain_a
                positions powers start (left + 1) start old_cost Hold_plan)
             as Hendpoint.
           rewrite Hright_start, Hendpoint in Hleft_plan.
           rewrite Hendpoint in Hold_plan.
           inversion Hleft_plan; subst; try lia.
           inversion Hold_plan; subst; try lia.
           replace (left + len - 1) with (left + 1) by lia.
           lia.
        -- assert (Hstart_right_strict : start < right) by lia.
           specialize (Hminimum_right Hstart_right_strict).
           unfold StreetlightEndpointMinimum, min_value_of_subset,
             min_object_of_subset in Hminimum_right.
           destruct Hminimum_right as
             [right_cost [[Hright_plan Hright_least] Hright_cost_eq]].
           pose proof
             (StreetlightEndpointMinimum_bounds__right_remain_a
                positions powers start (left + 1) right right
                (Znth right
                   (Znth (left + 1) right_table default_row) 0) n
                Hposlen Hpowlen Hposbound Hposstep Hpowerbound Hsum)
             as Hright_bounds.
           assert (Hright_minimum_original :
             StreetlightEndpointMinimum positions powers start
               (left + 1) right right
               (Znth right
                  (Znth (left + 1) right_table default_row) 0)).
           {
             unfold StreetlightEndpointMinimum, min_value_of_subset,
               min_object_of_subset.
             exists right_cost.
             repeat split; assumption.
           }
           specialize (Hright_bounds Hright_minimum_original).
           specialize (Hbest_right ltac:(nia)).
           specialize (Hright_least old_cost Hold_plan).
           lia.
  - lia.
Qed.
Lemma StreetlightPrefixProgress_remaining__right_remain_b :
  forall powers prefix n total left right remain,
    Zlength powers = n ->
    0 <= left ->
    left <= right ->
    right < n ->
    total = Znth n prefix 0 ->
    remain = total -
      (Znth (right + 1) prefix 0 - Znth (left + 1) prefix 0) ->
    StreetlightPrefixProgress powers prefix n ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers).
Proof.
  intros powers prefix n total left right remain Hpowers Hleft Hlr Hright
    Htotal Hremain Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [_ Hprefix].
  pose proof (Hprefix n ltac:(lia)) as Hn.
  pose proof (Hprefix (left + 1) ltac:(lia)) as Hleft_prefix.
  pose proof (Hprefix (right + 1) ltac:(lia)) as Hright_prefix.
  rewrite (sublist_self powers n (eq_sym Hpowers)) in Hn.
  rewrite (sublist_split 0 (right + 1) (left + 1) powers)
    in Hright_prefix by lia.
  rewrite sum_app in Hright_prefix.
  lia.
Qed.
Lemma StreetlightPlan_endpoint__right_remain_b :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  destruct Hplan; auto.
Qed.
Lemma StreetlightPlan_left_inv__right_remain_b :
  forall positions powers start left right cost,
    left < start ->
    StreetlightPlan positions powers start left right left cost ->
    exists endpoint previous,
      StreetlightPlan positions powers start (left + 1) right endpoint previous /\
      cost = previous +
        (Znth endpoint positions 0 - Znth left positions 0) *
        (sum powers - sum (sublist (left + 1) (right + 1) powers)).
Proof.
  intros positions powers start left right cost Hleft Hplan.
  inversion Hplan; subst; try lia.
  eauto.
Qed.
Lemma StreetlightLeftEntryCorrect_lower__right_remain_b :
  forall positions powers start left right value cost,
    StreetlightLeftEntryCorrect positions powers start left right value ->
    StreetlightPlan positions powers start left right left cost ->
    value <= cost.
Proof.
  intros positions powers start left right value cost Hcorrect Hplan.
  unfold StreetlightLeftEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - inversion Hplan; subst; lia.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [minimum [[Hlegal Hlower] Hvalue]].
    subst value.
    apply Hlower. exact Hplan.
  - inversion Hplan; subst; lia.
Qed.
Lemma StreetlightRightEntryCorrect_lower__right_remain_b :
  forall positions powers start left right value cost,
    StreetlightRightEntryCorrect positions powers start left right value ->
    StreetlightPlan positions powers start left right right cost ->
    value <= cost.
Proof.
  intros positions powers start left right value cost Hcorrect Hplan.
  unfold StreetlightRightEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - inversion Hplan; subst; lia.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [minimum [[Hlegal Hlower] Hvalue]].
    subst value.
    apply Hlower. exact Hplan.
  - inversion Hplan; subst; lia.
Qed.
Lemma StreetlightLeftEntryCorrect_finite_min__right_remain_b :
  forall positions powers start left right value,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightLeftEntryCorrect positions powers start left right value ->
    value < 2147483647 ->
    StreetlightEndpointMinimum positions powers start left right left value.
Proof.
  intros positions powers start left right value Hstart Hlength Hcorrect Hfinite.
  unfold StreetlightLeftEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset.
    exists 0. split.
    + split.
      * constructor; assumption.
      * intros cost Hplan. inversion Hplan; subst; lia.
    + reflexivity.
  - exact Hminimum.
  - lia.
Qed.
Lemma StreetlightRightEntryCorrect_finite_min__right_remain_b :
  forall positions powers start left right value,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightRightEntryCorrect positions powers start left right value ->
    value < 2147483647 ->
    StreetlightEndpointMinimum positions powers start left right right value.
Proof.
  intros positions powers start left right value Hstart Hlength Hcorrect Hfinite.
  unfold StreetlightRightEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset.
    exists 0. split.
    + split.
      * constructor; assumption.
      * intros cost Hplan. inversion Hplan; subst; lia.
    + reflexivity.
  - exact Hminimum.
  - lia.
Qed.
Lemma Znth_adjacent_strict_le__right_remain_b :
  forall (values : list Z) i j,
    0 <= i ->
    i <= j ->
    j < Zlength values ->
    (forall k, 0 <= k /\ k + 1 < Zlength values ->
       Znth k values 0 < Znth (k + 1) values 0) ->
    Znth i values 0 <= Znth j values 0.
Proof.
  intros values i j Hi Hij Hj Hadj.
  remember (Z.to_nat (j - i)) as distance eqn:Hdistance.
  assert (HdistanceZ : Z.of_nat distance = j - i).
  { rewrite Hdistance. rewrite Z2Nat.id; lia. }
  clear Hdistance.
  revert i Hi Hij HdistanceZ.
  induction distance as [|distance IH]; intros i Hi Hij HdistanceZ.
  - simpl in HdistanceZ. replace j with i by lia. lia.
  - assert (Hij' : i + 1 <= j) by (simpl in HdistanceZ; lia).
    assert (Hstep : Znth i values 0 < Znth (i + 1) values 0).
    { apply Hadj. split; lia. }
    assert (HdistanceZ' : Z.of_nat distance = j - (i + 1)).
    { simpl in HdistanceZ. lia. }
    specialize (IH (i + 1) ltac:(lia) Hij' HdistanceZ').
    lia.
Qed.
Lemma StreetlightEndpointMinimum_extend_left__right_remain_b :
  forall positions powers start n len left right remain left_value right_value best,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    2 <= len <= n ->
    0 <= left ->
    left < start <= right ->
    right < n ->
    1 <= remain ->
    (forall k, 0 <= k /\ k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers) ->
    StreetlightLeftEntryCorrect positions powers start (left + 1) right
      left_value ->
    StreetlightRightEntryCorrect positions powers start (left + 1) right
      right_value ->
    best <= (len - 1) * 40000000 ->
    (left_value < 2147483647 ->
       best <= left_value +
         (Znth (left + 1) positions 0 - Znth left positions 0) * remain) ->
    (right_value < 2147483647 ->
       best <= right_value +
         (Znth right positions 0 - Znth left positions 0) * remain) ->
    ((left_value < 2147483647 /\
      best = left_value +
        (Znth (left + 1) positions 0 - Znth left positions 0) * remain) \/
     (right_value < 2147483647 /\
      best = right_value +
        (Znth right positions 0 - Znth left positions 0) * remain)) ->
    StreetlightEndpointMinimum positions powers start left right left best.
Proof.
  intros positions powers start n len left right remain left_value right_value
    best Hpositions Hpowers Hn Hlen Hleft Hstart_right Hright Hremain_pos
    Hadj Hremain Hleft_correct Hright_correct Hbest_bound Hbest_left
    Hbest_right Hselected.
  assert (Hstart : 0 <= start < Zlength positions) by (rewrite Hpositions; lia).
  assert (Hpowers_positions : Zlength powers = Zlength positions) by lia.
  assert (Hbest_finite : best < 2147483647) by nia.
  assert (Hdelta_left :
      0 <= Znth (left + 1) positions 0 - Znth left positions 0).
  { specialize (Hadj left ltac:(split; [lia | rewrite Hpositions; lia])). lia. }
  assert (Hdelta_right :
      0 <= Znth right positions 0 - Znth left positions 0).
  { assert (Hmono := Znth_adjacent_strict_le__right_remain_b
        positions left right Hleft ltac:(lia) ltac:(rewrite Hpositions; lia) Hadj).
    lia. }
  assert (Hcurrent_lower :
      forall cost,
        StreetlightPlan positions powers start left right left cost ->
        best <= cost).
  { intros cost Hplan.
    destruct (StreetlightPlan_left_inv__right_remain_b
      positions powers start left right cost ltac:(lia) Hplan)
      as [endpoint [previous [Hprevious Hcost]]].
    destruct (StreetlightPlan_endpoint__right_remain_b
      positions powers start (left + 1) right endpoint previous Hprevious)
      as [Hendpoint | Hendpoint]; subst endpoint.
    - pose proof (StreetlightLeftEntryCorrect_lower__right_remain_b
        positions powers start (left + 1) right left_value previous
        Hleft_correct Hprevious) as Hminimum_lower.
      destruct (Z_lt_ge_dec left_value 2147483647) as [Hfinite | Hinfinite].
      + specialize (Hbest_left Hfinite). rewrite <- Hremain in Hcost. nia.
      + rewrite <- Hremain in Hcost. nia.
    - pose proof (StreetlightRightEntryCorrect_lower__right_remain_b
        positions powers start (left + 1) right right_value previous
        Hright_correct Hprevious) as Hminimum_lower.
      destruct (Z_lt_ge_dec right_value 2147483647) as [Hfinite | Hinfinite].
      + specialize (Hbest_right Hfinite). rewrite <- Hremain in Hcost. nia.
      + rewrite <- Hremain in Hcost. nia. }
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  destruct Hselected as [[Hfinite Hbest] | [Hfinite Hbest]].
  - pose proof (StreetlightLeftEntryCorrect_finite_min__right_remain_b
      positions powers start (left + 1) right left_value
      Hstart Hpowers_positions Hleft_correct Hfinite) as Hminimum.
    unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [previous [[Hprevious _] Hprevious_value]].
    subst previous.
    exists best. split.
    + split.
      * rewrite Hremain in Hbest. subst best.
        eapply StreetlightPlan_extend_left; eauto; lia.
      * exact Hcurrent_lower.
    + reflexivity.
  - pose proof (StreetlightRightEntryCorrect_finite_min__right_remain_b
      positions powers start (left + 1) right right_value
      Hstart Hpowers_positions Hright_correct Hfinite) as Hminimum.
    unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [previous [[Hprevious _] Hprevious_value]].
    subst previous.
    exists best. split.
    + split.
      * rewrite Hremain in Hbest. subst best.
        eapply StreetlightPlan_extend_left; eauto; lia.
      * exact Hcurrent_lower.
    + reflexivity.
Qed.
Lemma StreetlightTableShape_replace_cell__right_remain_b :
  forall table n row col value default,
    StreetlightTableShape table n ->
    0 <= row < n ->
    0 <= col < n ->
    StreetlightTableShape
      (replace_Znth row
        (replace_Znth col value (Znth row table default)) table) n.
Proof.
  intros table n row col value default Hshape Hrow Hcol.
  unfold StreetlightTableShape in *.
  destruct Hshape as [Hlength Hrows].
  split.
  - rewrite Zlength_replace_Znth. exact Hlength.
  - intros queried Hqueried.
    destruct (Z.eq_dec queried row) as [Heq | Hneq].
    + subst queried.
      rewrite Znth_replace_Znth_Same by (rewrite Hlength; exact Hrow).
      rewrite Zlength_replace_Znth.
      rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      apply Hrows. exact Hrow.
    + rewrite Znth_replace_Znth_Diff;
        try (rewrite Hlength; lia); try congruence.
      apply Hrows. exact Hqueried.
Qed.
Lemma StreetlightTable_replace_cell_same__right_remain_b :
  forall table n row col value default,
    StreetlightTableShape table n ->
    0 <= row < n ->
    0 <= col < n ->
    Znth col
      (Znth row
        (replace_Znth row
          (replace_Znth col value (Znth row table default)) table) []) 0 =
    value.
Proof.
  intros table n row col value default Hshape Hrow Hcol.
  unfold StreetlightTableShape in Hshape.
  destruct Hshape as [Hlength Hrows].
  rewrite Znth_replace_Znth_Same by (rewrite Hlength; exact Hrow).
  rewrite Znth_replace_Znth_Same.
  - reflexivity.
  - rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
    rewrite Hrows; auto.
Qed.
Lemma StreetlightTable_replace_cell_other__right_remain_b :
  forall table n row col queried_row queried_col value default,
    StreetlightTableShape table n ->
    0 <= row < n ->
    0 <= col < n ->
    0 <= queried_row < n ->
    0 <= queried_col < n ->
    (queried_row <> row \/ queried_col <> col) ->
    Znth queried_col
      (Znth queried_row
        (replace_Znth row
          (replace_Znth col value (Znth row table default)) table) []) 0 =
    Znth queried_col (Znth queried_row table []) 0.
Proof.
  intros table n row col queried_row queried_col value default Hshape Hrow Hcol
    Hqueried_row Hqueried_col Hother.
  unfold StreetlightTableShape in Hshape.
  destruct Hshape as [Hlength Hrows].
  destruct (Z.eq_dec queried_row row) as [Heq | Hneq].
  - subst queried_row.
    destruct Hother as [Hcontra | Hcol_neq]; [contradiction |].
    rewrite Znth_replace_Znth_Same by (rewrite Hlength; exact Hrow).
    rewrite Znth_replace_Znth_Diff.
    + rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      reflexivity.
    + rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      rewrite Hrows; auto.
    + rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      rewrite Hrows; auto.
    + congruence.
  - rewrite Znth_replace_Znth_Diff;
      try (rewrite Hlength; lia); try congruence.
Qed.
Lemma StreetlightLeftEndpointReady_store__right_remain_b :
  forall positions powers left_table right_table n start len left right value default,
    1 <= len ->
    0 <= left ->
    left < start ->
    right = left + len - 1 ->
    right < n ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    StreetlightLeftEntryCorrect positions powers start left right value ->
    StreetlightLeftEndpointReady positions powers
      (replace_Znth left
        (replace_Znth right value (Znth left left_table default)) left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table n start len left right value
    default Hlen Hleft Hleft_start Hright Hright_n Hprogress Hentry.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprocessed].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left [Hshape_right Hdone]].
  assert (Hleft_n : 0 <= left < n) by lia.
  assert (Hright_bounds : 0 <= right < n) by lia.
  assert (Hshape_updated :
      StreetlightTableShape
        (replace_Znth left
          (replace_Znth right value (Znth left left_table default)) left_table) n).
  { eapply StreetlightTableShape_replace_cell__right_remain_b; eauto. }
  unfold StreetlightLeftEndpointReady.
  split.
  - unfold StreetlightLeftProgress.
    split.
    + unfold StreetlightLengthsDone.
      split; [exact Hshape_updated |].
      split; [exact Hshape_right |].
      intros old_len old_left old_right Hold_len Hold_right Hold_left
        Hold_right_n Hold_contains.
      specialize (Hdone old_len old_left old_right Hold_len Hold_right Hold_left
        Hold_right_n Hold_contains).
      unfold StreetlightIntervalCorrect in *.
      destruct Hdone as [Hdone_left Hdone_right].
      split; [| exact Hdone_right].
      assert (Hold_left_n : 0 <= old_left < n) by lia.
      assert (Hold_right_bounds : 0 <= old_right < n) by lia.
      assert (Hother : old_left <> left \/ old_right <> right).
      { destruct (Z.eq_dec old_left left) as [Heq | Hneq].
        - right. subst old_left. lia.
        - left. exact Hneq. }
      rewrite (StreetlightTable_replace_cell_other__right_remain_b
        left_table n left right old_left old_right value default Hshape_left
        Hleft_n Hright_bounds Hold_left_n Hold_right_bounds Hother).
      exact Hdone_left.
    + intros old_left old_right Hold_left Hold_right Hold_right_n Hold_contains.
      specialize (Hprocessed old_left old_right Hold_left Hold_right
        Hold_right_n Hold_contains).
      unfold StreetlightIntervalCorrect in *.
      destruct Hprocessed as [Hprocessed_left Hprocessed_right].
      split; [| exact Hprocessed_right].
      assert (Hold_left_n : 0 <= old_left < n) by lia.
      assert (Hold_right_bounds : 0 <= old_right < n) by lia.
      assert (Hother : old_left <> left) by lia.
      rewrite (StreetlightTable_replace_cell_other__right_remain_b
        left_table n left right old_left old_right value default Hshape_left
        Hleft_n Hright_bounds Hold_left_n Hold_right_bounds
        (or_introl Hother)).
      exact Hprocessed_left.
  - replace (left + len - 1) with right by lia.
    rewrite (StreetlightTable_replace_cell_same__right_remain_b
      left_table n left right value default Hshape_left Hleft_n Hright_bounds).
    exact Hentry.
Qed.
Lemma StreetlightLeftEndpointReady_after_best__right_remain_b :
  forall positions powers left_table right_table n start len left right remain best default,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    2 <= len <= n ->
    0 <= left ->
    left < start <= right ->
    right = left + len - 1 ->
    right < n ->
    1 <= remain ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers) ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    best <= (len - 1) * 40000000 ->
    (Znth right (Znth (left + 1) left_table default) 0 < 2147483647 ->
       best <= Znth right (Znth (left + 1) left_table default) 0 +
         (Znth (left + 1) positions 0 - Znth left positions 0) * remain) ->
    (Znth right (Znth (left + 1) right_table default) 0 < 2147483647 ->
       best <= Znth right (Znth (left + 1) right_table default) 0 +
         (Znth right positions 0 - Znth left positions 0) * remain) ->
    ((Znth right (Znth (left + 1) left_table default) 0 < 2147483647 /\
      best = Znth right (Znth (left + 1) left_table default) 0 +
        (Znth (left + 1) positions 0 - Znth left positions 0) * remain) \/
     (Znth right (Znth (left + 1) right_table default) 0 < 2147483647 /\
      best = Znth right (Znth (left + 1) right_table default) 0 +
        (Znth right positions 0 - Znth left positions 0) * remain)) ->
    StreetlightLeftEndpointReady positions powers
      (replace_Znth left
        (replace_Znth right best (Znth left left_table default)) left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table n start len left right remain
    best default Hpositions Hpowers Hn Hlen Hleft Hstart_right Hright Hright_n
    Hremain_pos Hadj Hremain Hprogress Hbest_bound Hbest_left Hbest_right
    Hselected.
  pose proof Hprogress as Hprogress_copy.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left [Hshape_right Hdone]].
  specialize (Hdone (len - 1) (left + 1) right
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold StreetlightIntervalCorrect in Hdone.
  destruct Hdone as [Hleft_correct Hright_correct].
  assert (Hsub_left : 0 <= left + 1 < n) by lia.
  assert (Hleft_default :
      Znth (left + 1) left_table default =
      Znth (left + 1) left_table []).
  { apply Znth_indep. unfold StreetlightTableShape in Hshape_left. lia. }
  assert (Hright_default :
      Znth (left + 1) right_table default =
      Znth (left + 1) right_table []).
  { apply Znth_indep. unfold StreetlightTableShape in Hshape_right. lia. }
  rewrite <- Hleft_default in Hleft_correct.
  rewrite <- Hright_default in Hright_correct.
  assert (Hadj_length :
      forall k, 0 <= k /\ k + 1 < Zlength positions ->
        Znth k positions 0 < Znth (k + 1) positions 0).
  { intros k Hk. apply Hadj. rewrite <- Hpositions. exact Hk. }
  assert (Hendpoint :
      StreetlightEndpointMinimum positions powers start left right left best).
  { eapply StreetlightEndpointMinimum_extend_left__right_remain_b
      with (n := n) (len := len) (remain := remain)
        (left_value := Znth right (Znth (left + 1) left_table default) 0)
        (right_value := Znth right (Znth (left + 1) right_table default) 0);
      eauto. }
  eapply StreetlightLeftEndpointReady_store__right_remain_b.
  - lia.
  - exact Hleft.
  - lia.
  - exact Hright.
  - exact Hright_n.
  - exact Hprogress_copy.
  - unfold StreetlightLeftEntryCorrect.
    right. left. split; [lia | exact Hendpoint].
Qed.
Lemma StreetlightPrefixProgress_remaining__right_remain_c :
  forall powers prefix n total left right remain,
    Zlength powers = n ->
    0 <= left ->
    left <= right ->
    right < n ->
    total = Znth n prefix 0 ->
    remain = total -
      (Znth (right + 1) prefix 0 - Znth (left + 1) prefix 0) ->
    StreetlightPrefixProgress powers prefix n ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers).
Proof.
  intros powers prefix n total left right remain Hpowers Hleft Hlr Hright
    Htotal Hremain Hprefix.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [_ Hprefix].
  pose proof (Hprefix n ltac:(lia)) as Hn.
  pose proof (Hprefix (left + 1) ltac:(lia)) as Hleft_prefix.
  pose proof (Hprefix (right + 1) ltac:(lia)) as Hright_prefix.
  rewrite (sublist_self powers n (eq_sym Hpowers)) in Hn.
  rewrite (sublist_split 0 (right + 1) (left + 1) powers)
    in Hright_prefix by lia.
  rewrite sum_app in Hright_prefix.
  lia.
Qed.
Lemma StreetlightPlan_endpoint__right_remain_c :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  destruct Hplan; auto.
Qed.
Lemma StreetlightPlan_left_inv__right_remain_c :
  forall positions powers start left right cost,
    left < start ->
    StreetlightPlan positions powers start left right left cost ->
    exists endpoint previous,
      StreetlightPlan positions powers start (left + 1) right endpoint previous /\
      cost = previous +
        (Znth endpoint positions 0 - Znth left positions 0) *
        (sum powers - sum (sublist (left + 1) (right + 1) powers)).
Proof.
  intros positions powers start left right cost Hleft Hplan.
  inversion Hplan; subst; try lia.
  eauto.
Qed.
Lemma StreetlightLeftEntryCorrect_lower__right_remain_c :
  forall positions powers start left right value cost,
    StreetlightLeftEntryCorrect positions powers start left right value ->
    StreetlightPlan positions powers start left right left cost ->
    value <= cost.
Proof.
  intros positions powers start left right value cost Hcorrect Hplan.
  unfold StreetlightLeftEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - inversion Hplan; subst; lia.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [minimum [[Hlegal Hlower] Hvalue]].
    subst value.
    apply Hlower. exact Hplan.
  - inversion Hplan; subst; lia.
Qed.
Lemma StreetlightRightEntryCorrect_lower__right_remain_c :
  forall positions powers start left right value cost,
    StreetlightRightEntryCorrect positions powers start left right value ->
    StreetlightPlan positions powers start left right right cost ->
    value <= cost.
Proof.
  intros positions powers start left right value cost Hcorrect Hplan.
  unfold StreetlightRightEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - inversion Hplan; subst; lia.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [minimum [[Hlegal Hlower] Hvalue]].
    subst value.
    apply Hlower. exact Hplan.
  - inversion Hplan; subst; lia.
Qed.
Lemma StreetlightLeftEntryCorrect_finite_min__right_remain_c :
  forall positions powers start left right value,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightLeftEntryCorrect positions powers start left right value ->
    value < 2147483647 ->
    StreetlightEndpointMinimum positions powers start left right left value.
Proof.
  intros positions powers start left right value Hstart Hlength Hcorrect Hfinite.
  unfold StreetlightLeftEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset.
    exists 0. split.
    + split.
      * constructor; assumption.
      * intros cost Hplan. inversion Hplan; subst; lia.
    + reflexivity.
  - exact Hminimum.
  - lia.
Qed.
Lemma StreetlightRightEntryCorrect_finite_min__right_remain_c :
  forall positions powers start left right value,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightRightEntryCorrect positions powers start left right value ->
    value < 2147483647 ->
    StreetlightEndpointMinimum positions powers start left right right value.
Proof.
  intros positions powers start left right value Hstart Hlength Hcorrect Hfinite.
  unfold StreetlightRightEntryCorrect in Hcorrect.
  destruct Hcorrect as [[? [? ?]] | [[? Hminimum] | [? [? ?]]]]; subst.
  - unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset.
    exists 0. split.
    + split.
      * constructor; assumption.
      * intros cost Hplan. inversion Hplan; subst; lia.
    + reflexivity.
  - exact Hminimum.
  - lia.
Qed.
Lemma Znth_adjacent_strict_le__right_remain_c :
  forall (values : list Z) i j,
    0 <= i ->
    i <= j ->
    j < Zlength values ->
    (forall k, 0 <= k /\ k + 1 < Zlength values ->
       Znth k values 0 < Znth (k + 1) values 0) ->
    Znth i values 0 <= Znth j values 0.
Proof.
  intros values i j Hi Hij Hj Hadj.
  remember (Z.to_nat (j - i)) as distance eqn:Hdistance.
  assert (HdistanceZ : Z.of_nat distance = j - i).
  { rewrite Hdistance. rewrite Z2Nat.id; lia. }
  clear Hdistance.
  revert i Hi Hij HdistanceZ.
  induction distance as [|distance IH]; intros i Hi Hij HdistanceZ.
  - simpl in HdistanceZ. replace j with i by lia. lia.
  - assert (Hij' : i + 1 <= j) by (simpl in HdistanceZ; lia).
    assert (Hstep : Znth i values 0 < Znth (i + 1) values 0).
    { apply Hadj. split; lia. }
    assert (HdistanceZ' : Z.of_nat distance = j - (i + 1)).
    { simpl in HdistanceZ. lia. }
    specialize (IH (i + 1) ltac:(lia) Hij' HdistanceZ').
    lia.
Qed.
Lemma StreetlightEndpointMinimum_extend_left__right_remain_c :
  forall positions powers start n len left right remain left_value right_value best,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    2 <= len <= n ->
    0 <= left ->
    left < start <= right ->
    right < n ->
    1 <= remain ->
    (forall k, 0 <= k /\ k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers) ->
    StreetlightLeftEntryCorrect positions powers start (left + 1) right
      left_value ->
    StreetlightRightEntryCorrect positions powers start (left + 1) right
      right_value ->
    best <= (len - 1) * 40000000 ->
    (left_value < 2147483647 ->
       best <= left_value +
         (Znth (left + 1) positions 0 - Znth left positions 0) * remain) ->
    (right_value < 2147483647 ->
       best <= right_value +
         (Znth right positions 0 - Znth left positions 0) * remain) ->
    ((left_value < 2147483647 /\
      best = left_value +
        (Znth (left + 1) positions 0 - Znth left positions 0) * remain) \/
     (right_value < 2147483647 /\
      best = right_value +
        (Znth right positions 0 - Znth left positions 0) * remain)) ->
    StreetlightEndpointMinimum positions powers start left right left best.
Proof.
  intros positions powers start n len left right remain left_value right_value
    best Hpositions Hpowers Hn Hlen Hleft Hstart_right Hright Hremain_pos
    Hadj Hremain Hleft_correct Hright_correct Hbest_bound Hbest_left
    Hbest_right Hselected.
  assert (Hstart : 0 <= start < Zlength positions) by (rewrite Hpositions; lia).
  assert (Hpowers_positions : Zlength powers = Zlength positions) by lia.
  assert (Hbest_finite : best < 2147483647) by nia.
  assert (Hdelta_left :
      0 <= Znth (left + 1) positions 0 - Znth left positions 0).
  { specialize (Hadj left ltac:(split; [lia | rewrite Hpositions; lia])). lia. }
  assert (Hdelta_right :
      0 <= Znth right positions 0 - Znth left positions 0).
  { assert (Hmono := Znth_adjacent_strict_le__right_remain_c
        positions left right Hleft ltac:(lia) ltac:(rewrite Hpositions; lia) Hadj).
    lia. }
  assert (Hcurrent_lower :
      forall cost,
        StreetlightPlan positions powers start left right left cost ->
        best <= cost).
  { intros cost Hplan.
    destruct (StreetlightPlan_left_inv__right_remain_c
      positions powers start left right cost ltac:(lia) Hplan)
      as [endpoint [previous [Hprevious Hcost]]].
    destruct (StreetlightPlan_endpoint__right_remain_c
      positions powers start (left + 1) right endpoint previous Hprevious)
      as [Hendpoint | Hendpoint]; subst endpoint.
    - pose proof (StreetlightLeftEntryCorrect_lower__right_remain_c
        positions powers start (left + 1) right left_value previous
        Hleft_correct Hprevious) as Hminimum_lower.
      destruct (Z_lt_ge_dec left_value 2147483647) as [Hfinite | Hinfinite].
      + specialize (Hbest_left Hfinite). rewrite <- Hremain in Hcost. nia.
      + rewrite <- Hremain in Hcost. nia.
    - pose proof (StreetlightRightEntryCorrect_lower__right_remain_c
        positions powers start (left + 1) right right_value previous
        Hright_correct Hprevious) as Hminimum_lower.
      destruct (Z_lt_ge_dec right_value 2147483647) as [Hfinite | Hinfinite].
      + specialize (Hbest_right Hfinite). rewrite <- Hremain in Hcost. nia.
      + rewrite <- Hremain in Hcost. nia. }
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  destruct Hselected as [[Hfinite Hbest] | [Hfinite Hbest]].
  - pose proof (StreetlightLeftEntryCorrect_finite_min__right_remain_c
      positions powers start (left + 1) right left_value
      Hstart Hpowers_positions Hleft_correct Hfinite) as Hminimum.
    unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [previous [[Hprevious _] Hprevious_value]].
    subst previous.
    exists best. split.
    + split.
      * rewrite Hremain in Hbest. subst best.
        eapply StreetlightPlan_extend_left; eauto; lia.
      * exact Hcurrent_lower.
    + reflexivity.
  - pose proof (StreetlightRightEntryCorrect_finite_min__right_remain_c
      positions powers start (left + 1) right right_value
      Hstart Hpowers_positions Hright_correct Hfinite) as Hminimum.
    unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset in Hminimum.
    destruct Hminimum as [previous [[Hprevious _] Hprevious_value]].
    subst previous.
    exists best. split.
    + split.
      * rewrite Hremain in Hbest. subst best.
        eapply StreetlightPlan_extend_left; eauto; lia.
      * exact Hcurrent_lower.
    + reflexivity.
Qed.
Lemma StreetlightTableShape_replace_cell__right_remain_c :
  forall table n row col value default,
    StreetlightTableShape table n ->
    0 <= row < n ->
    0 <= col < n ->
    StreetlightTableShape
      (replace_Znth row
        (replace_Znth col value (Znth row table default)) table) n.
Proof.
  intros table n row col value default Hshape Hrow Hcol.
  unfold StreetlightTableShape in *.
  destruct Hshape as [Hlength Hrows].
  split.
  - rewrite Zlength_replace_Znth. exact Hlength.
  - intros queried Hqueried.
    destruct (Z.eq_dec queried row) as [Heq | Hneq].
    + subst queried.
      rewrite Znth_replace_Znth_Same by (rewrite Hlength; exact Hrow).
      rewrite Zlength_replace_Znth.
      rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      apply Hrows. exact Hrow.
    + rewrite Znth_replace_Znth_Diff;
        try (rewrite Hlength; lia); try congruence.
      apply Hrows. exact Hqueried.
Qed.
Lemma StreetlightTable_replace_cell_same__right_remain_c :
  forall table n row col value default,
    StreetlightTableShape table n ->
    0 <= row < n ->
    0 <= col < n ->
    Znth col
      (Znth row
        (replace_Znth row
          (replace_Znth col value (Znth row table default)) table) []) 0 =
    value.
Proof.
  intros table n row col value default Hshape Hrow Hcol.
  unfold StreetlightTableShape in Hshape.
  destruct Hshape as [Hlength Hrows].
  rewrite Znth_replace_Znth_Same by (rewrite Hlength; exact Hrow).
  rewrite Znth_replace_Znth_Same.
  - reflexivity.
  - rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
    rewrite Hrows; auto.
Qed.
Lemma StreetlightTable_replace_cell_other__right_remain_c :
  forall table n row col queried_row queried_col value default,
    StreetlightTableShape table n ->
    0 <= row < n ->
    0 <= col < n ->
    0 <= queried_row < n ->
    0 <= queried_col < n ->
    (queried_row <> row \/ queried_col <> col) ->
    Znth queried_col
      (Znth queried_row
        (replace_Znth row
          (replace_Znth col value (Znth row table default)) table) []) 0 =
    Znth queried_col (Znth queried_row table []) 0.
Proof.
  intros table n row col queried_row queried_col value default Hshape Hrow Hcol
    Hqueried_row Hqueried_col Hother.
  unfold StreetlightTableShape in Hshape.
  destruct Hshape as [Hlength Hrows].
  destruct (Z.eq_dec queried_row row) as [Heq | Hneq].
  - subst queried_row.
    destruct Hother as [Hcontra | Hcol_neq]; [contradiction |].
    rewrite Znth_replace_Znth_Same by (rewrite Hlength; exact Hrow).
    rewrite Znth_replace_Znth_Diff.
    + rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      reflexivity.
    + rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      rewrite Hrows; auto.
    + rewrite (Znth_indep table row default []) by (rewrite Hlength; exact Hrow).
      rewrite Hrows; auto.
    + congruence.
  - rewrite Znth_replace_Znth_Diff;
      try (rewrite Hlength; lia); try congruence.
Qed.
Lemma StreetlightLeftEndpointReady_store__right_remain_c :
  forall positions powers left_table right_table n start len left right value default,
    1 <= len ->
    0 <= left ->
    left < start ->
    right = left + len - 1 ->
    right < n ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    StreetlightLeftEntryCorrect positions powers start left right value ->
    StreetlightLeftEndpointReady positions powers
      (replace_Znth left
        (replace_Znth right value (Znth left left_table default)) left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table n start len left right value
    default Hlen Hleft Hleft_start Hright Hright_n Hprogress Hentry.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprocessed].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left [Hshape_right Hdone]].
  assert (Hleft_n : 0 <= left < n) by lia.
  assert (Hright_bounds : 0 <= right < n) by lia.
  assert (Hshape_updated :
      StreetlightTableShape
        (replace_Znth left
          (replace_Znth right value (Znth left left_table default)) left_table) n).
  { eapply StreetlightTableShape_replace_cell__right_remain_c; eauto. }
  unfold StreetlightLeftEndpointReady.
  split.
  - unfold StreetlightLeftProgress.
    split.
    + unfold StreetlightLengthsDone.
      split; [exact Hshape_updated |].
      split; [exact Hshape_right |].
      intros old_len old_left old_right Hold_len Hold_right Hold_left
        Hold_right_n Hold_contains.
      specialize (Hdone old_len old_left old_right Hold_len Hold_right Hold_left
        Hold_right_n Hold_contains).
      unfold StreetlightIntervalCorrect in *.
      destruct Hdone as [Hdone_left Hdone_right].
      split; [| exact Hdone_right].
      assert (Hold_left_n : 0 <= old_left < n) by lia.
      assert (Hold_right_bounds : 0 <= old_right < n) by lia.
      assert (Hother : old_left <> left \/ old_right <> right).
      { destruct (Z.eq_dec old_left left) as [Heq | Hneq].
        - right. subst old_left. lia.
        - left. exact Hneq. }
      rewrite (StreetlightTable_replace_cell_other__right_remain_c
        left_table n left right old_left old_right value default Hshape_left
        Hleft_n Hright_bounds Hold_left_n Hold_right_bounds Hother).
      exact Hdone_left.
    + intros old_left old_right Hold_left Hold_right Hold_right_n Hold_contains.
      specialize (Hprocessed old_left old_right Hold_left Hold_right
        Hold_right_n Hold_contains).
      unfold StreetlightIntervalCorrect in *.
      destruct Hprocessed as [Hprocessed_left Hprocessed_right].
      split; [| exact Hprocessed_right].
      assert (Hold_left_n : 0 <= old_left < n) by lia.
      assert (Hold_right_bounds : 0 <= old_right < n) by lia.
      assert (Hother : old_left <> left) by lia.
      rewrite (StreetlightTable_replace_cell_other__right_remain_c
        left_table n left right old_left old_right value default Hshape_left
        Hleft_n Hright_bounds Hold_left_n Hold_right_bounds
        (or_introl Hother)).
      exact Hprocessed_left.
  - replace (left + len - 1) with right by lia.
    rewrite (StreetlightTable_replace_cell_same__right_remain_c
      left_table n left right value default Hshape_left Hleft_n Hright_bounds).
    exact Hentry.
Qed.
Lemma streetlight_left_endpoint_minimum_extend__right_remain_c :
  forall positions powers left_table right_table n start len left right remain best default,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    2 <= len <= n ->
    0 <= left ->
    left < start <= right ->
    right = left + len - 1 ->
    right < n ->
    1 <= remain ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers) ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    best <= (len - 1) * 40000000 ->
    (Znth right (Znth (left + 1) left_table default) 0 < 2147483647 ->
       best <= Znth right (Znth (left + 1) left_table default) 0 +
         (Znth (left + 1) positions 0 - Znth left positions 0) * remain) ->
    (Znth right (Znth (left + 1) right_table default) 0 < 2147483647 ->
       best <= Znth right (Znth (left + 1) right_table default) 0 +
         (Znth right positions 0 - Znth left positions 0) * remain) ->
    ((Znth right (Znth (left + 1) left_table default) 0 < 2147483647 /\
      best = Znth right (Znth (left + 1) left_table default) 0 +
        (Znth (left + 1) positions 0 - Znth left positions 0) * remain) \/
     (Znth right (Znth (left + 1) right_table default) 0 < 2147483647 /\
      best = Znth right (Znth (left + 1) right_table default) 0 +
        (Znth right positions 0 - Znth left positions 0) * remain)) ->
    StreetlightLeftEndpointReady positions powers
      (replace_Znth left
        (replace_Znth right best (Znth left left_table default)) left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table n start len left right remain
    best default Hpositions Hpowers Hn Hlen Hleft Hstart_right Hright Hright_n
    Hremain_pos Hadj Hremain Hprogress Hbest_bound Hbest_left Hbest_right
    Hselected.
  pose proof Hprogress as Hprogress_copy.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hshape_left [Hshape_right Hdone]].
  specialize (Hdone (len - 1) (left + 1) right
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold StreetlightIntervalCorrect in Hdone.
  destruct Hdone as [Hleft_correct Hright_correct].
  assert (Hsub_left : 0 <= left + 1 < n) by lia.
  assert (Hleft_default :
      Znth (left + 1) left_table default =
      Znth (left + 1) left_table []).
  { apply Znth_indep. unfold StreetlightTableShape in Hshape_left. lia. }
  assert (Hright_default :
      Znth (left + 1) right_table default =
      Znth (left + 1) right_table []).
  { apply Znth_indep. unfold StreetlightTableShape in Hshape_right. lia. }
  rewrite <- Hleft_default in Hleft_correct.
  rewrite <- Hright_default in Hright_correct.
  assert (Hadj_length :
      forall k, 0 <= k /\ k + 1 < Zlength positions ->
        Znth k positions 0 < Znth (k + 1) positions 0).
  { intros k Hk. apply Hadj. rewrite <- Hpositions. exact Hk. }
  assert (Hendpoint :
      StreetlightEndpointMinimum positions powers start left right left best).
  { eapply StreetlightEndpointMinimum_extend_left__right_remain_c
      with (n := n) (len := len) (remain := remain)
        (left_value := Znth right (Znth (left + 1) left_table default) 0)
        (right_value := Znth right (Znth (left + 1) right_table default) 0);
      eauto. }
  eapply StreetlightLeftEndpointReady_store__right_remain_c.
  - lia.
  - exact Hleft.
  - lia.
  - exact Hright.
  - exact Hright_n.
  - exact Hprogress_copy.
  - unfold StreetlightLeftEntryCorrect.
    right. left. split; [lia | exact Hendpoint].
Qed.
Lemma streetlight_prefix_interval_sum__right_remain_d :
  forall powers prefix n lo hi,
    StreetlightPrefixProgress powers prefix n ->
    Zlength powers = n ->
    0 <= lo <= hi ->
    hi <= n ->
    Znth hi prefix 0 - Znth lo prefix 0 =
      sum (sublist lo hi powers).
Proof.
  intros powers prefix n lo hi [_ Hprefix] Hpowers Hlo Hhi.
  rewrite Hprefix by lia.
  rewrite Hprefix by lia.
  rewrite (sublist_split 0 hi lo powers) by lia.
  rewrite sum_app.
  lia.
Qed.
Lemma streetlight_plan_endpoint_boundary__right_remain_d :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; subst; auto.
Qed.
Lemma streetlight_right_entry_finite_min__right_remain_d :
  forall positions powers start left right value inf,
    inf = 2147483647 ->
    value < inf ->
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    left <= start <= right ->
    StreetlightRightEntryCorrect
      positions powers start left right value ->
    StreetlightEndpointMinimum
      positions powers start left right right value.
Proof.
  intros positions powers start left right value inf
    Hinf Hvalue Hstart Hlength Hbounds Hentry.
  unfold StreetlightRightEntryCorrect in Hentry.
  destruct Hentry as
    [[Hleft [Hright Hzero]] |
     [[Hright Hminimum] |
      [Hleft [Hright Hsentinel]]]].
  - subst left right value.
    unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset.
    exists 0.
    split; [split | reflexivity].
    + constructor; assumption.
    + intros candidate Hplan.
      inversion Hplan; subst; lia.
  - exact Hminimum.
  - subst value inf. lia.
Qed.
Lemma streetlight_left_plan_decompose__right_remain_d :
  forall positions powers start left right candidate,
    left < start ->
    StreetlightPlan positions powers start left right left candidate ->
    exists endpoint cost,
      StreetlightPlan positions powers start
        (left + 1) right endpoint cost /\
      candidate =
        cost +
        (Znth endpoint positions 0 - Znth left positions 0) *
        (sum powers - sum (sublist (left + 1) (right + 1) powers)).
Proof.
  intros positions powers start left right candidate Hleft Hplan.
  inversion Hplan; subst; try lia.
  eauto.
Qed.
Lemma streetlight_right_candidate_left_entry__right_remain_d :
  forall positions powers prefix left_table right_table
         n start len left right total remain best inf default_row,
    inf = 2147483647 ->
    Zlength positions = n ->
    Zlength powers = n ->
    0 <= start < n ->
    2 <= len <= n ->
    0 <= left < start ->
    right = left + len - 1 ->
    start <= right < n ->
    1 <= remain ->
    total = Znth n prefix 0 ->
    remain = total -
      (Znth (right + 1) prefix 0 - Znth (left + 1) prefix 0) ->
    best =
      Znth right (Znth (left + 1) right_table default_row) 0 +
      (Znth right positions 0 - Znth left positions 0) * remain ->
    Znth right (Znth (left + 1) right_table default_row) 0 < inf ->
    best < inf ->
    (inf <= Znth right (Znth (left + 1) left_table default_row) 0 \/
     best <
       Znth right (Znth (left + 1) left_table default_row) 0 +
       (Znth (left + 1) positions 0 - Znth left positions 0) * remain) ->
    (forall k,
      0 <= k /\ k + 1 < n ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    StreetlightPrefixProgress powers prefix n ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len left ->
    StreetlightLeftEntryCorrect positions powers start left right best.
Proof.
  intros positions powers prefix left_table right_table
    n start len left right total remain best inf default_row
    Hinf Hpositions_len Hpowers_len Hstart Hlen Hleft Hright
    Hright_bounds Hremain_pos Htotal Hremain Hbest Hright_value_inf
    Hbest_inf Hwin
    Hpositions Hprefix Hprogress.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hcurrent].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hdone]].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  specialize (Hdone (len - 1) (left + 1) right
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct Hdone as [Hleft_entry Hright_entry].
  assert (Hleft_row :
    Znth (left + 1) left_table default_row =
    Znth (left + 1) left_table []) by
    (apply Znth_indep; rewrite Hleft_table_len; lia).
  assert (Hright_row :
    Znth (left + 1) right_table default_row =
    Znth (left + 1) right_table []) by
    (apply Znth_indep; rewrite Hright_table_len; lia).
  rewrite Hleft_row in Hwin.
  rewrite Hright_row in Hbest.
  rewrite Hright_row in Hright_value_inf.
  set (left_value :=
    Znth right (Znth (left + 1) left_table []) 0) in *.
  set (right_value :=
    Znth right (Znth (left + 1) right_table []) 0) in *.
  assert (Hright_min :
    StreetlightEndpointMinimum positions powers start
      (left + 1) right right right_value).
  {
    eapply streetlight_right_entry_finite_min__right_remain_d.
    - exact Hinf.
    - exact Hright_value_inf.
    - rewrite Hpositions_len. exact Hstart.
    - lia.
    - lia.
    - exact Hright_entry.
  }
  assert (Htotal_sum : total = sum powers).
  {
    unfold StreetlightPrefixProgress in Hprefix.
    destruct Hprefix as [Hprefix_len Hprefix_values].
    pose proof (Hprefix_values n ltac:(lia)) as Hprefix_n.
    rewrite (sublist_self powers n) in Hprefix_n by lia.
    lia.
  }
  assert (Hinterval_sum :
    Znth (right + 1) prefix 0 - Znth (left + 1) prefix 0 =
      sum (sublist (left + 1) (right + 1) powers)).
  {
    eapply streetlight_prefix_interval_sum__right_remain_d;
      try eassumption; lia.
  }
  assert (Hremain_sum :
    remain = sum powers -
      sum (sublist (left + 1) (right + 1) powers)) by lia.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hright_min.
  destruct Hright_min as
    [right_cost [[Hright_plan Hright_least] Hright_value]].
  cbn in Hright_value.
  subst right_cost.
  assert (Hcandidate_plan :
    StreetlightPlan positions powers start left right left best).
  {
    rewrite Hbest, Hremain_sum.
    eapply StreetlightPlan_extend_left
      with (endpoint := right) (cost := right_value);
      try lia.
    exact Hright_plan.
  }
  unfold StreetlightLeftEntryCorrect.
  right; left; split; [lia |].
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists best.
  split; [split | reflexivity].
  - exact Hcandidate_plan.
  - intros candidate Hcandidate.
    destruct (streetlight_left_plan_decompose__right_remain_d
      positions powers start left right candidate ltac:(lia) Hcandidate)
      as [endpoint [cost [Hprevious Hcandidate_cost]]].
    destruct (streetlight_plan_endpoint_boundary__right_remain_d
      positions powers start (left + 1) right endpoint cost Hprevious)
      as [Hendpoint | Hendpoint].
    + subst endpoint.
      unfold StreetlightLeftEntryCorrect in Hleft_entry.
      destruct Hleft_entry as
        [[Hold_left [Hold_right Hleft_value]] |
         [[Hold_left Hleft_min] |
          [Hold_left [Hold_right Hleft_value]]]].
      * subst left_value.
        assert (left + 1 = right) by lia.
        rewrite H in Hprevious, Hcandidate_cost, Hright_least,
          Hremain_sum.
        specialize (Hright_least cost Hprevious).
        cbn in Hright_least.
        rewrite <- Hremain_sum in Hcandidate_cost.
        lia.
      * unfold StreetlightEndpointMinimum, min_value_of_subset,
          min_object_of_subset in Hleft_min.
        destruct Hleft_min as
          [left_cost [[Hleft_plan Hleft_least] Hleft_value]].
        cbn in Hleft_value.
        subst left_cost.
        specialize (Hleft_least cost Hprevious).
        cbn in Hleft_least.
        pose proof (Hpositions left ltac:(lia)) as Hposition_step.
        rewrite <- Hremain_sum in Hcandidate_cost.
        destruct Hwin as [Hleft_inf | Hstrict]; nia.
      * subst left_value.
        inversion Hprevious; subst; lia.
    + subst endpoint.
      specialize (Hright_least cost Hprevious).
      cbn in Hright_least.
      rewrite <- Hremain_sum in Hcandidate_cost.
      lia.
Qed.
Lemma streetlight_right_candidate_left_store__right_remain_d :
  forall positions powers left_table right_table
         n start len left right best default_row,
    right = left + len - 1 ->
    1 <= len ->
    0 <= left ->
    right < n ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len left ->
    StreetlightLeftEntryCorrect
      positions powers start left right best ->
    StreetlightLeftEndpointReady
      positions powers
      (replace_Znth left
        (replace_Znth right best (Znth left left_table default_row))
        left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table
    n start len left right best default_row
    Hright Hlen Hleft Hright_bound Hprogress Hentry.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hcurrent].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hdone]].
  destruct Hleft_shape as [Htable_len Hrow_len].
  assert (Hrow_default :
    Znth left left_table default_row = Znth left left_table []) by
    (apply Znth_indep; rewrite Htable_len; lia).
  set (row' :=
    replace_Znth right best (Znth left left_table default_row)).
  set (table' := replace_Znth left row' left_table).
  assert (Htable_shape : StreetlightTableShape table' n).
  {
    unfold StreetlightTableShape.
    split.
    - unfold table'. rewrite Zlength_replace_Znth. exact Htable_len.
    - intros row Hrow.
      destruct (Z.eq_dec row left) as [Heq | Hneq].
      + subst row.
        unfold table'.
        rewrite Znth_replace_Znth_Same by (rewrite Htable_len; lia).
        unfold row'.
        rewrite Zlength_replace_Znth, Hrow_default.
        apply Hrow_len; lia.
      + unfold table'.
        rewrite Znth_replace_Znth_Diff.
        * apply Hrow_len; lia.
        * rewrite Htable_len; lia.
        * rewrite Htable_len; lia.
        * congruence.
  }
  assert (Hlengths_done :
    StreetlightLengthsDone
      positions powers table' right_table n start len).
  {
    unfold StreetlightLengthsDone.
    split; [exact Htable_shape |].
    split; [exact Hright_shape |].
    intros old_len old_left old_right
      Hold_len Hold_right Hold_left Hold_right_bound Hold_start.
    specialize (Hdone old_len old_left old_right
      Hold_len Hold_right Hold_left Hold_right_bound Hold_start).
    unfold StreetlightIntervalCorrect in Hdone |- *.
    destruct Hdone as [Hdone_left Hdone_right].
    split; [|exact Hdone_right].
    assert (Hcell :
      Znth old_right (Znth old_left table' []) 0 =
      Znth old_right (Znth old_left left_table []) 0).
    {
      destruct (Z.eq_dec old_left left) as [Heq | Hneq].
      - subst old_left.
        unfold table'.
        rewrite Znth_replace_Znth_Same by (rewrite Htable_len; lia).
        unfold row'. rewrite Hrow_default.
        rewrite Znth_replace_Znth_Diff.
        * reflexivity.
        * rewrite Hrow_len by lia; lia.
        * rewrite Hrow_len by lia; lia.
        * lia.
      - unfold table'.
        rewrite Znth_replace_Znth_Diff.
        * reflexivity.
        * rewrite Htable_len; lia.
        * rewrite Htable_len; lia.
        * congruence.
    }
    rewrite Hcell. exact Hdone_left.
  }
  assert (Hleft_progress :
    StreetlightLeftProgress
      positions powers table' right_table n start len left).
  {
    unfold StreetlightLeftProgress.
    split; [exact Hlengths_done |].
    intros old_left old_right
      Hold_left Hold_right Hold_right_bound Hold_start.
    specialize (Hcurrent old_left old_right
      Hold_left Hold_right Hold_right_bound Hold_start).
    unfold StreetlightIntervalCorrect in Hcurrent |- *.
    destruct Hcurrent as [Hcurrent_left Hcurrent_right].
    split; [|exact Hcurrent_right].
    unfold table'.
    rewrite Znth_replace_Znth_Diff.
    - exact Hcurrent_left.
    - rewrite Htable_len; lia.
    - rewrite Htable_len; lia.
    - lia.
  }
  unfold StreetlightLeftEndpointReady.
  split; [exact Hleft_progress |].
  replace (left + len - 1) with right by lia.
  change (StreetlightLeftEntryCorrect positions powers start left right
    (Znth right (Znth left table' []) 0)).
  unfold table'.
  rewrite Znth_replace_Znth_Same by (rewrite Htable_len; lia).
  unfold row'.
  rewrite Znth_replace_Znth_Same by
    (rewrite Hrow_default; rewrite Hrow_len by lia; lia).
  exact Hentry.
Qed.
Lemma StreetlightLeftProgress_replace_current__right_remain_e :
  forall positions powers left_table right_table n start len left right value
    default_row,
    0 <= left < n ->
    0 <= right < n ->
    right = left + len - 1 ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    StreetlightLeftProgress positions powers
      (replace_Znth left
        (replace_Znth right value (Znth left left_table default_row))
        left_table)
      right_table n start len left.
Proof.
  intros positions powers left_table right_table n start len left right value
    default_row Hleft Hright Hright_eq Hprogress.
  unfold StreetlightLeftProgress in *.
  destruct Hprogress as [Hdone Hcurrent].
  unfold StreetlightLengthsDone in *.
  destruct Hdone as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape.
  destruct Hleft_shape as [Htable_len Hrow_len].
  split.
  - split.
    + unfold StreetlightTableShape.
      split.
      * rewrite Zlength_replace_Znth.
        exact Htable_len.
      * intros row Hrow.
        destruct (Z.eq_dec row left) as [Hsame | Hdiff].
        -- subst row.
           rewrite Znth_replace_Znth_Same by lia.
           rewrite Zlength_replace_Znth.
           rewrite (Znth_indep left_table left default_row nil) by lia.
           apply Hrow_len; lia.
        -- rewrite Znth_replace_Znth_Diff by lia.
           apply Hrow_len; lia.
    + split.
      * exact Hright_shape.
      * intros len0 left0 right0 Hlen0 Hright0_eq Hleft0 Hright0
          Hcontains.
        specialize (Hdone len0 left0 right0 Hlen0 Hright0_eq Hleft0
          Hright0 Hcontains).
        unfold StreetlightIntervalCorrect in *.
        destruct Hdone as [Hleft_entry Hright_entry].
        split.
        -- assert (Hcell :
             Znth right0
               (Znth left0
                 (replace_Znth left
                   (replace_Znth right value
                     (Znth left left_table default_row))
                   left_table) nil) 0 =
             Znth right0 (Znth left0 left_table nil) 0).
           { destruct (Z.eq_dec left0 left) as [Hsame | Hdiff].
             - subst left0.
               rewrite Znth_replace_Znth_Same by lia.
               rewrite (Znth_replace_Znth_Diff 0
                 (Znth left left_table default_row) right right0 value).
               + rewrite (Znth_indep left_table left default_row nil) by lia.
                 reflexivity.
               + rewrite (Znth_indep left_table left default_row nil) by lia.
                 rewrite Hrow_len by lia.
                 lia.
               + rewrite (Znth_indep left_table left default_row nil) by lia.
                 rewrite Hrow_len by lia.
                 lia.
               + lia.
             - rewrite Znth_replace_Znth_Diff by lia.
               reflexivity. }
           rewrite Hcell.
           exact Hleft_entry.
        -- exact Hright_entry.
  - intros left0 right0 Hleft0 Hright0_eq Hright0 Hcontains.
    specialize (Hcurrent left0 right0 Hleft0 Hright0_eq Hright0 Hcontains).
    unfold StreetlightIntervalCorrect in *.
    destruct Hcurrent as [Hleft_entry Hright_entry].
    split.
    + assert (Hdiff : left <> left0) by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      exact Hleft_entry.
    + exact Hright_entry.
Qed.
Lemma StreetlightPlan_endpoint_boundary__right_remain_e :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; subst; auto.
Qed.
Lemma StreetlightEndpointMinimum_singleton__right_remain_e :
  forall positions powers start,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightEndpointMinimum positions powers start start start start 0.
Proof.
  intros positions powers start Hstart Hlength.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists 0.
  split.
  - split.
    + constructor; auto.
    + intros cost Hplan.
      inversion Hplan; subst; lia.
  - reflexivity.
Qed.
Lemma StreetlightLeftEntryCorrect_right_choice__right_remain_e :
  forall positions powers prefix left_table right_table n start len left right
    total remain best default_row,
    Zlength positions = n ->
    Zlength powers = n ->
    0 <= left < start ->
    right = left + len - 1 ->
    start <= right < n ->
    2 <= len ->
    total = Znth n prefix 0 ->
    remain = total - (Znth (right + 1) prefix 0 -
      Znth (left + 1) prefix 0) ->
    Znth right (Znth (left + 1) right_table default_row) 0 < 2147483647 ->
    Znth right (Znth (left + 1) right_table default_row) 0 +
        (Znth right positions 0 - Znth left positions 0) * remain <
      Znth right (Znth (left + 1) left_table default_row) 0 +
        (Znth (left + 1) positions 0 - Znth left positions 0) * remain ->
    best = Znth right (Znth (left + 1) right_table default_row) 0 +
      (Znth right positions 0 - Znth left positions 0) * remain ->
    StreetlightPrefixProgress powers prefix n ->
    StreetlightLeftProgress positions powers left_table right_table
      n start len left ->
    StreetlightLeftEntryCorrect positions powers start left right best.
Proof.
  intros positions powers prefix left_table right_table n start len left right
    total remain best default_row Hpositions Hpowers Hleft Hright_eq Hright
    Hlen Htotal Hremain Hright_finite Hchoice Hbest Hprefix Hprogress.
  assert (Hremain_sum :
    remain = sum powers - sum (sublist (left + 1) (right + 1) powers)).
  { unfold StreetlightPrefixProgress in Hprefix.
    destruct Hprefix as [_ Hprefix].
    pose proof (Hprefix n ltac:(lia)) as Hprefix_n.
    pose proof (Hprefix (left + 1) ltac:(lia)) as Hprefix_left.
    pose proof (Hprefix (right + 1) ltac:(lia)) as Hprefix_right.
    rewrite (sublist_self powers n ltac:(lia)) in Hprefix_n.
    rewrite (sublist_split 0 (right + 1) (left + 1) powers)
      in Hprefix_right by lia.
    rewrite sum_app in Hprefix_right.
    lia. }
  pose proof Hprogress as Hprogress_parts.
  unfold StreetlightLeftProgress in Hprogress_parts.
  destruct Hprogress_parts as [Hdone _].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len _].
  destruct Hright_shape as [Hright_table_len _].
  pose proof (Hdone (len - 1) (left + 1) right
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hinterval.
  unfold StreetlightIntervalCorrect in Hinterval.
  destruct Hinterval as [Hleft_entry Hright_entry].
  rewrite (Znth_indep left_table (left + 1) nil default_row)
    in Hleft_entry by lia.
  rewrite (Znth_indep right_table (left + 1) nil default_row)
    in Hright_entry by lia.
  assert (Hright_min :
    StreetlightEndpointMinimum positions powers start (left + 1) right right
      (Znth right (Znth (left + 1) right_table default_row) 0)).
  { unfold StreetlightRightEntryCorrect in Hright_entry.
    destruct Hright_entry as
      [[Hsub_left [Hsub_right Hzero]] |
       [[Hstart_right Hmin] | [Hsub_left [Hsub_right Hinf]]]].
    - rewrite Hzero.
      replace (left + 1) with start by lia.
      replace right with start by lia.
      apply StreetlightEndpointMinimum_singleton__right_remain_e; lia.
    - exact Hmin.
    - lia. }
  unfold StreetlightLeftEntryCorrect.
  right; left.
  split; [lia|].
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hright_min |- *.
  destruct Hright_min as
    [right_cost [[Hright_plan Hright_lower] Hright_cost]].
  subst right_cost.
  exists best.
  split.
  - split.
    + rewrite Hbest, Hremain_sum.
      eapply StreetlightPlan_extend_left; eauto; lia.
    + intros cost Hplan.
      inversion Hplan; subst; try lia.
      pose proof
        (StreetlightPlan_endpoint_boundary__right_remain_e
          positions powers start (left + 1) (left + len - 1)
          endpoint cost0 H2)
        as Hendpoint.
      destruct Hendpoint as [Hendpoint | Hendpoint].
      * subst endpoint.
        assert (Hleft_le :
          Znth (left + len - 1)
            (Znth (left + 1) left_table default_row) 0 <=
          cost0).
        { unfold StreetlightLeftEntryCorrect in Hleft_entry.
          destruct Hleft_entry as
            [[Hsub_left [Hsub_right Hzero]] |
             [[Hleft_start Hmin] | [Hsub_left [Hstart_right Hinf]]]].
          - rewrite Hzero.
            inversion H2; subst; lia.
          - unfold StreetlightEndpointMinimum, min_value_of_subset,
              min_object_of_subset in Hmin.
            destruct Hmin as [left_cost [[_ Hlower] Hleft_cost]].
            specialize (Hlower cost0 H2).
            lia.
          - inversion H2; subst; lia. }
        rewrite Hremain_sum.
        lia.
      * subst endpoint.
        specialize (Hright_lower cost0 H2).
        rewrite Hremain_sum.
        lia.
  - reflexivity.
Qed.
Lemma streetlight_prefix_remaining_bounds__right_first :
  forall powers prefix n left right total,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    StreetlightPrefixProgress powers prefix n ->
    total = Znth n prefix 0 ->
    0 <= left ->
    left <= right ->
    right < n ->
    total <= 5000 ->
    1 <= total - (Znth right prefix 0 - Znth left prefix 0) <= 5000.
Proof.
  intros powers prefix n left right total Hlength Hpower Hprogress Htotal
    Hleft Hleft_right Hright Htotal_upper.
  assert (Hsum_nonnegative :
    forall lo hi,
      0 <= lo <= hi ->
      hi <= n ->
      0 <= sum (sublist lo hi powers)).
  {
    intros lo hi Hlohi Hhi.
    pose proof (sum_bound 100 (sublist lo hi powers)) as Hbound.
    assert (Hentries :
      forall i, 0 <= i ->
        0 <= Znth i (sublist lo hi powers) 0 <= 100).
    {
      intros i Hi.
      destruct (Z_lt_ge_dec i (hi - lo)) as [Hinside | Houtside].
      - rewrite Znth_sublist by lia.
        specialize (Hpower (i + lo) ltac:(lia)).
        lia.
      - rewrite Znth_sublist_ge by lia.
        lia.
    }
    specialize (Hbound Hentries).
    lia.
  }
  destruct Hprogress as [_ Hprefix].
  pose proof (Hprefix left ltac:(lia)) as Hprefix_left.
  pose proof (Hprefix right ltac:(lia)) as Hprefix_right.
  pose proof (Hprefix n ltac:(lia)) as Hprefix_n.
  pose proof (sublist_split 0 right left powers ltac:(lia) ltac:(lia))
    as Hsplit_left_right.
  pose proof (sublist_split 0 n right powers ltac:(lia) ltac:(lia))
    as Hsplit_right_n.
  pose proof
    (sublist_split right n (right + 1) powers ltac:(lia) ltac:(lia))
    as Hsplit_first_right.
  rewrite (sublist_single 0 right powers) in Hsplit_first_right by lia.
  pose proof (Hsum_nonnegative 0 left ltac:(lia) ltac:(lia))
    as Hsum_left.
  pose proof (Hsum_nonnegative left right ltac:(lia) ltac:(lia))
    as Hsum_middle.
  pose proof (Hsum_nonnegative (right + 1) n ltac:(lia) ltac:(lia))
    as Hsum_after_right.
  pose proof (Hpower right ltac:(lia)) as Hpower_right.
  pose proof (f_equal sum Hsplit_left_right) as Hsum_split_left_right.
  pose proof (f_equal sum Hsplit_right_n) as Hsum_split_right_n.
  pose proof (f_equal sum Hsplit_first_right) as Hsum_split_first_right.
  rewrite sum_app in Hsum_split_left_right.
  rewrite sum_app in Hsum_split_right_n.
  rewrite sum_app in Hsum_split_first_right.
  simpl in Hsum_split_first_right.
  rewrite Hprefix_left, Hprefix_right, Hprefix_n in *.
  lia.
Qed.
Lemma adjacent_Znth_le__right_second :
  forall (l : list Z),
    (forall i,
       0 <= i ->
       i + 1 < Zlength l ->
       Znth i l 0 <= Znth (i + 1) l 0) ->
    forall i j,
      0 <= i ->
      i <= j ->
      j < Zlength l ->
      Znth i l 0 <= Znth j l 0.
Proof.
  intros l Hadj i j Hi Hij Hj.
  assert (forall d k,
             0 <= k ->
             k + Z.of_nat d < Zlength l ->
             Znth k l 0 <= Znth (k + Z.of_nat d) l 0) as KEY.
  {
    induction d as [| d IHd]; intros k Hk Hb.
    - replace (k + Z.of_nat 0) with k by (simpl; lia).
      lia.
    - eapply Z.le_trans with (Znth (k + Z.of_nat d) l 0).
      + apply IHd; [lia |].
        rewrite Nat2Z.inj_succ in Hb.
        lia.
      + replace (k + Z.of_nat (S d))
          with ((k + Z.of_nat d) + 1)
          by (rewrite Nat2Z.inj_succ; lia).
        apply Hadj; [lia |].
        rewrite Nat2Z.inj_succ in Hb.
        lia.
  }
  specialize (KEY (Z.to_nat (j - i)) i Hi).
  rewrite Z2Nat.id in KEY by lia.
  replace (i + (j - i)) with j in KEY by lia.
  apply KEY.
  lia.
Qed.
Lemma sum_sublist_nonnegative__right_second :
  forall (l : list Z) lo hi b,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    0 <= b ->
    (forall i,
       0 <= i < Zlength l ->
       0 <= Znth i l 0 <= b) ->
    0 <= sum (sublist lo hi l).
Proof.
  intros l lo hi b Hlohi Hhi Hb Hrange.
  assert (Hlocal :
            forall i,
              0 <= i ->
              0 <= Znth i (sublist lo hi l) 0 <= b).
  {
    intros i Hi.
    destruct (Z_lt_ge_dec i (hi - lo)) as [Hin | Hout].
    - rewrite Znth_sublist by lia.
      apply Hrange.
      lia.
    - rewrite Znth_sublist_ge by lia.
      lia.
  }
  pose proof (sum_bound b (sublist lo hi l) Hlocal) as Hsum.
  lia.
Qed.
Lemma sum_sublist_bounds__right_second :
  forall (l : list Z) lo hi b,
    0 <= lo <= hi ->
    hi <= Zlength l ->
    0 <= b ->
    (forall i,
       0 <= i < Zlength l ->
       0 <= Znth i l 0 <= b) ->
    0 <= sum (sublist lo hi l) <= sum l.
Proof.
  intros l lo hi b Hlohi Hhi Hb Hrange.
  pose proof
    (sum_sublist_nonnegative__right_second
       l lo hi b Hlohi Hhi Hb Hrange) as Hmiddle.
  pose proof
    (sum_sublist_nonnegative__right_second
       l 0 lo b ltac:(lia) ltac:(lia) Hb Hrange) as Hprefix.
  pose proof
    (sum_sublist_nonnegative__right_second
       l hi (Zlength l) b ltac:(lia) ltac:(lia) Hb Hrange) as Hsuffix.
  assert (Hparts :
            l =
              sublist 0 lo l ++
              sublist lo hi l ++
              sublist hi (Zlength l) l).
  {
    pose proof
      (sublist_split 0 (Zlength l) lo l ltac:(lia) ltac:(lia))
      as Hsplit.
    rewrite (sublist_split lo (Zlength l) hi l) in Hsplit by lia.
    rewrite (sublist_self l (Zlength l) eq_refl) in Hsplit.
    exact Hsplit.
  }
  pose proof (f_equal sum Hparts) as Hsum_parts.
  rewrite !sum_app in Hsum_parts.
  lia.
Qed.
Lemma StreetlightPlan_bounds__right_second :
  forall positions powers start left right endpoint cost n,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k,
       0 <= k < n ->
       0 <= Znth k positions 0 <= 8000) ->
    (forall i j,
       0 <= i ->
       i <= j ->
       j < n ->
       Znth i positions 0 <= Znth j positions 0) ->
    (forall k,
       0 <= k < n ->
       0 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    StreetlightPlan positions powers start
      left right endpoint cost ->
    left <= endpoint <= right /\
    0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost n
    Hpositions_len Hpowers_len Hpositions_bound Hpositions_order
    Hpowers_bound Hpowers_sum Hplan.
  induction Hplan as
      [Hstart_bounds Hsame_length
      | left0 right0 endpoint0 cost0 Hleft0 Hbetween0 Hright0
        Hprevious IH
      | left0 right0 endpoint0 cost0 Hleft0 Hbetween0 Hright0
        Hprevious IH].
  - split; lia.
  - destruct IH as [IHendpoint IHcost].
    assert (Hleft_position :
              0 <= Znth left0 positions 0 <= 8000).
    {
      apply Hpositions_bound.
      lia.
    }
    assert (Hendpoint_position :
              0 <= Znth endpoint0 positions 0 <= 8000).
    {
      apply Hpositions_bound.
      lia.
    }
    assert (Hposition_order :
              Znth left0 positions 0 <= Znth endpoint0 positions 0).
    {
      apply Hpositions_order; lia.
    }
    pose proof
      (sum_sublist_bounds__right_second
         powers (left0 + 1) (right0 + 1) 100
         ltac:(lia) ltac:(lia) ltac:(lia)
         ltac:(intros k Hk; apply Hpowers_bound; lia))
      as Hsegment.
    assert (Hremaining :
              0 <=
                sum powers -
                sum (sublist (left0 + 1) (right0 + 1) powers)
              <= 5000) by lia.
    assert (Hdistance :
              0 <=
                Znth endpoint0 positions 0 - Znth left0 positions 0
              <= 8000) by lia.
    assert (Hstep :
              0 <=
                (Znth endpoint0 positions 0 - Znth left0 positions 0) *
                (sum powers -
                 sum (sublist (left0 + 1) (right0 + 1) powers))
              <= 40000000) by nia.
    split.
    + lia.
    + nia.
  - destruct IH as [IHendpoint IHcost].
    assert (Hright_position :
              0 <= Znth right0 positions 0 <= 8000).
    {
      apply Hpositions_bound.
      lia.
    }
    assert (Hendpoint_position :
              0 <= Znth endpoint0 positions 0 <= 8000).
    {
      apply Hpositions_bound.
      lia.
    }
    assert (Hposition_order :
              Znth endpoint0 positions 0 <= Znth right0 positions 0).
    {
      apply Hpositions_order; lia.
    }
    pose proof
      (sum_sublist_bounds__right_second
         powers left0 right0 100
         ltac:(lia) ltac:(lia) ltac:(lia)
         ltac:(intros k Hk; apply Hpowers_bound; lia))
      as Hsegment.
    assert (Hremaining :
              0 <= sum powers - sum (sublist left0 right0 powers)
              <= 5000) by lia.
    assert (Hdistance :
              0 <=
                Znth right0 positions 0 - Znth endpoint0 positions 0
              <= 8000) by lia.
    assert (Hstep :
              0 <=
                (Znth right0 positions 0 - Znth endpoint0 positions 0) *
                (sum powers - sum (sublist left0 right0 powers))
              <= 40000000) by nia.
    split.
    + lia.
    + nia.
Qed.
Lemma StreetlightEndpointMinimum_bounds__right_second :
  forall positions powers start left right endpoint value n,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k,
       0 <= k < n ->
       0 <= Znth k positions 0 <= 8000) ->
    (forall i j,
       0 <= i ->
       i <= j ->
       j < n ->
       Znth i positions 0 <= Znth j positions 0) ->
    (forall k,
       0 <= k < n ->
       0 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    StreetlightEndpointMinimum
      positions powers start left right endpoint value ->
    0 <= value <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint value n
    Hpositions_len Hpowers_len Hpositions_bound Hpositions_order
    Hpowers_bound Hpowers_sum Hminimum.
  unfold StreetlightEndpointMinimum,
    min_value_of_subset, min_object_of_subset in Hminimum.
  simpl in Hminimum.
  destruct Hminimum as [chosen [[Hplan Hleast] Hchosen]].
  subst value.
  pose proof
    (StreetlightPlan_bounds__right_second
       positions powers start left right endpoint chosen n
       Hpositions_len Hpowers_len Hpositions_bound Hpositions_order
       Hpowers_bound Hpowers_sum Hplan) as Hbounds.
  tauto.
Qed.
Lemma streetlight_right_predecessor_bounds__right_second :
  forall positions powers prefix left_table right_table
         (default : list Z)
         n start len left right total inf,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k,
       0 <= k < n ->
       0 <= Znth k positions 0 <= 8000) ->
    (forall k,
       0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k,
       0 <= k < n ->
       1 <= Znth k powers 0 <= 100) ->
    StreetlightPrefixProgress powers prefix n ->
    total = Znth n prefix 0 ->
    1 <= total <= 5000 ->
    inf = 2147483647 ->
    2 <= len ->
    0 <= left ->
    left <= start ->
    right = left + len - 1 ->
    right > start ->
    right < n ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    Znth (right - 1) (Znth left left_table default) 0 < inf ->
    0 <= Znth (right - 1) (Znth left left_table default) 0 <=
      (len - 2) * 40000000.
Proof.
  intros positions powers prefix left_table right_table default
    n start len left right total inf
    Hpositions_len Hpowers_len Hpositions_bound Hpositions_adjacent
    Hpowers_bound Hprefix Htotal Htotal_bounds Hinf_value Hlen Hleft
    Hleft_start Hright Hright_start Hright_n Hready Hvalue_inf.
  assert (Hpositions_order :
            forall i j,
              0 <= i ->
              i <= j ->
              j < n ->
              Znth i positions 0 <= Znth j positions 0).
  {
    intros i j Hi Hij Hj.
    pose proof (adjacent_Znth_le__right_second positions) as Hchain.
    apply Hchain.
    - intros k Hk Hnext.
      apply Z.lt_le_incl.
      apply Hpositions_adjacent.
      rewrite Hpositions_len in Hnext.
      lia.
    - exact Hi.
    - exact Hij.
    - rewrite Hpositions_len.
      exact Hj.
  }
  assert (Hpowers_bound0 :
            forall k,
              0 <= k < n ->
              0 <= Znth k powers 0 <= 100).
  {
    intros k Hk.
    specialize (Hpowers_bound k Hk).
    lia.
  }
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [Hprefix_len Hprefix_values].
  specialize (Hprefix_values n ltac:(lia)).
  assert (Hfull_sublist : sublist 0 n powers = powers).
  {
    apply sublist_self.
    lia.
  }
  rewrite Hfull_sublist in Hprefix_values.
  assert (Hpowers_sum : 0 <= sum powers <= 5000) by lia.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hcurrent].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hlengths_done Hleft_progress].
  unfold StreetlightLengthsDone in Hlengths_done.
  destruct Hlengths_done as
    [Hleft_shape [Hright_shape Hcompleted_lengths]].
  unfold StreetlightTableShape in Hleft_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_rows].
  assert (Hrow_default :
            Znth left left_table default = Znth left left_table []).
  {
    apply Znth_indep.
    lia.
  }
  rewrite Hrow_default in Hvalue_inf |- *.
  assert (Hprevious_interval :
            StreetlightIntervalCorrect
              positions powers left_table right_table
              start left (right - 1)).
  {
    apply (Hcompleted_lengths (len - 1) left (right - 1)); lia.
  }
  unfold StreetlightIntervalCorrect in Hprevious_interval.
  destruct Hprevious_interval as [Hleft_correct Hright_correct].
  unfold StreetlightLeftEntryCorrect in Hleft_correct.
  destruct Hleft_correct as
    [[Hleft_eq [Hright_eq Hzero]] |
     [[Hleft_lt Hminimum] |
      [Hleft_eq [Hstart_lt Hinf]]]].
  - lia.
  - pose proof
      (StreetlightEndpointMinimum_bounds__right_second
         positions powers start left (right - 1) left
         (Znth (right - 1) (Znth left left_table []) 0) n
         Hpositions_len Hpowers_len Hpositions_bound Hpositions_order
         Hpowers_bound0 Hpowers_sum Hminimum) as Hminimum_bounds.
    lia.
  - lia.
Qed.
Lemma streetlight_strict_positions__right_choose :
  forall (positions : list Z) (n i j : Z),
    (forall k : Z,
       0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    0 <= i ->
    i < j ->
    j < n ->
    Znth i positions 0 < Znth j positions 0.
Proof.
  intros positions n i j Hadj Hi Hij Hj.
  assert (Hchain :
    forall d : nat, forall k : Z,
      0 <= k ->
      k + Z.of_nat (S d) < n ->
      Znth k positions 0 < Znth (k + Z.of_nat (S d)) positions 0).
  {
    induction d as [| d IH]; intros k Hk Hbound.
    - replace (k + Z.of_nat 1) with (k + 1) by (simpl; lia).
      apply Hadj.
      lia.
    - eapply Z.lt_trans.
      + apply IH; [lia |].
        rewrite Nat2Z.inj_succ in Hbound.
        lia.
      + replace (k + Z.of_nat (S (S d)))
          with ((k + Z.of_nat (S d)) + 1)
          by (rewrite (Nat2Z.inj_succ (S d)); lia).
        apply Hadj.
        split; [lia |].
        rewrite (Nat2Z.inj_succ (S d)) in Hbound.
        lia.
  }
  specialize (Hchain (Z.to_nat (j - i - 1)) i Hi).
  rewrite Nat2Z.inj_succ in Hchain.
  rewrite Z2Nat.id in Hchain by lia.
  replace (i + Z.succ (j - i - 1)) with j in Hchain by lia.
  apply Hchain.
  lia.
Qed.
Lemma sum_nonnegative_Znth__right_bounds_a :
  forall (l : list Z),
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    0 <= sum l.
Proof.
  intros l.
  induction l as [| x xs IH]; intros Hnonneg; simpl.
  - lia.
  - pose proof (Zlength_nonneg xs) as Hlenxs.
    assert (Hx : 0 <= x).
    { specialize (Hnonneg 0).
      rewrite Zlength_cons in Hnonneg.
      specialize (Hnonneg ltac:(lia)).
      rewrite Znth0_cons in Hnonneg.
      exact Hnonneg. }
    assert (Hxs : 0 <= sum xs).
    { apply IH.
      intros i Hi.
      specialize (Hnonneg (i + 1)).
      rewrite Zlength_cons in Hnonneg.
      specialize (Hnonneg ltac:(lia)).
      rewrite Znth_cons in Hnonneg by lia.
      replace (i + 1 - 1) with i in Hnonneg by lia.
      exact Hnonneg. }
    lia.
Qed.
Lemma adjacent_Znth_lt__right_bounds_a :
  forall (l : list Z),
    (forall k, 0 <= k -> k + 1 < Zlength l ->
       Znth k l 0 < Znth (k + 1) l 0) ->
    forall i j, 0 <= i -> i < j -> j < Zlength l ->
      Znth i l 0 < Znth j l 0.
Proof.
  intros l Hadj i j Hi Hij Hj.
  assert (Hlower : i + 1 <= j) by lia.
  clear Hij.
  revert Hj.
  pattern j.
  apply Zlt_lower_bound_ind with (z := i + 1).
  - intros x IH Hix Hxlen.
    destruct (Z.eq_dec x (i + 1)) as [-> | Hne].
    + apply Hadj; lia.
    + specialize (IH (x - 1) ltac:(lia) ltac:(lia)).
      specialize (Hadj (x - 1) ltac:(lia) ltac:(lia)).
      replace (x - 1 + 1) with x in Hadj by lia.
      lia.
  - exact Hlower.
Qed.
Lemma sum_sublist_bounds__right_bounds_a :
  forall (l : list Z) lo hi,
    (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
    0 <= lo <= hi ->
    hi <= Zlength l ->
    0 <= sum (sublist lo hi l) <= sum l.
Proof.
  intros l lo hi Hnonneg Hlohi Hhi.
  assert (Hmid : 0 <= sum (sublist lo hi l)).
  { apply sum_nonnegative_Znth__right_bounds_a.
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hnonneg.
    lia. }
  assert (Hpre : 0 <= sum (sublist 0 lo l)).
  { apply sum_nonnegative_Znth__right_bounds_a.
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hnonneg.
    lia. }
  assert (Hpost : 0 <= sum (sublist hi (Zlength l) l)).
  { apply sum_nonnegative_Znth__right_bounds_a.
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hnonneg.
    lia. }
  pose proof (sublist_split 0 (Zlength l) lo l ltac:(lia) ltac:(lia))
    as Hsplit1.
  pose proof (sublist_split lo (Zlength l) hi l ltac:(lia) ltac:(lia))
    as Hsplit2.
  rewrite (sublist_self l (Zlength l) eq_refl) in Hsplit1.
  rewrite Hsplit2 in Hsplit1.
  pose proof (f_equal sum Hsplit1) as Hsum_split.
  rewrite !sum_app in Hsum_split.
  lia.
Qed.
Lemma StreetlightPlan_endpoint_bounds__right_bounds_a :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    left <= endpoint <= right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; subst; lia.
Qed.
Lemma StreetlightPlan_cost_bounds__right_bounds_a :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    (forall k, 0 <= k -> k + 1 < Zlength positions ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < Zlength positions ->
       0 <= Znth k positions 0 <= 8000) ->
    Zlength powers = Zlength positions ->
    (forall k, 0 <= k < Zlength powers -> 0 <= Znth k powers 0) ->
    sum powers <= 5000 ->
    0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  induction Hplan as
      [Hstart Hlength
      | left right endpoint cost Hleft Hspan Hright Hprev IH
      | left right endpoint cost Hleft Hspan Hright Hprev IH];
    intros Hmono Hpos Hlengths Hpower Hsum.
  - lia.
  - specialize (IH Hmono Hpos Hlengths Hpower Hsum).
    pose proof
      (StreetlightPlan_endpoint_bounds__right_bounds_a
         positions powers start (left + 1) right endpoint cost Hprev)
      as Hendpoint.
    assert (Hpos_left : 0 <= Znth left positions 0 <= 8000).
    { apply Hpos. lia. }
    assert (Hpos_endpoint : 0 <= Znth endpoint positions 0 <= 8000).
    { apply Hpos. lia. }
    assert (Hpos_order : Znth left positions 0 < Znth endpoint positions 0).
    { apply (adjacent_Znth_lt__right_bounds_a positions Hmono); lia. }
    pose proof
      (sum_sublist_bounds__right_bounds_a
         powers (left + 1) (right + 1) Hpower ltac:(lia) ltac:(lia))
      as Hsub.
    assert (Hremaining :
      0 <= sum powers - sum (sublist (left + 1) (right + 1) powers) <= 5000)
      by lia.
    nia.
  - specialize (IH Hmono Hpos Hlengths Hpower Hsum).
    pose proof
      (StreetlightPlan_endpoint_bounds__right_bounds_a
         positions powers start left (right - 1) endpoint cost Hprev)
      as Hendpoint.
    assert (Hpos_right : 0 <= Znth right positions 0 <= 8000).
    { apply Hpos. lia. }
    assert (Hpos_endpoint : 0 <= Znth endpoint positions 0 <= 8000).
    { apply Hpos. lia. }
    assert (Hpos_order : Znth endpoint positions 0 < Znth right positions 0).
    { apply (adjacent_Znth_lt__right_bounds_a positions Hmono); lia. }
    pose proof
      (sum_sublist_bounds__right_bounds_a
         powers left right Hpower ltac:(lia) ltac:(lia))
      as Hsub.
    assert (Hremaining :
      0 <= sum powers - sum (sublist left right powers) <= 5000)
      by lia.
    nia.
Qed.
Lemma streetlight_power_sublist_nonnegative__right_bounds_b :
  forall powers n lo hi,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum (sublist lo hi powers).
Proof.
  intros powers n lo hi Hlength Hpower Hlohi Hhi.
  pose proof (sum_bound 100 (sublist lo hi powers)) as Hsum.
  specialize (Hsum ltac:(
    intros i Hi;
    destruct (Z_lt_ge_dec i (Zlength (sublist lo hi powers)))
      as [Hin | Hout];
    [ rewrite Zlength_sublist in Hin by lia;
      rewrite Znth_sublist by lia;
      specialize (Hpower (i + lo) ltac:(lia));
      lia
    | unfold Znth;
      rewrite nth_overflow by (rewrite Zlength_correct in Hout; lia);
      lia ])).
  lia.
Qed.
Lemma streetlight_power_remainder_bounds__right_bounds_b :
  forall powers n lo hi,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum powers - sum (sublist lo hi powers) <= 5000.
Proof.
  intros powers n lo hi Hlength Hpower Htotal Hlohi Hhi.
  pose proof
    (streetlight_power_sublist_nonnegative__right_bounds_b
       powers n 0 lo Hlength Hpower ltac:(lia) ltac:(lia)) as Hprefix.
  pose proof
    (streetlight_power_sublist_nonnegative__right_bounds_b
       powers n hi n Hlength Hpower ltac:(lia) ltac:(lia)) as Hsuffix.
  pose proof
    (streetlight_power_sublist_nonnegative__right_bounds_b
       powers n lo hi Hlength Hpower Hlohi Hhi) as Hmiddle.
  pose proof (sublist_split 0 n lo powers ltac:(lia) ltac:(lia)) as Hsplit1.
  pose proof (sublist_split lo n hi powers ltac:(lia) ltac:(lia)) as Hsplit2.
  rewrite (sublist_self powers n (eq_sym Hlength)) in Hsplit1.
  rewrite Hsplit2 in Hsplit1.
  pose proof (f_equal sum Hsplit1) as Hsum_split.
  rewrite !sum_app in Hsum_split.
  lia.
Qed.
Lemma streetlight_position_delta_bounds__right_bounds_b :
  forall positions n i j,
    Zlength positions = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    0 <= i <= j ->
    j < n ->
    0 <= Znth j positions 0 - Znth i positions 0 <= 8000.
Proof.
  intros positions n i j Hlength Hposition Hadjacent Hij Hj.
  pose proof (Hposition i ltac:(lia)) as Hi_bounds.
  pose proof (Hposition j ltac:(lia)) as Hj_bounds.
  assert (Hchain :
    forall steps p,
      0 <= p ->
      p + Z.of_nat steps < n ->
      Znth p positions 0 <= Znth (p + Z.of_nat steps) positions 0).
  { induction steps as [|steps IH]; intros p Hp Hbound.
    - replace (p + Z.of_nat 0) with p by (simpl; lia).
      apply Z.le_refl.
    - rewrite Nat2Z.inj_succ.
      pose proof (IH p ltac:(lia) ltac:(lia)) as Hprevious.
      pose proof (Hadjacent (p + Z.of_nat steps) ltac:(lia)) as Hnext.
      replace (p + Z.succ (Z.of_nat steps))
        with (p + Z.of_nat steps + 1) by lia.
      lia. }
  pose proof (Hchain (Z.to_nat (j - i)) i ltac:(lia) ltac:(
    rewrite Z2Nat.id by lia; lia)) as Hij_value.
  rewrite Z2Nat.id in Hij_value by lia.
  replace (i + (j - i)) with j in Hij_value by lia.
  lia.
Qed.
Lemma streetlight_plan_endpoint_bounds__right_bounds_b :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    left <= endpoint <= right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  destruct Hplan; lia.
Qed.
Lemma streetlight_plan_cost_bounds__right_bounds_b :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    forall n,
      Zlength positions = n ->
      Zlength powers = n ->
      (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
      (forall k, 0 <= k /\ k + 1 < n ->
         Znth k positions 0 < Znth (k + 1) positions 0) ->
      (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
      0 <= sum powers <= 5000 ->
      0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  induction Hplan as
      [Hstart Hsame_length
      |left right endpoint cost Hleft Hstart_inside Hright Hprevious IH
      |left right endpoint cost Hleft Hstart_inside Hright Hprevious IH];
    intros n Hpositions_length Hpowers_length Hposition Hadjacent Hpower Htotal.
  - lia.
  - pose proof
      (IH n Hpositions_length Hpowers_length
         Hposition Hadjacent Hpower Htotal) as Hprevious_cost.
    pose proof
      (streetlight_plan_endpoint_bounds__right_bounds_b
         positions powers start (left + 1) right endpoint cost Hprevious)
      as Hendpoint.
    pose proof
      (streetlight_position_delta_bounds__right_bounds_b
         positions n left endpoint Hpositions_length Hposition Hadjacent
         ltac:(lia) ltac:(lia)) as Hdistance.
    pose proof
      (streetlight_power_remainder_bounds__right_bounds_b
         powers n (left + 1) (right + 1) Hpowers_length Hpower Htotal
         ltac:(lia) ltac:(rewrite <- Hpositions_length; lia)) as Hremaining.
    nia.
  - pose proof
      (IH n Hpositions_length Hpowers_length
         Hposition Hadjacent Hpower Htotal) as Hprevious_cost.
    pose proof
      (streetlight_plan_endpoint_bounds__right_bounds_b
         positions powers start left (right - 1) endpoint cost Hprevious)
      as Hendpoint.
    pose proof
      (streetlight_position_delta_bounds__right_bounds_b
         positions n endpoint right Hpositions_length Hposition Hadjacent
         ltac:(lia) ltac:(lia)) as Hdistance.
    pose proof
      (streetlight_power_remainder_bounds__right_bounds_b
         powers n left right Hpowers_length Hpower Htotal
         ltac:(lia) ltac:(rewrite <- Hpositions_length; lia)) as Hremaining.
    nia.
Qed.
Lemma streetlight_endpoint_minimum_bounds__right_bounds_b :
  forall positions powers n start left right endpoint answer,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= sum powers <= 5000 ->
    StreetlightEndpointMinimum
      positions powers start left right endpoint answer ->
    0 <= answer <= (right - left) * 40000000.
Proof.
  intros positions powers n start left right endpoint answer
    Hpositions_length Hpowers_length Hposition Hadjacent Hpower Htotal Hminimum.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  destruct Hminimum as [cost [[Hplan Hleast] Hanswer]].
  subst answer.
  pose proof
    (streetlight_plan_cost_bounds__right_bounds_b
       positions powers start left right endpoint cost Hplan n
       Hpositions_length Hpowers_length Hposition Hadjacent Hpower Htotal)
    as Hbounds.
  exact Hbounds.
Qed.
Lemma streetlight_right_predecessor_bounds__right_bounds_b :
  forall positions powers prefix left_table right_table default
         n start total len left right inf,
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k /\ k + 1 < n ->
       Znth k positions 0 < Znth (k + 1) positions 0) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    total = Znth n prefix 0 ->
    1 <= total <= 5000 ->
    2 <= len ->
    0 <= left ->
    left <= start ->
    right = left + len - 1 ->
    start < right ->
    right < n ->
    StreetlightPrefixProgress powers prefix n ->
    inf = 2147483647 ->
    Znth (right - 1) (Znth left right_table default) 0 < inf ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    0 <= Znth (right - 1) (Znth left right_table default) 0 <=
      (len - 2) * 40000000.
Proof.
  intros positions powers prefix left_table right_table default
    n start total len left right inf
    Hpositions_length Hpowers_length Hposition Hadjacent Hpower
    Htotal Htotal_bounds Hlen Hleft Hleft_start Hright Hstart_right Hright_n
    Hprefix Hinf_value Hfinite Hready.
  unfold StreetlightPrefixProgress in Hprefix.
  destruct Hprefix as [Hprefix_length Hprefix_values].
  specialize (Hprefix_values n ltac:(lia)).
  rewrite (sublist_self powers n (eq_sym Hpowers_length)) in Hprefix_values.
  assert (Hpower_sum : 0 <= sum powers <= 5000) by lia.

  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hcurrent_left].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprevious_lefts].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hdone]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Hright_table_length Hright_row_lengths].
  assert (Hdefault :
    Znth left right_table [] = Znth left right_table default).
  { apply Znth_indep. rewrite Hright_table_length. lia. }
  rewrite <- Hdefault in Hfinite |- *.

  pose proof
    (Hdone (len - 1) left (right - 1)
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Hinterval.
  unfold StreetlightIntervalCorrect in Hinterval.
  destruct Hinterval as [Hleft_entry Hright_entry].
  unfold StreetlightRightEntryCorrect in Hright_entry.
  destruct Hright_entry as
      [[Hbase_left [Hbase_right Hzero]]
      |[[Hinterior Hminimum]
       |[Hinf_left [Hinf_right Hinf]]]].
  - lia.
  - pose proof
      (streetlight_endpoint_minimum_bounds__right_bounds_b
         positions powers n start left (right - 1) (right - 1)
         (Znth (right - 1) (Znth left right_table []) 0)
         Hpositions_length Hpowers_length Hposition Hadjacent Hpower
         Hpower_sum Hminimum) as Hbounds.
    lia.
  - lia.
Qed.
Lemma streetlight_positions_order__right_close_a :
  forall positions n,
  Zlength positions = n ->
  (forall k, 0 <= k /\ k + 1 < n ->
    Znth k positions 0 < Znth (k + 1) positions 0) ->
  forall i j,
    0 <= i -> i < j -> j < n ->
    Znth i positions 0 < Znth j positions 0.
Proof.
  intros positions n Hlength Hadjacent.
  assert (Hsteps : forall d i,
    0 <= i -> i + Z.of_nat (S d) < n ->
    Znth i positions 0 < Znth (i + Z.of_nat (S d)) positions 0).
  {
    induction d as [| d IH].
    - intros i Hi Hbound. simpl.
      apply Hadjacent. lia.
    - intros i Hi Hbound.
      pose proof (Nat2Z.is_nonneg d) as Hd.
      pose proof (Hadjacent i ltac:(lia)) as Hfirst.
      assert (Heq :
        i + 1 + Z.of_nat (S d) = i + Z.of_nat (S (S d))).
      { rewrite !Nat2Z.inj_succ. lia. }
      pose proof (IH (i + 1) ltac:(lia) ltac:(rewrite Heq; exact Hbound))
        as Hrest.
      rewrite Heq in Hrest.
      lia.
  }
  intros i j Hi Hij Hj.
  replace j with
    (i + Z.of_nat (S (Z.to_nat (j - i - 1)))).
  - apply Hsteps; lia.
  - rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.
Lemma streetlight_sublist_sum_nonnegative__right_close_a :
  forall powers n lo hi,
  Zlength powers = n ->
  (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
  0 <= lo <= hi ->
  hi <= n ->
  0 <= sum (sublist lo hi powers).
Proof.
  intros powers n lo hi Hlength Hvalues Hlohi Hhi.
  pose proof (sum_bound 100 (sublist lo hi powers)) as Hsum.
  apply Hsum.
  intros i Hi.
  destruct (Z_lt_ge_dec i (hi - lo)) as [Hin | Hout].
  - rewrite Znth_sublist by lia.
    pose proof (Hvalues (i + lo) ltac:(lia)). lia.
  - rewrite Znth_sublist_ge by lia.
    lia.
Qed.
Lemma streetlight_plan_cost_bound__right_close_a :
  forall positions powers start left right endpoint cost n,
  Zlength positions = n ->
  n <= 50 ->
  (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
  (forall i j, 0 <= i -> i < j -> j < n ->
    Znth i positions 0 < Znth j positions 0) ->
  sum powers <= 5000 ->
  (forall lo hi, 0 <= lo <= hi -> hi <= n ->
    0 <= sum (sublist lo hi powers)) ->
  StreetlightPlan positions powers start left right endpoint cost ->
  0 <= left /\ left <= endpoint /\ endpoint <= right /\ right < n /\
  cost <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint cost n
    Hpositions Hn Hvalues Hmono Hsum Hsub Hplan.
  induction Hplan.
  - repeat split; lia.
  - destruct IHHplan as [Hleft [Hlo [Hhi [Hright Hcost]]]].
    pose proof (Hvalues left ltac:(lia)) as Hleft_value.
    pose proof (Hvalues endpoint ltac:(lia)) as Hendpoint_value.
    pose proof (Hmono left endpoint ltac:(lia) ltac:(lia) ltac:(lia))
      as Hposition_order.
    pose proof (Hsub (left + 1) (right + 1) ltac:(lia) ltac:(lia))
      as Hsub_nonnegative.
    repeat split; try lia.
    nia.
  - destruct IHHplan as [Hleft [Hlo [Hhi [Hright Hcost]]]].
    pose proof (Hvalues endpoint ltac:(lia)) as Hendpoint_value.
    pose proof (Hvalues right ltac:(lia)) as Hright_value.
    pose proof (Hmono endpoint right ltac:(lia) ltac:(lia) ltac:(lia))
      as Hposition_order.
    pose proof (Hsub left right ltac:(lia) ltac:(lia))
      as Hsub_nonnegative.
    repeat split; try lia.
    nia.
Qed.
Lemma streetlight_endpoint_minimum_below_inf__right_close_a :
  forall positions powers n start left right endpoint answer,
  Zlength positions = n ->
  n <= 50 ->
  (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
  (forall i j, 0 <= i -> i < j -> j < n ->
    Znth i positions 0 < Znth j positions 0) ->
  sum powers <= 5000 ->
  (forall lo hi, 0 <= lo <= hi -> hi <= n ->
    0 <= sum (sublist lo hi powers)) ->
  StreetlightEndpointMinimum
    positions powers start left right endpoint answer ->
  answer < 2147483647.
Proof.
  intros positions powers n start left right endpoint answer
    Hpositions Hn Hvalues Hmono Hsum Hsub Hminimum.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  destruct Hminimum as [cost [[Hplan Hleast] Hanswer]].
  simpl in Hanswer. subst answer.
  pose proof
    (streetlight_plan_cost_bound__right_close_a
      positions powers start left right endpoint cost n
      Hpositions Hn Hvalues Hmono Hsum Hsub Hplan)
    as [Hleft [Hlo [Hhi [Hright Hcost]]]].
  nia.
Qed.
Lemma streetlight_close_interval_right__right_close_a :
  forall positions powers left_table right_table n start len left right inf
    (default : list Z),
  Zlength positions = n ->
  n <= 50 ->
  (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
  (forall i j, 0 <= i -> i < j -> j < n ->
    Znth i positions 0 < Znth j positions 0) ->
  sum powers <= 5000 ->
  (forall lo hi, 0 <= lo <= hi -> hi <= n ->
    0 <= sum (sublist lo hi powers)) ->
  2 <= len ->
  0 <= left ->
  left <= start ->
  right = left + len - 1 ->
  start < right ->
  right < n ->
  inf = 2147483647 ->
  Znth (right - 1) (Znth left left_table default) 0 = inf ->
  Znth (right - 1) (Znth left right_table default) 0 = inf ->
  StreetlightLeftEndpointReady
    positions powers left_table right_table n start len left ->
  False.
Proof.
  intros positions powers left_table right_table n start len left right inf
    default Hpositions Hn Hvalues Hmono Hsum Hsub Hlen Hleft Hleft_le_start
    Hright Hstart Hbound Hinf Hleft_inf Hright_inf Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hleft_ready].
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprevious].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hintervals]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_rows].
  destruct Hright_shape as [Hright_table_length Hright_rows].
  rewrite (Znth_indep left_table left default (@nil Z)) in Hleft_inf by lia.
  rewrite (Znth_indep right_table left default (@nil Z)) in Hright_inf by lia.
  pose proof
    (Hintervals (len - 1) left (right - 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Hinterval.
  unfold StreetlightIntervalCorrect in Hinterval.
  destruct Hinterval as [Hleft_entry Hright_entry].
  unfold StreetlightLeftEntryCorrect in Hleft_entry.
  unfold StreetlightRightEntryCorrect in Hright_entry.
  destruct Hleft_entry as
    [[Hleft_start [Hprevious_start Hleft_zero]] |
     [[Hleft_before Hleft_minimum] |
      [Hleft_start [Hprevious_after Hleft_cell]]]].
  - lia.
  - rewrite Hleft_inf in Hleft_minimum.
    pose proof
      (streetlight_endpoint_minimum_below_inf__right_close_a
        positions powers n start left (right - 1) left inf
        Hpositions Hn Hvalues Hmono Hsum Hsub Hleft_minimum).
    lia.
  - destruct Hright_entry as
      [[Hleft_start' [Hprevious_start' Hright_zero]] |
       [[Hprevious_after' Hright_minimum] |
        [Hleft_before' [Hprevious_start' Hright_cell]]]].
    + lia.
    + rewrite Hright_inf in Hright_minimum.
      pose proof
        (streetlight_endpoint_minimum_below_inf__right_close_a
          positions powers n start left (right - 1) (right - 1) inf
          Hpositions Hn Hvalues Hmono Hsum Hsub Hright_minimum).
      lia.
    + lia.
Qed.
Lemma streetlight_start_endpoint_minimum__right_close_b :
  forall positions powers start,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    StreetlightEndpointMinimum
      positions powers start start start start 0.
Proof.
  intros positions powers start Hstart Hlength.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists 0.
  split.
  - split.
    + constructor; assumption.
    + intros cost Hplan.
      inversion Hplan; subst; lia.
  - reflexivity.
Qed.
Lemma streetlight_plan_endpoint_boundary__right_close_b :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; subst; auto.
Qed.
Lemma streetlight_plan_right_decompose__right_close_b :
  forall positions powers start left right cost,
    start < right ->
    StreetlightPlan positions powers start left right right cost ->
    exists endpoint previous_cost,
      StreetlightPlan positions powers start
        left (right - 1) endpoint previous_cost /\
      cost =
        previous_cost +
        (Znth right positions 0 - Znth endpoint positions 0) *
        (sum powers - sum (sublist left right powers)).
Proof.
  intros positions powers start left right cost Hstart_right Hplan.
  inversion Hplan; subst; try lia.
  eexists; eexists.
  split; [eassumption | reflexivity].
Qed.
Lemma streetlight_right_endpoint_minimum__right_close_b :
  forall positions powers prefix left_table right_table
    n start len left right remain best inf default_row,
    inf = 2147483647 ->
    1 <= n ->
    n <= 50 ->
    2 <= len ->
    len <= n ->
    0 <= start ->
    start < n ->
    0 <= left ->
    left <= start ->
    right = left + len - 1 ->
    start < right ->
    right < n ->
    1 <= remain ->
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k,
      0 <= k /\ k + 1 < n ->
      Znth k positions 0 < Znth (k + 1) positions 0) ->
    remain =
      Znth n prefix 0 -
      (Znth right prefix 0 - Znth left prefix 0) ->
    StreetlightPrefixProgress powers prefix n ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    Znth (right - 1) (Znth left left_table default_row) 0 < inf ->
    best <= (len - 1) * 40000000 ->
    best =
      Znth (right - 1) (Znth left left_table default_row) 0 +
      (Znth right positions 0 - Znth left positions 0) * remain ->
    (Znth (right - 1) (Znth left left_table default_row) 0 < inf ->
      best <=
        Znth (right - 1) (Znth left left_table default_row) 0 +
        (Znth right positions 0 - Znth left positions 0) * remain) ->
    (Znth (right - 1) (Znth left right_table default_row) 0 < inf ->
      best <=
        Znth (right - 1) (Znth left right_table default_row) 0 +
        (Znth right positions 0 - Znth (right - 1) positions 0) *
          remain) ->
    StreetlightEndpointMinimum
      positions powers start left right right best.
Proof.
  intros positions powers prefix left_table right_table
    n start len left right remain best inf default_row
    Hinf Hn Hn_upper Hlen Hlen_upper Hstart Hstart_upper
    Hleft Hleft_start Hright Hstart_right Hright_upper Hremain_pos
    Hpositions_length Hpowers_length Hpositions_increasing Hremain
    Hprefix Hready Hleft_finite Hbest_upper Hbest
    Hleft_candidate Hright_candidate.

  pose proof Hready as Hready_shape.
  unfold StreetlightLeftEndpointReady in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgress in Hprogress_shape.
  destruct Hprogress_shape as [Hdone_shape _].
  unfold StreetlightLengthsDone in Hdone_shape.
  destruct Hdone_shape as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_length].
  destruct Hright_shape as [Hright_table_length Hright_row_length].
  assert (Hleft_table_index : 0 <= left < Zlength left_table) by lia.
  assert (Hright_table_index : 0 <= left < Zlength right_table) by lia.
  rewrite (Znth_indep left_table left default_row [] Hleft_table_index)
    in Hleft_finite, Hbest, Hleft_candidate.
  rewrite (Znth_indep right_table left default_row [] Hright_table_index)
    in Hright_candidate.

  assert (Henergy :
    remain = sum powers - sum (sublist left right powers)).
  {
    pose proof Hprefix as Hprefix_values.
    unfold StreetlightPrefixProgress in Hprefix_values.
    destruct Hprefix_values as [_ Hprefix_values].
    pose proof (Hprefix_values n ltac:(lia)) as Hall.
    pose proof (Hprefix_values right ltac:(lia)) as Hright_sum.
    pose proof (Hprefix_values left ltac:(lia)) as Hleft_sum.
    rewrite (sublist_self powers n (eq_sym Hpowers_length)) in Hall.
    rewrite
      (sublist_split 0 right left powers ltac:(lia) ltac:(lia)),
      sum_app in Hright_sum.
    lia.
  }

  pose proof Hready as Hready_previous.
  unfold StreetlightLeftEndpointReady in Hready_previous.
  destruct Hready_previous as [Hprogress_previous _].
  unfold StreetlightLeftProgress in Hprogress_previous.
  destruct Hprogress_previous as [Hdone_previous _].
  unfold StreetlightLengthsDone in Hdone_previous.
  destruct Hdone_previous as [_ [_ Hshorter]].
  pose proof
    (Hshorter (len - 1) left (right - 1)
      ltac:(lia) ltac:(lia) Hleft ltac:(lia) ltac:(lia))
    as Hprevious_interval.
  unfold StreetlightIntervalCorrect in Hprevious_interval.
  destruct Hprevious_interval as [Hprevious_left Hprevious_right].

  assert (Hleft_minimum :
    StreetlightEndpointMinimum positions powers start
      left (right - 1) left
      (Znth (right - 1) (Znth left left_table []) 0)).
  {
    unfold StreetlightLeftEntryCorrect in Hprevious_left.
    destruct Hprevious_left as
      [Hbase | [Hminimum | Hinfinite]].
    - destruct Hbase as [Hleft_start' [Hright_start Hvalue]].
      rewrite Hvalue.
      replace left with start by lia.
      replace (right - 1) with start by lia.
      apply streetlight_start_endpoint_minimum__right_close_b.
      + rewrite Hpositions_length. lia.
      + lia.
    - destruct Hminimum as [_ Hminimum].
      exact Hminimum.
    - destruct Hinfinite as [_ [_ Hvalue]].
      exfalso; lia.
  }
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hleft_minimum.
  destruct Hleft_minimum as
    [left_cost [[Hleft_plan Hleft_least] Hleft_cost]].
  cbn in Hleft_cost.
  subst left_cost.

  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists best.
  split.
  - split.
    + rewrite Hbest, Henergy.
      eapply StreetlightPlan_extend_right; try lia.
      exact Hleft_plan.
    + intros arbitrary_cost Harbitrary_plan.
      destruct
        (streetlight_plan_right_decompose__right_close_b
          positions powers start left right arbitrary_cost
          Hstart_right Harbitrary_plan)
        as [endpoint [previous_cost [Hprevious_plan Harbitrary_cost]]].
      pose proof
        (streetlight_plan_endpoint_boundary__right_close_b
          positions powers start left (right - 1) endpoint previous_cost
          Hprevious_plan) as Hendpoint.
      destruct Hendpoint as [Hendpoint | Hendpoint].
      * subst endpoint.
        pose proof (Hleft_least previous_cost Hprevious_plan) as Hleast.
        specialize (Hleft_candidate Hleft_finite).
        rewrite Harbitrary_cost, <- Henergy.
        nia.
      * subst endpoint.
        assert (Hright_minimum :
          StreetlightEndpointMinimum positions powers start
            left (right - 1) (right - 1)
            (Znth (right - 1) (Znth left right_table []) 0)).
        {
          unfold StreetlightRightEntryCorrect in Hprevious_right.
          destruct Hprevious_right as
            [Hbase | [Hminimum | Hinfinite]].
          - destruct Hbase as [Hleft_start' [Hright_start Hvalue]].
            rewrite Hvalue.
            replace left with start by lia.
            replace (right - 1) with start by lia.
            apply streetlight_start_endpoint_minimum__right_close_b.
            + rewrite Hpositions_length. lia.
            + lia.
          - destruct Hminimum as [_ Hminimum].
            exact Hminimum.
          - destruct Hinfinite as [Hleft_strict [Hright_start _]].
            exfalso.
            inversion Hprevious_plan; subst; lia.
        }
        unfold StreetlightEndpointMinimum, min_value_of_subset,
          min_object_of_subset in Hright_minimum.
        destruct Hright_minimum as
          [right_cost [[Hright_plan Hright_least] Hright_cost]].
        cbn in Hright_cost.
        subst right_cost.
        destruct
          (Z_lt_ge_dec
            (Znth (right - 1) (Znth left right_table []) 0) inf)
          as [Hright_finite | Hright_infinite].
        -- pose proof
             (Hright_least previous_cost Hprevious_plan) as Hleast.
           specialize (Hright_candidate Hright_finite).
           rewrite Harbitrary_cost, <- Henergy.
           nia.
        -- assert (Hbest_inf : best < inf) by nia.
           pose proof
             (Hright_least previous_cost Hprevious_plan) as Hleast.
           specialize
             (Hpositions_increasing (right - 1) ltac:(lia))
             as Hposition_step.
           replace (right - 1 + 1) with right in Hposition_step by lia.
           rewrite Harbitrary_cost, <- Henergy.
           nia.
  - reflexivity.
Qed.
Lemma streetlight_close_interval_and_advance__right_close_b :
  forall positions powers left_table right_table n start len left right
    best default_row,
    2 <= len ->
    0 <= left ->
    right = left + len - 1 ->
    start < right ->
    right < n ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    StreetlightEndpointMinimum
      positions powers start left right right best ->
    StreetlightLeftProgress
      positions powers left_table
      (replace_Znth left
        (replace_Znth right best (Znth left right_table default_row))
        right_table)
      n start len (left + 1).
Proof.
  intros positions powers left_table right_table n start len left right
    best default_row Hlen Hleft Hright Hstart_right Hright_upper
    Hready Hminimum.
  unfold StreetlightLeftEndpointReady in Hready.
  destruct Hready as [Hprogress Hcurrent_left].
  rewrite <- Hright in Hcurrent_left.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprevious].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hshorter]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table) by lia.
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table [])) by
    (rewrite Hrow_length by lia; lia).
  rewrite (Znth_indep right_table left default_row [] Hleft_index).
  unfold StreetlightLeftProgress.
  split.
  - unfold StreetlightLengthsDone.
    split; [exact Hleft_shape |].
    split.
    + unfold StreetlightTableShape.
      split.
      * rewrite Zlength_replace_Znth.
        exact Htable_length.
      * intros row Hrow.
        destruct (Z.eq_dec row left) as [Heq | Hneq].
        -- subst row.
           rewrite Znth_replace_Znth_Same by exact Hleft_index.
           rewrite Zlength_replace_Znth.
           apply Hrow_length; lia.
        -- rewrite Znth_replace_Znth_Diff by
             (try rewrite Htable_length; try lia; exact Hneq).
           apply Hrow_length; exact Hrow.
    + intros shorter_len shorter_left shorter_right
        Hshorter_len Hshorter_right Hshorter_left Hshorter_bound
        Hshorter_contains.
      pose proof
        (Hshorter shorter_len shorter_left shorter_right
          Hshorter_len Hshorter_right Hshorter_left Hshorter_bound
          Hshorter_contains) as Hinterval.
      unfold StreetlightIntervalCorrect in Hinterval |- *.
      destruct Hinterval as [Hleft_correct Hright_correct].
      split; [exact Hleft_correct |].
      destruct (Z.eq_dec shorter_left left) as [Heq | Hneq].
      * subst shorter_left.
        rewrite Znth_replace_Znth_Same by exact Hleft_index.
        rewrite Znth_replace_Znth_Diff by
          (try rewrite Hrow_length by lia; try lia).
        exact Hright_correct.
      * rewrite Znth_replace_Znth_Diff by
          (try rewrite Htable_length; try lia; exact Hneq).
        exact Hright_correct.
  - intros done_left interval_right Hdone_left Hinterval_right
      Hinterval_bound Hinterval_contains.
    destruct (Z_lt_ge_dec done_left left) as [Hbefore | Hcurrent].
    + pose proof
        (Hprevious done_left interval_right ltac:(lia)
          Hinterval_right Hinterval_bound Hinterval_contains)
        as Hinterval.
      unfold StreetlightIntervalCorrect in Hinterval |- *.
      destruct Hinterval as [Hleft_correct Hright_correct].
      split; [exact Hleft_correct |].
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia).
      exact Hright_correct.
    + assert (Hdone_eq : done_left = left) by lia.
      subst done_left.
      replace interval_right with right in * by lia.
      unfold StreetlightIntervalCorrect.
      split; [exact Hcurrent_left |].
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Same by exact Hright_index.
      unfold StreetlightRightEntryCorrect.
      right; left.
      split; assumption.
Qed.
Lemma streetlight_sublist_sum_nonnegative__right_close_c :
  forall powers n lo hi,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum (sublist lo hi powers).
Proof.
  intros powers n lo hi Hlength Hbounds Hlo Hhi.
  assert (Hsum :
    0 <= sum (sublist lo hi powers) <=
      Z.of_nat (length (sublist lo hi powers)) * 100).
  {
    apply sum_bound.
    intros i Hi.
    destruct (Z_lt_ge_dec i (hi - lo)) as [Hin | Hout].
    - rewrite Znth_sublist by lia.
      replace (i + lo) with (lo + i) by lia.
      pose proof (Hbounds (lo + i) ltac:(lia)) as Hb.
      lia.
    - rewrite Znth_sublist_ge by lia.
      lia.
  }
  lia.
Qed.
Lemma streetlight_remaining_bounds__right_close_c :
  forall powers n lo hi,
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    0 <= lo <= hi ->
    hi <= n ->
    0 <= sum powers - sum (sublist lo hi powers) <= 5000.
Proof.
  intros powers n lo hi Hlength Hbounds Htotal Hlo Hhi.
  pose proof
    (streetlight_sublist_sum_nonnegative__right_close_c
       powers n 0 lo Hlength Hbounds ltac:(lia) ltac:(lia)) as Hbefore.
  pose proof
    (streetlight_sublist_sum_nonnegative__right_close_c
       powers n hi n Hlength Hbounds ltac:(lia) ltac:(lia)) as Hafter.
  pose proof
    (streetlight_sublist_sum_nonnegative__right_close_c
       powers n lo hi Hlength Hbounds Hlo Hhi) as Hmiddle.
  assert (Hdecompose :
    sum powers =
      sum (sublist 0 lo powers) +
      sum (sublist lo hi powers) +
      sum (sublist hi n powers)).
  {
    rewrite <- (sublist_self powers n) at 1 by lia.
    rewrite (sublist_split 0 n lo powers) by lia.
    rewrite (sublist_split lo n hi powers) by lia.
    rewrite !sum_app.
    lia.
  }
  lia.
Qed.
Lemma streetlight_plan_endpoint_boundary__right_close_c :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; subst; auto.
Qed.
Lemma streetlight_plan_end_right_inv__right_close_c :
  forall positions powers start left right cost,
    left <= start < right ->
    StreetlightPlan positions powers start left right right cost ->
    exists endpoint previous,
      StreetlightPlan positions powers start
        left (right - 1) endpoint previous /\
      cost =
        previous +
        (Znth right positions 0 - Znth endpoint positions 0) *
        (sum powers - sum (sublist left right powers)).
Proof.
  intros positions powers start left right cost Hrange Hplan.
  inversion Hplan; subst; try lia.
  eexists; eexists; split; [eassumption | reflexivity].
Qed.
Lemma streetlight_plan_left_at_start_singleton__right_close_c :
  forall positions powers start right cost,
    StreetlightPlan positions powers start start right start cost ->
    right = start /\ cost = 0.
Proof.
  intros positions powers start right cost Hplan.
  inversion Hplan; subst; try lia.
Qed.
Lemma streetlight_plan_upper_bound__right_close_c :
  forall positions powers n start left right endpoint cost,
    Zlength positions = n ->
    Zlength powers = n ->
    n <= 50 ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    StreetlightPlan positions powers start left right endpoint cost ->
    0 <= endpoint < n /\ cost <= (right - left) * 40000000.
Proof.
  intros positions powers n start left right endpoint cost
    Hpositions Hpowers Hn Hposition_bounds Hpower_bounds Htotal Hplan.
  induction Hplan as
    [Hstart Hsame_length
    | left right endpoint cost Hleft Hspan Hright Hprevious IH
    | left right endpoint cost Hleft Hspan Hright Hprevious IH].
  - rewrite Hpositions in Hstart.
    split; [exact Hstart | lia].
  - destruct IH as [Hendpoint Hcost].
    pose proof (Hposition_bounds endpoint Hendpoint) as Hendpoint_position.
    pose proof (Hposition_bounds left ltac:(lia)) as Hleft_position.
    pose proof
      (streetlight_remaining_bounds__right_close_c
         powers n (left + 1) (right + 1) Hpowers Hpower_bounds Htotal
         ltac:(lia) ltac:(lia)) as Hremaining.
    split; [lia | nia].
  - destruct IH as [Hendpoint Hcost].
    pose proof (Hposition_bounds endpoint Hendpoint) as Hendpoint_position.
    pose proof (Hposition_bounds right ltac:(lia)) as Hright_position.
    pose proof
      (streetlight_remaining_bounds__right_close_c
         powers n left right Hpowers Hpower_bounds Htotal
         ltac:(lia) ltac:(lia)) as Hremaining.
    split; [lia | nia].
Qed.
Lemma streetlight_right_entry_finite_minimum__right_close_c :
  forall positions powers start left right value,
    0 <= start < Zlength positions ->
    Zlength powers = Zlength positions ->
    left <= start <= right ->
    value < 2147483647 ->
    StreetlightRightEntryCorrect
      positions powers start left right value ->
    StreetlightEndpointMinimum
      positions powers start left right right value.
Proof.
  intros positions powers start left right value
    Hstart Hlength Hrange Hfinite Hcorrect.
  unfold StreetlightRightEntryCorrect in Hcorrect.
  destruct Hcorrect as
    [[Hleft [Hright Hvalue]] |
     [[Hright Hminimum] | [Hleft [Hright Hvalue]]]].
  - subst left right value.
    unfold StreetlightEndpointMinimum, min_value_of_subset,
      min_object_of_subset.
    exists 0.
    split.
    + split.
      * constructor; assumption.
      * intros candidate Hcandidate.
        inversion Hcandidate; subst; try lia.
    + reflexivity.
  - exact Hminimum.
  - subst value.
    lia.
Qed.
Lemma streetlight_close_endpoint_right__right_close_c :
  forall positions powers left_table right_table n start len left right
      inf remain best,
    inf = 2147483647 ->
    n <= 50 ->
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    2 <= len ->
    0 <= left ->
    left <= start < right ->
    right < n ->
    right = left + len - 1 ->
    remain = sum powers - sum (sublist left right powers) ->
    Znth (right - 1) (Znth left right_table []) 0 < inf ->
    best =
      Znth (right - 1) (Znth left right_table []) 0 +
      (Znth right positions 0 - Znth (right - 1) positions 0) * remain ->
    (Znth (right - 1) (Znth left left_table []) 0 < inf ->
     best <=
       Znth (right - 1) (Znth left left_table []) 0 +
       (Znth right positions 0 - Znth left positions 0) * remain) ->
    (Znth (right - 1) (Znth left right_table []) 0 < inf ->
     best <=
       Znth (right - 1) (Znth left right_table []) 0 +
       (Znth right positions 0 - Znth (right - 1) positions 0) * remain) ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    StreetlightEndpointMinimum
      positions powers start left right right best.
Proof.
  intros positions powers left_table right_table n start len left right
    inf remain best Hinf Hn Hpositions Hpowers Hposition_bounds
    Hpower_bounds Htotal Hlen Hleft Hrange Hright Hright_eq Hremaining
    Hright_finite Hbest Hbest_left Hbest_right Hready.
  set (left_value :=
    Znth (right - 1) (Znth left left_table []) 0) in *.
  set (right_value :=
    Znth (right - 1) (Znth left right_table []) 0) in *.
  unfold StreetlightLeftEndpointReady in Hready.
  cbn in Hready.
  destruct Hready as [Hprogress Hcurrent_left].
  replace (left + len - 1) with right in Hcurrent_left by lia.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprevious].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hshorter]].
  pose proof
    (Hshorter (len - 1) left (right - 1)
       ltac:(lia) ltac:(lia) Hleft ltac:(lia) ltac:(lia))
    as Hpredecessor_correct.
  unfold StreetlightIntervalCorrect in Hpredecessor_correct.
  destruct Hpredecessor_correct as [Hleft_entry Hright_entry].
  fold left_value in Hleft_entry.
  fold right_value in Hright_entry.
  assert (Hright_finite' : right_value < 2147483647) by lia.
  assert (Hstart : 0 <= start < Zlength positions) by
    (rewrite Hpositions; lia).
  assert (Hsame_length : Zlength powers = Zlength positions) by lia.
  pose proof
    (streetlight_right_entry_finite_minimum__right_close_c
       positions powers start left (right - 1) right_value
       Hstart Hsame_length ltac:(lia) Hright_finite' Hright_entry)
    as Hright_minimum.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hright_minimum.
  destruct Hright_minimum as
    [right_cost [[Hright_plan Hright_least] Hright_cost]].
  cbn in Hright_cost.
  subst right_cost.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset.
  exists best.
  split.
  - split.
    + rewrite Hbest, Hremaining.
      eapply StreetlightPlan_extend_right.
      * exact Hleft.
      * exact Hrange.
      * rewrite Hpositions. exact Hright.
      * exact Hright_plan.
    + intros candidate Hcandidate.
      destruct
        (streetlight_plan_end_right_inv__right_close_c
           positions powers start left right candidate Hrange Hcandidate)
        as [endpoint [previous [Hprevious_plan Hcandidate_value]]].
      rewrite <- Hremaining in Hcandidate_value.
      destruct
        (streetlight_plan_endpoint_boundary__right_close_c
           positions powers start left (right - 1) endpoint previous
           Hprevious_plan) as [Hendpoint | Hendpoint].
      * subst endpoint.
        unfold StreetlightLeftEntryCorrect in Hleft_entry.
        destruct Hleft_entry as
          [[Hleft_start [Hright_start Hleft_value]] |
           [[Hleft_start Hleft_minimum] |
            [Hleft_start [Hright_start Hleft_value]]]].
        -- assert (Hprevious_zero : previous = 0).
           {
             rewrite Hleft_start in Hprevious_plan.
             pose proof
               (streetlight_plan_left_at_start_singleton__right_close_c
                  positions powers start (right - 1) previous
                  Hprevious_plan) as [_ Hzero].
             exact Hzero.
           }
           pose proof Hbest_left ltac:(lia) as Hbest_bound.
           lia.
        -- unfold StreetlightEndpointMinimum, min_value_of_subset,
             min_object_of_subset in Hleft_minimum.
           destruct Hleft_minimum as
             [left_cost [[Hleft_plan Hleft_least] Hleft_cost]].
           cbn in Hleft_cost.
           subst left_cost.
           pose proof (Hleft_least previous Hprevious_plan) as Hleft_le.
           pose proof
             (streetlight_plan_upper_bound__right_close_c
                positions powers n start left (right - 1) left previous
                Hpositions Hpowers Hn Hposition_bounds Hpower_bounds Htotal
                Hprevious_plan) as [_ Hprevious_bound].
           assert (Hleft_finite : left_value < inf) by nia.
           pose proof (Hbest_left Hleft_finite) as Hbest_bound.
           lia.
        -- rewrite Hleft_start in Hprevious_plan.
           pose proof
             (streetlight_plan_left_at_start_singleton__right_close_c
                positions powers start (right - 1) previous
                Hprevious_plan) as [Hsingleton _].
           lia.
      * subst endpoint.
        pose proof (Hright_least previous Hprevious_plan) as Hright_le.
        pose proof (Hbest_right Hright_finite) as Hbest_bound.
        lia.
  - reflexivity.
Qed.
Lemma streetlight_close_interval_right__right_close_c :
  forall positions powers left_table right_table n start len left right best,
    0 <= left ->
    left <= start < right ->
    right < n ->
    right = left + len - 1 ->
    StreetlightEndpointMinimum
      positions powers start left right right best ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    StreetlightLeftProgress
      positions powers left_table
      (replace_Znth left
         (replace_Znth right best (Znth left right_table []))
         right_table)
      n start len (left + 1).
Proof.
  intros positions powers left_table right_table n start len left right best
    Hleft Hrange Hright Hright_eq Hminimum Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  cbn in Hready.
  destruct Hready as [Hprogress Hcurrent_left].
  replace (left + len - 1) with right in Hcurrent_left by lia.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprevious].
  unfold StreetlightLengthsDone in Hdone.
  destruct Hdone as [Hleft_shape [Hright_shape Hshorter]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table) by
    (rewrite Htable_length; lia).
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table [])) by
    (rewrite Hrow_length by lia; lia).
  unfold StreetlightLeftProgress.
  split.
  - unfold StreetlightLengthsDone.
    split; [exact Hleft_shape |].
    split.
    + unfold StreetlightTableShape.
      split.
      * rewrite Zlength_replace_Znth. exact Htable_length.
      * intros row Hrow.
        destruct (Z.eq_dec row left) as [-> | Hrow_neq].
        -- rewrite Znth_replace_Znth_Same by exact Hleft_index.
           rewrite Zlength_replace_Znth.
           apply Hrow_length. lia.
        -- rewrite Znth_replace_Znth_Diff by
               (try rewrite Htable_length; try lia; exact Hrow_neq).
           apply Hrow_length. exact Hrow.
    + intros old_len done_left interval_right Hold_len Hinterval_right
        Hdone_left Hinterval_bound Hcontains.
      pose proof
        (Hshorter old_len done_left interval_right Hold_len Hinterval_right
           Hdone_left Hinterval_bound Hcontains) as Hcorrect.
      unfold StreetlightIntervalCorrect in Hcorrect |- *.
      destruct Hcorrect as [Hleft_entry Hright_entry].
      split; [exact Hleft_entry |].
      destruct (Z.eq_dec done_left left) as [Hsame | Hdiff].
      * subst done_left.
        rewrite Znth_replace_Znth_Same by exact Hleft_index.
        rewrite Znth_replace_Znth_Diff by
          (try rewrite Hrow_length by lia; lia).
        exact Hright_entry.
      * rewrite Znth_replace_Znth_Diff by
          (try rewrite Htable_length; try lia; exact Hdiff).
        exact Hright_entry.
  - intros done_left interval_right Hdone_left Hinterval_right
      Hinterval_bound Hcontains.
    destruct (Z.eq_dec done_left left) as [Hsame | Hdiff].
    + subst done_left.
      assert (Hsame_right : interval_right = right) by lia.
      subst interval_right.
      unfold StreetlightIntervalCorrect.
      rewrite Hsame_right.
      split; [exact Hcurrent_left |].
      unfold StreetlightRightEntryCorrect.
      right; left.
      split; [lia |].
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Same by exact Hright_index.
      exact Hminimum.
    + pose proof
        (Hprevious done_left interval_right ltac:(lia) Hinterval_right
           Hinterval_bound Hcontains) as Hcorrect.
      unfold StreetlightIntervalCorrect in Hcorrect |- *.
      destruct Hcorrect as [Hleft_entry Hright_entry].
      split; [exact Hleft_entry |].
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia; exact Hdiff).
      exact Hright_entry.
Qed.
Lemma streetlight_endpoint_interval_advance__right_close_c :
  forall positions powers left_table right_table n start len left right
      inf remain best,
    inf = 2147483647 ->
    n <= 50 ->
    Zlength positions = n ->
    Zlength powers = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k positions 0 <= 8000) ->
    (forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) ->
    sum powers <= 5000 ->
    2 <= len ->
    0 <= left ->
    left <= start < right ->
    right < n ->
    right = left + len - 1 ->
    remain = sum powers - sum (sublist left right powers) ->
    Znth (right - 1) (Znth left right_table []) 0 < inf ->
    best =
      Znth (right - 1) (Znth left right_table []) 0 +
      (Znth right positions 0 - Znth (right - 1) positions 0) * remain ->
    (Znth (right - 1) (Znth left left_table []) 0 < inf ->
     best <=
       Znth (right - 1) (Znth left left_table []) 0 +
       (Znth right positions 0 - Znth left positions 0) * remain) ->
    (Znth (right - 1) (Znth left right_table []) 0 < inf ->
     best <=
       Znth (right - 1) (Znth left right_table []) 0 +
       (Znth right positions 0 - Znth (right - 1) positions 0) * remain) ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    StreetlightEndpointMinimum
      positions powers start left right right best /\
    StreetlightLeftProgress
      positions powers left_table
      (replace_Znth left
         (replace_Znth right best (Znth left right_table []))
         right_table)
      n start len (left + 1).
Proof.
  intros positions powers left_table right_table n start len left right
    inf remain best Hinf Hn Hpositions Hpowers Hposition_bounds
    Hpower_bounds Htotal Hlen Hleft Hrange Hright Hright_eq Hremaining
    Hright_finite Hbest Hbest_left Hbest_right Hready.
  assert (Hminimum :
    StreetlightEndpointMinimum
      positions powers start left right right best).
  {
    eapply
      (streetlight_close_endpoint_right__right_close_c
         positions powers left_table right_table n start len left right
         inf remain best);
      eauto.
  }
  split; [exact Hminimum |].
  eapply
    (streetlight_close_interval_right__right_close_c
       positions powers left_table right_table n start len left right best);
    eauto.
Qed.
Lemma streetlight_close_interval_right__right_close_d :
  forall positions powers left_table right_table (default : list Z)
    n start len left right inf,
    inf = 2147483647 ->
    2 <= len ->
    0 <= left ->
    left <= start ->
    right = left + len - 1 ->
    start <= right ->
    right <= start ->
    right < n ->
    (right = start ->
      Znth right (Znth left right_table default) 0 = inf) ->
    StreetlightLeftEndpointReady
      positions powers left_table right_table n start len left ->
    StreetlightLeftProgress
      positions powers left_table right_table n start len (left + 1).
Proof.
  intros positions powers left_table right_table default n start len left right inf
    Hinf Hlen Hleft_nonnegative Hleft_start Hright Hstart_right
    Hright_start Hright_bound Hright_inf Hready.
  unfold StreetlightLeftEndpointReady in Hready.
  cbn in Hready.
  destruct Hready as [Hprogress Hleft_entry].
  unfold StreetlightLeftProgress in Hprogress |- *.
  destruct Hprogress as [Hlengths_done Hprevious].
  pose proof Hlengths_done as Htable_shapes.
  unfold StreetlightLengthsDone in Htable_shapes.
  destruct Htable_shapes as [_ [Hright_shape _]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Hright_table_length _].
  split.
  - exact Hlengths_done.
  - intros current_left current_right Hcurrent_left Hcurrent_right
      Hcurrent_bound Hcurrent_contains.
    destruct (Z_lt_ge_dec current_left left) as [Hbefore | Hat_or_after].
    + apply Hprevious.
      * lia.
      * exact Hcurrent_right.
      * exact Hcurrent_bound.
      * exact Hcurrent_contains.
    + assert (Hcurrent_left_eq : current_left = left) by lia.
      subst current_left.
      replace current_right with right by lia.
      unfold StreetlightIntervalCorrect.
      split.
      * rewrite Hright.
        exact Hleft_entry.
      * unfold StreetlightRightEntryCorrect.
        right; right.
        split; [lia |].
        split; [lia |].
        rewrite (Znth_indep right_table left [] default) by
          (rewrite Hright_table_length; lia).
        assert (Hentry_inf :
          Znth right (Znth left right_table default) 0 = inf).
        { apply Hright_inf. lia. }
        rewrite Hentry_inf.
        exact Hinf.
Qed.
Lemma streetlight_lengths_done_succ__length_close_a :
  forall positions powers left_table right_table n start len next_left,
    StreetlightLeftProgress
      positions powers left_table right_table n start len next_left ->
    (forall left,
       0 <= left ->
       left + len - 1 < n ->
       left <= start <= left + len - 1 ->
       left < next_left) ->
    StreetlightLengthsDone
      positions powers left_table right_table n start (len + 1).
Proof.
  intros positions powers left_table right_table n start len next_left
    Hprogress Hterminal.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprocessed].
  unfold StreetlightLengthsDone in Hdone |- *.
  destruct Hdone as [Hleft_shape [Hright_shape Hshorter]].
  split; [exact Hleft_shape |].
  split; [exact Hright_shape |].
  intros query_len query_left query_right
    [Hquery_positive Hquery_upper] Hquery_right
    Hquery_left Hquery_right_bound Hquery_contains.
  subst query_right.
  destruct (Z.eq_dec query_len len) as [Hequal | Hunequal].
  - subst query_len.
    apply Hprocessed.
    + split; [exact Hquery_left |].
      apply Hterminal; assumption.
    + reflexivity.
    + exact Hquery_right_bound.
    + exact Hquery_contains.
  - apply Hshorter with
      (len := query_len)
      (left := query_left)
      (right := query_left + query_len - 1).
    + lia.
    + reflexivity.
    + exact Hquery_left.
    + exact Hquery_right_bound.
    + exact Hquery_contains.
Qed.
Lemma streetlight_lengths_done_succ__length_close_b :
  forall positions powers left_table right_table n start len next_left,
    StreetlightLeftProgress
      positions powers left_table right_table n start len next_left ->
    (forall left,
       0 <= left ->
       left + len - 1 < n ->
       left <= start <= left + len - 1 ->
       left < next_left) ->
    StreetlightLengthsDone
      positions powers left_table right_table n start (len + 1).
Proof.
  intros positions powers left_table right_table n start len next_left
    Hprogress Hterminal.
  unfold StreetlightLeftProgress in Hprogress.
  destruct Hprogress as [Hdone Hprocessed].
  unfold StreetlightLengthsDone in Hdone |- *.
  destruct Hdone as [Hleft_shape [Hright_shape Hshorter]].
  split; [exact Hleft_shape |].
  split; [exact Hright_shape |].
  intros query_len query_left query_right
    [Hquery_positive Hquery_upper] Hquery_right
    Hquery_left Hquery_right_bound Hquery_contains.
  subst query_right.
  destruct (Z.eq_dec query_len len) as [Hequal | Hunequal].
  - subst query_len.
    apply Hprocessed.
    + split; [exact Hquery_left |].
      apply Hterminal; assumption.
    + reflexivity.
    + exact Hquery_right_bound.
    + exact Hquery_contains.
  - apply Hshorter with
      (len := query_len)
      (left := query_left)
      (right := query_left + query_len - 1).
    + lia.
    + reflexivity.
    + exact Hquery_left.
    + exact Hquery_right_bound.
    + exact Hquery_contains.
Qed.
Lemma streetlight_endpoint_pair_minimum__final_state :
  forall positions powers start left_answer right_answer,
    StreetlightEndpointMinimum positions powers start
      0 (Zlength positions - 1) 0 left_answer ->
    StreetlightEndpointMinimum positions powers start
      0 (Zlength positions - 1) (Zlength positions - 1) right_answer ->
    StreetlightMinimumEnergy positions powers start
      (Z.min left_answer right_answer).
Proof.
  intros positions powers start left_answer right_answer Hleft Hright.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hleft, Hright.
  cbn in Hleft, Hright.
  destruct Hleft as [left_cost [[Hleft_plan Hleft_min] Hleft_value]].
  destruct Hright as [right_cost [[Hright_plan Hright_min] Hright_value]].
  unfold StreetlightMinimumEnergy, StreetlightCompletePlan,
    min_value_of_subset, min_object_of_subset.
  cbn.
  destruct (Z_le_dec left_answer right_answer) as [Horder | Horder].
  - rewrite Z.min_l by exact Horder.
    exists left_cost.
    split.
    + split.
      * exists 0.
        exact Hleft_plan.
      * intros candidate [endpoint Hcandidate].
        assert (Hendpoint :
          endpoint = 0 \/ endpoint = Zlength positions - 1).
        { inversion Hcandidate; auto. }
        destruct Hendpoint as [Hendpoint | Hendpoint]; subst endpoint.
        -- apply Hleft_min.
           exact Hcandidate.
        -- pose proof (Hright_min candidate Hcandidate) as Hbound.
           lia.
    + exact Hleft_value.
  - rewrite Z.min_r by lia.
    exists right_cost.
    split.
    + split.
      * exists (Zlength positions - 1).
        exact Hright_plan.
      * intros candidate [endpoint Hcandidate].
        assert (Hendpoint :
          endpoint = 0 \/ endpoint = Zlength positions - 1).
        { inversion Hcandidate; auto. }
        destruct Hendpoint as [Hendpoint | Hendpoint]; subst endpoint.
        -- pose proof (Hleft_min candidate Hcandidate) as Hbound.
           lia.
        -- apply Hright_min.
           exact Hcandidate.
    + exact Hright_value.
Qed.
Lemma streetlight_plan_endpoint_boundary__final_state :
  forall positions powers start left right endpoint cost,
    StreetlightPlan positions powers start left right endpoint cost ->
    endpoint = left \/ endpoint = right.
Proof.
  intros positions powers start left right endpoint cost Hplan.
  inversion Hplan; auto.
Qed.
Lemma streetlight_adjacent_positions__final_state :
  forall positions,
    (forall i,
      0 <= i ->
      i + 1 < Zlength positions ->
      Znth i positions 0 < Znth (i + 1) positions 0) ->
    forall i j,
      0 <= i ->
      i < j ->
      j < Zlength positions ->
      Znth i positions 0 < Znth j positions 0.
Proof.
  intros positions Hadj i j Hi Hij Hj.
  assert (Hchain :
    forall d k,
      0 <= k ->
      k + Z.of_nat (S d) < Zlength positions ->
      Znth k positions 0 < Znth (k + Z.of_nat (S d)) positions 0).
  { induction d as [| d IHd]; intros k Hk Hb.
    - replace (k + Z.of_nat 1) with (k + 1) by (simpl; lia).
      apply Hadj; lia.
    - eapply Z.lt_trans with (Znth (k + Z.of_nat (S d)) positions 0).
      + apply IHd; [lia |].
        rewrite Nat2Z.inj_succ in Hb.
        lia.
      + replace (k + Z.of_nat (S (S d)))
          with ((k + Z.of_nat (S d)) + 1)
          by (rewrite (Nat2Z.inj_succ (S d)); lia).
        apply Hadj; [lia |].
        rewrite (Nat2Z.inj_succ (S d)) in Hb.
        lia. }
  specialize (Hchain (Z.to_nat (j - i - 1)) i Hi).
  rewrite Nat2Z.inj_succ in Hchain.
  rewrite Z2Nat.id in Hchain by lia.
  replace (i + Z.succ (j - i - 1)) with j in Hchain by lia.
  apply Hchain.
  lia.
Qed.
Lemma streetlight_sublist_sum_bounds__final_state :
  forall powers lo hi,
    (forall i,
      0 <= i < Zlength powers ->
      0 <= Znth i powers 0 <= 100) ->
    0 <= lo <= hi ->
    hi <= Zlength powers ->
    0 <= sum (sublist lo hi powers) <= sum powers.
Proof.
  intros powers lo hi Hrange Hlo Hhi.
  assert (Hsegment :
    forall a b,
      0 <= a <= b ->
      b <= Zlength powers ->
      0 <= sum (sublist a b powers)).
  { intros a b Hab Hb.
    assert (Hentries :
      forall i,
        0 <= i ->
        0 <= Znth i (sublist a b powers) 0 <= 100).
    { intros i Hi.
      destruct (Z_lt_ge_dec i (b - a)) as [Hin | Hout].
      - rewrite Znth_sublist by lia.
        apply Hrange.
        lia.
      - rewrite Znth_sublist_ge by lia.
        lia. }
    pose proof (sum_bound 100 (sublist a b powers) Hentries) as Hsum.
    lia. }
  pose proof (sublist_split 0 (Zlength powers) lo powers
    ltac:(lia) ltac:(lia)) as Hsplit_left.
  pose proof (sublist_split lo (Zlength powers) hi powers
    ltac:(lia) ltac:(lia)) as Hsplit_right.
  rewrite (sublist_self powers (Zlength powers) eq_refl) in Hsplit_left.
  rewrite Hsplit_right in Hsplit_left.
  pose proof (Hsegment 0 lo ltac:(lia) ltac:(lia)) as Hprefix.
  pose proof (Hsegment lo hi ltac:(lia) ltac:(lia)) as Hmiddle.
  pose proof (Hsegment hi (Zlength powers) ltac:(lia) ltac:(lia)) as Hsuffix.
  pose proof (f_equal sum Hsplit_left) as Hsum_parts.
  rewrite !sum_app in Hsum_parts.
  lia.
Qed.
Lemma streetlight_plan_cost_bounds__final_state :
  forall positions powers start,
    Zlength positions <= 50 ->
    Zlength powers = Zlength positions ->
    (forall i,
      0 <= i < Zlength positions ->
      0 <= Znth i positions 0 <= 8000) ->
    (forall i,
      0 <= i /\ i + 1 < Zlength positions ->
      Znth i positions 0 < Znth (i + 1) positions 0) ->
    (forall i,
      0 <= i < Zlength powers ->
      1 <= Znth i powers 0 <= 100) ->
    sum powers <= 5000 ->
    forall left right endpoint cost,
      StreetlightPlan positions powers start left right endpoint cost ->
      0 <= left ->
      left <= start <= right ->
      right < Zlength positions ->
      0 <= cost <= (right - left) * 40000000.
Proof.
  intros positions powers start Hn Hlength Hpositions Hadj Hpowers Hsum.
  assert (Hmono :
    forall i j,
      0 <= i ->
      i < j ->
      j < Zlength positions ->
      Znth i positions 0 < Znth j positions 0).
  { apply streetlight_adjacent_positions__final_state.
    intros i Hi Hnext.
    apply Hadj.
    lia. }
  intros left right endpoint cost Hplan.
  induction Hplan as
    [ Hstart Hpower_length
    | left right endpoint cost Hleft Hcover Hright Hinner IH
    | left right endpoint cost Hleft Hcover Hright Hinner IH ];
    intros Houter_left Houter_cover Houter_right.
  - lia.
  - specialize (IH ltac:(lia) ltac:(lia) ltac:(lia)).
    pose proof
      (streetlight_plan_endpoint_boundary__final_state
        positions powers start (left + 1) right endpoint cost Hinner)
      as Hendpoint.
    destruct Hendpoint as [Hendpoint | Hendpoint]; subst endpoint.
    + pose proof (Hmono left (left + 1) ltac:(lia) ltac:(lia) ltac:(lia))
        as Hposition_order.
      pose proof (Hpositions left ltac:(lia)) as Hposition_left.
      pose proof (Hpositions (left + 1) ltac:(lia)) as Hposition_endpoint.
      pose proof
        (streetlight_sublist_sum_bounds__final_state
          powers (left + 1) (right + 1)
          ltac:(intros i Hi; pose proof (Hpowers i Hi); lia)
          ltac:(lia) ltac:(lia)) as Hcovered.
      nia.
    + pose proof (Hmono left right ltac:(lia) ltac:(lia) ltac:(lia))
        as Hposition_order.
      pose proof (Hpositions left ltac:(lia)) as Hposition_left.
      pose proof (Hpositions right ltac:(lia)) as Hposition_endpoint.
      pose proof
        (streetlight_sublist_sum_bounds__final_state
          powers (left + 1) (right + 1)
          ltac:(intros i Hi; pose proof (Hpowers i Hi); lia)
          ltac:(lia) ltac:(lia)) as Hcovered.
      nia.
  - specialize (IH ltac:(lia) ltac:(lia) ltac:(lia)).
    pose proof
      (streetlight_plan_endpoint_boundary__final_state
        positions powers start left (right - 1) endpoint cost Hinner)
      as Hendpoint.
    destruct Hendpoint as [Hendpoint | Hendpoint]; subst endpoint.
    + pose proof (Hmono left right ltac:(lia) ltac:(lia) ltac:(lia))
        as Hposition_order.
      pose proof (Hpositions left ltac:(lia)) as Hposition_endpoint.
      pose proof (Hpositions right ltac:(lia)) as Hposition_right.
      pose proof
        (streetlight_sublist_sum_bounds__final_state
          powers left right
          ltac:(intros i Hi; pose proof (Hpowers i Hi); lia)
          ltac:(lia) ltac:(lia)) as Hcovered.
      nia.
    + pose proof (Hmono (right - 1) right ltac:(lia) ltac:(lia) ltac:(lia))
        as Hposition_order.
      pose proof (Hpositions (right - 1) ltac:(lia)) as Hposition_endpoint.
      pose proof (Hpositions right ltac:(lia)) as Hposition_right.
      pose proof
        (streetlight_sublist_sum_bounds__final_state
          powers left right
          ltac:(intros i Hi; pose proof (Hpowers i Hi); lia)
          ltac:(lia) ltac:(lia)) as Hcovered.
      nia.
Qed.
Lemma streetlight_endpoint_minimum_bounds__final_state :
  forall positions powers start left right endpoint answer,
    Zlength positions <= 50 ->
    Zlength powers = Zlength positions ->
    (forall i,
      0 <= i < Zlength positions ->
      0 <= Znth i positions 0 <= 8000) ->
    (forall i,
      0 <= i /\ i + 1 < Zlength positions ->
      Znth i positions 0 < Znth (i + 1) positions 0) ->
    (forall i,
      0 <= i < Zlength powers ->
      1 <= Znth i powers 0 <= 100) ->
    sum powers <= 5000 ->
    0 <= left ->
    left <= start <= right ->
    right < Zlength positions ->
    StreetlightEndpointMinimum
      positions powers start left right endpoint answer ->
    0 <= answer <= (right - left) * 40000000.
Proof.
  intros positions powers start left right endpoint answer
    Hn Hlength Hpositions Hadj Hpowers Hsum
    Hleft Hcover Hright Hminimum.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  cbn in Hminimum.
  destruct Hminimum as [cost [[Hplan Hleast] Hvalue]].
  subst answer.
  exact
    (streetlight_plan_cost_bounds__final_state
      positions powers start Hn Hlength Hpositions Hadj Hpowers Hsum
      left right endpoint cost Hplan Hleft Hcover Hright).
Qed.
Lemma streetlight_singleton_minimum__final_state :
  forall positions powers,
    Zlength positions = 1 ->
    Zlength powers = 1 ->
    StreetlightMinimumEnergy positions powers 0 0.
Proof.
  intros positions powers Hpositions Hpowers.
  unfold StreetlightMinimumEnergy, StreetlightCompletePlan,
    min_value_of_subset, min_object_of_subset.
  cbn.
  exists 0.
  split.
  - split.
    + exists 0.
      replace (Zlength positions - 1) with 0 by lia.
      apply StreetlightPlan_start; lia.
    + intros candidate [endpoint Hcandidate].
      inversion Hcandidate; subst; lia.
  - reflexivity.
Qed.
Lemma streetlight_left_endpoint_global__final_state :
  forall positions powers start answer,
    0 < start ->
    start = Zlength positions - 1 ->
    answer <= 1960000000 ->
    StreetlightEndpointMinimum positions powers start
      0 (Zlength positions - 1) 0 answer ->
    StreetlightMinimumEnergy positions powers start
      (Z.min answer 2147483647).
Proof.
  intros positions powers start answer Hstart Hright Hbound Hminimum.
  rewrite Z.min_l by lia.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  cbn in Hminimum.
  destruct Hminimum as [cost [[Hplan Hleast] Hvalue]].
  unfold StreetlightMinimumEnergy, StreetlightCompletePlan,
    min_value_of_subset, min_object_of_subset.
  cbn.
  exists cost.
  split.
  - split.
    + exists 0.
      exact Hplan.
    + intros candidate [endpoint Hcandidate].
      assert (Hendpoint : endpoint = 0).
      { inversion Hcandidate; subst; lia. }
      subst endpoint.
      apply Hleast.
      exact Hcandidate.
  - exact Hvalue.
Qed.
Lemma streetlight_right_endpoint_global__final_state :
  forall positions powers start answer,
    start = 0 ->
    0 < Zlength positions - 1 ->
    answer <= 1960000000 ->
    StreetlightEndpointMinimum positions powers start
      0 (Zlength positions - 1) (Zlength positions - 1) answer ->
    StreetlightMinimumEnergy positions powers start
      (Z.min 2147483647 answer).
Proof.
  intros positions powers start answer Hstart Hright Hbound Hminimum.
  rewrite Z.min_r by lia.
  unfold StreetlightEndpointMinimum, min_value_of_subset,
    min_object_of_subset in Hminimum.
  cbn in Hminimum.
  destruct Hminimum as [cost [[Hplan Hleast] Hvalue]].
  unfold StreetlightMinimumEnergy, StreetlightCompletePlan,
    min_value_of_subset, min_object_of_subset.
  cbn.
  exists cost.
  split.
  - split.
    + exists (Zlength positions - 1).
      exact Hplan.
    + intros candidate [endpoint Hcandidate].
      assert (Hendpoint : endpoint = Zlength positions - 1).
      { inversion Hcandidate; subst; lia. }
      subst endpoint.
      apply Hleast.
      exact Hcandidate.
  - exact Hvalue.
Qed.
Lemma streetlight_final_candidates_cases__final_state :
  forall positions powers left_table right_table n start
    left_answer right_answer,
    Zlength positions = n ->
    Zlength powers = n ->
    1 <= n <= 50 ->
    0 <= start < n ->
    (forall i,
      0 <= i < n ->
      0 <= Znth i positions 0 <= 8000) ->
    (forall i,
      0 <= i /\ i + 1 < n ->
      Znth i positions 0 < Znth (i + 1) positions 0) ->
    (forall i,
      0 <= i < n ->
      1 <= Znth i powers 0 <= 100) ->
    sum powers <= 5000 ->
    StreetlightLeftEntryCorrect
      positions powers start 0 (n - 1) left_answer ->
    StreetlightRightEntryCorrect
      positions powers start 0 (n - 1) right_answer ->
    StreetlightFinalCandidates
      positions powers left_table right_table start
      left_answer right_answer /\
    ((right_answer = 2147483647 /\
      0 <= left_answer /\ left_answer <= 1960000000 /\
      left_answer < 2147483647) \/
     (0 <= left_answer /\ left_answer <= 1960000000 /\
      0 <= right_answer /\ right_answer <= 1960000000 /\
      right_answer < 2147483647) \/
     (0 <= left_answer /\ left_answer <= 1960000000 /\
      0 <= right_answer /\ right_answer <= 1960000000 /\
      left_answer < 2147483647) \/
     (left_answer = 2147483647 /\
      0 <= right_answer /\ right_answer <= 1960000000 /\
      right_answer < 2147483647)).
Proof.
  intros positions powers left_table right_table n start
    left_answer right_answer Hpositions_length Hpowers_length
    Hn Hstart Hpositions Hadj Hpowers Hsum Hleft_entry Hright_entry.
  pose proof Hleft_entry as Hleft_saved.
  pose proof Hright_entry as Hright_saved.
  unfold StreetlightLeftEntryCorrect in Hleft_entry.
  unfold StreetlightRightEntryCorrect in Hright_entry.
  destruct Hleft_entry as
    [[Hleft_start [Hright_start Hleft_value]] |
     [[Hleft_lt Hleft_minimum] |
      [Hleft_start [Hstart_right Hleft_value]]]].
  - destruct Hright_entry as
      [[Hleft_start' [Hright_start' Hright_value]] |
       [[Hstart_right' Hright_minimum] |
        [Hleft_start' [Hright_start' Hright_value]]]].
    + assert (n = 1) by lia.
      assert (Hpositions_one : Zlength positions = 1) by lia.
      assert (Hpowers_one : Zlength powers = 1) by lia.
      subst n start left_answer right_answer.
      assert (Hglobal : StreetlightMinimumEnergy positions powers 0 0).
      { apply streetlight_singleton_minimum__final_state; assumption. }
      split.
      * unfold StreetlightFinalCandidates.
        split.
        -- exact Hleft_saved.
        -- split.
           ++ exact Hright_saved.
           ++ exact Hglobal.
      * right; left; lia.
    + exfalso; lia.
    + exfalso; lia.
  - destruct Hright_entry as
      [[Hleft_start' [Hright_start' Hright_value]] |
       [[Hstart_right' Hright_minimum] |
        [Hleft_start' [Hright_start' Hright_value]]]].
    + exfalso; lia.
    + assert (Hleft_bound : 0 <= left_answer <= 1960000000).
      { pose proof
          (streetlight_endpoint_minimum_bounds__final_state
            positions powers start 0 (n - 1) 0 left_answer
            ltac:(lia) ltac:(lia)
            ltac:(intros i Hi; apply Hpositions; lia)
            ltac:(intros i Hi; apply Hadj; lia)
            ltac:(intros i Hi; apply Hpowers; lia)
            Hsum ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
          as Hbound.
        nia. }
      assert (Hright_bound : 0 <= right_answer <= 1960000000).
      { pose proof
          (streetlight_endpoint_minimum_bounds__final_state
            positions powers start 0 (n - 1) (n - 1) right_answer
            ltac:(lia) ltac:(lia)
            ltac:(intros i Hi; apply Hpositions; lia)
            ltac:(intros i Hi; apply Hadj; lia)
            ltac:(intros i Hi; apply Hpowers; lia)
            Hsum ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
          as Hbound.
        nia. }
      assert (Hglobal :
        StreetlightMinimumEnergy positions powers start
          (Z.min left_answer right_answer)).
      { apply streetlight_endpoint_pair_minimum__final_state;
          rewrite Hpositions_length; assumption. }
      split.
      * unfold StreetlightFinalCandidates.
        rewrite Hpositions_length.
        repeat split; assumption.
      * right; left; lia.
    + subst right_answer.
      assert (Hleft_bound : 0 <= left_answer <= 1960000000).
      { pose proof
          (streetlight_endpoint_minimum_bounds__final_state
            positions powers start 0 (n - 1) 0 left_answer
            ltac:(lia) ltac:(lia)
            ltac:(intros i Hi; apply Hpositions; lia)
            ltac:(intros i Hi; apply Hadj; lia)
            ltac:(intros i Hi; apply Hpowers; lia)
            Hsum ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
          as Hbound.
        nia. }
      assert (Hglobal :
        StreetlightMinimumEnergy positions powers start
          (Z.min left_answer 2147483647)).
      { apply streetlight_left_endpoint_global__final_state;
          try lia.
        rewrite Hpositions_length.
        exact Hleft_minimum. }
      split.
      * unfold StreetlightFinalCandidates.
        rewrite Hpositions_length.
        repeat split; assumption.
      * left; lia.
  - destruct Hright_entry as
      [[Hleft_start' [Hright_start' Hright_value]] |
       [[Hstart_right' Hright_minimum] |
        [Hleft_start' [Hright_start' Hright_value]]]].
    + exfalso; lia.
    + subst left_answer.
      assert (Hright_bound : 0 <= right_answer <= 1960000000).
      { pose proof
          (streetlight_endpoint_minimum_bounds__final_state
            positions powers start 0 (n - 1) (n - 1) right_answer
            ltac:(lia) ltac:(lia)
            ltac:(intros i Hi; apply Hpositions; lia)
            ltac:(intros i Hi; apply Hadj; lia)
            ltac:(intros i Hi; apply Hpowers; lia)
            Hsum ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
          as Hbound.
        nia. }
      assert (Hglobal :
        StreetlightMinimumEnergy positions powers start
          (Z.min 2147483647 right_answer)).
      { apply streetlight_right_endpoint_global__final_state;
          try lia.
        rewrite Hpositions_length.
        exact Hright_minimum. }
      split.
      * unfold StreetlightFinalCandidates.
        rewrite Hpositions_length.
        repeat split; assumption.
      * right; right; right; lia.
    + exfalso; lia.
Qed.
