Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ChoirStrictlyIncreasingValues
    (heights indices : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength indices ->
    Znth (Znth p indices 0) heights 0 <
    Znth (Znth q indices 0) heights 0.

Definition ChoirStrictlyDecreasingValues
    (heights indices : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength indices ->
    Znth (Znth q indices 0) heights 0 <
    Znth (Znth p indices 0) heights 0.

Definition ChoirValidIncreasingEndingAt
    (heights : list Z) (peak : Z) (indices : list Z) : Prop :=
  0 <= peak < Zlength heights /\
  Forall (fun idx => 0 <= idx <= peak) indices /\
  mono_inc indices /\
  ChoirStrictlyIncreasingValues heights indices /\
  exists prefix, indices = prefix ++ peak :: nil.

Definition ChoirValidDecreasingStartingAt
    (heights : list Z) (peak : Z) (indices : list Z) : Prop :=
  0 <= peak < Zlength heights /\
  Forall (fun idx => peak <= idx < Zlength heights) indices /\
  mono_inc indices /\
  ChoirStrictlyDecreasingValues heights indices /\
  exists suffix, indices = peak :: suffix.

Definition ChoirLeftLength
    (heights : list Z) (peak answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun indices => ChoirValidIncreasingEndingAt heights peak indices)
    (fun indices => Zlength indices)
    answer.

Definition ChoirRightLength
    (heights : list Z) (peak answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun indices => ChoirValidDecreasingStartingAt heights peak indices)
    (fun indices => Zlength indices)
    answer.

Definition ChoirOnesPrefix (values : list Z) (written : Z) : Prop :=
  Zlength values = written /\
  forall k, 0 <= k < written -> Znth k values 0 = 1.

Definition ChoirOnesFull (values : list Z) (n : Z) : Prop :=
  Zlength values = n /\
  forall k, 0 <= k < n -> Znth k values 0 = 1.

Definition ChoirDPLeftPrefix
    (heights dp_left : list Z) (hi : Z) : Prop :=
  0 <= hi <= Zlength heights /\
  Zlength dp_left = Zlength heights /\
  (forall k,
      0 <= k < hi ->
      ChoirLeftLength heights k (Znth k dp_left 0) /\
      1 <= Znth k dp_left 0 <= k + 1) /\
  (forall k,
      hi <= k < Zlength heights ->
      Znth k dp_left 0 = 1).

Definition ChoirLeftCandidate
    (heights dp_left : list Z)
    (peak scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    scanned <= k < peak /\
    Znth k heights 0 < Znth peak heights 0 /\
    candidate = Znth k dp_left 0 + 1.

Definition ChoirLeftInnerProgress
    (heights dp_left : list Z) (peak scanned : Z) : Prop :=
  0 <= peak < Zlength heights /\
  0 <= scanned <= peak /\
  Zlength dp_left = Zlength heights /\
  (forall k,
      0 <= k < peak ->
      ChoirLeftLength heights k (Znth k dp_left 0) /\
      1 <= Znth k dp_left 0 <= k + 1) /\
  (forall k,
      peak < k < Zlength heights ->
      Znth k dp_left 0 = 1) /\
  max_value_of_subset Z.le
    (fun candidate =>
       ChoirLeftCandidate heights dp_left peak scanned candidate)
    (fun candidate => candidate)
    (Znth peak dp_left 0) /\
  1 <= Znth peak dp_left 0 <= peak + 1.

Definition ChoirDPRightSuffix
    (heights dp_right : list Z) (lo : Z) : Prop :=
  0 <= lo <= Zlength heights /\
  Zlength dp_right = Zlength heights /\
  (forall k,
      lo <= k < Zlength heights ->
      ChoirRightLength heights k (Znth k dp_right 0) /\
      1 <= Znth k dp_right 0 <= Zlength heights - k) /\
  (forall k,
      0 <= k < lo ->
      Znth k dp_right 0 = 1).

Definition ChoirRightCandidate
    (heights dp_right : list Z)
    (peak scanned candidate : Z) : Prop :=
  candidate = 1 \/
  exists k,
    peak < k < scanned /\
    Znth k heights 0 < Znth peak heights 0 /\
    candidate = Znth k dp_right 0 + 1.

Definition ChoirRightInnerProgress
    (heights dp_right : list Z) (peak scanned : Z) : Prop :=
  0 <= peak < Zlength heights /\
  peak + 1 <= scanned <= Zlength heights /\
  Zlength dp_right = Zlength heights /\
  (forall k,
      peak < k < Zlength heights ->
      ChoirRightLength heights k (Znth k dp_right 0) /\
      1 <= Znth k dp_right 0 <= Zlength heights - k) /\
  (forall k,
      0 <= k < peak ->
      Znth k dp_right 0 = 1) /\
  max_value_of_subset Z.le
    (fun candidate =>
       ChoirRightCandidate heights dp_right peak scanned candidate)
    (fun candidate => candidate)
    (Znth peak dp_right 0) /\
  1 <= Znth peak dp_right 0 <= Zlength heights - peak.

Definition ChoirPeakLength
    (heights : list Z) (peak answer : Z) : Prop :=
  exists left right,
    ChoirLeftLength heights peak left /\
    ChoirRightLength heights peak right /\
    answer = left + right - 1.

Definition ChoirBestPrefix
    (heights : list Z) (limit answer : Z) : Prop :=
  0 <= limit <= Zlength heights /\
  ((limit = 0 /\ answer = 0) \/
   (0 < limit /\
    max_value_of_subset Z.le
      (fun candidate =>
         exists peak,
           0 <= peak < limit /\
           ChoirPeakLength heights peak candidate)
      (fun candidate => candidate)
      answer)).

Definition ChoirLength (heights : list Z) (answer : Z) : Prop :=
  ChoirBestPrefix heights (Zlength heights) answer.

Definition ChoirMinimumRemovals
    (heights : list Z) (removed : Z) : Prop :=
  exists best,
    ChoirLength heights best /\
    removed = Zlength heights - best.

Lemma choir_ones_prefix_snoc__ones_initialization :
  forall values written,
    ChoirOnesPrefix values written ->
    ChoirOnesPrefix (values ++ [1]) (written + 1).
Proof.
  intros values written [Hlength Hones].
  unfold ChoirOnesPrefix.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k written) as [Hbefore | Hat_or_after].
    + rewrite app_Znth1 by lia.
      apply Hones.
      lia.
    + assert (k = written) by lia.
      subst k.
      rewrite app_Znth2 by lia.
      rewrite Hlength.
      replace (written - written) with 0 by lia.
      reflexivity.
Qed.
Lemma choir_left_inner_progress_base__ones_initialization :
  forall heights dp peak,
    ChoirDPLeftPrefix heights dp peak ->
    0 <= peak < Zlength heights ->
    ChoirLeftInnerProgress heights dp peak peak.
Proof.
  intros heights dp peak Hprefix Hpeak.
  unfold ChoirDPLeftPrefix in Hprefix.
  destruct Hprefix as
      [Hhi [Hlength [Hcomputed Huncomputed]]].
  assert (Hpeak_value : Znth peak dp 0 = 1).
  {
    apply Huncomputed.
    lia.
  }
  unfold ChoirLeftInnerProgress.
  split; [exact Hpeak |].
  split; [lia |].
  split; [exact Hlength |].
  split; [exact Hcomputed |].
  split.
  - intros k Hk.
    apply Huncomputed.
    lia.
  - split.
    + unfold max_value_of_subset, max_object_of_subset.
      exists 1.
      rewrite Hpeak_value.
      split.
      * split.
        -- unfold ChoirLeftCandidate.
           left.
           reflexivity.
        -- intros candidate Hcandidate.
           unfold ChoirLeftCandidate in Hcandidate.
           destruct Hcandidate as [-> | [k [[Hscan Hbefore] [_ ->]]]].
           ++ lia.
           ++ lia.
      * reflexivity.
    + rewrite Hpeak_value.
      lia.
Qed.
Lemma choir_left_progress_step_update__left_dp_transitions :
  forall heights dp peak j,
    ChoirLeftInnerProgress heights dp peak (j + 1) ->
    0 <= j < peak ->
    Znth j heights 0 < Znth peak heights 0 ->
    Znth peak dp 0 < Znth j dp 0 + 1 ->
    ChoirLeftInnerProgress heights
      (replace_Znth peak (Znth j dp 0 + 1) dp) peak j.
Proof.
  intros heights dp peak j Hprogress Hj Hheight Himproved.
  unfold ChoirLeftInnerProgress in *.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hprefix [Hsuffix [Hmaximum Hbounds]]]]]].
  assert (Hpeak_dp : 0 <= peak < Zlength dp) by (rewrite Hlen; lia).
  split; [exact Hpeak |].
  split; [lia |].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros k Hk.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hprefix. exact Hk.
    + split.
      * intros k Hk.
        rewrite Znth_replace_Znth_Diff by lia.
        apply Hsuffix. exact Hk.
      * split.
        -- unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
           destruct Hmaximum as
             [old_best [[Hold_candidate Hold_upper] Hold_eq]].
           exists (Znth j dp 0 + 1).
           split.
           ++ split.
              ** right. exists j. repeat split; try lia; auto.
                 rewrite Znth_replace_Znth_Diff by lia. reflexivity.
              ** intros candidate Hcandidate.
                 unfold ChoirLeftCandidate in Hcandidate.
                 destruct Hcandidate as
                   [Hone | [k [Hk [Hheight_k Hcandidate]]]].
                 --- subst candidate. lia.
                 --- rewrite Znth_replace_Znth_Diff in Hcandidate by lia.
                     destruct (Z.eq_dec k j) as [-> | Hkj].
                     +++ lia.
                     +++ assert (Hk_old : j + 1 <= k < peak) by lia.
                         specialize (Hold_upper (Znth k dp 0 + 1)).
                         assert (Hold_k :
                           ChoirLeftCandidate heights dp peak (j + 1)
                             (Znth k dp 0 + 1)).
                         {
                           right. exists k. split; [exact Hk_old |].
                           split; [exact Hheight_k | reflexivity].
                         }
                         specialize (Hold_upper Hold_k).
                         simpl in Hold_upper. lia.
           ++ rewrite Znth_replace_Znth_Same by exact Hpeak_dp.
              reflexivity.
        -- rewrite Znth_replace_Znth_Same by exact Hpeak_dp.
           specialize (Hprefix j Hj) as [_ Hj_bounds].
           lia.
Qed.
Lemma choir_left_progress_step_ineligible__left_dp_transitions :
  forall heights dp peak j,
    ChoirLeftInnerProgress heights dp peak (j + 1) ->
    0 <= j < peak ->
    Znth peak heights 0 <= Znth j heights 0 ->
    ChoirLeftInnerProgress heights dp peak j.
Proof.
  intros heights dp peak j Hprogress Hj Hineligible.
  unfold ChoirLeftInnerProgress in *.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hprefix [Hsuffix [Hmaximum Hbounds]]]]]].
  split; [exact Hpeak |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hprefix |].
  split; [exact Hsuffix |].
  split.
  - unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best. split.
    + split.
      * unfold ChoirLeftCandidate in *.
        destruct Hbest_candidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- left. exact Hone.
        -- right. exists k. split; [lia |].
           split; [exact Hheight_k | exact Hcandidate].
      * intros candidate Hcandidate.
        apply Hbest_upper.
        unfold ChoirLeftCandidate in *.
        destruct Hcandidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- left. exact Hone.
        -- destruct (Z.eq_dec k j) as [-> | Hkj].
           ++ lia.
           ++ right. exists k. split; [lia |].
              split; [exact Hheight_k | exact Hcandidate].
    + exact Hbest_eq.
  - exact Hbounds.
Qed.
Lemma choir_left_progress_step_dominated__left_dp_transitions :
  forall heights dp peak j,
    ChoirLeftInnerProgress heights dp peak (j + 1) ->
    0 <= j < peak ->
    Znth j heights 0 < Znth peak heights 0 ->
    Znth j dp 0 + 1 <= Znth peak dp 0 ->
    ChoirLeftInnerProgress heights dp peak j.
Proof.
  intros heights dp peak j Hprogress Hj Hheight Hdominated.
  unfold ChoirLeftInnerProgress in *.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hprefix [Hsuffix [Hmaximum Hbounds]]]]]].
  split; [exact Hpeak |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hprefix |].
  split; [exact Hsuffix |].
  split.
  - unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best. split.
    + split.
      * unfold ChoirLeftCandidate in *.
        destruct Hbest_candidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- left. exact Hone.
        -- right. exists k. split; [lia |].
           split; [exact Hheight_k | exact Hcandidate].
      * intros candidate Hcandidate.
        unfold ChoirLeftCandidate in Hcandidate.
        destruct Hcandidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- apply Hbest_upper. left. exact Hone.
        -- destruct (Z.eq_dec k j) as [-> | Hkj].
           ++ subst candidate. rewrite Hbest_eq. exact Hdominated.
           ++ apply Hbest_upper. right. exists k. split; [lia |].
              split; [exact Hheight_k | exact Hcandidate].
    + exact Hbest_eq.
  - exact Hbounds.
Qed.
Lemma choir_left_progress_complete__left_dp_transitions :
  forall heights dp peak,
    ChoirLeftInnerProgress heights dp peak 0 ->
    ChoirDPLeftPrefix heights dp (peak + 1).
Proof.
  intros heights dp peak Hprogress.
  unfold ChoirLeftInnerProgress in Hprogress.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hprefix [Hsuffix
      [Hcandidate_max Hcurrent_bounds]]]]]].
  assert (Hvalid_singleton :
    forall i,
      0 <= i < Zlength heights ->
      ChoirValidIncreasingEndingAt heights i (i :: nil)).
  {
    intros i Hi.
    unfold ChoirValidIncreasingEndingAt.
    split; [exact Hi |].
    split.
    - constructor; [lia | constructor].
    - split.
      + apply mono_inc_single.
      + split.
        * unfold ChoirStrictlyIncreasingValues.
          intros p q [Hp [Hpq Hq]].
          rewrite Zlength_cons, Zlength_nil in Hq. lia.
        * exists nil. reflexivity.
  }
  assert (Hvalid_extend :
    forall k i idxs,
      ChoirValidIncreasingEndingAt heights k idxs ->
      0 <= i < Zlength heights ->
      k < i ->
      Znth k heights 0 < Znth i heights 0 ->
      ChoirValidIncreasingEndingAt heights i (idxs ++ i :: nil) /\
      Zlength (idxs ++ i :: nil) = Zlength idxs + 1).
  {
    intros k i idxs Hending Hi Hki Hvalues_ki.
    unfold ChoirValidIncreasingEndingAt in Hending.
    destruct Hending as
      [Hk [Hall [Hmono [Hvalues [prefix Hidxs]]]]].
    assert (Hlen_pos : 0 < Zlength idxs).
    {
      rewrite Hidxs, Zlength_app_cons.
      pose proof (Zlength_nonneg prefix). lia.
    }
    assert (Hlast : Znth (Zlength idxs - 1) idxs 0 = k).
    {
      rewrite Hidxs, Zlength_app_cons.
      replace (Zlength prefix + 1 - 1) with (Zlength prefix) by lia.
      rewrite app_Znth2 by lia.
      replace (Zlength prefix - Zlength prefix) with 0 by lia.
      reflexivity.
    }
    split.
    - unfold ChoirValidIncreasingEndingAt.
      split; [exact Hi |].
      split.
      + apply Forall_app. split.
        * eapply Forall_impl with
            (P := fun x => 0 <= x <= k).
          -- intros x Hx. lia.
          -- exact Hall.
        * constructor; [lia | constructor].
      + split.
        * unfold mono_inc in *.
          intros p q Hp Hpq Hq.
          rewrite Zlength_app_cons in Hq.
          destruct (Z_lt_ge_dec q (Zlength idxs))
            as [Hq_old | Hq_last].
          -- rewrite !app_Znth1 by lia.
             apply Hmono; lia.
          -- assert (q = Zlength idxs) by lia. subst q.
             rewrite
               (app_Znth2 0 idxs (i :: nil) (Zlength idxs))
               by lia.
             replace (Zlength idxs - Zlength idxs) with 0 by lia.
             rewrite Znth0_cons.
             rewrite app_Znth1 by lia.
             pose proof
               ((proj1 (Forall_Znth
                 (fun x => 0 <= x <= k) 0 idxs))
                 Hall p ltac:(lia)) as Hp_bound.
             destruct Hp_bound as [_ Hp_k].
             lia.
        * split.
          -- unfold ChoirStrictlyIncreasingValues in *.
             intros p q [Hp [Hpq Hq]].
             rewrite Zlength_app_cons in Hq.
             destruct (Z_lt_ge_dec q (Zlength idxs))
               as [Hq_old | Hq_last].
             ++ rewrite !app_Znth1 by lia.
                apply Hvalues. lia.
             ++ assert (q = Zlength idxs) by lia. subst q.
                rewrite
                  (app_Znth2 0 idxs (i :: nil) (Zlength idxs))
                  by lia.
                replace (Zlength idxs - Zlength idxs) with 0 by lia.
                rewrite Znth0_cons.
                rewrite app_Znth1 by lia.
                destruct (Z.eq_dec p (Zlength idxs - 1))
                  as [Hp_last | Hp_old].
                ** subst p. rewrite Hlast. exact Hvalues_ki.
                ** pose proof
                     (Hvalues p (Zlength idxs - 1)
                       ltac:(lia)) as Hp_to_last.
                   rewrite Hlast in Hp_to_last. lia.
          -- exists idxs. reflexivity.
    - rewrite Zlength_app_cons. reflexivity.
  }
  assert (Hvalid_split :
    forall i idxs,
      ChoirValidIncreasingEndingAt heights i idxs ->
      idxs = i :: nil \/
      exists prefix k,
        idxs = prefix ++ i :: nil /\
        ChoirValidIncreasingEndingAt heights k prefix /\
        k < i /\
        Znth k heights 0 < Znth i heights 0 /\
        Zlength idxs = Zlength prefix + 1).
  {
    intros i idxs Hending.
    unfold ChoirValidIncreasingEndingAt in Hending.
    destruct Hending as
      [Hi [Hall [Hmono [Hvalues [before Hidxs]]]]].
    destruct before as [| a rest].
    - left. simpl in Hidxs. exact Hidxs.
    - assert (Hnonempty : a :: rest <> nil) by discriminate.
      destruct (exists_last Hnonempty) as [before0 [k Hbefore]].
      assert (Hlen_pos : 0 < Zlength (a :: rest)).
      {
        rewrite Hbefore, Zlength_app_cons.
        pose proof (Zlength_nonneg before0). lia.
      }
      assert (Hlast :
        Znth (Zlength (a :: rest) - 1) (a :: rest) 0 = k).
      {
        rewrite Hbefore, Zlength_app_cons.
        replace (Zlength before0 + 1 - 1) with
          (Zlength before0) by lia.
        rewrite app_Znth2 by lia.
        replace (Zlength before0 - Zlength before0) with 0 by lia.
        reflexivity.
      }
      rewrite Hidxs in Hall, Hmono, Hvalues.
      apply Forall_app in Hall as [Hall_before Hall_i].
      assert (Hk_bound : 0 <= k <= i).
      {
        pose proof
          ((proj1 (Forall_Znth
            (fun x => 0 <= x <= i) 0 (a :: rest)))
            Hall_before (Zlength (a :: rest) - 1)
            ltac:(lia)) as Hbound.
        rewrite Hlast in Hbound. exact Hbound.
      }
      assert (Hki : k < i).
      {
        unfold mono_inc in Hmono.
        pose proof
          (Hmono (Zlength (a :: rest) - 1)
            (Zlength (a :: rest))
            ltac:(lia) ltac:(lia)
            ltac:(rewrite Zlength_app_cons; lia)) as Hord.
        rewrite app_Znth1 in Hord by lia.
        rewrite app_Znth2 in Hord by lia.
        replace (Zlength (a :: rest) - Zlength (a :: rest))
          with 0 in Hord by lia.
        rewrite Znth0_cons in Hord.
        rewrite Hlast in Hord. exact Hord.
      }
      assert (Hvalues_ki :
        Znth k heights 0 < Znth i heights 0).
      {
        unfold ChoirStrictlyIncreasingValues in Hvalues.
        pose proof
          (Hvalues (Zlength (a :: rest) - 1)
            (Zlength (a :: rest))
            ltac:(rewrite Zlength_app_cons; lia)) as Hord.
        rewrite app_Znth1 in Hord by lia.
        rewrite app_Znth2 in Hord by lia.
        replace (Zlength (a :: rest) - Zlength (a :: rest))
          with 0 in Hord by lia.
        rewrite Znth0_cons in Hord.
        rewrite Hlast in Hord. exact Hord.
      }
      right. exists (a :: rest), k.
      split; [exact Hidxs |].
      split.
      + unfold ChoirValidIncreasingEndingAt.
        split; [lia |].
        split.
        * apply (proj2
            (Forall_Znth
              (fun x => 0 <= x <= k) 0 (a :: rest))).
          intros p Hp.
          pose proof
            ((proj1 (Forall_Znth
              (fun x => 0 <= x <= i) 0 (a :: rest)))
              Hall_before p Hp) as Hp_bound.
          destruct Hp_bound as [Hp_nonneg Hp_before_i].
          destruct (Z.eq_dec p (Zlength (a :: rest) - 1))
            as [Hp_last | Hp_old].
          -- subst p. rewrite Hlast. lia.
          -- assert (p < Zlength (a :: rest) - 1) by lia.
             unfold mono_inc in Hmono.
             pose proof
               (Hmono p (Zlength (a :: rest) - 1)
                 ltac:(lia) ltac:(lia)
                 ltac:(rewrite Zlength_app_cons; lia)) as Hp_to_last.
             rewrite !app_Znth1 in Hp_to_last by lia.
             rewrite Hlast in Hp_to_last.
             split; [exact Hp_nonneg | lia].
        * split.
          -- unfold mono_inc in *.
             intros p q Hp Hpq Hq.
             specialize (Hmono p q Hp Hpq
               ltac:(rewrite Zlength_app_cons; lia)).
             rewrite !app_Znth1 in Hmono by lia.
             exact Hmono.
          -- split.
             ++ unfold ChoirStrictlyIncreasingValues in *.
                intros p q Hpq.
                specialize (Hvalues p q
                  ltac:(rewrite Zlength_app_cons; lia)).
                rewrite !app_Znth1 in Hvalues by lia.
                exact Hvalues.
             ++ exists before0. exact Hbefore.
      + split; [exact Hki |].
        split; [exact Hvalues_ki |].
        rewrite Hidxs, Zlength_app_cons. reflexivity.
  }
  assert (Hcandidate_to_valid :
    forall candidate,
      ChoirLeftCandidate heights dp peak 0 candidate ->
      exists idxs,
        ChoirValidIncreasingEndingAt heights peak idxs /\
        Zlength idxs = candidate).
  {
    intros candidate Hcandidate.
    unfold ChoirLeftCandidate in Hcandidate.
    destruct Hcandidate as
      [Hone | [k [Hk [Hvalues Hcandidate]]]].
    - subst candidate. exists (peak :: nil). split.
      + apply Hvalid_singleton. exact Hpeak.
      + rewrite Zlength_cons, Zlength_nil. lia.
    - specialize (Hprefix k Hk) as [Hending_k Hbounds_k].
      unfold ChoirLeftLength,
        MaxMin.max_value_of_subset, MaxMin.max_object_of_subset
        in Hending_k.
      destruct Hending_k as
        [idxs [[Hvalid_k Hupper_k] Hidxs_len]].
      destruct
        (Hvalid_extend k peak idxs Hvalid_k Hpeak
          ltac:(lia) Hvalues)
        as [Hvalid_peak Hlen_snoc].
      exists (idxs ++ peak :: nil). split; [exact Hvalid_peak |].
      lia.
  }
  assert (Hvalid_to_candidate_bound :
    forall idxs,
      ChoirValidIncreasingEndingAt heights peak idxs ->
      exists candidate,
        ChoirLeftCandidate heights dp peak 0 candidate /\
        Zlength idxs <= candidate).
  {
    intros idxs Hvalid.
    destruct (Hvalid_split peak idxs Hvalid)
      as [Hsingle |
          [prefix [k
            [Hidxs [Hvalid_k [Hki [Hvalues Hidxs_len]]]]]]].
    - exists 1. split.
      + left. reflexivity.
      + rewrite Hsingle, Zlength_cons, Zlength_nil. lia.
    - pose proof Hvalid_k as Hvalid_k_bounds.
      unfold ChoirValidIncreasingEndingAt in Hvalid_k_bounds.
      destruct Hvalid_k_bounds as [Hk_in_heights _].
      assert (Hk_nonneg : 0 <= k) by lia.
      specialize (Hprefix k (conj Hk_nonneg Hki))
        as [Hending_k Hbounds_k].
      unfold ChoirLeftLength,
        MaxMin.max_value_of_subset, MaxMin.max_object_of_subset
        in Hending_k.
      destruct Hending_k as
        [best_idxs [[Hbest_valid Hbest_upper] Hbest_len]].
      specialize (Hbest_upper prefix Hvalid_k).
      exists (Znth k dp 0 + 1). split.
      + right. exists k. split; [lia |].
        split; [exact Hvalues | reflexivity].
      + lia.
  }
  assert (Hending_peak :
    ChoirLeftLength heights peak (Znth peak dp 0)).
  {
    unfold ChoirLeftLength,
      MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hcandidate_max as
      [best_candidate [[Hbest_candidate Hbest_upper] Hbest_eq]].
    destruct (Hcandidate_to_valid best_candidate Hbest_candidate)
      as [best_idxs [Hbest_valid Hbest_len]].
    exists best_idxs. split.
    - split; [exact Hbest_valid |].
      intros idxs Hvalid.
      destruct (Hvalid_to_candidate_bound idxs Hvalid)
        as [candidate [Hcandidate Hlen_bound]].
      specialize (Hbest_upper candidate Hcandidate).
      lia.
    - lia.
  }
  unfold ChoirDPLeftPrefix.
  split; [lia |].
  split; [exact Hlen |].
  split.
  - intros k Hk.
    destruct (Z_lt_ge_dec k peak) as [Hk_old | Hk_last].
    + apply Hprefix. lia.
    + assert (k = peak) by lia. subst k.
      split; [exact Hending_peak | exact Hcurrent_bounds].
  - intros k Hk.
    apply Hsuffix. lia.
Qed.
Lemma choir_right_suffix_from_ones__phase_bridges :
  forall heights dp n,
    ChoirOnesFull dp n ->
    Zlength heights = n ->
    ChoirDPRightSuffix heights dp n.
Proof.
  intros heights dp n [Hdp_len Hdp_one] Hheights_len.
  pose proof (Zlength_nonneg heights) as Hheights_nonneg.
  unfold ChoirDPRightSuffix.
  split.
  - split; lia.
  - split.
    + lia.
    + split.
      * intros k Hk.
        exfalso.
        lia.
      * intros k Hk.
        apply Hdp_one.
        lia.
Qed.
Lemma choir_right_inner_progress_base__phase_bridges :
  forall heights dp peak,
    0 <= peak ->
    ChoirDPRightSuffix heights dp (peak + 1) ->
    ChoirRightInnerProgress heights dp peak (peak + 1).
Proof.
  intros heights dp peak Hpeak
    [Hrange [Hdp_len [Hcomputed Hones]]].
  assert (Hpeak_one : Znth peak dp 0 = 1).
  {
    apply Hones.
    lia.
  }
  unfold ChoirRightInnerProgress.
  split.
  - split; lia.
  - split.
    + split; lia.
    + split.
      * exact Hdp_len.
      * split.
        -- intros k Hk.
           apply Hcomputed.
           lia.
        -- split.
           ++ intros k Hk.
              apply Hones.
              lia.
           ++ split.
              ** rewrite Hpeak_one.
                 apply
                   (@max_1 Z Z.le Zle_TotalOrder Z 1
                      (fun candidate =>
                         ChoirRightCandidate
                           heights dp peak (peak + 1) candidate)
                      (fun candidate => candidate)).
                 intros candidate.
                 unfold ChoirRightCandidate.
                 split.
                 --- intros [Hcandidate | [k [Hk _]]].
                     ++++ lia.
                     ++++ exfalso.
                          lia.
                 --- intros Hcandidate.
                     left.
                     lia.
              ** split.
                 --- lia.
                 --- rewrite Hpeak_one.
                     lia.
Qed.
Lemma choir_right_progress_step_update__right_dp_transitions :
  forall heights dp_right peak scanned,
    ChoirRightInnerProgress heights dp_right peak scanned ->
    scanned < Zlength heights ->
    Znth scanned heights 0 < Znth peak heights 0 ->
    Znth peak dp_right 0 < Znth scanned dp_right 0 + 1 ->
    ChoirRightInnerProgress heights
      (replace_Znth peak (Znth scanned dp_right 0 + 1) dp_right)
      peak (scanned + 1).
Proof.
  intros heights dp_right peak scanned
    Hprogress Hscanned Hheight Himproves.
  unfold ChoirRightInnerProgress in *.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hsuffix [Hones [Hmaximum Hcurrent_bounds]]]]]].
  assert (Hpeak_dp : 0 <= peak < Zlength dp_right)
    by (rewrite Hlen; lia).
  assert (Hscanned_dp : 0 <= scanned < Zlength dp_right)
    by (rewrite Hlen; lia).
  pose proof (Hsuffix scanned ltac:(lia))
    as [Hright_scanned Hscanned_bounds].
  split; [exact Hpeak |].
  split; [lia |].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros k Hk.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hsuffix. exact Hk.
    + split.
      * intros k Hk.
        rewrite Znth_replace_Znth_Diff by lia.
        apply Hones. exact Hk.
      * split.
        -- unfold MaxMin.max_value_of_subset,
             MaxMin.max_object_of_subset in *.
           destruct Hmaximum as
             [old_best [[Hold_candidate Hold_upper] Hold_eq]].
           exists (Znth scanned dp_right 0 + 1).
           split.
           ++ split.
              ** right. exists scanned. repeat split; try lia.
                 rewrite Znth_replace_Znth_Diff by lia.
                 reflexivity.
              ** intros candidate Hcandidate.
                 unfold ChoirRightCandidate in Hcandidate.
                 destruct Hcandidate as
                   [Hone | [k [Hk [Hheight_k Hcandidate]]]].
                 --- subst candidate. lia.
                 --- rewrite Znth_replace_Znth_Diff in Hcandidate by lia.
                     destruct (Z.eq_dec k scanned) as [-> | Hneq].
                     +++ lia.
                     +++ assert (Hk_old : peak < k < scanned) by lia.
                         specialize (Hold_upper (Znth k dp_right 0 + 1)).
                         assert (Hold_k :
                           ChoirRightCandidate heights dp_right
                             peak scanned (Znth k dp_right 0 + 1)).
                         { right. exists k. split; [exact Hk_old |].
                           split; [exact Hheight_k | reflexivity]. }
                         specialize (Hold_upper Hold_k).
                         simpl in Hold_upper. lia.
           ++ rewrite Znth_replace_Znth_Same by exact Hpeak_dp.
              reflexivity.
        -- rewrite Znth_replace_Znth_Same by exact Hpeak_dp.
           lia.
Qed.
Lemma choir_right_progress_step_ineligible__right_dp_transitions :
  forall heights dp_right peak scanned,
    ChoirRightInnerProgress heights dp_right peak scanned ->
    scanned < Zlength heights ->
    Znth peak heights 0 <= Znth scanned heights 0 ->
    ChoirRightInnerProgress heights dp_right peak (scanned + 1).
Proof.
  intros heights dp_right peak scanned
    Hprogress Hscanned Hheight.
  unfold ChoirRightInnerProgress in *.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hsuffix [Hones [Hmaximum Hcurrent_bounds]]]]]].
  split; [exact Hpeak |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hsuffix |].
  split; [exact Hones |].
  split.
  - unfold MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best. split.
    + split.
      * unfold ChoirRightCandidate in *.
        destruct Hbest_candidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- left. exact Hone.
        -- right. exists k. split; [lia |].
           split; [exact Hheight_k | exact Hcandidate].
      * intros candidate Hcandidate.
        apply Hbest_upper.
        unfold ChoirRightCandidate in *.
        destruct Hcandidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- left. exact Hone.
        -- destruct (Z.eq_dec k scanned) as [-> | Hneq].
           ++ lia.
           ++ right. exists k. split; [lia |].
              split; [exact Hheight_k | exact Hcandidate].
    + exact Hbest_eq.
  - exact Hcurrent_bounds.
Qed.
Lemma choir_right_progress_step_dominated__right_dp_transitions :
  forall heights dp_right peak scanned,
    ChoirRightInnerProgress heights dp_right peak scanned ->
    scanned < Zlength heights ->
    Znth scanned heights 0 < Znth peak heights 0 ->
    Znth scanned dp_right 0 + 1 <= Znth peak dp_right 0 ->
    ChoirRightInnerProgress heights dp_right peak (scanned + 1).
Proof.
  intros heights dp_right peak scanned
    Hprogress Hscanned Hheight Hdominated.
  unfold ChoirRightInnerProgress in *.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hsuffix [Hones [Hmaximum Hcurrent_bounds]]]]]].
  split; [exact Hpeak |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hsuffix |].
  split; [exact Hones |].
  split.
  - unfold MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best. split.
    + split.
      * unfold ChoirRightCandidate in *.
        destruct Hbest_candidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- left. exact Hone.
        -- right. exists k. split; [lia |].
           split; [exact Hheight_k | exact Hcandidate].
      * intros candidate Hcandidate.
        unfold ChoirRightCandidate in Hcandidate.
        destruct Hcandidate as
          [Hone | [k [Hk [Hheight_k Hcandidate]]]].
        -- apply Hbest_upper. left. exact Hone.
        -- destruct (Z.eq_dec k scanned) as [-> | Hneq].
           ++ subst candidate. lia.
           ++ apply Hbest_upper. right. exists k.
              split; [lia |].
              split; [exact Hheight_k | exact Hcandidate].
    + exact Hbest_eq.
  - exact Hcurrent_bounds.
Qed.
Lemma choir_valid_decreasing_starting_singleton__right_dp_transitions :
  forall heights peak,
    0 <= peak < Zlength heights ->
    ChoirValidDecreasingStartingAt heights peak (peak :: nil).
Proof.
  intros heights peak Hpeak.
  unfold ChoirValidDecreasingStartingAt.
  split; [exact Hpeak |].
  split.
  - constructor; [lia | constructor].
  - split.
    + apply mono_inc_single.
    + split.
      * unfold ChoirStrictlyDecreasingValues.
        intros p q [Hp [Hpq Hq]].
        rewrite Zlength_cons, Zlength_nil in Hq. lia.
      * exists nil. reflexivity.
Qed.
Lemma choir_valid_decreasing_starting_prepend__right_dp_transitions :
  forall heights peak k indices,
    ChoirValidDecreasingStartingAt heights k indices ->
    0 <= peak < Zlength heights ->
    peak < k ->
    Znth k heights 0 < Znth peak heights 0 ->
    ChoirValidDecreasingStartingAt heights peak (peak :: indices) /\
    Zlength (peak :: indices) = Zlength indices + 1.
Proof.
  intros heights peak k indices Hvalid Hpeak Hpeak_k Hheight.
  unfold ChoirValidDecreasingStartingAt in Hvalid.
  destruct Hvalid as [Hk [Hall [Hmono [Hvalues [suffix Hindices]]]]].
  assert (Hhead : Znth 0 indices 0 = k).
  { rewrite Hindices. reflexivity. }
  split.
  - unfold ChoirValidDecreasingStartingAt.
    split; [exact Hpeak |].
    split.
    + constructor.
      * lia.
      * eapply Forall_impl
          with (P := fun idx => k <= idx < Zlength heights);
          [| exact Hall].
        intros x Hx. lia.
    + split.
      * apply (proj2 (mono_inc_cons peak indices)).
        split; [| exact Hmono].
        eapply Forall_impl
          with (P := fun idx => k <= idx < Zlength heights);
          [| exact Hall].
        intros x Hx. lia.
      * split.
        -- unfold ChoirStrictlyDecreasingValues in *.
           intros p q [Hp [Hpq Hq]].
           rewrite Zlength_cons in Hq.
           destruct (Z.eq_dec p 0) as [-> | Hp0].
           ++ rewrite Znth0_cons.
              rewrite Znth_cons by lia.
              destruct (Z.eq_dec q 1) as [-> | Hq1].
              ** replace (1 - 1) with 0 by lia.
                 rewrite Hhead. exact Hheight.
              ** pose proof
                   (Hvalues 0 (q - 1) ltac:(lia)) as Htail.
                 rewrite Hhead in Htail. lia.
           ++ rewrite !Znth_cons by lia.
              apply Hvalues. lia.
        -- exists indices. reflexivity.
  - rewrite Zlength_cons. lia.
Qed.
Lemma choir_valid_decreasing_starting_split__right_dp_transitions :
  forall heights peak indices,
    ChoirValidDecreasingStartingAt heights peak indices ->
    indices = peak :: nil \/
    exists tail k,
      indices = peak :: tail /\
      ChoirValidDecreasingStartingAt heights k tail /\
      peak < k /\
      Znth k heights 0 < Znth peak heights 0 /\
      Zlength indices = Zlength tail + 1.
Proof.
  intros heights peak indices Hvalid.
  unfold ChoirValidDecreasingStartingAt in Hvalid.
  destruct Hvalid as
    [Hpeak [Hall [Hmono [Hvalues [suffix Hindices]]]]].
  subst indices.
  destruct suffix as [| k rest].
  - left. reflexivity.
  - right. exists (k :: rest), k.
    assert (Hall_tail :
      Forall (fun idx => peak <= idx < Zlength heights) (k :: rest)).
    { inversion Hall; assumption. }
    assert (Hmono_parts :
      Forall (fun y => peak < y) (k :: rest) /\ mono_inc (k :: rest)).
    { apply (proj1 (mono_inc_cons peak (k :: rest))).
      exact Hmono. }
    destruct Hmono_parts as [Hpeak_less Hmono_tail].
    assert (Hmono_tail_parts :
      Forall (fun y => k < y) rest /\ mono_inc rest).
    { apply (proj1 (mono_inc_cons k rest)).
      exact Hmono_tail. }
    destruct Hmono_tail_parts as [Hk_less Hmono_rest].
    assert (Hpeak_k : peak < k).
    { inversion Hpeak_less; assumption. }
    assert (Hk_bounds : 0 <= k < Zlength heights).
    { inversion Hall_tail. lia. }
    assert (Hheight : Znth k heights 0 < Znth peak heights 0).
    { specialize (Hvalues 0 1).
      rewrite !Znth0_cons in Hvalues.
      rewrite Znth_cons in Hvalues by lia.
      replace (1 - 1) with 0 in Hvalues by lia.
      rewrite Znth0_cons in Hvalues.
      apply Hvalues.
      rewrite !Zlength_cons. pose proof (Zlength_nonneg rest). lia. }
    split; [reflexivity |].
    split.
    + unfold ChoirValidDecreasingStartingAt.
      split; [exact Hk_bounds |].
      split.
      * constructor.
        -- lia.
        -- apply Forall_forall.
           intros x Hin.
           rewrite Forall_forall in Hk_less.
           specialize (Hk_less x Hin).
           inversion Hall_tail as [| ? ? Hk_old Hall_rest]; subst.
           rewrite Forall_forall in Hall_rest.
           specialize (Hall_rest x Hin).
           lia.
      * split; [exact Hmono_tail |].
        split.
        -- unfold ChoirStrictlyDecreasingValues in *.
           intros p q Hpq.
           destruct Hpq as [Hp [Hpq Hqlen]].
           pose proof
             (Hvalues (p + 1) (q + 1)
               ltac:(rewrite Zlength_cons; lia)) as Hshift.
           replace (Znth (p + 1) (peak :: k :: rest) 0)
             with (Znth p (k :: rest) 0) in Hshift.
           2: { rewrite (Znth_cons 0 (p + 1) peak (k :: rest)) by lia.
                replace (p + 1 - 1) with p by lia.
                reflexivity. }
           replace (Znth (q + 1) (peak :: k :: rest) 0)
             with (Znth q (k :: rest) 0) in Hshift.
           2: { rewrite (Znth_cons 0 (q + 1) peak (k :: rest)) by lia.
                replace (q + 1 - 1) with q by lia.
                reflexivity. }
           exact Hshift.
        -- exists rest. reflexivity.
    + split; [exact Hpeak_k |].
      split; [exact Hheight |].
      rewrite Zlength_cons. lia.
Qed.
Lemma choir_right_progress_complete__right_dp_transitions :
  forall heights dp_right peak,
    ChoirRightInnerProgress heights dp_right peak (Zlength heights) ->
    ChoirDPRightSuffix heights dp_right peak.
Proof.
  intros heights dp_right peak Hprogress.
  unfold ChoirRightInnerProgress in Hprogress.
  destruct Hprogress as
    [Hpeak [Hscan [Hlen [Hsuffix [Hones
      [Hcandidate_max Hcurrent_bounds]]]]]].
  assert (Hcandidate_to_valid :
    forall candidate,
      ChoirRightCandidate heights dp_right peak (Zlength heights) candidate ->
      exists indices,
        ChoirValidDecreasingStartingAt heights peak indices /\
        Zlength indices = candidate).
  {
    intros candidate Hcandidate.
    unfold ChoirRightCandidate in Hcandidate.
    destruct Hcandidate as
      [Hone | [k [Hk [Hheight Hcandidate]]]].
    - subst candidate. exists (peak :: nil). split.
      + apply choir_valid_decreasing_starting_singleton__right_dp_transitions.
        exact Hpeak.
      + rewrite Zlength_cons, Zlength_nil. lia.
    - specialize (Hsuffix k Hk) as [Hright_k Hbounds_k].
      unfold ChoirRightLength,
        MaxMin.max_value_of_subset,
        MaxMin.max_object_of_subset in Hright_k.
      destruct Hright_k as
        [indices [[Hvalid_k Hupper_k] Hindices_len]].
      destruct
        (choir_valid_decreasing_starting_prepend__right_dp_transitions
          heights peak k indices Hvalid_k Hpeak ltac:(lia) Hheight)
        as [Hvalid_peak Hlen_cons].
      exists (peak :: indices). split; [exact Hvalid_peak |].
      lia.
  }
  assert (Hvalid_to_candidate_bound :
    forall indices,
      ChoirValidDecreasingStartingAt heights peak indices ->
      exists candidate,
        ChoirRightCandidate heights dp_right
          peak (Zlength heights) candidate /\
        Zlength indices <= candidate).
  {
    intros indices Hvalid.
    destruct
      (choir_valid_decreasing_starting_split__right_dp_transitions
        heights peak indices Hvalid)
      as [Hsingle |
          [tail [k [Hindices [Hvalid_k
            [Hpeak_k [Hheight Hindices_len]]]]]]].
    - exists 1. split.
      + left. reflexivity.
      + rewrite Hsingle, Zlength_cons, Zlength_nil. lia.
    - pose proof Hvalid_k as Hvalid_k_bounds.
      unfold ChoirValidDecreasingStartingAt in Hvalid_k_bounds.
      destruct Hvalid_k_bounds as [Hk_in_heights Hvalid_k_rest].
      specialize (Hsuffix k (conj Hpeak_k (proj2 Hk_in_heights)))
        as [Hright_k Hbounds_k].
      unfold ChoirRightLength,
        MaxMin.max_value_of_subset,
        MaxMin.max_object_of_subset in Hright_k.
      destruct Hright_k as
        [best_indices [[Hbest_valid Hbest_upper] Hbest_len]].
      specialize (Hbest_upper tail Hvalid_k).
      exists (Znth k dp_right 0 + 1). split.
      + right. exists k. split.
        * exact (conj Hpeak_k (proj2 Hk_in_heights)).
        * split; [exact Hheight | reflexivity].
      + lia.
  }
  assert (Hright_peak :
    ChoirRightLength heights peak (Znth peak dp_right 0)).
  {
    unfold ChoirRightLength,
      MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset in *.
    destruct Hcandidate_max as
      [best_candidate [[Hbest_candidate Hbest_upper] Hbest_eq]].
    destruct (Hcandidate_to_valid best_candidate Hbest_candidate)
      as [best_indices [Hbest_valid Hbest_len]].
    exists best_indices. split.
    - split; [exact Hbest_valid |].
      intros indices Hvalid.
      destruct (Hvalid_to_candidate_bound indices Hvalid)
        as [candidate [Hcandidate Hlen_bound]].
      specialize (Hbest_upper candidate Hcandidate).
      lia.
    - lia.
  }
  unfold ChoirDPRightSuffix.
  split; [lia |].
  split; [exact Hlen |].
  split.
  - intros k Hk.
    destruct (Z_lt_ge_dec peak k) as [Hk_later | Hk_peak].
    + apply Hsuffix. lia.
    + assert (k = peak) by lia. subst k.
      split; [exact Hright_peak | exact Hcurrent_bounds].
  - exact Hones.
Qed.
Lemma choir_peak_length_unique__best_prefix_fold :
  forall heights peak first second,
    ChoirPeakLength heights peak first ->
    ChoirPeakLength heights peak second ->
    first = second.
Proof.
  intros heights peak first second Hfirst Hsecond.
  unfold ChoirPeakLength in *.
  destruct Hfirst as
      [left_first [right_first [Hleft_first [Hright_first Hfirst]]]].
  destruct Hsecond as
      [left_second [right_second [Hleft_second [Hright_second Hsecond]]]].
  unfold ChoirLeftLength in Hleft_first, Hleft_second.
  unfold ChoirRightLength in Hright_first, Hright_second.
  unfold max_value_of_subset, max_object_of_subset
    in Hleft_first, Hleft_second, Hright_first, Hright_second.
  destruct Hleft_first as
      [left_indices_first
        [[Hleft_indices_first Hleft_upper_first] Hleft_value_first]].
  destruct Hleft_second as
      [left_indices_second
        [[Hleft_indices_second Hleft_upper_second] Hleft_value_second]].
  assert (left_first = left_second).
  { specialize
      (Hleft_upper_first left_indices_second Hleft_indices_second).
    specialize
      (Hleft_upper_second left_indices_first Hleft_indices_first).
    lia. }
  destruct Hright_first as
      [right_indices_first
        [[Hright_indices_first Hright_upper_first] Hright_value_first]].
  destruct Hright_second as
      [right_indices_second
        [[Hright_indices_second Hright_upper_second] Hright_value_second]].
  assert (right_first = right_second).
  { specialize
      (Hright_upper_first right_indices_second Hright_indices_second).
    specialize
      (Hright_upper_second right_indices_first Hright_indices_first).
    lia. }
  lia.
Qed.
Lemma choir_peak_length_from_dp__best_prefix_fold :
  forall heights dp_left dp_right peak,
    ChoirDPLeftPrefix heights dp_left (Zlength heights) ->
    ChoirDPRightSuffix heights dp_right 0 ->
    0 <= peak < Zlength heights ->
    ChoirPeakLength heights peak
      (Znth peak dp_left 0 + Znth peak dp_right 0 - 1) /\
    1 <= Znth peak dp_left 0 + Znth peak dp_right 0 - 1
      <= Zlength heights.
Proof.
  intros heights dp_left dp_right peak Hleft Hright Hpeak.
  unfold ChoirDPLeftPrefix in Hleft.
  unfold ChoirDPRightSuffix in Hright.
  destruct Hleft as [_ [_ [Hleft _]]].
  destruct Hright as [_ [_ [Hright _]]].
  specialize (Hleft peak Hpeak) as
      [Hleft_length [Hleft_lower Hleft_upper]].
  specialize (Hright peak Hpeak) as
      [Hright_length [Hright_lower Hright_upper]].
  split.
  - unfold ChoirPeakLength.
    exists (Znth peak dp_left 0), (Znth peak dp_right 0).
    repeat split; auto.
  - lia.
Qed.
Lemma choir_best_prefix_step_take__best_prefix_fold :
  forall heights k old new,
    ChoirBestPrefix heights k old ->
    0 <= k < Zlength heights ->
    ChoirPeakLength heights k new ->
    old <= new ->
    ChoirBestPrefix heights (k + 1) new.
Proof.
  intros heights k old new Hbest Hk Hpeak Hold_new.
  unfold ChoirBestPrefix in *.
  destruct Hbest as [_ Hbest].
  split; [lia |].
  right.
  split; [lia |].
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [[Hk_zero Hold_zero] | [Hk_positive Hmaximum]].
  - subst k old.
    exists new.
    split.
    + split.
      * exists 0.
        split; [lia | exact Hpeak].
      * intros candidate
          [candidate_peak [[Hcandidate_lower Hcandidate_upper]
            Hcandidate_peak]].
        assert (candidate_peak = 0) by lia.
        subst candidate_peak.
        pose proof
          (choir_peak_length_unique__best_prefix_fold
             heights 0 candidate new Hcandidate_peak Hpeak).
        lia.
    + reflexivity.
  - destruct Hmaximum as
        [old_candidate [[Hold_member Hold_upper] Hold_candidate]].
    simpl in Hold_candidate.
    subst old_candidate.
    exists new.
    split.
    + split.
      * exists k.
        split; [lia | exact Hpeak].
      * intros candidate
          [candidate_peak [[Hcandidate_lower Hcandidate_upper]
            Hcandidate_peak]].
        destruct (Z_lt_ge_dec candidate_peak k) as
            [Hcandidate_old | Hcandidate_endpoint].
        -- specialize (Hold_upper candidate).
           assert (candidate <= old).
           { apply Hold_upper.
             exists candidate_peak.
             split; [lia | exact Hcandidate_peak]. }
           lia.
        -- assert (candidate_peak = k) by lia.
           subst candidate_peak.
           pose proof
             (choir_peak_length_unique__best_prefix_fold
                heights k candidate new Hcandidate_peak Hpeak).
           lia.
    + reflexivity.
Qed.
Lemma choir_best_prefix_step_keep__best_prefix_fold :
  forall heights k old new,
    ChoirBestPrefix heights k old ->
    0 <= k < Zlength heights ->
    ChoirPeakLength heights k new ->
    1 <= new ->
    new <= old ->
    ChoirBestPrefix heights (k + 1) old.
Proof.
  intros heights k old new Hbest Hk Hpeak Hnew_positive Hnew_old.
  unfold ChoirBestPrefix in *.
  destruct Hbest as [_ Hbest].
  split; [lia |].
  right.
  split; [lia |].
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [[Hk_zero Hold_zero] | [Hk_positive Hmaximum]].
  - lia.
  - destruct Hmaximum as
        [old_candidate [[Hold_member Hold_upper] Hold_candidate]].
    simpl in Hold_candidate.
    subst old_candidate.
    exists old.
    split.
    + split.
      * destruct Hold_member as
            [old_peak [[Hold_peak_lower Hold_peak_upper] Hold_peak]].
        exists old_peak.
        split; [lia | exact Hold_peak].
      * intros candidate
          [candidate_peak [[Hcandidate_lower Hcandidate_upper]
            Hcandidate_peak]].
        destruct (Z_lt_ge_dec candidate_peak k) as
            [Hcandidate_old | Hcandidate_endpoint].
        -- apply Hold_upper.
           exists candidate_peak.
           split; [lia | exact Hcandidate_peak].
        -- assert (candidate_peak = k) by lia.
           subst candidate_peak.
           pose proof
             (choir_peak_length_unique__best_prefix_fold
                heights k candidate new Hcandidate_peak Hpeak).
           lia.
    + reflexivity.
Qed.
Lemma choir_best_prefix_positive__best_prefix_fold :
  forall heights dp_left dp_right limit best,
    0 < limit ->
    limit <= Zlength heights ->
    ChoirDPLeftPrefix heights dp_left (Zlength heights) ->
    ChoirDPRightSuffix heights dp_right 0 ->
    ChoirBestPrefix heights limit best ->
    1 <= best.
Proof.
  intros heights dp_left dp_right limit best
    Hlimit_positive Hlimit_bound Hleft Hright Hbest.
  pose proof
    (choir_peak_length_from_dp__best_prefix_fold
       heights dp_left dp_right 0 Hleft Hright ltac:(lia))
    as [Hpeak [Hpeak_positive Hpeak_bound]].
  unfold ChoirBestPrefix in Hbest.
  destruct Hbest as [_ [[Hlimit_zero Hbest_zero] |
      [Hlimit_positive' Hmaximum]]]; [lia |].
  unfold max_value_of_subset, max_object_of_subset in Hmaximum.
  destruct Hmaximum as
      [maximum [[Hmaximum_member Hmaximum_upper] Hmaximum_value]].
  simpl in Hmaximum_value.
  subst maximum.
  specialize
    (Hmaximum_upper
       (Znth 0 dp_left 0 + Znth 0 dp_right 0 - 1)).
  assert (Znth 0 dp_left 0 + Znth 0 dp_right 0 - 1 <= best).
  { apply Hmaximum_upper.
    exists 0.
    split; [lia | exact Hpeak]. }
  lia.
Qed.
