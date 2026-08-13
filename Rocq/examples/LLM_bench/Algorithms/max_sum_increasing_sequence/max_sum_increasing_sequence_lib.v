Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition MSISStrictlyIncreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 < Znth (Znth q idxs 0) l 0.

Definition MSISValidSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  0 < Zlength idxs /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  MSISStrictlyIncreasingValues l idxs.

Definition MSISSubsequenceSum (l idxs : list Z) : Z :=
  sum (map (fun idx => Znth idx l 0) idxs).

Definition MSISPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => MSISValidSubsequence l limit idxs)
    (fun idxs => MSISSubsequenceSum l idxs)
    ans.

Definition MSISMaximum (l : list Z) (ans : Z) : Prop :=
  MSISPrefix l (Zlength l) ans.

Definition MSISValidSubsequenceEndingAt
    (l : list Z) (i : Z) (idxs : list Z) : Prop :=
  0 <= i < Zlength l /\
  MSISValidSubsequence l (i + 1) idxs /\
  exists prefix, idxs = prefix ++ i :: nil.

Definition MSISEndingAt (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => MSISValidSubsequenceEndingAt l i idxs)
    (fun idxs => MSISSubsequenceSum l idxs)
    ans.

Definition MSISDPTablePrefix
    (l dp : list Z) (hi : Z) : Prop :=
  1 <= hi <= Zlength l /\
  Zlength dp = hi /\
  forall k,
    0 <= k < hi ->
    MSISEndingAt l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= (k + 1) * 10000.

Definition MSISInnerCandidate
    (l dp : list Z) (i scanned candidate : Z) : Prop :=
  candidate = Znth i l 0 \/
  exists k,
    0 <= k < scanned /\
    Znth k l 0 < Znth i l 0 /\
    candidate = Znth k dp 0 + Znth i l 0.

Definition MSISInnerProgress
    (l dp : list Z) (i scanned : Z) : Prop :=
  1 <= i < Zlength l /\
  0 <= scanned <= i /\
  Zlength dp = i + 1 /\
  (forall k,
    0 <= k < i ->
    MSISEndingAt l k (Znth k dp 0) /\
    1 <= Znth k dp 0 <= (k + 1) * 10000) /\
  max_value_of_subset Z.le
    (fun candidate => MSISInnerCandidate l dp i scanned candidate)
    (fun candidate => candidate)
    (Znth i dp 0) /\
  1 <= Znth i dp 0 <= (i + 1) * 10000.

Definition MSISBestSoFar (l : list Z) (limit ans : Z) : Prop :=
  1 <= limit <= Zlength l /\
  MSISPrefix l limit ans.

Lemma msis_valid_limit_one_singleton__initialization :
  forall l idxs,
    MSISValidSubsequence l 1 idxs ->
    idxs = 0 :: nil.
Proof.
  intros l idxs Hvalid.
  unfold MSISValidSubsequence in Hvalid.
  destruct Hvalid as [_ [Hnonempty [Hall [Hmono _]]]].
  destruct idxs as [| x xs].
  - rewrite Zlength_nil in Hnonempty. lia.
  - assert (Hx : 0 <= Znth 0 (x :: xs) 0 < 1).
    {
      apply (proj1
        (Forall_Znth (fun idx => 0 <= idx < 1) 0 (x :: xs)));
        [exact Hall |].
      pose proof (Zlength_nonneg xs).
      rewrite Zlength_cons. lia.
    }
    rewrite Znth0_cons in Hx.
    assert (Hx0 : x = 0) by lia.
    subst x.
    destruct xs as [| y ys].
    + reflexivity.
    + assert (Hy : 0 <= Znth 1 (0 :: y :: ys) 0 < 1).
      {
        apply (proj1
          (Forall_Znth (fun idx => 0 <= idx < 1) 0
            (0 :: y :: ys)));
          [exact Hall |].
        pose proof (Zlength_nonneg ys).
        rewrite !Zlength_cons. lia.
      }
      rewrite Znth_cons in Hy by lia.
      rewrite Znth0_cons in Hy.
      unfold mono_inc in Hmono.
      specialize (Hmono 0 1 ltac:(lia) ltac:(lia)).
      pose proof (Zlength_nonneg ys).
      rewrite !Zlength_cons in Hmono.
      specialize (Hmono ltac:(lia)).
      rewrite Znth0_cons in Hmono.
      rewrite Znth_cons in Hmono by lia.
      rewrite Znth0_cons in Hmono.
      lia.
Qed.
Lemma msis_initial_semantics__initialization :
  forall l,
    0 < Zlength l ->
    MSISEndingAt l 0 (Znth 0 l 0) /\
    MSISPrefix l 1 (Znth 0 l 0).
Proof.
  intros l Hlen.
  assert (Hvalid : MSISValidSubsequence l 1 (0 :: nil)).
  {
    unfold MSISValidSubsequence.
    split; [lia |].
    split.
    - rewrite Zlength_cons, Zlength_nil. lia.
    - split.
      + constructor; [lia | constructor].
      + split.
        * apply mono_inc_single.
        * unfold MSISStrictlyIncreasingValues.
          intros p q [Hp [Hpq Hq]].
          rewrite Zlength_cons, Zlength_nil in Hq. lia.
  }
  split.
  - unfold MSISEndingAt, MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset.
    exists (0 :: nil).
    split.
    + split.
      * unfold MSISValidSubsequenceEndingAt.
        split; [lia |].
        split; [exact Hvalid |].
        exists nil. reflexivity.
      * intros idxs Hending.
        unfold MSISValidSubsequenceEndingAt in Hending.
        destruct Hending as [_ [Hvalid_idxs _]].
        pose proof
          (msis_valid_limit_one_singleton__initialization
            l idxs Hvalid_idxs) as Hidxs.
        subst idxs. lia.
    + unfold MSISSubsequenceSum. simpl. lia.
  - unfold MSISPrefix, MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset.
    exists (0 :: nil).
    split.
    + split.
      * exact Hvalid.
      * intros idxs Hvalid_idxs.
        pose proof
          (msis_valid_limit_one_singleton__initialization
            l idxs Hvalid_idxs) as Hidxs.
        subst idxs. lia.
    + unfold MSISSubsequenceSum. simpl. lia.
Qed.
Lemma msis_inner_progress_zero__initialization :
  forall l d i,
    MSISDPTablePrefix l d i ->
    1 <= i < Zlength l ->
    1 <= Znth i l 0 <= 10000 ->
    MSISInnerProgress l (d ++ Znth i l 0 :: nil) i 0.
Proof.
  intros l d i Hprefix Hi Hvalue.
  unfold MSISDPTablePrefix in Hprefix.
  destruct Hprefix as [Hhi [Hlen Hentries]].
  assert (Hlast :
    Znth i (d ++ Znth i l 0 :: nil) 0 = Znth i l 0).
  {
    rewrite app_Znth2 by lia.
    replace (i - Zlength d) with 0 by lia.
    rewrite Znth0_cons.
    reflexivity.
  }
  unfold MSISInnerProgress.
  split; [exact Hi |].
  split; [lia |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split.
    + intros k Hk.
      rewrite app_Znth1 by lia.
      apply Hentries. exact Hk.
    + split.
      * unfold MaxMin.max_value_of_subset,
          MaxMin.max_object_of_subset.
        exists (Znth i l 0).
        rewrite Hlast.
        split.
        -- split.
           ++ unfold MSISInnerCandidate. left. reflexivity.
           ++ intros candidate Hcandidate.
              unfold MSISInnerCandidate in Hcandidate.
              destruct Hcandidate as
                [-> | [k [[Hk0 Hklt] [_ ->]]]];
                lia.
        -- reflexivity.
      * rewrite Hlast. lia.
Qed.
Lemma msis_inner_progress_entry_bound__inner_transitions :
  forall l dp i scanned k,
    MSISInnerProgress l dp i scanned ->
    0 <= k < i ->
    1 <= Znth k dp 0 <= (k + 1) * 10000.
Proof.
  intros l dp i scanned k Hprogress Hk.
  unfold MSISInnerProgress in Hprogress.
  destruct Hprogress as [_ [_ [_ [Hprefix _]]]].
  exact (proj2 (Hprefix k Hk)).
Qed.
Lemma max_value_of_subset_insert__inner_transitions :
  forall (P : Z -> Prop) best x,
    max_value_of_subset Z.le P (fun y => y) best ->
    (x <= best ->
      max_value_of_subset Z.le
        (fun y => P y \/ y = x) (fun y => y) best) /\
    (best < x ->
      max_value_of_subset Z.le
        (fun y => P y \/ y = x) (fun y => y) x).
Proof.
  intros P best x Hmaximum.
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hmaximum as [a [[Ha Hupper] Heq]].
  split.
  - intros Hx.
    exists a.
    split.
    + split.
      * left; exact Ha.
      * intros b [Hb | ->].
        -- specialize (Hupper b Hb). lia.
        -- lia.
    + exact Heq.
  - intros Hx.
    exists x.
    split.
    + split.
      * right; reflexivity.
      * intros b [Hb | ->].
        -- specialize (Hupper b Hb). lia.
        -- lia.
    + reflexivity.
Qed.
Lemma msis_inner_candidate_step__inner_transitions :
  forall l dp i j candidate,
    0 <= j < i ->
    (MSISInnerCandidate l dp i (j + 1) candidate <->
      MSISInnerCandidate l dp i j candidate \/
      (Znth j l 0 < Znth i l 0 /\
       candidate = Znth j dp 0 + Znth i l 0)).
Proof.
  intros l dp i j candidate Hj.
  unfold MSISInnerCandidate.
  split.
  - intros [Hbase | [k [[Hk0 Hkscan] [Hvalues Hcandidate]]]].
    + left; left; exact Hbase.
    + destruct (Z.eq_dec k j) as [-> | Hkj].
      * right; split; assumption.
      * left; right.
        exists k.
        repeat split; try assumption; lia.
  - intros [[Hbase | [k [[Hk0 Hkscan] [Hvalues Hcandidate]]]] |
            [Hvalues Hcandidate]].
    + left; exact Hbase.
    + right.
      exists k.
      repeat split; try assumption; lia.
    + right.
      exists j.
      repeat split; try assumption; lia.
Qed.
Lemma replace_Znth_inner_progress_step__inner_transitions :
  forall l dp i j,
    MSISInnerProgress l dp i j ->
    0 <= j < i ->
    Znth j l 0 < Znth i l 0 ->
    Znth i dp 0 < Znth j dp 0 + Znth i l 0 ->
    1 <= Znth i l 0 <= 10000 ->
    MSISInnerProgress l
      (replace_Znth i (Znth j dp 0 + Znth i l 0) dp) i (j + 1).
Proof.
  intros l dp i j Hprogress Hj Hvalues Hlarger Hi_value.
  unfold MSISInnerProgress in *.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hmaximum Hcurrent_bounds]]]]].
  assert (Hi_dp : 0 <= i < Zlength dp) by (rewrite Hlen; lia).
  split; [exact Hi |].
  split; [lia |].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros k Hk.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hprefix. exact Hk.
    + split.
      * unfold MaxMin.max_value_of_subset,
          MaxMin.max_object_of_subset in *.
        destruct Hmaximum as
          [old_best [[Hold_candidate Hold_upper] Hold_eq]].
        exists (Znth j dp 0 + Znth i l 0).
        split.
        -- split.
           ++ unfold MSISInnerCandidate.
              right.
              exists j.
              repeat split; try assumption; try lia.
              rewrite Znth_replace_Znth_Diff by lia.
              reflexivity.
           ++ intros candidate Hcandidate.
              unfold MSISInnerCandidate in Hcandidate.
              destruct Hcandidate as
                [Hbase | [k [[Hk0 Hkscan] [Hkvalues Hcandidate]]]].
              ** subst candidate.
                 specialize (Hold_upper (Znth i l 0)).
                 assert (Hold_base :
                   MSISInnerCandidate l dp i j (Znth i l 0)).
                 { left; reflexivity. }
                 specialize (Hold_upper Hold_base).
                 simpl in Hold_upper.
                 lia.
              ** rewrite Znth_replace_Znth_Diff in Hcandidate by lia.
                 destruct (Z.eq_dec k j) as [-> | Hkj].
                 --- subst candidate. lia.
                 --- assert (Hk_old : 0 <= k < j) by lia.
                     specialize
                       (Hold_upper (Znth k dp 0 + Znth i l 0)).
                     assert (Hold_k :
                       MSISInnerCandidate l dp i j
                         (Znth k dp 0 + Znth i l 0)).
                     {
                       right.
                       exists k.
                       split; [exact Hk_old |].
                       split; [exact Hkvalues | reflexivity].
                     }
                     specialize (Hold_upper Hold_k).
                     simpl in Hold_upper.
                     subst candidate.
                     lia.
        -- rewrite Znth_replace_Znth_Same by exact Hi_dp.
           reflexivity.
      * rewrite Znth_replace_Znth_Same by exact Hi_dp.
        specialize (Hprefix j Hj) as [_ Hj_bounds].
        lia.
Qed.
Lemma msis_inner_progress_skip_dominated__inner_transitions :
  forall l dp i j,
    MSISInnerProgress l dp i j ->
    0 <= j < i ->
    Znth j l 0 < Znth i l 0 ->
    Znth j dp 0 + Znth i l 0 <= Znth i dp 0 ->
    MSISInnerProgress l dp i (j + 1).
Proof.
  intros l dp i j Hprogress Hj Hvalues Hdominated.
  unfold MSISInnerProgress in *.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hmaximum Hcurrent_bounds]]]]].
  split; [exact Hi |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hprefix |].
  split.
  - unfold MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best.
    split.
    + split.
      * unfold MSISInnerCandidate in *.
        destruct Hbest_candidate as
          [Hbase | [k [[Hk0 Hkscan] [Hkvalues Hcandidate]]]].
        -- left; exact Hbase.
        -- right.
           exists k.
           repeat split; try assumption; lia.
      * intros candidate Hcandidate.
        unfold MSISInnerCandidate in Hcandidate.
        destruct Hcandidate as
          [Hbase | [k [[Hk0 Hkscan] [Hkvalues Hcandidate]]]].
        -- apply Hbest_upper.
           left; exact Hbase.
        -- destruct (Z.eq_dec k j) as [-> | Hkj].
           ++ subst candidate. lia.
           ++ apply Hbest_upper.
              right.
              exists k.
              repeat split; try assumption; lia.
    + exact Hbest_eq.
  - exact Hcurrent_bounds.
Qed.
Lemma msis_inner_progress_skip_nonincreasing__inner_transitions :
  forall l dp i j,
    MSISInnerProgress l dp i j ->
    0 <= j < i ->
    Znth i l 0 <= Znth j l 0 ->
    MSISInnerProgress l dp i (j + 1).
Proof.
  intros l dp i j Hprogress Hj Hnonincreasing.
  unfold MSISInnerProgress in *.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hmaximum Hcurrent_bounds]]]]].
  split; [exact Hi |].
  split; [lia |].
  split; [exact Hlen |].
  split; [exact Hprefix |].
  split.
  - unfold MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset in *.
    destruct Hmaximum as
      [best [[Hbest_candidate Hbest_upper] Hbest_eq]].
    exists best.
    split.
    + split.
      * unfold MSISInnerCandidate in *.
        destruct Hbest_candidate as
          [Hbase | [k [[Hk0 Hkscan] [Hkvalues Hcandidate]]]].
        -- left; exact Hbase.
        -- right.
           exists k.
           repeat split; try assumption; lia.
      * intros candidate Hcandidate.
        apply Hbest_upper.
        unfold MSISInnerCandidate in *.
        destruct Hcandidate as
          [Hbase | [k [[Hk0 Hkscan] [Hkvalues Hcandidate]]]].
        -- left; exact Hbase.
        -- destruct (Z.eq_dec k j) as [-> | Hkj].
           ++ lia.
           ++ right.
              exists k.
              repeat split; try assumption; lia.
    + exact Hbest_eq.
  - exact Hcurrent_bounds.
Qed.
Lemma msis_znth_app_singleton_old__outer_transitions :
  forall xs x k,
    0 <= k < Zlength xs ->
    Znth k (xs ++ x :: nil) 0 = Znth k xs 0.
Proof.
  intros xs x k Hk.
  rewrite app_Znth1; auto.
Qed.
Lemma msis_znth_app_singleton_last__outer_transitions :
  forall xs x,
    Znth (Zlength xs) (xs ++ x :: nil) 0 = x.
Proof.
  intros xs x.
  rewrite app_Znth2 by lia.
  replace (Zlength xs - Zlength xs) with 0 by lia.
  reflexivity.
Qed.
Lemma msis_valid_ending_singleton__outer_transitions :
  forall l i,
    0 <= i < Zlength l ->
    MSISValidSubsequenceEndingAt l i (i :: nil).
Proof.
  intros l i Hi.
  unfold MSISValidSubsequenceEndingAt.
  split; [exact Hi |].
  split.
  - unfold MSISValidSubsequence.
    split; [lia |].
    split.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + split.
      * constructor; [lia | constructor].
      * split.
        -- apply mono_inc_single.
        -- unfold MSISStrictlyIncreasingValues.
           intros p q [Hp [Hpq Hq]].
           rewrite Zlength_cons, Zlength_nil in Hq. lia.
  - exists nil. reflexivity.
Qed.
Lemma msis_valid_ending_extend__outer_transitions :
  forall l k i idxs,
    MSISValidSubsequenceEndingAt l k idxs ->
    0 <= i < Zlength l ->
    k < i ->
    Znth k l 0 < Znth i l 0 ->
    MSISValidSubsequenceEndingAt l i (idxs ++ i :: nil) /\
    MSISSubsequenceSum l (idxs ++ i :: nil) =
      MSISSubsequenceSum l idxs + Znth i l 0.
Proof.
  intros l k i idxs Hending Hi Hki Hvalues_ki.
  unfold MSISValidSubsequenceEndingAt in Hending.
  destruct Hending as [Hk [Hvalid [prefix Hidxs]]].
  unfold MSISValidSubsequence in Hvalid.
  destruct Hvalid as [Hlimit [Hlen_pos [Hall [Hmono Hvalues]]]].
  assert (Hlast : Znth (Zlength idxs - 1) idxs 0 = k).
  {
    rewrite Hidxs, Zlength_app_cons.
    replace (Zlength prefix + 1 - 1) with (Zlength prefix) by lia.
    apply msis_znth_app_singleton_last__outer_transitions.
  }
  split.
  - unfold MSISValidSubsequenceEndingAt.
    split; [exact Hi |].
    split.
    + unfold MSISValidSubsequence.
      split; [lia |].
      split.
      * rewrite Zlength_app_cons. lia.
      * split.
        -- apply Forall_app. split.
           ++ eapply Forall_impl with (P := fun x => 0 <= x < k + 1).
              ** intros x Hx. lia.
              ** exact Hall.
           ++ constructor; [lia | constructor].
        -- split.
           ++ unfold mono_inc in *.
              intros p q Hp Hpq Hq.
              rewrite Zlength_app_cons in Hq.
              destruct (Z_lt_ge_dec q (Zlength idxs))
                as [Hq_old | Hq_last].
              ** rewrite !msis_znth_app_singleton_old__outer_transitions
                   by lia.
                 apply Hmono; lia.
              ** assert (q = Zlength idxs) by lia. subst q.
                 rewrite msis_znth_app_singleton_last__outer_transitions.
                 rewrite msis_znth_app_singleton_old__outer_transitions by lia.
                 pose proof
                   ((proj1 (Forall_Znth (fun x => 0 <= x < k + 1) 0 idxs))
                      Hall p ltac:(lia)) as Hp_bound.
                 destruct Hp_bound as [_ Hp_k].
                 lia.
           ++ unfold MSISStrictlyIncreasingValues in *.
              intros p q [Hp [Hpq Hq]].
              rewrite Zlength_app_cons in Hq.
              destruct (Z_lt_ge_dec q (Zlength idxs))
                as [Hq_old | Hq_last].
              ** rewrite !msis_znth_app_singleton_old__outer_transitions
                   by lia.
                 apply Hvalues. lia.
              ** assert (q = Zlength idxs) by lia. subst q.
                 rewrite msis_znth_app_singleton_last__outer_transitions.
                 rewrite msis_znth_app_singleton_old__outer_transitions by lia.
                 destruct (Z.eq_dec p (Zlength idxs - 1))
                   as [Hp_last | Hp_old].
                 --- subst p. rewrite Hlast. exact Hvalues_ki.
                 --- pose proof
                       (Hvalues p (Zlength idxs - 1) ltac:(lia))
                       as Hp_to_last.
                     rewrite Hlast in Hp_to_last. lia.
    + exists idxs. reflexivity.
  - unfold MSISSubsequenceSum.
    rewrite map_app. simpl.
    rewrite sum_app. simpl. lia.
Qed.
Lemma msis_valid_ending_split__outer_transitions :
  forall l i idxs,
    MSISValidSubsequenceEndingAt l i idxs ->
    idxs = i :: nil \/
    exists prefix k,
      idxs = prefix ++ i :: nil /\
      MSISValidSubsequenceEndingAt l k prefix /\
      k < i /\
      Znth k l 0 < Znth i l 0 /\
      MSISSubsequenceSum l idxs =
        MSISSubsequenceSum l prefix + Znth i l 0.
Proof.
  intros l i idxs Hending.
  unfold MSISValidSubsequenceEndingAt in Hending.
  destruct Hending as [Hi [Hvalid [before Hidxs]]].
  unfold MSISValidSubsequence in Hvalid.
  destruct Hvalid as [Hlimit [Hlen_pos [Hall [Hmono Hvalues]]]].
  destruct before as [| a rest].
  - left. simpl in Hidxs. exact Hidxs.
  - assert (Hnonempty : a :: rest <> nil) by discriminate.
    destruct (exists_last Hnonempty) as [before0 [k Hbefore]].
    assert (Hprefix_len_pos : 0 < Zlength (a :: rest)).
    {
      rewrite Hbefore, Zlength_app_cons.
      pose proof (Zlength_nonneg before0). lia.
    }
    assert (Hlast : Znth (Zlength (a :: rest) - 1) (a :: rest) 0 = k).
    {
      rewrite Hbefore, Zlength_app_cons.
      replace (Zlength before0 + 1 - 1) with (Zlength before0) by lia.
      apply msis_znth_app_singleton_last__outer_transitions.
    }
    rewrite Hidxs in Hall, Hmono, Hvalues.
    apply Forall_app in Hall as [Hall_before Hall_i].
    assert (Hk_bound : 0 <= k < i + 1).
    {
      pose proof
        ((proj1 (Forall_Znth (fun x => 0 <= x < i + 1) 0 (a :: rest)))
           Hall_before (Zlength (a :: rest) - 1) ltac:(lia)) as Hbound.
      rewrite Hlast in Hbound. exact Hbound.
    }
    assert (Hki : k < i).
    {
      unfold mono_inc in Hmono.
      pose proof
        (Hmono (Zlength (a :: rest) - 1) (Zlength (a :: rest))
          ltac:(lia) ltac:(lia)
          ltac:(rewrite Zlength_app_cons; lia)) as Hord.
      rewrite msis_znth_app_singleton_old__outer_transitions in Hord by lia.
      rewrite msis_znth_app_singleton_last__outer_transitions in Hord.
      rewrite Hlast in Hord. exact Hord.
    }
    assert (Hvalues_ki : Znth k l 0 < Znth i l 0).
    {
      unfold MSISStrictlyIncreasingValues in Hvalues.
      pose proof
        (Hvalues (Zlength (a :: rest) - 1) (Zlength (a :: rest))
          ltac:(rewrite Zlength_app_cons; lia)) as Hord.
      rewrite msis_znth_app_singleton_old__outer_transitions in Hord by lia.
      rewrite msis_znth_app_singleton_last__outer_transitions in Hord.
      rewrite Hlast in Hord. exact Hord.
    }
    right. exists (a :: rest), k.
    split; [exact Hidxs |].
    split.
    + unfold MSISValidSubsequenceEndingAt.
      split; [lia |].
      split.
      * unfold MSISValidSubsequence.
        split; [lia |].
        split; [exact Hprefix_len_pos |].
        split.
        -- apply
             (proj2 (Forall_Znth
               (fun x => 0 <= x < k + 1) 0 (a :: rest))).
           intros p Hp.
           pose proof
             ((proj1 (Forall_Znth
                (fun x => 0 <= x < i + 1) 0 (a :: rest)))
                Hall_before p Hp) as Hp_bound.
           destruct Hp_bound as [Hp_nonneg Hp_before_i].
           destruct (Z.eq_dec p (Zlength (a :: rest) - 1))
             as [Hp_last | Hp_old].
           ++ subst p. rewrite Hlast. lia.
           ++ assert (p < Zlength (a :: rest) - 1) by lia.
              unfold mono_inc in Hmono.
              pose proof
                (Hmono p (Zlength (a :: rest) - 1)
                  ltac:(lia) ltac:(lia)
                  ltac:(rewrite Zlength_app_cons; lia)) as Hp_to_last.
              rewrite !msis_znth_app_singleton_old__outer_transitions
                in Hp_to_last by lia.
              rewrite Hlast in Hp_to_last.
              split; [exact Hp_nonneg | lia].
        -- split.
           ++ unfold mono_inc in *.
              intros p q Hp Hpq Hq.
              specialize
                (Hmono p q Hp Hpq
                  ltac:(rewrite Zlength_app_cons; lia)).
              rewrite !msis_znth_app_singleton_old__outer_transitions
                in Hmono by lia.
              exact Hmono.
           ++ unfold MSISStrictlyIncreasingValues in *.
              intros p q Hpq.
              specialize
                (Hvalues p q ltac:(rewrite Zlength_app_cons; lia)).
              rewrite !msis_znth_app_singleton_old__outer_transitions
                in Hvalues by lia.
              exact Hvalues.
      * exists before0. exact Hbefore.
    + split; [exact Hki |].
      split; [exact Hvalues_ki |].
      unfold MSISSubsequenceSum.
      rewrite Hidxs, map_app. simpl.
      rewrite sum_app. simpl. lia.
Qed.
Lemma msis_inner_complete_dp_prefix__outer_transitions :
  forall l dp i,
    MSISInnerProgress l dp i i ->
    MSISDPTablePrefix l dp (i + 1).
Proof.
  intros l dp i Hprogress.
  unfold MSISInnerProgress in Hprogress.
  destruct Hprogress as
    [Hi [Hscan [Hlen [Hprefix [Hcandidate_max Hcurrent_bounds]]]]].
  assert (Hcandidate_to_valid :
    forall candidate,
      MSISInnerCandidate l dp i i candidate ->
      exists idxs,
        MSISValidSubsequenceEndingAt l i idxs /\
        MSISSubsequenceSum l idxs = candidate).
  {
    intros candidate Hcandidate.
    unfold MSISInnerCandidate in Hcandidate.
    destruct Hcandidate as [Hbase | [k [Hk [Hvalues Hcandidate]]]].
    - subst candidate. exists (i :: nil). split.
      + apply msis_valid_ending_singleton__outer_transitions. lia.
      + unfold MSISSubsequenceSum. simpl. lia.
    - specialize (Hprefix k Hk) as [Hending_k Hbounds_k].
      unfold MSISEndingAt,
        MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hending_k.
      destruct Hending_k as
        [idxs [[Hvalid_k Hupper_k] Hidxs_sum]].
      destruct
        (msis_valid_ending_extend__outer_transitions
          l k i idxs Hvalid_k ltac:(lia) ltac:(lia) Hvalues)
        as [Hvalid_i Hsum_snoc].
      exists (idxs ++ i :: nil). split; [exact Hvalid_i |].
      lia.
  }
  assert (Hvalid_to_candidate_bound :
    forall idxs,
      MSISValidSubsequenceEndingAt l i idxs ->
      exists candidate,
        MSISInnerCandidate l dp i i candidate /\
        MSISSubsequenceSum l idxs <= candidate).
  {
    intros idxs Hvalid.
    destruct
      (msis_valid_ending_split__outer_transitions l i idxs Hvalid)
      as [Hsingle |
          [prefix [k
            [Hidxs [Hvalid_k [Hki [Hvalues Hidxs_sum]]]]]]].
    - exists (Znth i l 0). split.
      + left. reflexivity.
      + rewrite Hsingle.
        unfold MSISSubsequenceSum. simpl. lia.
    - pose proof Hvalid_k as Hvalid_k_bounds.
      unfold MSISValidSubsequenceEndingAt in Hvalid_k_bounds.
      destruct Hvalid_k_bounds as [Hk_in_l Hvalid_k_rest].
      assert (Hk_nonneg : 0 <= k) by lia.
      specialize (Hprefix k (conj Hk_nonneg Hki))
        as [Hending_k Hbounds_k].
      unfold MSISEndingAt,
        MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hending_k.
      destruct Hending_k as
        [best_idxs [[Hbest_valid Hbest_upper] Hbest_sum]].
      specialize (Hbest_upper prefix Hvalid_k).
      exists (Znth k dp 0 + Znth i l 0). split.
      + right. exists k. split; [lia |].
        split; [exact Hvalues | reflexivity].
      + lia.
  }
  assert (Hending_i : MSISEndingAt l i (Znth i dp 0)).
  {
    unfold MSISEndingAt,
      MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hcandidate_max as
      [best_candidate [[Hbest_candidate Hbest_upper] Hbest_eq]].
    destruct (Hcandidate_to_valid best_candidate Hbest_candidate)
      as [best_idxs [Hbest_valid Hbest_sum]].
    exists best_idxs. split.
    - split; [exact Hbest_valid |].
      intros idxs Hvalid.
      destruct (Hvalid_to_candidate_bound idxs Hvalid)
        as [candidate [Hcandidate Hsum_bound]].
      specialize (Hbest_upper candidate Hcandidate).
      lia.
    - lia.
  }
  unfold MSISDPTablePrefix.
  split; [lia |].
  split; [exact Hlen |].
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hk_old | Hk_last].
  - apply Hprefix. lia.
  - assert (k = i) by lia. subst k.
    split; [exact Hending_i | exact Hcurrent_bounds].
Qed.
Lemma msis_valid_subsequence_extend_limit__outer_transitions :
  forall l old new idxs,
    old <= new ->
    new <= Zlength l ->
    MSISValidSubsequence l old idxs ->
    MSISValidSubsequence l new idxs.
Proof.
  intros l old new idxs Hold_new Hnew Hvalid.
  unfold MSISValidSubsequence in *.
  destruct Hvalid as [Hold [Hlen_pos [Hall [Hmono Hvalues]]]].
  split; [lia |].
  split; [exact Hlen_pos |].
  split.
  - eapply Forall_impl with (P := fun idx => 0 <= idx < old).
    + intros idx Hidx. lia.
    + exact Hall.
  - split; assumption.
Qed.
Lemma msis_valid_prefix_step_cases__outer_transitions :
  forall l i idxs,
    0 <= i < Zlength l ->
    MSISValidSubsequence l (i + 1) idxs ->
    MSISValidSubsequence l i idxs \/
    MSISValidSubsequenceEndingAt l i idxs.
Proof.
  intros l i idxs Hi Hvalid.
  destruct idxs as [| first rest].
  - exfalso.
    unfold MSISValidSubsequence in Hvalid.
    destruct Hvalid as [_ [Hlen_pos _]].
    rewrite Zlength_nil in Hlen_pos. lia.
  - assert (Hnonempty : first :: rest <> nil) by discriminate.
    destruct (exists_last Hnonempty) as [prefix [last Hidxs]].
    rewrite Hidxs in Hvalid.
    pose proof Hvalid as Hparts.
    unfold MSISValidSubsequence in Hparts.
    destruct Hparts as [Hlimit [Hlen_pos [Hall [Hmono Hvalues]]]].
    rewrite Forall_app in Hall.
    destruct Hall as [Hall_prefix Hall_last].
    inversion Hall_last as [| ? ? Hlast_bound _]; subst.
    pose proof (proj1 (mono_inc_iff_ind _) Hmono) as Hmono_ind.
    pose proof
      (proj1 (mono_inc_ind_app prefix (last :: nil)) Hmono_ind)
      as [Hprefix_mono_ind [_ Hcross]].
    destruct (Z_lt_ge_dec last i) as [Hlast_lt | Hlast_ge].
    + left.
      rewrite Hidxs.
      unfold MSISValidSubsequence.
      split; [lia |].
      split; [exact Hlen_pos |].
      split.
      * apply Forall_app. split.
        -- apply Forall_forall.
           intros idx Hin.
           pose proof Hall_prefix as Hall_prefix_forall.
           rewrite Forall_forall in Hall_prefix_forall.
           specialize (Hall_prefix_forall idx Hin).
           assert (Hidx_last : idx < last).
           {
             eapply Hcross; [exact Hin |].
             simpl. auto.
           }
           lia.
        -- constructor; [lia | constructor].
      * split; [exact Hmono | exact Hvalues].
    + assert (Hlast_i : last = i) by lia.
      subst last.
      right.
      rewrite Hidxs.
      unfold MSISValidSubsequenceEndingAt.
      split; [exact Hi |].
      split.
      * exact Hvalid.
      * exists prefix. reflexivity.
Qed.
Lemma msis_prefix_extend_by_ending__outer_transitions :
  forall l i old current,
    MSISBestSoFar l i old ->
    MSISEndingAt l i current ->
    MSISBestSoFar l (i + 1) (Z.max old current).
Proof.
  intros l i old current Hbest Hcurrent.
  unfold MSISBestSoFar in Hbest.
  destruct Hbest as [Hi Hold].
  pose proof Hcurrent as Hcurrent_bounds.
  unfold MSISEndingAt in Hcurrent_bounds.
  unfold MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hcurrent_bounds.
  destruct Hcurrent_bounds as
    [current_witness [[Hcurrent_valid_full Hcurrent_upper] Hcurrent_sum]].
  destruct Hcurrent_valid_full as [Hi_current [Hcurrent_valid Hcurrent_last]].
  unfold MSISBestSoFar.
  split; [lia |].
  unfold MSISPrefix, MSISEndingAt,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hold as [old_idxs [[Hold_valid Hold_upper] Hold_sum]].
  destruct Hcurrent as
    [current_idxs [[Hcurrent_ending Hcurrent_bound] Hcurrent_sum']].
  destruct Hcurrent_ending as [_ [Hcurrent_valid' _]].
  destruct (Z_le_gt_dec old current) as [Hold_current | Hcurrent_old].
  - exists current_idxs.
    split.
    + split; [exact Hcurrent_valid' |].
      intros idxs Hvalid.
      rewrite Hcurrent_sum'.
      destruct
        (msis_valid_prefix_step_cases__outer_transitions
          l i idxs ltac:(lia) Hvalid)
        as [Hvalid_old | Hvalid_current].
      * specialize (Hold_upper idxs Hvalid_old). lia.
      * specialize (Hcurrent_bound idxs Hvalid_current). lia.
    + rewrite Hcurrent_sum', Z.max_r by lia. reflexivity.
  - exists old_idxs.
    split.
    + split.
      * eapply msis_valid_subsequence_extend_limit__outer_transitions
          with (old := i); eauto; lia.
      * intros idxs Hvalid.
        rewrite Hold_sum.
        destruct
          (msis_valid_prefix_step_cases__outer_transitions
            l i idxs ltac:(lia) Hvalid)
          as [Hvalid_old | Hvalid_current].
        -- specialize (Hold_upper idxs Hvalid_old). lia.
        -- specialize (Hcurrent_bound idxs Hvalid_current). lia.
    + rewrite Hold_sum, Z.max_l by lia. reflexivity.
Qed.
