Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition max_Z (a b : Z) : Z := Z.max a b.

Definition SubarraySum (l : list Z) (lo hi s : Z) : Prop :=
  0 <= lo /\ lo < hi /\ hi <= Zlength l /\ s = sum (sublist lo hi l).

Definition MaxSuffixSumPrefix (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun lo => 0 <= lo /\ lo < i)
    (fun lo => sum (sublist lo i l))
    ans.

Definition MaxSubarraySumPrefix (l : list Z) (i ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun p : Z * Z =>
       let '(lo, hi) := p in
       0 <= lo /\ lo < hi /\ hi <= i)
    (fun p : Z * Z =>
       let '(lo, hi) := p in
       sum (sublist lo hi l))
    ans.

Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
Import SetsNotation.

Lemma sum_sublist_single :
  forall (l : list Z) (n : Z),
    0 <= n < Zlength l ->
    sum (sublist n (n + 1) l) = Znth n l 0.
Proof.
  intros l n Hn.
  rewrite (sublist_single 0 n l) by lia.
  simpl; lia.
Qed.

Lemma sum_sublist_snoc :
  forall (l : list Z) (lo hi : Z),
    0 <= lo <= hi ->
    hi + 1 <= Zlength l ->
    sum (sublist lo (hi + 1) l) =
      sum (sublist lo hi l) + Znth hi l 0.
Proof.
  intros l lo hi Hlo Hhi.
  rewrite (sublist_split lo (hi + 1) hi l) by lia.
  rewrite sum_app.
  rewrite sum_sublist_single by lia.
  lia.
Qed.

Lemma MaxSuffixSumPrefix_single :
  forall (l : list Z),
    1 <= Zlength l ->
    MaxSuffixSumPrefix l 1 (Znth 0 l 0).
Proof.
  intros l Hlen.
  unfold MaxSuffixSumPrefix.
  replace (Znth 0 l 0) with (sum (sublist 0 1 l)).
  - eapply (@max_1 Z Z.le Zle_TotalOrder Z 0).
    intros lo; split; intros Hlo; lia.
  - rewrite sum_sublist_single by lia. reflexivity.
Qed.

Lemma MaxSubarraySumPrefix_single :
  forall (l : list Z),
    1 <= Zlength l ->
    MaxSubarraySumPrefix l 1 (Znth 0 l 0).
Proof.
  intros l Hlen.
  unfold MaxSubarraySumPrefix.
  replace (Znth 0 l 0) with (sum (sublist 0 1 l)).
  - eapply (@max_1 Z Z.le Zle_TotalOrder (Z * Z)%type (0, 1)).
    intros [lo hi]; simpl; split; intros H.
    + destruct H as [? [? ?]].
      f_equal; lia.
    + inversion H; subst; lia.
  - rewrite sum_sublist_single by lia. reflexivity.
Qed.

Lemma MaxSuffixSumPrefix_step :
  forall (l : list Z) (i cur : Z),
    0 <= i ->
    i + 1 <= Zlength l ->
    MaxSuffixSumPrefix l i cur ->
    MaxSuffixSumPrefix l (i + 1)
      (max_Z (Znth i l 0) (cur + Znth i l 0)).
Proof.
  intros l i cur Hi Hlen Hcur.
  unfold MaxSuffixSumPrefix in *.
  destruct Hcur as [a [[Ha_in Ha_max] Ha_eq]].
  simpl in Ha_in, Ha_max.
  sets_unfold in Ha_in.
  sets_unfold in Ha_max.
  set (x := Znth i l 0).
  destruct (Z_le_dec x (cur + x)) as [Hle | Hnle].
  - exists a. split.
    + unfold max_object_of_subset; simpl.
      sets_unfold.
      split; [lia |].
      intros b Hb.
      simpl in Hb.
      destruct (Z.eq_dec b i) as [-> | Hbneq].
      * rewrite sum_sublist_single by lia.
        rewrite (sum_sublist_snoc l a i) by lia.
        rewrite Ha_eq.
        unfold x in *; lia.
      * assert (Hb_old : 0 <= b /\ b < i) by lia.
        rewrite sum_sublist_snoc by lia.
        rewrite (sum_sublist_snoc l a i) by lia.
        specialize (Ha_max b Hb_old).
        unfold x in *; lia.
    + rewrite sum_sublist_snoc by lia.
      rewrite Ha_eq.
      unfold max_Z. rewrite Z.max_r by lia. reflexivity.
  - exists i. split.
    + unfold max_object_of_subset; simpl.
      sets_unfold.
      split; [lia |].
      intros b Hb.
      simpl in Hb.
      destruct (Z.eq_dec b i) as [-> | Hbneq].
      * rewrite sum_sublist_single by lia. lia.
      * assert (Hb_old : 0 <= b /\ b < i) by lia.
        rewrite sum_sublist_snoc by lia.
        rewrite sum_sublist_single by lia.
        specialize (Ha_max b Hb_old).
        rewrite Ha_eq in Ha_max.
        unfold x in *.
        lia.
    + rewrite sum_sublist_single by lia.
      unfold max_Z, x. rewrite Z.max_l by lia. reflexivity.
Qed.

Lemma MaxSubarraySumPrefix_step :
  forall (l : list Z) (i res cur : Z),
    MaxSubarraySumPrefix l i res ->
    MaxSuffixSumPrefix l (i + 1) cur ->
    MaxSubarraySumPrefix l (i + 1) (max_Z res cur).
Proof.
  intros l i res cur Hres Hcur.
  unfold MaxSubarraySumPrefix in *.
  unfold MaxSuffixSumPrefix in Hcur.
  destruct Hres as [[lo hi] [[Hobj_in Hobj_max] Hobj_eq]].
  destruct Hcur as [s [[Hs_in Hs_max] Hs_eq]].
  simpl in Hobj_in, Hobj_max, Hs_in, Hs_max.
  sets_unfold in Hobj_in.
  sets_unfold in Hobj_max.
  sets_unfold in Hs_in.
  sets_unfold in Hs_max.
  destruct (Z_le_dec cur res) as [Hle | Hnle].
  - exists (lo, hi). split.
    + unfold max_object_of_subset; simpl.
      sets_unfold.
      split; [lia |].
      intros [blo bhi] Hb.
      simpl in Hb.
      destruct (Z.eq_dec bhi (i + 1)) as [Hbhi | Hbhi].
      * subst bhi.
        specialize (Hs_max blo ltac:(lia)).
        rewrite Hs_eq in Hs_max.
        rewrite Hobj_eq.
        lia.
      * assert (Hb_old : 0 <= blo /\ blo < bhi /\ bhi <= i) by lia.
        specialize (Hobj_max (blo, bhi) Hb_old).
        exact Hobj_max.
    + rewrite Hobj_eq.
      unfold max_Z. rewrite Z.max_l by lia. reflexivity.
  - exists (s, i + 1). split.
    + unfold max_object_of_subset; simpl.
      sets_unfold.
      split; [lia |].
      intros [blo bhi] Hb.
      simpl in Hb.
      destruct (Z.eq_dec bhi (i + 1)) as [Hbhi | Hbhi].
      * subst bhi.
        specialize (Hs_max blo ltac:(lia)).
        exact Hs_max.
      * assert (Hb_old : 0 <= blo /\ blo < bhi /\ bhi <= i) by lia.
        specialize (Hobj_max (blo, bhi) Hb_old).
        rewrite Hobj_eq in Hobj_max.
        rewrite Hs_eq.
        lia.
    + rewrite Hs_eq.
      unfold max_Z. rewrite Z.max_r by lia. reflexivity.
Qed.

Lemma sum_upper_bound :
  forall (l : list Z) (b : Z),
    0 <= b ->
    (forall i : Z, 0 <= i < Zlength l -> Znth i l 0 <= b) ->
    sum l <= Zlength l * b.
Proof.
  induction l as [| a l IH]; intros b Hb Hbound.
  - simpl. change (Zlength (@nil Z)) with 0. lia.
  - simpl.
    rewrite Zlength_cons.
    assert (Ha : a <= b).
    {
      specialize (Hbound 0).
      rewrite Znth0_cons in Hbound.
      apply Hbound.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l); lia.
    }
    assert (Htail : forall i : Z, 0 <= i < Zlength l -> Znth i l 0 <= b).
    {
      intros i Hi.
      specialize (Hbound (i + 1)).
      rewrite Znth_cons in Hbound by lia.
      replace (i + 1 - 1) with i in Hbound by lia.
      apply Hbound.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l); lia.
    }
    specialize (IH b Hb Htail).
    lia.
Qed.

Lemma sum_sublist_upper_bound :
  forall (l : list Z) (lo hi n b : Z),
    0 <= b ->
    0 <= lo <= hi ->
    hi <= n ->
    n <= Zlength l ->
    (forall k : Z, 0 <= k < n -> Znth k l 0 <= b) ->
    sum (sublist lo hi l) <= (hi - lo) * b.
Proof.
  intros l lo hi n b Hb Hlo Hhi Hn Hbound.
  eapply Z.le_trans with (m := Zlength (sublist lo hi l) * b).
  - apply sum_upper_bound; [lia |].
    intros j Hj.
    assert (Hj' : 0 <= j < hi - lo).
    {
      rewrite Zlength_sublist in Hj by lia.
      lia.
    }
    rewrite Znth_sublist by lia.
    apply Hbound; lia.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma MaxSuffixSumPrefix_upper_bound :
  forall (l : list Z) (i ans n : Z),
    0 <= i <= n ->
    n <= Zlength l ->
    n <= 100000 ->
    (forall k : Z, 0 <= k < n -> Znth k l 0 <= 10000) ->
    MaxSuffixSumPrefix l i ans ->
    ans <= 1000000000.
Proof.
  intros l i ans n Hi Hn Hn_bound Hbound Hmax.
  unfold MaxSuffixSumPrefix in Hmax.
  destruct Hmax as [lo [[Hlo_in _] Hsum]].
  simpl in Hlo_in.
  sets_unfold in Hlo_in.
  rewrite <- Hsum.
  eapply Z.le_trans.
  - eapply sum_sublist_upper_bound with (n := n) (b := 10000); try lia.
    exact Hbound.
  - lia.
Qed.
