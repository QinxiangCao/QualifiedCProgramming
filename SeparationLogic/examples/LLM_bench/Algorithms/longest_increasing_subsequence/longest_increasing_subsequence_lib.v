Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition StrictlyIncreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 < Znth (Znth q idxs 0) l 0.

Definition ValidIncreasingSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  StrictlyIncreasingValues l idxs.

Definition LastIndexOf (idxs : list Z) (last : Z) : Prop :=
  0 < Zlength idxs /\
  Znth (Zlength idxs - 1) idxs 0 = last.

Definition ValidIncreasingSubsequenceEndingAt
    (l : list Z) (i : Z) (idxs : list Z) : Prop :=
  0 <= i < Zlength l /\
  ValidIncreasingSubsequence l (i + 1) idxs /\
  LastIndexOf idxs i.

Definition LISEndingAtPrefix (l : list Z) (i len : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequenceEndingAt l i idxs)
    (fun idxs => Zlength idxs)
    len.

Definition LISPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidIncreasingSubsequence l limit idxs)
    (fun idxs => Zlength idxs)
    ans.

Definition LISLength (l : list Z) (ans : Z) : Prop :=
  LISPrefix l (Zlength l) ans.

Definition LISDPState (l d : list Z) (i : Z) : Prop :=
  0 <= i <= Zlength l /\
  Zlength d = i /\
  (forall k,
      0 <= k < i ->
      LISEndingAtPrefix l k (Znth k d 0) /\
      1 <= Znth k d 0 <= k + 1).

Definition LISInnerCandidate
    (l d : list Z) (i j value : Z) : Prop :=
  value = 1 \/
  exists k,
    0 <= k < j /\
    k < i /\
    Znth k l 0 < Znth i l 0 /\
    LISEndingAtPrefix l k (Znth k d 0) /\
    value = Znth k d 0 + 1.

Definition LISInnerBest
    (l d : list Z) (i j best : Z) : Prop :=
  0 <= i < Zlength l /\
  0 <= j <= i /\
  LISDPState l d i /\
  max_value_of_subset Z.le
    (fun value => LISInnerCandidate l d i j value)
    (fun value => value)
    best.

Definition LISOuterState
    (l d : list Z) (i ans : Z) : Prop :=
  LISDPState l d i /\
  1 <= ans <= Z.max 1 i /\
  ((i = 0 /\ ans = 1) \/
   (0 < i /\ LISPrefix l i ans)).

Require Import Coq.micromega.Psatz.

Lemma znth_app_singleton_last_Z :
  forall (A : Type) (dflt x : A) (xs : list A) i,
    Zlength xs = i ->
    Znth i (xs ++ x :: nil) dflt = x.
Proof.
  intros A dflt x xs i Hlen.
  rewrite app_Znth2.
  - rewrite Hlen. replace (i - i) with 0 by lia. reflexivity.
  - rewrite Hlen. lia.
Qed.

Lemma znth_app_singleton_old_Z :
  forall (A : Type) (dflt x : A) (xs : list A) k,
    0 <= k < Zlength xs ->
    Znth k (xs ++ x :: nil) dflt = Znth k xs dflt.
Proof.
  intros A dflt x xs k Hk.
  rewrite app_Znth1; auto.
Qed.

Lemma Forall_snoc :
  forall (A : Type) (P : A -> Prop) (xs : list A) x,
    Forall P xs ->
    P x ->
    Forall P (xs ++ x :: nil).
Proof.
  intros A P xs x Hxs Hx.
  apply Forall_app. split; auto.
Qed.

Lemma Forall_Znth :
  forall (A : Type) (P : A -> Prop) (xs : list A) (dflt : A) k,
    Forall P xs ->
    0 <= k < Zlength xs ->
    P (Znth k xs dflt).
Proof.
  intros A P xs dflt k HForall Hk.
  apply Forall_forall with (x := Znth k xs dflt) in HForall; auto.
  unfold Znth.
  apply nth_In.
  replace (length xs) with (Z.to_nat (Zlength xs)).
  - apply Z2Nat.inj_lt; lia.
  - rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma last_index_snoc :
  forall xs last,
    LastIndexOf xs last ->
    exists prefix, xs = prefix ++ last :: nil.
Proof.
  intros xs last Hlast.
  destruct Hlast as [Hnz Hlast].
  assert (xs <> nil) as Hxs_nonempty.
  { intro Hnil. subst xs. rewrite Zlength_nil in Hnz. lia. }
  destruct (exists_last Hxs_nonempty) as [prefix [x Hxs]].
  exists prefix.
  subst xs.
  assert (Znth (Zlength (prefix ++ x :: nil) - 1) (prefix ++ x :: nil) 0 = x) as Htail.
  { rewrite Zlength_app_cons.
    rewrite app_Znth2.
    - replace (Zlength prefix + 1 - 1 - Zlength prefix) with 0 by lia.
      reflexivity.
    - lia. }
  rewrite Htail in Hlast. subst x. reflexivity.
Qed.

Lemma StrictlyIncreasingZList_snoc :
  forall xs x,
    mono_inc xs ->
    Forall (fun idx => idx < x) xs ->
    mono_inc (xs ++ x :: nil).
Proof.
  intros xs x Hinc Hall.
  apply (proj2 (mono_inc_iff_ind (xs ++ x :: nil))).
  apply (proj2 (mono_inc_ind_app xs (x :: nil))).
  repeat split.
  - apply (proj1 (mono_inc_iff_ind xs)); exact Hinc.
  - apply (proj1 (mono_inc_iff_ind (x :: nil))).
    apply mono_inc_single.
  - intros a b Ha Hb.
    destruct Hb as [Hb | Hb]; [subst b | contradiction].
    rewrite Forall_forall in Hall.
    apply Hall; exact Ha.
Qed.

Lemma StrictlyIncreasingValues_snoc :
  forall l xs x,
    StrictlyIncreasingValues l xs ->
    Forall (fun idx => Znth idx l 0 < Znth x l 0) xs ->
    StrictlyIncreasingValues l (xs ++ x :: nil).
Proof.
  intros l xs x Hinc Hall.
  unfold StrictlyIncreasingValues in *.
  intros p q [Hp [Hpq Hq]].
  rewrite Zlength_app_cons in Hq.
  assert (q < Zlength xs \/ q = Zlength xs) as [Hq_old | Hq_last] by lia.
  - rewrite !znth_app_singleton_old_Z by lia.
    apply Hinc. lia.
  - subst q.
    rewrite znth_app_singleton_last_Z with (i := Zlength xs) by reflexivity.
    rewrite znth_app_singleton_old_Z by lia.
    apply (Forall_Znth Z (fun idx => Znth idx l 0 < Znth x l 0) xs 0 p Hall).
    lia.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_single :
  forall l i,
    0 <= i < Zlength l ->
  ValidIncreasingSubsequenceEndingAt l i (i :: nil).
Proof.
  intros l i Hi.
  unfold ValidIncreasingSubsequenceEndingAt, ValidIncreasingSubsequence,
    LastIndexOf, StrictlyIncreasingValues.
  repeat split; try lia.
  - constructor; [lia | constructor].
  - apply mono_inc_single.
  - intros p q [Hp [Hpq Hq]].
    rewrite Zlength_cons, Zlength_nil in Hq. lia.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_snoc_strong :
  forall l xs i,
    0 <= i < Zlength l ->
    Forall (fun idx => 0 <= idx < i) xs ->
    mono_inc xs ->
    StrictlyIncreasingValues l xs ->
    Forall (fun idx => Znth idx l 0 < Znth i l 0) xs ->
    ValidIncreasingSubsequenceEndingAt l i (xs ++ i :: nil).
Proof.
  intros l xs i Hi Hbounds Hidx Hvals Hval_bounds.
  unfold ValidIncreasingSubsequenceEndingAt, ValidIncreasingSubsequence, LastIndexOf.
  repeat split; try lia.
  - apply Forall_snoc.
    + eapply Forall_impl with (P := fun idx => 0 <= idx < i); [| exact Hbounds].
      intros a Ha. lia.
    + lia.
  - apply StrictlyIncreasingZList_snoc; auto.
    eapply Forall_impl with (P := fun idx => 0 <= idx < i); [| exact Hbounds].
    intros a Ha. lia.
  - apply StrictlyIncreasingValues_snoc; auto.
  - rewrite Zlength_app_cons.
    pose proof (Zlength_nonneg xs). lia.
  - rewrite Zlength_app_cons.
    replace (Zlength xs + 1 - 1) with (Zlength xs) by lia.
    rewrite znth_app_singleton_last_Z with (i := Zlength xs) by reflexivity.
    reflexivity.
Qed.

Lemma lis_inner_best_step_take :
  forall l d i j best,
    0 <= j < i ->
    Znth j l 0 < Znth i l 0 ->
    Znth j d 0 + 1 <= best ->
    LISInnerBest l d i j best ->
    LISInnerBest l d i (j + 1) best.
Proof.
  intros l d i j best Hj Hltj Hcand_le Hbest.
  unfold LISInnerBest in *.
  destruct Hbest as [Hi [Hjold [Hdp Hmax]]].
  split; [exact Hi |].
  split; [lia |].
  split; [exact Hdp |].
  destruct Hmax as [a [[Ha Hle] Ha_eq]].
    exists a. split; [split | exact Ha_eq].
    + unfold SetElement.SetsEle.In in *; simpl in *; unfold LISInnerCandidate in *.
      destruct Ha as [Ha | [k [Hk0 [Hki [Hlt [Hlis Ha]]]]]].
      * left; exact Ha.
      * right. exists k. repeat split; try lia; auto.
    + intros b Hb.
      unfold SetElement.SetsEle.In in *; simpl in *; unfold LISInnerCandidate in *.
      destruct Hb as [Hb | [k [Hk0 [Hki [Hlt [Hlis Hb]]]]]].
      * apply Hle. left; exact Hb.
      * assert (k < j \/ k = j) as [Hkj | Hkj] by lia.
        -- apply Hle. right. exists k. repeat split; try lia; auto.
        -- subst k. rewrite Hb. rewrite Ha_eq. exact Hcand_le.
Qed.

Lemma lis_inner_best_step_skip :
  forall l d i j best,
    0 <= j < i ->
    Znth j l 0 >= Znth i l 0 ->
    LISInnerBest l d i j best ->
    LISInnerBest l d i (j + 1) best.
Proof.
  intros l d i j best Hj Hge Hbest.
  unfold LISInnerBest in *.
  destruct Hbest as [Hi [Hjold [Hdp Hmax]]].
  split; [exact Hi |].
  split; [lia |].
  split; [exact Hdp |].
  destruct Hmax as [a [[Ha Hle] Ha_eq]].
    exists a. split; [split | exact Ha_eq].
    + unfold SetElement.SetsEle.In in *; simpl in *; unfold LISInnerCandidate in *.
      destruct Ha as [Ha | [k [Hk0 [Hki [Hlt [Hlis Ha]]]]]].
      * left; exact Ha.
      * right. exists k. repeat split; try lia; auto.
    + intros b Hb. apply Hle.
      unfold SetElement.SetsEle.In in *; simpl in *; unfold LISInnerCandidate in *.
      destruct Hb as [Hb | [k [Hk0 [Hki [Hlt [Hlis Hb]]]]]].
      * left; exact Hb.
      * right. exists k. repeat split; try lia; auto.
        assert (k <> j) by (intro Heq; subst k; lia). lia.
Qed.

Lemma In_Znth_Zlength :
  forall (A : Type) (xs : list A) (x dflt : A),
    In x xs ->
    exists p, 0 <= p < Zlength xs /\ Znth p xs dflt = x.
Proof.
  intros A xs x dflt Hin.
  apply In_nth with (d := dflt) in Hin as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.

Lemma Forall_Znth_intro :
  forall (A : Type) (P : A -> Prop) (xs : list A) (dflt : A),
    (forall p, 0 <= p < Zlength xs -> P (Znth p xs dflt)) ->
    Forall P xs.
Proof.
  intros A P xs dflt Hnth.
  apply Forall_forall.
  intros x Hin.
  destruct (In_Znth_Zlength A xs x dflt Hin) as [p [Hp Hx]].
  rewrite <- Hx.
  apply Hnth; exact Hp.
Qed.

Lemma Forall_snoc_inv :
  forall (A : Type) (P : A -> Prop) (xs : list A) x,
    Forall P (xs ++ x :: nil) ->
    Forall P xs /\ P x.
Proof.
  intros A P xs x H.
  apply Forall_app in H as [Hxs Hx].
  inversion Hx; subst.
  split; auto.
Qed.

Lemma StrictlyIncreasingZList_snoc_inv :
  forall xs x,
    mono_inc (xs ++ x :: nil) ->
    mono_inc xs.
Proof.
  intros xs x Hinc.
  unfold mono_inc in *.
  intros p q Hp Hpq Hq.
  specialize (Hinc p q Hp Hpq ltac:(rewrite Zlength_app_cons; lia)).
  rewrite !znth_app_singleton_old_Z in Hinc by lia.
  exact Hinc.
Qed.

Lemma StrictlyIncreasingValues_snoc_inv :
  forall l xs x,
    StrictlyIncreasingValues l (xs ++ x :: nil) ->
    StrictlyIncreasingValues l xs.
Proof.
  intros l xs x Hinc.
  unfold StrictlyIncreasingValues in *.
  intros p q Hp.
  specialize (Hinc p q ltac:(rewrite Zlength_app_cons; lia)).
  rewrite !znth_app_singleton_old_Z in Hinc by lia.
  exact Hinc.
Qed.

Lemma StrictlyIncreasingZList_snoc_last :
  forall xs x,
    mono_inc (xs ++ x :: nil) ->
    Forall (fun idx => idx < x) xs.
Proof.
  intros xs x Hinc.
  apply (Forall_Znth_intro Z (fun idx => idx < x) xs 0).
  intros p Hp.
  pose proof (Hinc p (Zlength xs)
    ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_app_cons; lia)) as Hlt.
  rewrite znth_app_singleton_old_Z in Hlt by lia.
  rewrite znth_app_singleton_last_Z with (i := Zlength xs) in Hlt by reflexivity.
  exact Hlt.
Qed.

Lemma StrictlyIncreasingValues_snoc_last :
  forall l xs x,
    StrictlyIncreasingValues l (xs ++ x :: nil) ->
    Forall (fun idx => Znth idx l 0 < Znth x l 0) xs.
Proof.
  intros l xs x Hinc.
  apply (Forall_Znth_intro Z (fun idx => Znth idx l 0 < Znth x l 0) xs 0).
  intros p Hp.
  pose proof (Hinc p (Zlength xs)) as Hlt.
  rewrite znth_app_singleton_old_Z in Hlt by lia.
  rewrite znth_app_singleton_last_Z with (i := Zlength xs) in Hlt by reflexivity.
  apply Hlt.
  rewrite Zlength_app_cons.
  lia.
Qed.

Lemma ValidIncreasingSubsequence_snoc_prefix_same_limit :
  forall l limit xs x,
    ValidIncreasingSubsequence l limit (xs ++ x :: nil) ->
    ValidIncreasingSubsequence l limit xs.
Proof.
  intros l limit xs x Hvalid.
  unfold ValidIncreasingSubsequence in *.
  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
  destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < limit) xs x Hall) as [Hallxs _].
  repeat split.
  - lia.
  - lia.
  - exact Hallxs.
  - apply StrictlyIncreasingZList_snoc_inv with (x := x); auto.
  - apply StrictlyIncreasingValues_snoc_inv with (x := x); auto.
Qed.

Lemma ValidIncreasingSubsequence_tighten_to_last :
  forall l limit xs x,
    ValidIncreasingSubsequence l limit (xs ++ x :: nil) ->
    ValidIncreasingSubsequence l (x + 1) (xs ++ x :: nil).
Proof.
  intros l limit xs x Hvalid.
  unfold ValidIncreasingSubsequence in *.
  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
  destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < limit) xs x Hall) as [Hallxs Hx].
  pose proof (StrictlyIncreasingZList_snoc_last xs x Hidx) as Hall_lt.
  repeat split.
  - lia.
  - lia.
  - apply Forall_snoc; [| lia].
    apply Forall_forall.
    intros a Hin.
    apply Forall_forall with (x := a) in Hallxs; auto.
    apply Forall_forall with (x := a) in Hall_lt; auto.
    lia.
  - exact Hidx.
  - exact Hvals.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_length_pos :
  forall l i xs,
    ValidIncreasingSubsequenceEndingAt l i xs ->
    0 < Zlength xs.
Proof.
  intros l i xs [_ [_ [Hlen _]]].
  exact Hlen.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_bounds_before :
  forall l k i xs,
    ValidIncreasingSubsequenceEndingAt l k xs ->
    k < i ->
    Forall (fun idx => 0 <= idx < i) xs.
Proof.
  intros l k i xs Hend Hki.
  unfold ValidIncreasingSubsequenceEndingAt, ValidIncreasingSubsequence in Hend.
  destruct Hend as [_ [[_ [Hall _]] _]].
  eapply Forall_impl with (P := fun idx => 0 <= idx < k + 1); [| exact Hall].
  intros a Ha. lia.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_values_before :
  forall l k i xs,
    ValidIncreasingSubsequenceEndingAt l k xs ->
    Znth k l 0 < Znth i l 0 ->
    Forall (fun idx => Znth idx l 0 < Znth i l 0) xs.
Proof.
  intros l k i xs Hend Hki_val.
  unfold ValidIncreasingSubsequenceEndingAt in Hend.
  destruct Hend as [_ [Hvalid Hlast]].
  destruct (last_index_snoc xs k Hlast) as [prefix Hxs].
  subst xs.
  unfold ValidIncreasingSubsequence in Hvalid.
  destruct Hvalid as [_ [_ [_ Hvals]]].
  apply Forall_snoc; [| exact Hki_val].
  pose proof (StrictlyIncreasingValues_snoc_last l prefix k Hvals) as Hprefix.
  eapply Forall_impl with
    (P := fun idx => Znth idx l 0 < Znth k l 0); [| exact Hprefix].
  intros a Ha. lia.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_extend :
  forall l xs k i,
    ValidIncreasingSubsequenceEndingAt l k xs ->
    k < i ->
    0 <= i < Zlength l ->
    Znth k l 0 < Znth i l 0 ->
    ValidIncreasingSubsequenceEndingAt l i (xs ++ i :: nil).
Proof.
  intros l xs k i Hend Hki Hi Hval.
  pose proof Hend as Hend0.
  unfold ValidIncreasingSubsequenceEndingAt in Hend.
  destruct Hend as [Hk [Hvalid Hlast]].
  unfold ValidIncreasingSubsequence in Hvalid.
  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
  apply ValidIncreasingSubsequenceEndingAt_snoc_strong.
  - exact Hi.
  - eapply Forall_impl with (P := fun idx => 0 <= idx < k + 1); [| exact Hall].
    intros a Ha. lia.
  - exact Hidx.
  - exact Hvals.
  - exact (ValidIncreasingSubsequenceEndingAt_values_before l k i xs Hend0 Hval).
Qed.

Lemma LISEndingAtPrefix_bound :
  forall l i len xs,
    LISEndingAtPrefix l i len ->
    ValidIncreasingSubsequenceEndingAt l i xs ->
    Zlength xs <= len.
Proof.
  intros l i len xs Hlis Hvalid.
  unfold LISEndingAtPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hlis.
  destruct Hlis as [best_obj [[Hbest_valid Hbest_max] Hlen]].
  specialize (Hbest_max xs Hvalid).
  lia.
Qed.

Lemma LISEndingAtPrefix_witness :
  forall l i len,
    LISEndingAtPrefix l i len ->
    exists xs,
      ValidIncreasingSubsequenceEndingAt l i xs /\
      Zlength xs = len.
Proof.
  intros l i len Hlis.
  unfold LISEndingAtPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hlis.
  destruct Hlis as [xs [[Hvalid _] Hlen]].
  exists xs. auto.
Qed.

Lemma LISInnerCandidate_realizable :
  forall l d i value,
    0 <= i < Zlength l ->
    LISInnerCandidate l d i i value ->
    exists xs,
      ValidIncreasingSubsequenceEndingAt l i xs /\
      Zlength xs = value.
Proof.
  intros l d i value Hi Hcand.
  unfold LISInnerCandidate in Hcand.
  destruct Hcand as [Hone | Hcand].
  - subst value.
    exists (i :: nil).
    split.
    + apply ValidIncreasingSubsequenceEndingAt_single; exact Hi.
    + rewrite Zlength_cons, Zlength_nil. lia.
  - destruct Hcand as [k [Hk0 [Hki [Hlt [Hlis Hvalue]]]]].
    destruct (LISEndingAtPrefix_witness l k (Znth k d 0) Hlis)
      as [xs [Hxs Hxs_len]].
    exists (xs ++ i :: nil).
    split.
    + apply ValidIncreasingSubsequenceEndingAt_extend with (k := k); auto.
    + rewrite Zlength_app_cons. lia.
Qed.

Lemma LastIndexOf_snoc :
  forall xs x,
    LastIndexOf (xs ++ x :: nil) x.
Proof.
  intros xs x.
  unfold LastIndexOf.
  split.
  - rewrite Zlength_app_cons.
    pose proof (Zlength_nonneg xs). lia.
  - rewrite Zlength_app_cons.
    replace (Zlength xs + 1 - 1) with (Zlength xs) by lia.
    rewrite znth_app_singleton_last_Z with (i := Zlength xs) by reflexivity.
    reflexivity.
Qed.

Lemma ValidIncreasingSubsequenceEndingAt_predecessor :
  forall l i ys,
    ValidIncreasingSubsequenceEndingAt l i ys ->
    1 < Zlength ys ->
    exists prefix k,
      ys = prefix ++ i :: nil /\
      LastIndexOf prefix k /\
      0 <= k < i /\
      Znth k l 0 < Znth i l 0 /\
      ValidIncreasingSubsequenceEndingAt l k prefix /\
      Zlength ys = Zlength prefix + 1.
Proof.
  intros l i ys Hend Hlong.
  unfold ValidIncreasingSubsequenceEndingAt in Hend.
  destruct Hend as [Hi [Hvalid Hlast_i]].
  destruct (last_index_snoc ys i Hlast_i) as [prefix Hys].
  subst ys.
  assert (Hprefix_nonempty : prefix <> nil).
  { intro Hnil. subst prefix. rewrite Zlength_app_cons, Zlength_nil in Hlong. lia. }
  destruct (exists_last Hprefix_nonempty) as [pre [k Hprefix]].
  exists prefix, k.
  pose proof Hvalid as Hprefix_valid.
  apply ValidIncreasingSubsequence_snoc_prefix_same_limit in Hprefix_valid.
  pose proof Hvalid as Hidxvals.
  unfold ValidIncreasingSubsequence in Hidxvals.
  destruct Hidxvals as [_ [_ [Hidx_all Hvals_all]]].
  pose proof (StrictlyIncreasingZList_snoc_last prefix i Hidx_all) as Hprefix_lt_i.
  pose proof (StrictlyIncreasingValues_snoc_last l prefix i Hvals_all) as Hprefix_val_lt_i.
  subst prefix.
  pose proof (LastIndexOf_snoc pre k) as Hlast_k.
  assert (Hk_lt_i : k < i).
  { apply Forall_snoc_inv in Hprefix_lt_i as [_ Hklt]. exact Hklt. }
  assert (Hk_val_lt_i : Znth k l 0 < Znth i l 0).
  { apply Forall_snoc_inv in Hprefix_val_lt_i as [_ Hklt]. exact Hklt. }
  assert (Hprefix_valid_tight :
    ValidIncreasingSubsequence l (k + 1) (pre ++ k :: nil)).
  { eapply ValidIncreasingSubsequence_tighten_to_last with (limit := i + 1).
    exact Hprefix_valid. }
  unfold ValidIncreasingSubsequence in Hprefix_valid_tight.
  destruct Hprefix_valid_tight as [Hklim [Hkforall [Hkidx Hkvals]]].
  destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < k + 1) pre k Hkforall)
    as [_ Hk_bound].
  split; [reflexivity |].
  split; [exact Hlast_k |].
  split; [lia |].
  split; [exact Hk_val_lt_i |].
  split.
  - unfold ValidIncreasingSubsequenceEndingAt.
    split; [lia |].
    split; [| exact Hlast_k].
    unfold ValidIncreasingSubsequence.
    repeat split; try lia; auto.
  - rewrite Zlength_app_cons. lia.
Qed.

Lemma LISInnerBest_realizable :
  forall l d i best,
    LISInnerBest l d i i best ->
    exists xs,
      ValidIncreasingSubsequenceEndingAt l i xs /\
      Zlength xs = best.
Proof.
  intros l d i best Hbest.
  unfold LISInnerBest in Hbest.
  destruct Hbest as [Hi [_ [_ Hmax]]].
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [value [[Hcand _] Hvalue]].
  subst best.
  eapply LISInnerCandidate_realizable with (d := d); eauto.
Qed.

Lemma LISInnerBest_bound_ending :
  forall l d i best ys,
    LISInnerBest l d i i best ->
    ValidIncreasingSubsequenceEndingAt l i ys ->
    Zlength ys <= best.
Proof.
  intros l d i best ys Hbest Hend.
  unfold LISInnerBest in Hbest.
  destruct Hbest as [Hi [_ [Hdp Hmax]]].
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [value [[Hcand Hmax] Hvalue]].
  subst best.
  pose proof (ValidIncreasingSubsequenceEndingAt_length_pos l i ys Hend) as Hpos.
  destruct (Z_le_gt_dec (Zlength ys) 1) as [Hle1 | Hgt1].
  - assert (Zlength ys = 1) by lia.
    rewrite H.
    apply Hmax.
    unfold LISInnerCandidate.
    left; reflexivity.
  - assert (Hgt1' : 1 < Zlength ys) by lia.
    destruct (ValidIncreasingSubsequenceEndingAt_predecessor l i ys Hend Hgt1')
      as [prefix [k Hpred]].
    destruct Hpred as [Hys [Hlast_k [Hk [Hval_lt [Hend_k Hlen_ys]]]]].
    destruct Hdp as [_ [_ Hdp_facts]].
    destruct (Hdp_facts k Hk) as [Hlis_k _].
    pose proof (LISEndingAtPrefix_bound l k (Znth k d 0) prefix Hlis_k Hend_k)
      as Hprefix_bound.
    assert (Hcand_k : LISInnerCandidate l d i i (Znth k d 0 + 1)).
    { unfold LISInnerCandidate.
      right. exists k. repeat split; try lia; auto. }
    specialize (Hmax (Znth k d 0 + 1) Hcand_k).
    lia.
Qed.

Lemma LISInnerBest_to_LISEndingAtPrefix :
  forall l d i best,
    LISInnerBest l d i i best ->
    LISEndingAtPrefix l i best.
Proof.
  intros l d i best Hbest.
  destruct (LISInnerBest_realizable l d i best Hbest) as [xs [Hxs Hlen]].
  unfold LISEndingAtPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  exists xs.
  split.
  - split.
    + exact Hxs.
    + intros ys Hys.
      rewrite Hlen.
      apply LISInnerBest_bound_ending with (l := l) (d := d) (i := i); auto.
  - exact Hlen.
Qed.

Lemma ValidIncreasingSubsequence_monotone_limit :
  forall l old new xs,
    old <= new ->
    new <= Zlength l ->
    ValidIncreasingSubsequence l old xs ->
    ValidIncreasingSubsequence l new xs.
Proof.
  intros l old new xs Hold_new Hnew Hvalid.
  unfold ValidIncreasingSubsequence in *.
  destruct Hvalid as [Hold [Hall [Hidx Hvals]]].
  repeat split; try lia; auto.
  eapply Forall_impl with (P := fun idx => 0 <= idx < old); [| exact Hall].
  intros a Ha. lia.
Qed.

Lemma ValidIncreasingSubsequence_zero_length :
  forall l xs,
    ValidIncreasingSubsequence l 0 xs ->
    Zlength xs = 0.
Proof.
  intros l xs Hvalid.
  unfold ValidIncreasingSubsequence in Hvalid.
  destruct Hvalid as [_ [Hall _]].
  destruct xs as [| x xs].
  - rewrite Zlength_nil. reflexivity.
  - inversion Hall; subst. lia.
Qed.

Lemma ValidIncreasingSubsequence_split_last :
  forall l i xs,
    0 <= i < Zlength l ->
    ValidIncreasingSubsequence l (i + 1) xs ->
    ValidIncreasingSubsequence l i xs \/
    ValidIncreasingSubsequenceEndingAt l i xs.
Proof.
  intros l i xs Hi Hvalid.
  destruct xs as [| x xs_tail].
  - left.
    unfold ValidIncreasingSubsequence.
    repeat split; try lia.
    + constructor.
    + apply mono_inc_nil.
    + unfold StrictlyIncreasingValues.
      intros p q Hp; rewrite Zlength_nil in Hp; lia.
  - assert (Hnonempty : x :: xs_tail <> nil) by discriminate.
    destruct (exists_last Hnonempty) as [prefix [k Hxs]].
    rewrite Hxs in Hvalid.
    pose proof Hvalid as Hvalid_unfold.
    unfold ValidIncreasingSubsequence in Hvalid_unfold.
    destruct Hvalid_unfold as [Hlim [Hall [Hidx Hvals]]].
    destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < i + 1) prefix k Hall)
      as [Hall_prefix Hk_bound].
    destruct (Z_lt_ge_dec k i) as [Hklt | Hkge].
    + left.
      rewrite Hxs.
      eapply ValidIncreasingSubsequence_monotone_limit
        with (old := k + 1).
      * lia.
      * lia.
      * eapply ValidIncreasingSubsequence_tighten_to_last
          with (limit := i + 1).
        exact Hvalid.
    + assert (Hki : k = i) by lia.
      subst k.
      right.
      rewrite Hxs.
      unfold ValidIncreasingSubsequenceEndingAt.
      split; [exact Hi |].
      split; [exact Hvalid |].
      apply LastIndexOf_snoc.
Qed.

Lemma LISPrefix_bound :
  forall l limit ans xs,
    LISPrefix l limit ans ->
    ValidIncreasingSubsequence l limit xs ->
    Zlength xs <= ans.
Proof.
  intros l limit ans xs Hlis Hvalid.
  unfold LISPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hlis.
  destruct Hlis as [best_obj [[Hbest_valid Hbest_max] Hlen]].
  specialize (Hbest_max xs Hvalid).
  lia.
Qed.

Lemma LISPrefix_witness :
  forall l limit ans,
    LISPrefix l limit ans ->
    exists xs,
      ValidIncreasingSubsequence l limit xs /\
      Zlength xs = ans.
Proof.
  intros l limit ans Hlis.
  unfold LISPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hlis.
  destruct Hlis as [xs [[Hvalid _] Hlen]].
  exists xs. auto.
Qed.

Lemma LISDPState_snoc :
  forall l d i best,
    0 <= i < Zlength l ->
    LISDPState l d i ->
    LISEndingAtPrefix l i best ->
    1 <= best <= i + 1 ->
    LISDPState l (d ++ best :: nil) (i + 1).
Proof.
  intros l d i best Hi_strict Hdp Hending Hbest_bounds.
  unfold LISDPState in *.
  destruct Hdp as [Hi [Hdlen Hfacts]].
  split; [lia |].
  split; [rewrite Zlength_app_cons; lia |].
  intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + rewrite znth_app_singleton_old_Z by (rewrite Hdlen; lia).
      destruct (Hfacts k ltac:(lia)) as [Hending_k Hbounds_k].
      split; [exact Hending_k | lia].
    + assert (k = i) by lia.
      subst k.
      rewrite znth_app_singleton_last_Z with (i := i) by exact Hdlen.
      split; auto.
Qed.

Lemma LISPrefix_step_take_from_outer :
  forall l d i ans best,
    0 <= i < Zlength l ->
    LISOuterState l d i ans ->
    LISEndingAtPrefix l i best ->
    ans < best ->
    LISPrefix l (i + 1) best.
Proof.
  intros l d i ans best Hi Houter Hending Hans_best.
  destruct (LISEndingAtPrefix_witness l i best Hending) as [best_xs [Hbest_xs Hbest_len]].
  unfold LISPrefix, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists best_xs.
  split.
  - split.
    + unfold ValidIncreasingSubsequenceEndingAt in Hbest_xs.
      destruct Hbest_xs as [_ [Hvalid _]].
      exact Hvalid.
    + intros ys Hys.
      destruct (ValidIncreasingSubsequence_split_last l i ys Hi Hys) as [Hold | Hend].
      * unfold LISOuterState in Houter.
        destruct Houter as [_ [_ Hcase]].
        destruct Hcase as [[Hi0 Hans1] | [_ Hprefix]].
        -- subst i ans.
           pose proof (ValidIncreasingSubsequence_zero_length l ys Hold).
           lia.
        -- pose proof (LISPrefix_bound l i ans ys Hprefix Hold).
           lia.
      * pose proof (LISEndingAtPrefix_bound l i best ys Hending Hend).
        lia.
  - exact Hbest_len.
Qed.

Lemma LISPrefix_step_keep_from_outer :
  forall l d i ans best,
    0 <= i < Zlength l ->
    LISOuterState l d i ans ->
    LISEndingAtPrefix l i best ->
    best <= ans ->
    LISPrefix l (i + 1) ans.
Proof.
  intros l d i ans best Hi Houter Hending Hbest_ans.
  unfold LISPrefix, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  assert (Hwitness :
    exists xs,
      ValidIncreasingSubsequence l (i + 1) xs /\
      Zlength xs = ans).
  {
    unfold LISOuterState in Houter.
    destruct Houter as [_ [Hans_bounds Hcase]].
    destruct Hcase as [[Hi0 Hans1] | [_ Hprefix]].
    - subst i ans.
      destruct (LISEndingAtPrefix_witness l 0 best Hending) as [xs [Hxs Hlen]].
      assert (Hone_le_best : 1 <= best).
      { pose proof (LISEndingAtPrefix_bound l 0 best (0 :: nil)
          Hending (ValidIncreasingSubsequenceEndingAt_single l 0 Hi)).
        rewrite Zlength_cons, Zlength_nil in H. lia. }
      exists xs.
      split.
      + unfold ValidIncreasingSubsequenceEndingAt in Hxs.
        destruct Hxs as [_ [Hvalid _]].
        exact Hvalid.
      + lia.
    - destruct (LISPrefix_witness l i ans Hprefix) as [xs [Hxs Hlen]].
      exists xs.
      split; [| exact Hlen].
      eapply ValidIncreasingSubsequence_monotone_limit with (old := i); eauto; lia.
  }
  destruct Hwitness as [witness [Hwitness_valid Hwitness_len]].
  exists witness.
  split.
  - split; [exact Hwitness_valid |].
    intros ys Hys.
    destruct (ValidIncreasingSubsequence_split_last l i ys Hi Hys) as [Hold | Hend].
    + unfold LISOuterState in Houter.
      destruct Houter as [_ [_ Hcase]].
      destruct Hcase as [[Hi0 Hans1] | [_ Hprefix]].
      * subst i ans.
        pose proof (ValidIncreasingSubsequence_zero_length l ys Hold).
        lia.
      * pose proof (LISPrefix_bound l i ans ys Hprefix Hold).
        lia.
    + pose proof (LISEndingAtPrefix_bound l i best ys Hending Hend).
      lia.
  - exact Hwitness_len.
Qed.

Lemma LISOuterState_snoc_take :
  forall l d i ans best,
    LISOuterState l d i ans ->
    LISInnerBest l d i i best ->
    1 <= best <= i + 1 ->
    ans < best ->
    LISOuterState l (d ++ best :: nil) (i + 1) best.
Proof.
  intros l d i ans best Houter Hinner Hbest_bounds Hans_best.
  pose proof Houter as Houter0.
  pose proof (LISInnerBest_to_LISEndingAtPrefix l d i best Hinner) as Hending.
  unfold LISOuterState in *.
  destruct Houter as [Hdp [Hans_bounds Hcase]].
  unfold LISInnerBest in Hinner.
  destruct Hinner as [Hi [_ [_ _]]].
  split.
  - apply LISDPState_snoc; auto.
  - split.
    + rewrite Z.max_r by lia. lia.
    + right.
      split; [lia |].
      apply LISPrefix_step_take_from_outer with (d := d) (ans := ans); auto.
Qed.

Lemma LISOuterState_snoc_keep :
  forall l d i ans best,
    LISOuterState l d i ans ->
    LISInnerBest l d i i best ->
    1 <= best <= i + 1 ->
    best <= ans ->
    LISOuterState l (d ++ best :: nil) (i + 1) ans.
Proof.
  intros l d i ans best Houter Hinner Hbest_bounds Hbest_ans.
  pose proof Houter as Houter0.
  pose proof (LISInnerBest_to_LISEndingAtPrefix l d i best Hinner) as Hending.
  unfold LISOuterState in *.
  destruct Houter as [Hdp [Hans_bounds Hcase]].
  unfold LISInnerBest in Hinner.
  destruct Hinner as [Hi [_ [_ _]]].
  split.
  - apply LISDPState_snoc; auto.
  - split.
    + rewrite Z.max_r by lia.
      assert (ans <= Z.max 1 i) by lia.
      destruct (Z_lt_ge_dec i 1); lia.
    + right.
      split; [lia |].
      apply LISPrefix_step_keep_from_outer with (d := d) (best := best); auto.
Qed.
