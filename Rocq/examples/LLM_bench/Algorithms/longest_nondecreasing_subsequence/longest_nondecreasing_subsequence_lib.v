Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition NondecreasingValues (l idxs : list Z) : Prop :=
  forall p q,
    0 <= p /\ p < q /\ q < Zlength idxs ->
    Znth (Znth p idxs 0) l 0 <= Znth (Znth q idxs 0) l 0.

Definition ValidNondecreasingSubsequence
    (l : list Z) (limit : Z) (idxs : list Z) : Prop :=
  0 <= limit <= Zlength l /\
  Forall (fun idx => 0 <= idx < limit) idxs /\
  mono_inc idxs /\
  NondecreasingValues l idxs.

Definition LNDSLengthPrefix (l : list Z) (limit ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun idxs => ValidNondecreasingSubsequence l limit idxs)
    (fun idxs => Zlength idxs)
    ans.

Definition LNDSLength (l : list Z) (ans : Z) : Prop :=
  LNDSLengthPrefix l (Zlength l) ans.

Definition LastValueOf (l idxs : list Z) (v : Z) : Prop :=
  0 < Zlength idxs /\
  v = Znth (Znth (Zlength idxs - 1) idxs 0) l 0.

(* Data representation for the initialized prefix of the caller-owned
   workspace.  It deliberately says nothing about LNDS optimality. *)
Definition LNDTailsRepresentation (tails : list Z) (len : Z) : Prop :=
  Zlength tails = len /\
  increasing tails.

(* Every stored tail is realized by a subsequence of the corresponding
   length in the processed input prefix. *)
Definition LNDTailsRealizability
    (l : list Z) (i : Z) (tails : list Z) (len : Z) : Prop :=
  forall k,
    0 <= k < len ->
    exists idxs,
      ValidNondecreasingSubsequence l i idxs /\
      Zlength idxs = k + 1 /\
      LastValueOf l idxs (Znth k tails 0).

(* Optimal output length for the processed prefix. *)
Definition LNDSOptimalLength (l : list Z) (i len : Z) : Prop :=
  LNDSLengthPrefix l i len.

(* Each realized frontier entry is the minimum possible tail among
   subsequences of the same length. *)
Definition LNDTailsMinimality
    (l : list Z) (i : Z) (tails : list Z) (len : Z) : Prop :=
  forall idxs k v,
    ValidNondecreasingSubsequence l i idxs ->
    Zlength idxs = k + 1 ->
    0 <= k < len ->
    LastValueOf l idxs v ->
    Znth k tails 0 <= v.

(* Compatibility predicate used only by the established transition lemmas.
   C annotations use the finer public layers above. *)
Definition LNDTailsState (l : list Z) (i : Z) (tails : list Z) (len : Z) : Prop :=
  0 <= i <= Zlength l /\
  0 <= len <= i /\
  Zlength tails = len /\
  increasing tails /\
  LNDSLengthPrefix l i len /\
  (forall k,
      0 <= k < len ->
      exists idxs,
        ValidNondecreasingSubsequence l i idxs /\
        Zlength idxs = k + 1 /\
        LastValueOf l idxs (Znth k tails 0)) /\
  (forall idxs,
      ValidNondecreasingSubsequence l i idxs ->
      Zlength idxs <= len) /\
  (forall idxs k v,
      ValidNondecreasingSubsequence l i idxs ->
      Zlength idxs = k + 1 ->
      0 <= k < len ->
      LastValueOf l idxs v ->
      Znth k tails 0 <= v).

(* Mathematical partition maintained by upper-bound search.  Bounds and
   array representation remain explicit C safety facts. *)
Definition UpperBoundPartition
    (tails : list Z) (len x left right : Z) : Prop :=
  (forall k, 0 <= k < left -> Znth k tails 0 <= x) /\
  (forall k, right <= k < len -> x < Znth k tails 0).

Definition UpperBoundSearch
    (tails : list Z) (len x left right : Z) : Prop :=
  Zlength tails = len /\
  0 <= left /\ left <= right /\ right <= len /\
  increasing tails /\
  UpperBoundPartition tails len x left right.

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

Lemma NondecreasingValues_snoc :
  forall l xs x,
    NondecreasingValues l xs ->
    Forall (fun idx => Znth idx l 0 <= Znth x l 0) xs ->
    NondecreasingValues l (xs ++ x :: nil).
Proof.
  intros l xs x Hinc Hall.
  unfold NondecreasingValues in *.
  intros p q [Hp [Hpq Hq]].
  rewrite Zlength_app_cons in Hq.
  assert (q < Zlength xs \/ q = Zlength xs) as [Hq_old | Hq_last] by lia.
  - rewrite !znth_app_singleton_old_Z by lia.
    apply Hinc. lia.
  - subst q.
    rewrite znth_app_singleton_last_Z with (i := Zlength xs) by reflexivity.
    rewrite znth_app_singleton_old_Z by lia.
    apply (Forall_Znth Z (fun idx => Znth idx l 0 <= Znth x l 0) xs 0 p Hall).
    lia.
Qed.

Lemma NondecreasingValues_snoc_inv :
  forall l xs x,
    NondecreasingValues l (xs ++ x :: nil) ->
    NondecreasingValues l xs.
Proof.
  intros l xs x Hinc.
  unfold NondecreasingValues in *.
  intros p q Hp.
  specialize (Hinc p q ltac:(rewrite Zlength_app_cons; lia)).
  rewrite !znth_app_singleton_old_Z in Hinc by lia.
  exact Hinc.
Qed.

Lemma NondecreasingValues_snoc_last :
  forall l xs x,
    NondecreasingValues l (xs ++ x :: nil) ->
    Forall (fun idx => Znth idx l 0 <= Znth x l 0) xs.
Proof.
  intros l xs x Hinc.
  apply (Forall_Znth_intro Z (fun idx => Znth idx l 0 <= Znth x l 0) xs 0).
  intros p Hp.
  pose proof (Hinc p (Zlength xs)) as Hle.
  rewrite znth_app_singleton_old_Z in Hle by lia.
  rewrite znth_app_singleton_last_Z with (i := Zlength xs) in Hle by reflexivity.
  apply Hle.
  rewrite Zlength_app_cons.
  lia.
Qed.

Lemma NondecreasingZList_snoc :
  forall xs x,
    increasing xs ->
    Forall (fun v => v <= x) xs ->
    increasing (xs ++ x :: nil).
Proof.
  intros xs x Hnd Hall.
  apply (proj2 (increasing_app xs (x :: nil))).
  split; [exact Hnd |].
  split.
  - simpl; auto.
  - intros a b Ha Hb.
    destruct Hb as [Hb | Hb]; [subst b | contradiction].
    rewrite Forall_forall in Hall.
    apply Hall; exact Ha.
Qed.

Lemma LastValueOf_snoc :
  forall l xs x,
    LastValueOf l (xs ++ x :: nil) (Znth x l 0).
Proof.
  intros l xs x.
  unfold LastValueOf.
  split.
  - rewrite Zlength_app_cons.
    pose proof (Zlength_nonneg xs). lia.
  - rewrite Zlength_app_cons.
    replace (Zlength xs + 1 - 1) with (Zlength xs) by lia.
    rewrite znth_app_singleton_last_Z with (i := Zlength xs) by reflexivity.
    reflexivity.
Qed.

Lemma LastValueOf_snoc_eq :
  forall l xs x v,
    LastValueOf l (xs ++ x :: nil) v ->
    v = Znth x l 0.
Proof.
  intros l xs x v Hlast.
  unfold LastValueOf in Hlast.
  destruct Hlast as [_ Hlast].
  rewrite Zlength_app_cons in Hlast.
  replace (Zlength xs + 1 - 1) with (Zlength xs) in Hlast by lia.
  rewrite znth_app_singleton_last_Z with (i := Zlength xs) in Hlast by reflexivity.
  exact Hlast.
Qed.

Lemma ValidNondecreasingSubsequence_empty :
  forall l,
    ValidNondecreasingSubsequence l 0 nil.
Proof.
  intros l.
  unfold ValidNondecreasingSubsequence.
  pose proof (Zlength_nonneg l).
  split; [lia |].
  split; [constructor |].
  split.
  - apply mono_inc_nil.
  - unfold NondecreasingValues.
    intros p q [Hp [Hpq Hq]].
    rewrite Zlength_nil in Hq. lia.
Qed.

Lemma ValidNondecreasingSubsequence_limit0_length :
  forall l idxs,
    ValidNondecreasingSubsequence l 0 idxs ->
    Zlength idxs <= 0.
Proof.
  intros l idxs Hvalid.
  unfold ValidNondecreasingSubsequence in Hvalid.
  destruct Hvalid as [_ [Hall _]].
  destruct idxs as [| a idxs].
  - rewrite Zlength_nil. lia.
  - inversion Hall; subst.
    simpl in H1. lia.
Qed.

Lemma LNDSLengthPrefix_empty :
  forall l,
    LNDSLengthPrefix l 0 0.
Proof.
  intros l.
  unfold LNDSLengthPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  exists (@nil Z).
  split.
  - split.
    + apply ValidNondecreasingSubsequence_empty.
    + intros idxs Hvalid.
      pose proof (ValidNondecreasingSubsequence_limit0_length l idxs Hvalid).
      rewrite Zlength_nil. lia.
  - rewrite Zlength_nil. reflexivity.
Qed.

Lemma LNDTailsState_empty :
  forall l,
    LNDTailsState l 0 nil 0.
Proof.
  intros l.
  unfold LNDTailsState.
  pose proof (Zlength_nonneg l).
  split; [lia |].
  split; [lia |].
  split.
  - rewrite Zlength_nil. reflexivity.
  - split.
    + simpl; auto.
    + split.
      * apply LNDSLengthPrefix_empty.
      * split.
        -- intros k Hk. lia.
        -- split.
           ++ intros idxs Hvalid.
              pose proof (ValidNondecreasingSubsequence_limit0_length l idxs Hvalid).
              exact H0.
           ++ intros idxs k v _ _ Hk _. lia.
Qed.

Lemma UpperBoundSearch_full :
  forall tails len x,
    Zlength tails = len ->
    increasing tails ->
    0 <= len ->
    UpperBoundSearch tails len x 0 len.
Proof.
  intros tails len x Hlen Hnd Hnonneg.
  unfold UpperBoundSearch, UpperBoundPartition.
  repeat split; auto; try lia.
Qed.

Lemma UpperBoundSearch_left_preserve :
  forall tails len x left right mid,
    UpperBoundSearch tails len x left right ->
    Znth mid tails 0 > x ->
    left <= mid ->
    mid < right ->
    UpperBoundSearch tails len x left mid.
Proof.
  intros tails len x left right mid Hsearch Hmid Hleft Hright.
  unfold UpperBoundSearch, UpperBoundPartition in *.
  destruct Hsearch as
    [Hlen [Hleft0 [Hleftright [Hrightlen [Hnd [Hlow Hhigh]]]]]].
  repeat split; auto; try lia.
  intros k Hk.
  destruct (Z.eq_dec k mid) as [Heq | Hneq].
  - subst k. apply Z.gt_lt in Hmid. exact Hmid.
  - assert (mid < k \/ right <= k) as [Hmk | Hrk] by lia.
    + pose proof (proj2 (mono_nondec_iff_increasing tails) Hnd) as Hmono.
      pose proof (Hmono mid k ltac:(lia) ltac:(lia) ltac:(lia)).
      apply Z.gt_lt in Hmid. lia.
    + apply Hhigh. lia.
Qed.

Lemma UpperBoundSearch_right_preserve :
  forall tails len x left right mid,
    UpperBoundSearch tails len x left right ->
    Znth mid tails 0 <= x ->
    left <= mid ->
    mid < right ->
    UpperBoundSearch tails len x (mid + 1) right.
Proof.
  intros tails len x left right mid Hsearch Hmid Hleft Hright.
  unfold UpperBoundSearch, UpperBoundPartition in *.
  destruct Hsearch as
    [Hlen [Hleft0 [Hleftright [Hrightlen [Hnd [Hlow Hhigh]]]]]].
  repeat split; auto; try lia.
  intros k Hk.
  destruct (Z_lt_ge_dec k left) as [Hkl | Hkl].
  - apply Hlow. lia.
  - assert (k = mid \/ k < mid) as [Heq | Hkm] by lia.
    + subst k. exact Hmid.
    + pose proof (proj2 (mono_nondec_iff_increasing tails) Hnd) as Hmono.
      pose proof (Hmono k mid ltac:(lia) ltac:(lia) ltac:(lia)).
      lia.
Qed.

Lemma replace_Znth_sublist :
  forall (A : Type) (d x : A) (xs : list A) n,
    0 <= n < Zlength xs ->
    replace_Znth n x xs =
      sublist 0 n xs ++ x :: sublist (n + 1) (Zlength xs) xs.
Proof.
  intros A d x xs n Hn.
  apply (proj2 (list_eq_ext _ _ d)).
  split.
  - rewrite Zlength_replace_Znth.
    rewrite Zlength_app, Zlength_cons.
    rewrite Zlength_sublist0 by lia.
    rewrite Zlength_sublist by lia.
    lia.
  - intros i Hi.
    rewrite Zlength_replace_Znth in Hi.
    destruct (Z_lt_ge_dec i n) as [Hin | Hin].
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite app_Znth1 by (rewrite Zlength_sublist0 by lia; lia).
      rewrite Znth_sublist0 by lia. reflexivity.
    + destruct (Z.eq_dec i n) as [Heq | Hneq].
      * subst i.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite app_Znth2 by (rewrite Zlength_sublist0 by lia; lia).
        rewrite Zlength_sublist0 by lia.
        replace (n - n) with 0 by lia.
        rewrite Znth0_cons. reflexivity.
      * assert (n < i) by lia.
	      rewrite Znth_replace_Znth_Diff by lia.
        rewrite app_Znth2 by (rewrite Zlength_sublist0 by lia; lia).
        rewrite Zlength_sublist0 by lia.
        rewrite Znth_cons by lia.
        replace (i - n - 1) with (i - (n + 1)) by lia.
        rewrite Znth_sublist by lia.
        replace (i - (n + 1) + (n + 1)) with i by lia.
        reflexivity.
Qed.

Lemma LNDSLengthPrefix_bound :
  forall l limit ans idxs,
    LNDSLengthPrefix l limit ans ->
    ValidNondecreasingSubsequence l limit idxs ->
    Zlength idxs <= ans.
Proof.
  intros l limit ans idxs Hlen Hvalid.
  unfold LNDSLengthPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hlen.
  destruct Hlen as [best [[_ Hmax] Hbest_len]].
  specialize (Hmax idxs Hvalid).
  lia.
Qed.

Lemma LNDSLengthPrefix_witness :
  forall l limit ans,
    LNDSLengthPrefix l limit ans ->
    exists idxs,
      ValidNondecreasingSubsequence l limit idxs /\
      Zlength idxs = ans.
Proof.
  intros l limit ans Hlen.
  unfold LNDSLengthPrefix, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in Hlen.
  destruct Hlen as [idxs [[Hvalid _] Hidxs_len]].
  exists idxs. auto.
Qed.

Lemma ValidNondecreasingSubsequence_monotone_limit :
  forall l old new idxs,
    old <= new ->
    new <= Zlength l ->
    ValidNondecreasingSubsequence l old idxs ->
    ValidNondecreasingSubsequence l new idxs.
Proof.
  intros l old new idxs Hold_new Hnew Hvalid.
  unfold ValidNondecreasingSubsequence in *.
  destruct Hvalid as [Hold [Hall [Hidx Hvals]]].
  repeat split; try lia; auto.
  eapply Forall_impl with (P := fun idx => 0 <= idx < old); [| exact Hall].
  intros a Ha. lia.
Qed.

Lemma ValidNondecreasingSubsequence_prefix_same_limit :
  forall l limit xs x,
    ValidNondecreasingSubsequence l limit (xs ++ x :: nil) ->
    ValidNondecreasingSubsequence l limit xs.
Proof.
  intros l limit xs x Hvalid.
	  unfold ValidNondecreasingSubsequence in *.
	  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
	  destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < limit) xs x Hall) as [Hallxs _].
	  repeat split.
	  - lia.
	  - lia.
	  - exact Hallxs.
	  - apply StrictlyIncreasingZList_snoc_inv with (x := x); auto.
	  - apply NondecreasingValues_snoc_inv with (x := x); auto.
Qed.

Lemma ValidNondecreasingSubsequence_tighten_to_last :
  forall l limit xs x,
    ValidNondecreasingSubsequence l limit (xs ++ x :: nil) ->
    ValidNondecreasingSubsequence l (x + 1) (xs ++ x :: nil).
Proof.
  intros l limit xs x Hvalid.
  unfold ValidNondecreasingSubsequence in *.
  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
  destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < limit) xs x Hall)
    as [Hallxs Hx].
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

Lemma ValidNondecreasingSubsequence_prefix_before_last :
  forall l limit xs x,
    ValidNondecreasingSubsequence l limit (xs ++ x :: nil) ->
    ValidNondecreasingSubsequence l x xs.
Proof.
  intros l limit xs x Hvalid.
  pose proof Hvalid as Hprefix.
	  apply ValidNondecreasingSubsequence_prefix_same_limit in Hprefix.
	  unfold ValidNondecreasingSubsequence in *.
	  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
	  destruct Hprefix as [_ [Hallxs [Hidx_prefix Hvals_prefix]]].
	  destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < limit) xs x Hall)
	    as [_ Hx].
	  pose proof (StrictlyIncreasingZList_snoc_last xs x Hidx) as Hall_lt.
	  repeat split.
	  - lia.
	  - lia.
	  - apply Forall_Znth_intro with (dflt := 0).
	    intros p Hp.
	    pose proof (Forall_Znth Z (fun idx => idx < x) xs 0 p Hall_lt Hp) as Hlt.
	    pose proof (Forall_Znth Z (fun idx => 0 <= idx < limit) xs 0 p Hallxs Hp)
	      as Hbounds.
	    destruct Hbounds as [Hnonneg _].
	    exact (conj Hnonneg Hlt).
	  - exact Hidx_prefix.
	  - exact Hvals_prefix.
Qed.

Lemma ValidNondecreasingSubsequence_values_le_last :
  forall l limit idxs v,
    ValidNondecreasingSubsequence l limit idxs ->
    LastValueOf l idxs v ->
    Forall (fun idx => Znth idx l 0 <= v) idxs.
Proof.
  intros l limit idxs v Hvalid Hlast.
  unfold ValidNondecreasingSubsequence in Hvalid.
  destruct Hvalid as [_ [_ [_ Hvals]]].
  unfold LastValueOf in Hlast.
  destruct Hlast as [Hpos Hv].
  apply Forall_Znth_intro with (dflt := 0).
  intros p Hp.
  assert (p < Zlength idxs - 1 \/ p = Zlength idxs - 1) as [Hp_last | Hp_last]
    by lia.
  - unfold NondecreasingValues in Hvals.
    pose proof (Hvals p (Zlength idxs - 1) ltac:(lia)).
    rewrite Hv. exact H.
  - subst p. rewrite Hv. lia.
Qed.

Lemma ValidNondecreasingSubsequence_snoc_at :
  forall l i idxs,
    0 <= i < Zlength l ->
    ValidNondecreasingSubsequence l i idxs ->
    Forall (fun idx => Znth idx l 0 <= Znth i l 0) idxs ->
    ValidNondecreasingSubsequence l (i + 1) (idxs ++ i :: nil).
Proof.
  intros l i idxs Hi Hvalid Hall_values.
  unfold ValidNondecreasingSubsequence in *.
  destruct Hvalid as [Hlim [Hall [Hidx Hvals]]].
  repeat split; try lia.
  - apply Forall_snoc.
    + eapply Forall_impl with (P := fun idx => 0 <= idx < i); [| exact Hall].
      intros a Ha. lia.
    + lia.
  - apply StrictlyIncreasingZList_snoc; auto.
    eapply Forall_impl with (P := fun idx => 0 <= idx < i); [| exact Hall].
    intros a Ha. lia.
  - apply NondecreasingValues_snoc; auto.
Qed.

Lemma ValidNondecreasingSubsequence_single :
  forall l i,
    0 <= i < Zlength l ->
    ValidNondecreasingSubsequence l (i + 1) (i :: nil).
Proof.
  intros l i Hi.
  unfold ValidNondecreasingSubsequence.
  repeat split; try lia.
  - constructor; [lia | constructor].
  - apply mono_inc_single.
  - unfold NondecreasingValues.
    intros p q [Hp [Hpq Hq]].
    rewrite Zlength_cons, Zlength_nil in Hq. lia.
Qed.

Lemma ValidNondecreasingSubsequence_split_last :
  forall l i idxs,
    0 <= i < Zlength l ->
    ValidNondecreasingSubsequence l (i + 1) idxs ->
    ValidNondecreasingSubsequence l i idxs \/
    exists prefix,
      idxs = prefix ++ i :: nil /\
      ValidNondecreasingSubsequence l i prefix /\
      Zlength idxs = Zlength prefix + 1 /\
      Forall (fun idx => Znth idx l 0 <= Znth i l 0) prefix.
Proof.
  intros l i idxs Hi Hvalid.
  destruct idxs as [| first rest].
  - left.
    unfold ValidNondecreasingSubsequence.
    repeat split; try lia.
    + constructor.
    + apply mono_inc_nil.
    + unfold NondecreasingValues.
      intros p q Hp. rewrite Zlength_nil in Hp. lia.
  - assert (Hnonempty : first :: rest <> nil) by discriminate.
    destruct (exists_last Hnonempty) as [prefix [last Hidxs]].
    rewrite Hidxs in Hvalid.
    pose proof Hvalid as Hvalid_unfold.
    unfold ValidNondecreasingSubsequence in Hvalid_unfold.
    destruct Hvalid_unfold as [Hlim [Hall [Hidx Hvals]]].
    destruct (Forall_snoc_inv Z (fun idx => 0 <= idx < i + 1) prefix last Hall)
      as [Hall_prefix Hlast_bound].
    destruct (Z_lt_ge_dec last i) as [Hlast_lt | Hlast_ge].
    + left.
      rewrite Hidxs.
      eapply ValidNondecreasingSubsequence_monotone_limit
        with (old := last + 1).
      * lia.
      * lia.
      * eapply ValidNondecreasingSubsequence_tighten_to_last
          with (limit := i + 1).
        exact Hvalid.
    + assert (Hlast_i : last = i) by lia.
	      subst last.
	      right.
	      exists prefix.
	      split; [exact Hidxs |].
	      split.
	      * apply ValidNondecreasingSubsequence_prefix_before_last
	          with (limit := i + 1).
	        exact Hvalid.
	      * split.
	        -- rewrite Hidxs. rewrite Zlength_app_cons. lia.
	        -- apply NondecreasingValues_snoc_last.
	           exact Hvals.
Qed.

Lemma NondecreasingZList_replace_upper_bound :
  forall tails len x left,
    Zlength tails = len ->
    increasing tails ->
    0 <= left < len ->
    (forall k, 0 <= k < left -> Znth k tails 0 <= x) ->
    (forall k, left <= k < len -> x < Znth k tails 0) ->
    increasing (replace_Znth left x tails).
Proof.
  intros tails len x left Hlen Hnd Hleft Hlow Hhigh.
  apply (proj1 (mono_nondec_iff_increasing _)).
  pose proof (proj2 (mono_nondec_iff_increasing tails) Hnd) as Hmono.
  unfold mono_nondec in *.
  intros p q Hp Hpq Hq.
  rewrite Zlength_replace_Znth in Hq.
  destruct (Z.eq_dec p q) as [-> | Hpq_neq].
  - lia.
  - assert (Hpq_lt : p < q) by lia.
    destruct (Z.eq_dec p left) as [Hp_left | Hp_left];
    destruct (Z.eq_dec q left) as [Hq_left | Hq_left].
    + lia.
    + subst p.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Z.lt_le_incl. apply Hhigh. lia.
    + subst q.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Same by lia.
      apply Hlow. lia.
    + rewrite !Znth_replace_Znth_Diff by lia.
      apply Hmono; lia.
Qed.

Lemma LNDTailsState_extend_at :
  forall l i tails len x k,
    0 <= i < Zlength l ->
    x = Znth i l 0 ->
    LNDTailsState l i tails len ->
    UpperBoundSearch tails len x k k ->
    0 <= k <= len ->
    exists idxs,
      ValidNondecreasingSubsequence l (i + 1) idxs /\
      Zlength idxs = k + 1 /\
      LastValueOf l idxs x.
Proof.
  intros l i tails len x k Hi Hx Hstate Hsearch Hk.
	  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
	  - subst k.
	    exists (i :: nil).
	    split.
	    + apply ValidNondecreasingSubsequence_single. exact Hi.
	    + split.
	      * rewrite Zlength_cons, Zlength_nil. lia.
	      * unfold LastValueOf.
	        split.
	        -- rewrite Zlength_cons, Zlength_nil. lia.
	        -- rewrite Zlength_cons, Zlength_nil.
	           replace (1 - 1) with 0 by lia.
	           rewrite Znth0_cons. exact Hx.
  - unfold LNDTailsState in Hstate.
    destruct Hstate as
      [_ [_ [_ [_ [_ [Hwitness _]]]]]].
    unfold UpperBoundSearch, UpperBoundPartition in Hsearch.
    destruct Hsearch as [_ [_ [_ [_ [_ [Hlow _]]]]]].
    destruct (Hwitness (k - 1) ltac:(lia)) as
      [idxs [Hvalid [Hidxs_len Hlast]]].
    assert (Hlast_le : Znth (k - 1) tails 0 <= x).
    { apply Hlow. lia. }
    pose proof (ValidNondecreasingSubsequence_values_le_last
      l i idxs (Znth (k - 1) tails 0) Hvalid Hlast) as Hall_tail.
    assert (Hall_x : Forall (fun idx => Znth idx l 0 <= Znth i l 0) idxs).
    {
      rewrite <- Hx.
      eapply Forall_impl with
        (P := fun idx => Znth idx l 0 <= Znth (k - 1) tails 0);
        [| exact Hall_tail].
      intros a Ha. lia.
	    }
	    exists (idxs ++ i :: nil).
	    split.
	    + apply ValidNondecreasingSubsequence_snoc_at; auto.
	    + split.
	      * rewrite Zlength_app_cons. lia.
	      * rewrite Hx. apply LastValueOf_snoc.
Qed.

Lemma LNDTailsState_append :
  forall l i tails len x,
    0 <= i < Zlength l ->
    x = Znth i l 0 ->
    LNDTailsState l i tails len ->
    UpperBoundSearch tails len x len len ->
    LNDTailsState l (i + 1) (tails ++ x :: nil) (len + 1).
Proof.
  intros l i tails len x Hi Hx Hstate Hsearch.
  pose proof Hstate as Hstate0.
  pose proof Hsearch as Hsearch0.
  unfold LNDTailsState in Hstate.
  destruct Hstate as
    [Hi_old [Hlen_i [Htails_len [Hnd [Hbest [Hwitness [Hbound Hmin]]]]]]].
  unfold UpperBoundSearch, UpperBoundPartition in Hsearch.
  destruct Hsearch as
    [Hsearch_len [Hleft0 [_ [Hrightlen [Hnd_search [Hlow _]]]]]].
  unfold LNDTailsState.
  split; [lia |].
  split; [lia |].
  split.
  - rewrite Zlength_app_cons. lia.
  - split.
    + apply NondecreasingZList_snoc; auto.
      apply Forall_Znth_intro with (dflt := 0).
      intros k Hk. apply Hlow. lia.
    + split.
      * destruct (LNDTailsState_extend_at l i tails len x len Hi Hx Hstate0 Hsearch0)
          as [best_idxs [Hbest_valid [Hbest_len _]]]; [lia |].
        unfold LNDSLengthPrefix, MaxMin.max_value_of_subset,
          MaxMin.max_object_of_subset.
        exists best_idxs.
        split.
        -- split; [exact Hbest_valid |].
           intros idxs Hvalid.
           destruct (ValidNondecreasingSubsequence_split_last l i idxs Hi Hvalid)
             as [Hold | [prefix [Hidxs_eq [Hprefix_valid [Hidxs_len _]]]]].
           ++ pose proof (Hbound idxs Hold). lia.
           ++ pose proof (Hbound prefix Hprefix_valid). lia.
        -- exact Hbest_len.
      * split.
        -- intros k Hk.
           destruct (Z_lt_ge_dec k len) as [Hk_old | Hk_last].
           ++ destruct (Hwitness k ltac:(lia)) as
                [idxs [Hvalid [Hidxs_len Hlast]]].
              exists idxs.
              split.
              ** eapply ValidNondecreasingSubsequence_monotone_limit
                   with (old := i); eauto; lia.
              ** split; [exact Hidxs_len |].
                 rewrite znth_app_singleton_old_Z by lia.
                 exact Hlast.
           ++ assert (Hk_eq : k = len) by lia.
              subst k.
              destruct (LNDTailsState_extend_at l i tails len x len Hi Hx Hstate0 Hsearch0)
                as [idxs [Hvalid [Hidxs_len Hlast]]]; [lia |].
              exists idxs.
              split; [exact Hvalid |].
              split; [exact Hidxs_len |].
              rewrite znth_app_singleton_last_Z with (i := len) by lia.
              exact Hlast.
        -- split.
           ++ intros idxs Hvalid.
              destruct (ValidNondecreasingSubsequence_split_last l i idxs Hi Hvalid)
                as [Hold | [prefix [Hidxs_eq [Hprefix_valid [Hidxs_len _]]]]].
              ** pose proof (Hbound idxs Hold). lia.
              ** pose proof (Hbound prefix Hprefix_valid). lia.
           ++ intros idxs k v Hvalid Hidxs_len Hk Hlast.
              destruct (ValidNondecreasingSubsequence_split_last l i idxs Hi Hvalid)
                as [Hold | [prefix [Hidxs_eq [Hprefix_valid [Hidxs_len_split _]]]]].
              ** assert (k < len) by (pose proof (Hbound idxs Hold); lia).
                 rewrite znth_app_singleton_old_Z by lia.
                 eapply Hmin; eauto; lia.
              ** subst idxs.
                 pose proof (LastValueOf_snoc_eq l prefix i v Hlast) as Hv.
	                 destruct (Z_lt_ge_dec k len) as [Hk_old | Hk_last].
	                 --- rewrite znth_app_singleton_old_Z by lia.
	                     eapply Z.le_trans; [apply Hlow; lia | lia].
	                 --- assert (Hk_eq : k = len) by lia.
	                     subst k.
	                     rewrite znth_app_singleton_last_Z with (i := len) by lia.
	                     lia.
Qed.

Lemma LNDTailsState_replace :
  forall l i tails len x left,
    0 <= i < Zlength l ->
    x = Znth i l 0 ->
    0 <= left < len ->
    LNDTailsState l i tails len ->
    UpperBoundSearch tails len x left left ->
    LNDTailsState l (i + 1) (replace_Znth left x tails) len.
Proof.
  intros l i tails len x left Hi Hx Hleft Hstate Hsearch.
  pose proof Hstate as Hstate0.
  pose proof Hsearch as Hsearch0.
  unfold LNDTailsState in Hstate.
  destruct Hstate as
    [Hi_old [Hlen_i [Htails_len [Hnd [Hbest [Hwitness [Hbound Hmin]]]]]]].
  unfold UpperBoundSearch, UpperBoundPartition in Hsearch.
  destruct Hsearch as
    [Hsearch_len [Hleft0 [_ [Hrightlen [Hnd_search [Hlow Hhigh]]]]]].
  assert (Hnew_bound :
    forall idxs,
      ValidNondecreasingSubsequence l (i + 1) idxs ->
      Zlength idxs <= len).
  {
    intros idxs Hvalid.
    destruct (ValidNondecreasingSubsequence_split_last l i idxs Hi Hvalid)
      as [Hold | [prefix [Hidxs_eq [Hprefix_valid [Hidxs_len Hprefix_values]]]]].
    - pose proof (Hbound idxs Hold). lia.
    - assert (Hprefix_lt : Zlength prefix < len).
      {
        pose proof (Hbound prefix Hprefix_valid) as Hprefix_le.
        destruct (Z_lt_ge_dec (Zlength prefix) len) as [Hlt | Hge]; [exact Hlt |].
        assert (Hprefix_len : Zlength prefix = len) by lia.
        assert (Hlen_pos : 0 < len) by lia.
        set (vprefix := Znth (Znth (Zlength prefix - 1) prefix 0) l 0).
        assert (Hlast_prefix : LastValueOf l prefix vprefix).
        { unfold LastValueOf, vprefix. split; [lia | reflexivity]. }
        pose proof (Hmin prefix (len - 1) vprefix Hprefix_valid
          ltac:(lia) ltac:(lia) Hlast_prefix) as Htail_le.
	        pose proof (Forall_Znth Z
	          (fun idx => Znth idx l 0 <= Znth i l 0)
	          prefix 0 (Zlength prefix - 1) Hprefix_values ltac:(lia)) as Hprefix_val_le.
	        fold vprefix in Hprefix_val_le.
        pose proof (Hhigh (len - 1) ltac:(lia)) as Hx_lt_tail.
        rewrite <- Hx in Hprefix_val_le.
        lia.
      }
      lia.
  }
  unfold LNDTailsState.
  split; [lia |].
  split; [lia |].
  split.
  - rewrite Zlength_replace_Znth. lia.
  - split.
    + apply NondecreasingZList_replace_upper_bound with (len := len); auto.
    + split.
      * destruct (LNDSLengthPrefix_witness l i len Hbest)
          as [best_idxs [Hbest_valid Hbest_len]].
        unfold LNDSLengthPrefix, MaxMin.max_value_of_subset,
          MaxMin.max_object_of_subset.
        exists best_idxs.
        split.
        -- split.
           ++ eapply ValidNondecreasingSubsequence_monotone_limit
                with (old := i); eauto; lia.
	           ++ intros idxs Hvalid. rewrite Hbest_len. apply Hnew_bound; exact Hvalid.
        -- exact Hbest_len.
      * split.
        -- intros k Hk.
           destruct (Z_lt_ge_dec k left) as [Hk_left | Hk_ge_left].
           ++ destruct (Hwitness k ltac:(lia)) as
                [idxs [Hvalid [Hidxs_len Hlast]]].
              exists idxs.
              split.
              ** eapply ValidNondecreasingSubsequence_monotone_limit
                   with (old := i); eauto; lia.
              ** split; [exact Hidxs_len |].
                 rewrite Znth_replace_Znth_Diff by lia.
                 exact Hlast.
           ++ destruct (Z.eq_dec k left) as [Hk_eq | Hk_neq].
              ** subst k.
                 destruct (LNDTailsState_extend_at l i tails len x left Hi Hx Hstate0 Hsearch0)
                   as [idxs [Hvalid [Hidxs_len Hlast]]]; [lia |].
                 exists idxs.
                 split; [exact Hvalid |].
                 split; [exact Hidxs_len |].
                 rewrite Znth_replace_Znth_Same by lia.
                 exact Hlast.
              ** destruct (Hwitness k ltac:(lia)) as
                   [idxs [Hvalid [Hidxs_len Hlast]]].
                 exists idxs.
                 split.
                 --- eapply ValidNondecreasingSubsequence_monotone_limit
                       with (old := i); eauto; lia.
                 --- split; [exact Hidxs_len |].
                     rewrite Znth_replace_Znth_Diff by lia.
                     exact Hlast.
        -- split.
           ++ intros idxs Hvalid. apply Hnew_bound; exact Hvalid.
           ++ intros idxs k v Hvalid Hidxs_len Hk Hlast.
              destruct (ValidNondecreasingSubsequence_split_last l i idxs Hi Hvalid)
                as [Hold | [prefix [Hidxs_eq [Hprefix_valid [Hidxs_len_split Hprefix_values]]]]].
              ** destruct (Z_lt_ge_dec k left) as [Hk_left | Hk_ge_left].
                 --- rewrite Znth_replace_Znth_Diff by lia.
                     eapply Hmin; eauto; lia.
	                 --- destruct (Z.eq_dec k left) as [Hk_eq | Hk_neq].
	                     ---- subst k.
	                       rewrite Znth_replace_Znth_Same by lia.
	                       pose proof (Hmin idxs left v Hold Hidxs_len ltac:(lia) Hlast)
	                         as Htail_le_v.
	                       pose proof (Hhigh left ltac:(lia)) as Hx_lt_tail.
	                       lia.
	                     ---- rewrite Znth_replace_Znth_Diff by lia.
	                       eapply Hmin; eauto; lia.
              ** subst idxs.
                 pose proof (LastValueOf_snoc_eq l prefix i v Hlast) as Hv.
                 assert (Hprefix_len : Zlength prefix = k) by
                   (rewrite Zlength_app_cons in Hidxs_len; lia).
	                 destruct (Z_lt_ge_dec k left) as [Hk_left | Hk_ge_left].
	                 --- rewrite Znth_replace_Znth_Diff by lia.
	                     eapply Z.le_trans; [apply Hlow; lia | lia].
		                 --- destruct (Z.eq_dec k left) as [Hk_eq | Hk_neq].
		                     ---- subst k.
		                       rewrite Hk_eq.
		                       rewrite Znth_replace_Znth_Same by lia.
		                       lia.
	                     ---- exfalso.
                       assert (Hk_gt_left : left < k) by lia.
                       assert (Hk_pos : 0 < k) by lia.
                       set (vprefix := Znth (Znth (Zlength prefix - 1) prefix 0) l 0).
                       assert (Hlast_prefix : LastValueOf l prefix vprefix).
                       { unfold LastValueOf, vprefix. split; [lia | reflexivity]. }
	                       pose proof (Hmin prefix (k - 1) vprefix Hprefix_valid
	                         ltac:(lia) ltac:(lia) Hlast_prefix) as Htail_le.
	                       pose proof (Forall_Znth Z
	                         (fun idx => Znth idx l 0 <= Znth i l 0)
	                         prefix 0 (Zlength prefix - 1) Hprefix_values ltac:(lia))
	                         as Hprefix_val_le.
	                       fold vprefix in Hprefix_val_le.
                       pose proof (Hhigh (k - 1) ltac:(lia)) as Hx_lt_tail.
	                       rewrite <- Hx in Hprefix_val_le.
	                       lia.
Qed.

Lemma sublist_update_append_prefix :
  forall (tails_old : list Z) (numsSize len x : Z),
    Zlength tails_old = numsSize ->
    0 <= len < numsSize ->
    sublist 0 (len + 1)
      (sublist 0 len tails_old ++ x :: sublist (len + 1) numsSize tails_old) =
    sublist 0 len tails_old ++ x :: nil.
Proof.
  intros tails_old numsSize len x Hlen Hbounds.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Zlength_sublist by
      (rewrite Zlength_app, Zlength_sublist0, Zlength_cons,
         Zlength_sublist by lia; lia).
    rewrite Zlength_app, Zlength_sublist0, Zlength_cons, Zlength_nil by lia.
    lia.
  - intros i Hi.
    rewrite Zlength_sublist in Hi by
      (rewrite Zlength_app, Zlength_sublist0, Zlength_cons,
         Zlength_sublist by lia; lia).
    rewrite Znth_sublist0 by lia.
    destruct (Z_lt_ge_dec i len) as [Hi_len | Hi_len].
    + rewrite app_Znth1 by (rewrite Zlength_sublist0 by lia; lia).
      rewrite app_Znth1 by (rewrite Zlength_sublist0 by lia; lia).
      rewrite !Znth_sublist0 by lia.
      reflexivity.
    + assert (Hi_eq : i = len) by lia.
      subst i.
      rewrite app_Znth2 by (rewrite Zlength_sublist0 by lia; lia).
      rewrite app_Znth2 by (rewrite Zlength_sublist0 by lia; lia).
      rewrite Zlength_sublist0 by lia.
      replace (len - len) with 0 by lia.
      rewrite !Znth0_cons.
      reflexivity.
Qed.

Lemma sublist_update_replace_prefix :
  forall (tails_old : list Z) (numsSize len left x : Z),
    Zlength tails_old = numsSize ->
    0 <= left < len ->
    len <= numsSize ->
    sublist 0 len
      (sublist 0 left tails_old ++ x :: sublist (left + 1) numsSize tails_old) =
    replace_Znth left x (sublist 0 len tails_old).
Proof.
  intros tails_old numsSize len left x Hlen Hleft Hlen_bound.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Zlength_sublist by
      (rewrite Zlength_app, Zlength_sublist0, Zlength_cons,
         Zlength_sublist by lia; lia).
    rewrite Zlength_replace_Znth, Zlength_sublist0 by lia.
    lia.
  - intros i Hi.
    rewrite Zlength_sublist in Hi by
      (rewrite Zlength_app, Zlength_sublist0, Zlength_cons,
         Zlength_sublist by lia; lia).
    rewrite Znth_sublist0 by lia.
    destruct (Z_lt_ge_dec i left) as [Hi_left | Hi_left].
	    + rewrite app_Znth1 by (rewrite Zlength_sublist0 by lia; lia).
	      rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_sublist0 by lia; lia).
      rewrite !Znth_sublist0 by lia.
      reflexivity.
    + destruct (Z.eq_dec i left) as [Hi_eq | Hi_eq].
      * subst i.
        rewrite app_Znth2 by (rewrite Zlength_sublist0 by lia; lia).
        rewrite Zlength_sublist0 by lia.
        replace (left - left) with 0 by lia.
        rewrite Znth0_cons.
	        rewrite Znth_replace_Znth_Same by (try rewrite Zlength_sublist0 by lia; lia).
        reflexivity.
      * assert (left < i) by lia.
        rewrite app_Znth2 by (rewrite Zlength_sublist0 by lia; lia).
        rewrite Zlength_sublist0 by lia.
        rewrite Znth_cons by lia.
        replace (i - left - 1) with (i - (left + 1)) by lia.
        rewrite Znth_sublist by lia.
        replace (i - (left + 1) + (left + 1)) with i by lia.
	        rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_sublist0 by lia; lia).
        rewrite Znth_sublist0 by lia.
        reflexivity.
Qed.

Lemma LNDTailsState_of_public__lnds_state_transitions :
  forall l i tails len,
    0 <= i <= Zlength l ->
    0 <= len <= i ->
    LNDTailsRepresentation tails len ->
    LNDTailsRealizability l i tails len ->
    LNDSOptimalLength l i len ->
    LNDTailsMinimality l i tails len ->
    LNDTailsState l i tails len.
Proof.
  intros l i tails len Hi Hlen Hrep Hreal Hopt Hmin.
  destruct Hrep as [Htails Hinc].
  unfold LNDTailsState.
  split; [exact Hi |].
  split; [exact Hlen |].
  split; [exact Htails |].
  split; [exact Hinc |].
  split; [exact Hopt |].
  split; [exact Hreal |].
  split; [| exact Hmin].
  intros idxs Hvalid.
  eapply LNDSLengthPrefix_bound; eauto.
Qed.
Lemma LNDTailsPublic_append__lnds_state_transitions :
  forall l i tails len x,
    0 <= i < Zlength l ->
    x = Znth i l 0 ->
    0 <= len <= i ->
    LNDTailsRepresentation tails len ->
    LNDTailsRealizability l i tails len ->
    LNDSOptimalLength l i len ->
    LNDTailsMinimality l i tails len ->
    UpperBoundPartition tails len x len len ->
    LNDTailsRepresentation (tails ++ x :: nil) (len + 1) /\
    LNDTailsRealizability l (i + 1) (tails ++ x :: nil) (len + 1) /\
    LNDSOptimalLength l (i + 1) (len + 1) /\
    LNDTailsMinimality l (i + 1) (tails ++ x :: nil) (len + 1).
Proof.
  intros l i tails len x Hi Hx Hlen Hrep Hreal Hopt Hmin Hpart.
  pose proof Hrep as [Htails Hinc].
  assert (Hstate : LNDTailsState l i tails len).
  { eapply LNDTailsState_of_public__lnds_state_transitions; eauto; lia. }
  assert (Hsearch : UpperBoundSearch tails len x len len).
  { unfold UpperBoundSearch.
    split; [exact Htails |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [exact Hinc | exact Hpart]. }
  pose proof (LNDTailsState_append l i tails len x Hi Hx Hstate Hsearch) as Hnew.
  unfold LNDTailsState in Hnew.
  destruct Hnew as [_ [_ [Hnewlen [Hnewinc [Hnewopt [Hnewreal [_ Hnewmin]]]]]]].
  repeat split; auto.
Qed.
Lemma LNDTailsPublic_replace__lnds_state_transitions :
  forall l i tails len x left,
    0 <= i < Zlength l ->
    x = Znth i l 0 ->
    0 <= len <= i ->
    0 <= left < len ->
    LNDTailsRepresentation tails len ->
    LNDTailsRealizability l i tails len ->
    LNDSOptimalLength l i len ->
    LNDTailsMinimality l i tails len ->
    UpperBoundPartition tails len x left left ->
    LNDTailsRepresentation (replace_Znth left x tails) len /\
    LNDTailsRealizability l (i + 1) (replace_Znth left x tails) len /\
    LNDSOptimalLength l (i + 1) len /\
    LNDTailsMinimality l (i + 1) (replace_Znth left x tails) len.
Proof.
  intros l i tails len x left Hi Hx Hlen Hleft Hrep Hreal Hopt Hmin Hpart.
  pose proof Hrep as [Htails Hinc].
  assert (Hstate : LNDTailsState l i tails len).
  { eapply LNDTailsState_of_public__lnds_state_transitions; eauto; lia. }
  assert (Hsearch : UpperBoundSearch tails len x left left).
  { unfold UpperBoundSearch.
    split; [exact Htails |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [exact Hinc | exact Hpart]. }
  pose proof (LNDTailsState_replace l i tails len x left
    Hi Hx Hleft Hstate Hsearch) as Hnew.
  unfold LNDTailsState in Hnew.
  destruct Hnew as [_ [_ [Hnewlen [Hnewinc [Hnewopt [Hnewreal [_ Hnewmin]]]]]]].
  repeat split; auto.
Qed.

Lemma UpperBoundPartition_right_preserve__partition_search_steps :
  forall tails len x left right mid,
    Zlength tails = len ->
    increasing tails ->
    UpperBoundPartition tails len x left right ->
    Znth mid tails 0 <= x ->
    0 <= left ->
    left <= mid ->
    mid < right ->
    right <= len ->
    UpperBoundPartition tails len x (mid + 1) right.
Proof.
  intros tails len x left right mid Hlen Hinc Hpart Hmid
    Hleft Hleftmid Hmidright Hrightlen.
  unfold UpperBoundPartition in *.
  destruct Hpart as [Hlow Hhigh].
  split.
  - intros k Hk.
    destruct (Z_lt_ge_dec k left) as [Hkleft | Hleftk].
    + apply Hlow. lia.
    + destruct (Z.eq_dec k mid) as [Heq | Hneq].
      * subst k. exact Hmid.
      * pose proof (proj2 (mono_nondec_iff_increasing tails) Hinc) as Hmono.
        pose proof (Hmono k mid ltac:(lia) ltac:(lia) ltac:(lia)).
        lia.
  - exact Hhigh.
Qed.
Lemma UpperBoundPartition_left_preserve__partition_search_steps :
  forall tails len x left right mid,
    Zlength tails = len ->
    increasing tails ->
    UpperBoundPartition tails len x left right ->
    Znth mid tails 0 > x ->
    0 <= left ->
    left <= mid ->
    mid < right ->
    right <= len ->
    UpperBoundPartition tails len x left mid.
Proof.
  intros tails len x left right mid Hlen Hinc Hpart Hmid
    Hleft Hleftmid Hmidright Hrightlen.
  unfold UpperBoundPartition in *.
  destruct Hpart as [Hlow Hhigh].
  split.
  - exact Hlow.
  - intros k Hk.
    destruct (Z.eq_dec k mid) as [Heq | Hneq].
    + subst k. lia.
    + destruct (Z_lt_ge_dec k right) as [Hkright | Hrightk].
      * pose proof (proj2 (mono_nondec_iff_increasing tails) Hinc) as Hmono.
        pose proof (Hmono mid k ltac:(lia) ltac:(lia) ltac:(lia)).
        lia.
      * apply Hhigh. lia.
Qed.
Lemma LNDTailsPublic_append_update__append_transition :
  forall numsSize l tails_old i len x left,
    Zlength l = numsSize ->
    Zlength tails_old = numsSize ->
    0 <= i < numsSize ->
    0 <= len <= i ->
    x = Znth i l 0 ->
    left = len ->
    LNDTailsRepresentation (sublist 0 len tails_old) len ->
    LNDTailsRealizability l i (sublist 0 len tails_old) len ->
    LNDSOptimalLength l i len ->
    LNDTailsMinimality l i (sublist 0 len tails_old) len ->
    UpperBoundPartition (sublist 0 len tails_old) len x left left ->
    let tails_cur :=
      sublist 0 left tails_old ++ x :: sublist (left + 1) numsSize tails_old in
    Zlength tails_cur = numsSize /\
    LNDTailsMinimality l (i + 1) (sublist 0 (len + 1) tails_cur) (len + 1) /\
    LNDSOptimalLength l (i + 1) (len + 1) /\
    LNDTailsRealizability l (i + 1) (sublist 0 (len + 1) tails_cur) (len + 1) /\
    LNDTailsRepresentation (sublist 0 (len + 1) tails_cur) (len + 1).
Proof.
  intros numsSize l tails_old i len x left Hl Htails Hi Hlen Hx Hleft
    Hrep Hreal Hopt Hmin Hpart.
  subst left.
  cbv zeta.
  assert (Hlen_size : 0 <= len < numsSize) by lia.
  assert (Hprefix :
    sublist 0 (len + 1)
      (sublist 0 len tails_old ++ x :: sublist (len + 1) numsSize tails_old) =
    sublist 0 len tails_old ++ x :: nil).
  { eapply sublist_update_append_prefix; eauto. }
  pose proof (LNDTailsPublic_append__lnds_state_transitions
    l i (sublist 0 len tails_old) len x) as Happend.
  specialize (Happend ltac:(lia) Hx Hlen Hrep Hreal Hopt Hmin Hpart).
  destruct Happend as [Hrep' [Hreal' [Hopt' Hmin']]].
  split.
  - assert (Hleft_len : Zlength (sublist 0 len tails_old) = len).
    { apply Zlength_sublist0. lia. }
    assert (Hright_len :
      Zlength (sublist (len + 1) numsSize tails_old) =
      numsSize - (len + 1)).
    { apply Zlength_sublist. lia. }
    rewrite Zlength_app.
    rewrite Hleft_len.
    rewrite Zlength_cons.
    rewrite Hright_len.
    lia.
  - rewrite Hprefix.
    split; [exact Hmin' |].
    split; [exact Hopt' |].
    split; [exact Hreal' | exact Hrep'].
Qed.
Lemma LNDTailsPublic_replace_update__replace_transition :
  forall l tails_old i len x left numsSize,
    Zlength tails_old = numsSize ->
    0 <= i < Zlength l ->
    x = Znth i l 0 ->
    0 <= len <= i ->
    0 <= left < len ->
    len <= numsSize ->
    LNDTailsRepresentation (sublist 0 len tails_old) len ->
    LNDTailsRealizability l i (sublist 0 len tails_old) len ->
    LNDSOptimalLength l i len ->
    LNDTailsMinimality l i (sublist 0 len tails_old) len ->
    UpperBoundPartition (sublist 0 len tails_old) len x left left ->
    let updated :=
      sublist 0 left tails_old ++
      x :: sublist (left + 1) numsSize tails_old in
    LNDTailsRepresentation (sublist 0 len updated) len /\
    LNDTailsRealizability l (i + 1) (sublist 0 len updated) len /\
    LNDSOptimalLength l (i + 1) len /\
    LNDTailsMinimality l (i + 1) (sublist 0 len updated) len.
Proof.
  intros l tails_old i len x left numsSize Htails Hi Hx Hlen Hleft HlenSize
    Hrep Hreal Hopt Hmin Hpart.
  cbv zeta.
  rewrite sublist_update_replace_prefix by lia.
  eapply LNDTailsPublic_replace__lnds_state_transitions; eauto.
Qed.
