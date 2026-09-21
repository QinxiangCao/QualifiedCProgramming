Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Require Import SumLib.ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

(** Implementation-independent semantics of one legal container. *)
Definition ContainerHeightNLogN (l : list Z) (i j : Z) : Z :=
  Z.min (Znth i l 0) (Znth j l 0).

Definition ContainerAreaNLogN (l : list Z) (i j : Z) : Z :=
  (j - i) * ContainerHeightNLogN l i j.

Definition ContainerPairNLogN (l : list Z) (i j : Z) : Prop :=
  0 <= i /\ i < j /\ j < Zlength l.

(** The exact attained global optimum, stated only in terms of original
    indices.  A different implementation can satisfy the same predicate. *)
Definition MaximumContainerArea (l : list Z) (ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun ij : Z * Z => ContainerPairNLogN l (fst ij) (snd ij))
    (fun ij => ContainerAreaNLogN l (fst ij) (snd ij)) ans.

Lemma MaximumContainerArea_unfold l ans :
  MaximumContainerArea l ans <->
  exists i j, 0 <= i /\ i < j /\ j < Zlength l /\
    ans = (j-i) * Z.min (Znth i l 0) (Znth j l 0) /\
    forall p q, 0 <= p -> p < q -> q < Zlength l ->
      (q-p) * Z.min (Znth p l 0) (Znth q l 0) <= ans.
Proof.
  unfold MaximumContainerArea, max_value_of_subset, max_object_of_subset,
    ContainerPairNLogN, ContainerAreaNLogN, ContainerHeightNLogN.
  cbn beta. split.
  - intros [[i j] [[Hp Hbound] Heq]]. cbn in *.
    change (0 <= i /\ i < j /\ j < Zlength l) in Hp.
    exists i,j. split; [tauto|]. split; [tauto|]. split; [tauto|].
    split; [lia|]. intros p q H0 Hlt Hlen. specialize (Hbound (p,q) ltac:(change (0<=p /\ p<q /\q<Zlength l);tauto)). cbn in Hbound. lia.
  - intros [i [j [H0 [Hij [Hj [Heq Hbound]]]]]]. exists (i,j). cbn.
    split; [split |lia]; [change (0<=i /\ i<j /\j<Zlength l);tauto|]. intros [p q] Hp. cbn in *. change (0<=p /\ p<q /\ q<Zlength l) in Hp.
    specialize (Hbound p q ltac:(tauto) ltac:(tauto) ltac:(tauto)). lia.
Qed.

(** Canonical list of the input's [(height,index)] pairs. *)
Definition IndexedHeightsNLogN (l : list Z) : list (Z * Z) :=
  map (fun k : Z => (Znth k l 0, k)) (Zrange 0 (Zlength l)).

(** Bridge for the pre-existing helper proofs, whose internal induction is on nat. *)
Lemma Zrange_aux_seq n start :
  Zrange_aux (Z.of_nat start) n = map Z.of_nat (seq start n).
Proof.
  revert start. induction n; intros start; cbn; [reflexivity |].
  replace (Z.of_nat start + 1) with (Z.of_nat (S start)) by lia.
  rewrite IHn. reflexivity.
Qed.
Lemma IndexedHeightsNLogN_legacy l :
  IndexedHeightsNLogN l =
  map (fun k : nat => (nth k l 0, Z.of_nat k)) (seq 0 (length l)).
Proof.
  unfold IndexedHeightsNLogN, Zrange.
  rewrite Z.sub_0_r, Zlength_correct, Nat2Z.id.
  change 0 with (Z.of_nat 0). rewrite Zrange_aux_seq, map_map.
  apply map_ext. intros k. unfold Znth. rewrite Nat2Z.id. reflexivity.
Qed.


Definition HeightIndexPermutationNLogN
    (l heights indices : list Z) : Prop :=
  Zlength heights = Zlength l /\
  Zlength indices = Zlength l /\
  Permutation (combine heights indices) (IndexedHeightsNLogN l).

Definition HeightIndexRangeDescendingNLogN
    (heights : list Z) (lo hi : Z) : Prop :=
  forall p q,
    lo <= p -> p <= q -> q < hi ->
    Znth q heights 0 <= Znth p heights 0.

Definition SortedHeightIndexWorkspaceNLogN
    (l heights indices : list Z) : Prop :=
  HeightIndexPermutationNLogN l heights indices /\
  HeightIndexRangeDescendingNLogN heights 0 (Zlength heights).

Lemma NLogN_Forall2_indexed {A B : Type} (R : A -> B -> Prop)
    (f : Z -> A) (g : Z -> B) lo hi :
  Forall2 R (map f (Zrange lo hi)) (map g (Zrange lo hi)) <->
  forall p, lo <= p < hi -> R (f p) (g p).
Proof.
  assert (Hmap : forall xs, Forall2 R (map f xs) (map g xs) <->
    Forall (fun p => R (f p) (g p)) xs).
  { induction xs as [|x xs IH]; cbn.
    - split; intros; constructor.
    - split; intro H; inversion H; subst; constructor; try assumption;
      apply IH; assumption. }
  rewrite Hmap, Forall_forall. split; intros H p Hp; apply H;
    [apply In_Zrange | apply In_Zrange]; assumption.
Qed.

(** Prefix produced while the four caller-owned work arrays are initialized. *)
Definition WorkspacePrefixNLogN
    (l heights indices : list Z) (k : Z) : Prop :=
  Forall2 eq
    (map (fun p => Znth p heights 0) (Zrange 0 k))
    (map (fun p => Znth p l 0) (Zrange 0 k)) /\
  (forall p, 0 <= p < k -> Znth p indices 0 = p).

Lemma WorkspacePrefixNLogN_unfold l heights indices k :
  WorkspacePrefixNLogN l heights indices k <->
  (forall p, 0 <= p < k -> Znth p heights 0 = Znth p l 0) /\
  (forall p, 0 <= p < k -> Znth p indices 0 = p).
Proof. unfold WorkspacePrefixNLogN. rewrite NLogN_Forall2_indexed. reflexivity. Qed.


Lemma NLogN_Forall2_filtered {A B : Type} (R : A -> B -> Prop)
    (f : Z -> A) (g : Z -> B) (keep : Z -> bool) lo hi :
  Forall2 R (map f (filter keep (Zrange lo hi)))
    (map g (filter keep (Zrange lo hi))) <->
  forall p, lo <= p < hi -> keep p = true -> R (f p) (g p).
Proof.
  assert (Hmap : forall xs, Forall2 R (map f xs) (map g xs) <->
    Forall (fun p => R (f p) (g p)) xs).
  { induction xs as [|x xs IH]; cbn.
    - split; intros; constructor.
    - split; intro H; inversion H; subst; constructor; try assumption;
      apply IH; assumption. }
  rewrite Hmap, Forall_forall. split; intros H p Hp.
  - intro Hkeep. apply H. apply filter_In. split; [apply In_Zrange|]; assumption.
  - apply filter_In in Hp. destruct Hp as [Hp Hkeep].
    apply H; [apply In_Zrange|]; assumption.
Qed.

Definition SameHeightIndexOutsideNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Zlength after_h = Zlength before_h /\
  Zlength after_i = Zlength before_i /\
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun idx => (Znth idx after_h 0, Znth idx after_i 0)) (filter (fun idx => orb (idx <? lo) (hi <=? idx)) (Zrange 0 (Zlength before_h))))
    (map (fun idx => (Znth idx before_h 0, Znth idx before_i 0)) (filter (fun idx => orb (idx <? lo) (hi <=? idx)) (Zrange 0 (Zlength before_h)))).

Lemma SameHeightIndexOutsideNLogN_unfold before_h before_i after_h after_i lo hi :
  SameHeightIndexOutsideNLogN before_h before_i after_h after_i lo hi <->
  Zlength after_h = Zlength before_h /\
  Zlength after_i = Zlength before_i /\
  forall k,
    0 <= k < Zlength before_h ->
    (k < lo \/ hi <= k) ->
    Znth k after_h 0 = Znth k before_h 0 /\
    Znth k after_i 0 = Znth k before_i 0.
Proof.
  unfold SameHeightIndexOutsideNLogN. rewrite NLogN_Forall2_filtered.
  setoid_rewrite Bool.orb_true_iff. setoid_rewrite Z.ltb_lt.
  setoid_rewrite Z.leb_le. cbn. firstorder.
Qed.

Definition HeightIndexRangePermutationNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Permutation
    (combine (sublist lo hi after_h) (sublist lo hi after_i))
    (combine (sublist lo hi before_h) (sublist lo hi before_i)).

(** Mathematical result of sorting one half-open range. *)
Definition HeightIndexRangeSortResultNLogN
    (before_h before_i after_h after_i : list Z)
    (lo hi : Z) : Prop :=
  Zlength before_h = Zlength before_i /\
  Zlength after_h = Zlength after_i /\
  SameHeightIndexOutsideNLogN
    before_h before_i after_h after_i lo hi /\
  HeightIndexRangePermutationNLogN
    before_h before_i after_h after_i lo hi /\
  HeightIndexRangeDescendingNLogN after_h lo hi.

(** State of a standard merge of two descending source ranges.  It says that
    the destination prefix contains exactly the consumed source pairs, is
    descending, and dominates every still-pending height. *)
Definition MergePrefixStateNLogN
    (source_h source_i dest0_h dest0_i dest_h dest_i : list Z)
    (left middle right p q output : Z) : Prop :=
  HeightIndexRangeDescendingNLogN source_h left middle /\
  HeightIndexRangeDescendingNLogN source_h middle right /\
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun idx => (Znth idx dest_h 0, Znth idx dest_i 0)) (filter (fun idx => orb (idx <? left) (output <=? idx)) (Zrange 0 (Zlength dest0_h))))
    (map (fun idx => (Znth idx dest0_h 0, Znth idx dest0_i 0)) (filter (fun idx => orb (idx <? left) (output <=? idx)) (Zrange 0 (Zlength dest0_h)))) /\
  Permutation
    (combine (sublist left output dest_h) (sublist left output dest_i))
    (combine (sublist left p source_h) (sublist left p source_i) ++
     combine (sublist middle q source_h) (sublist middle q source_i)) /\
  (forall u v,
     left <= u -> u <= v -> v < output ->
     Znth v dest_h 0 <= Znth u dest_h 0) /\
  (forall u v,
     left <= u < output ->
     ((p <= v < middle) \/ (q <= v < right)) ->
     Znth v source_h 0 <= Znth u dest_h 0).

Lemma MergePrefixStateNLogN_unfold source_h source_i dest0_h dest0_i dest_h dest_i left middle right p q output :
  MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left middle right p q output <->
  HeightIndexRangeDescendingNLogN source_h left middle /\
  HeightIndexRangeDescendingNLogN source_h middle right /\
  (forall t,
     0 <= t < Zlength dest0_h ->
     (t < left \/ output <= t) ->
     Znth t dest_h 0 = Znth t dest0_h 0 /\
     Znth t dest_i 0 = Znth t dest0_i 0) /\
  Permutation
    (combine (sublist left output dest_h) (sublist left output dest_i))
    (combine (sublist left p source_h) (sublist left p source_i) ++
     combine (sublist middle q source_h) (sublist middle q source_i)) /\
  (forall u v,
     left <= u -> u <= v -> v < output ->
     Znth v dest_h 0 <= Znth u dest_h 0) /\
  (forall u v,
     left <= u < output ->
     ((p <= v < middle) \/ (q <= v < right)) ->
     Znth v source_h 0 <= Znth u dest_h 0).
Proof.
  unfold MergePrefixStateNLogN. rewrite NLogN_Forall2_filtered.
  setoid_rewrite Bool.orb_true_iff. setoid_rewrite Z.ltb_lt.
  setoid_rewrite Z.leb_le. cbn. firstorder.
Qed.

Definition HeightIndexRangeMergeResultNLogN
    (source_h source_i dest0_h dest0_i dest_h dest_i : list Z)
    (left middle right : Z) : Prop :=
  SameHeightIndexOutsideNLogN
    dest0_h dest0_i dest_h dest_i left right /\
  Permutation
    (combine (sublist left right dest_h) (sublist left right dest_i))
    (combine (sublist left right source_h) (sublist left right source_i)) /\
  HeightIndexRangeDescendingNLogN dest_h left right.

(** State while copying a merged range from the buffer back to the work
    arrays. *)
Definition CopyHeightIndexPrefixNLogN
    (source_h source_i dest0_h dest0_i dest_h dest_i : list Z)
    (left right k : Z) : Prop :=
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun p => (Znth p dest_h 0, Znth p dest_i 0)) (Zrange left k))
    (map (fun p => (Znth p source_h 0, Znth p source_i 0)) (Zrange left k)) /\
  Forall2 (fun a b : Z * Z => fst a = fst b /\ snd a = snd b)
    (map (fun idx => (Znth idx dest_h 0, Znth idx dest_i 0)) (filter (fun idx => orb (idx <? left) (k <=? idx)) (Zrange 0 (Zlength dest0_h))))
    (map (fun idx => (Znth idx dest0_h 0, Znth idx dest0_i 0)) (filter (fun idx => orb (idx <? left) (k <=? idx)) (Zrange 0 (Zlength dest0_h)))).

Lemma CopyHeightIndexPrefixNLogN_unfold source_h source_i dest0_h dest0_i dest_h dest_i left right k :
  CopyHeightIndexPrefixNLogN source_h source_i dest0_h dest0_i dest_h dest_i left right k <->
  (forall p, left <= p < k ->
     Znth p dest_h 0 = Znth p source_h 0 /\
     Znth p dest_i 0 = Znth p source_i 0) /\
  (forall p,
     0 <= p < Zlength dest0_h ->
     (p < left \/ k <= p) ->
     Znth p dest_h 0 = Znth p dest0_h 0 /\
     Znth p dest_i 0 = Znth p dest0_i 0).
Proof.
  unfold CopyHeightIndexPrefixNLogN. rewrite NLogN_Forall2_indexed, NLogN_Forall2_filtered.
  setoid_rewrite Bool.orb_true_iff. setoid_rewrite Z.ltb_lt.
  setoid_rewrite Z.leb_le. cbn. firstorder.
Qed.


(** Endpoints of the original indices represented by a nonempty sorted
    prefix.  These endpoints are sufficient to find the farthest prior bar. *)
Definition ProcessedIndexEndpointsNLogN
    (indices : list Z) (k minimum maximum : Z) : Prop :=
  min_value_of_subset Z.le (fun p : Z => 0 <= p < k)
    (fun p => Znth p indices 0) minimum /\
  max_value_of_subset Z.le (fun p : Z => 0 <= p < k)
    (fun p => Znth p indices 0) maximum.

Lemma ProcessedIndexEndpointsNLogN_unfold indices k minimum maximum :
  ProcessedIndexEndpointsNLogN indices k minimum maximum <->
  (exists p, 0 <= p < k /\ Znth p indices 0 = minimum) /\
  (exists p, 0 <= p < k /\ Znth p indices 0 = maximum) /\
  (forall p, 0 <= p < k -> minimum <= Znth p indices 0 <= maximum).
Proof.
  unfold ProcessedIndexEndpointsNLogN, min_value_of_subset, min_object_of_subset,
    max_value_of_subset, max_object_of_subset. cbn beta. split.
  - intros [[p [[Hp Hmin] Heqmin]] [q [[Hq Hmax] Heqmax]]].
    split; [exists p;auto|]. split; [exists q;auto|].
    intros r Hr. specialize (Hmin r Hr). specialize (Hmax r Hr). lia.
  - intros [[p [Hp Heqmin]] [[q [Hq Heqmax]] Hall]]. split.
    + exists p. split; [split; [exact Hp|] |exact Heqmin].
      intros r Hr. specialize (Hall r Hr). lia.
    + exists q. split; [split; [exact Hq|] |exact Heqmax].
      intros r Hr. specialize (Hall r Hr). lia.
Qed.


Definition ProcessedContainerPairNLogN
    (l indices : list Z) (k : Z) (ij : Z * Z) : Prop :=
  ContainerPairNLogN l (fst ij) (snd ij) /\
  In (fst ij) (sublist 0 k indices) /\
  In (snd ij) (sublist 0 k indices).

Definition ProcessedContainerMaximumNLogN
    (l indices : list Z) (k ans : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (ProcessedContainerPairNLogN l indices k)
    (fun ij : Z * Z =>
       ContainerAreaNLogN l (fst ij) (snd ij))
    0 ans.

Lemma sublist_replace_Znth_before__merge_core :
  forall (A : Type) (d : A) (l : list A) lo hi (v : A),
    0 <= lo <= hi ->
    hi < Zlength l ->
    sublist lo hi (replace_Znth hi v l) = sublist lo hi l.
Proof.
  intros A d l lo hi v Hlohi Hhi.
  apply (proj2 (list_eq_ext _ _ d)).
  split.
  - rewrite (Zlength_sublist lo hi (replace_Znth hi v l)) by
        (rewrite Zlength_replace_Znth; lia).
    rewrite (Zlength_sublist lo hi l) by lia.
    reflexivity.
  - intros k Hk.
    assert (Hkbound : 0 <= k < hi - lo).
    {
      rewrite (Zlength_sublist lo hi (replace_Znth hi v l)) in Hk by
          (rewrite Zlength_replace_Znth; lia).
      lia.
    }
    rewrite !Znth_sublist by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.
Lemma sublist_replace_Znth_extend__merge_core :
  forall (A : Type) (d : A) (l : list A) lo hi (v : A),
    0 <= lo <= hi ->
    hi < Zlength l ->
    sublist lo (hi + 1) (replace_Znth hi v l) =
      sublist lo hi l ++ [v].
Proof.
  intros A d l lo hi v Hlohi Hhi.
  rewrite (sublist_split lo (hi + 1) hi (replace_Znth hi v l)) by
      (rewrite ?Zlength_replace_Znth; lia).
  rewrite (sublist_replace_Znth_before__merge_core A d l lo hi v) by lia.
  rewrite (sublist_single d hi (replace_Znth hi v l)) by
      (rewrite Zlength_replace_Znth; lia).
  rewrite (Znth_replace_Znth_Same d l hi v) by lia.
  reflexivity.
Qed.
Lemma merge_prefix_init__merge_core :
  forall source_h source_i dest0_h dest0_i left middle right,
    0 <= left ->
    left <= middle ->
    middle <= right ->
    HeightIndexRangeDescendingNLogN source_h left middle ->
    HeightIndexRangeDescendingNLogN source_h middle right ->
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      dest0_h dest0_i left middle right left middle left.
Proof.
  intros source_h source_i dest0_h dest0_i left middle right
    Hleft Hmiddle Hright Hdesc_left Hdesc_right.
  rewrite MergePrefixStateNLogN_unfold.
  split; [exact Hdesc_left |].
  split; [exact Hdesc_right |].
  split.
  - intros t Ht _. split; reflexivity.
  - split.
    + assert (Hempty : forall (A : Type) (l : list A) x,
        0 <= x -> sublist x x l = []).
      {
        intros A l x Hx. unfold sublist.
        change (Nsublist (Z.to_nat x) (Z.to_nat x) l = []).
        apply sublist_nil. lia.
      }
      repeat rewrite Hempty by lia. simpl. apply Permutation_refl.
    + split.
      * intros u v Hu Huv Hv. lia.
      * intros u v Hu _. lia.
Qed.
Lemma merge_prefix_take_left__merge_core :
  forall source_h source_i dest0_h dest0_i dest_h dest_i
         left middle right p q output,
    Zlength source_i = Zlength source_h ->
    Zlength dest0_h = Zlength source_h ->
    Zlength dest0_i = Zlength source_h ->
    Zlength dest_h = Zlength dest0_h ->
    Zlength dest_i = Zlength dest0_i ->
    0 <= left ->
    left <= p ->
    p < middle ->
    middle <= q ->
    q <= right ->
    right <= Zlength source_h ->
    output = left + (p - left) + (q - middle) ->
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      dest_h dest_i left middle right p q output ->
    (q = right \/ Znth q source_h 0 <= Znth p source_h 0) ->
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      (replace_Znth output (Znth p source_h 0) dest_h)
      (replace_Znth output (Znth p source_i 0) dest_i)
      left middle right (p + 1) q (output + 1).
Proof.
  intros source_h source_i dest0_h dest0_i dest_h dest_i
    left middle right p q output
    Hsource_i Hdest0_h Hdest0_i Hdest_h Hdest_i
    Hleft Hleft_p Hp_middle Hmiddle_q Hq_right Hright_len Houtput
    Hstate Hchoice.
  assert (Hout : 0 <= output < Zlength dest_h).
  { rewrite Hdest_h, Hdest0_h. lia. }
  assert (Hout_i : 0 <= output < Zlength dest_i).
  { rewrite Hdest_i, Hdest0_i. lia. }
  rewrite MergePrefixStateNLogN_unfold in Hstate.
  destruct Hstate as
      [Hdesc_left [Hdesc_right [Houtside [Hperm [Hdescending Hpending]]]]].
  pose proof Hdesc_left as Hdesc_left_parts.
  pose proof Hdesc_right as Hdesc_right_parts.
  pose proof Hdesc_left_parts as Hleft_order.
  pose proof Hdesc_right_parts as Hright_order.
  rewrite MergePrefixStateNLogN_unfold.
  split; [exact Hdesc_left |].
  split; [exact Hdesc_right |].
  split.
  - intros t Ht Hregion.
    assert (Hold_region : t < left \/ output <= t) by lia.
    specialize (Houtside t Ht Hold_region) as [Hoh Hoi].
    split.
    + rewrite (Znth_replace_Znth_Diff 0 dest_h output t
          (Znth p source_h 0)) by (rewrite ?Hdest_h; lia).
      exact Hoh.
    + rewrite (Znth_replace_Znth_Diff 0 dest_i output t
          (Znth p source_i 0)) by (rewrite ?Hdest_i; lia).
      exact Hoi.
  - split.
    + assert (Hdest_pairs :
        combine
          (sublist left (output + 1)
            (replace_Znth output (Znth p source_h 0) dest_h))
          (sublist left (output + 1)
            (replace_Znth output (Znth p source_i 0) dest_i)) =
        combine (sublist left output dest_h) (sublist left output dest_i) ++
          [(Znth p source_h 0, Znth p source_i 0)]).
    {
      rewrite (sublist_replace_Znth_extend__merge_core Z 0 dest_h
        left output (Znth p source_h 0)) by lia.
      rewrite (sublist_replace_Znth_extend__merge_core Z 0 dest_i
        left output (Znth p source_i 0)) by lia.
      rewrite combine_app.
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct.
        rewrite !Zlength_sublist by lia. lia.
    }
    assert (Hsource_pairs :
        combine (sublist left (p + 1) source_h)
                (sublist left (p + 1) source_i) =
        combine (sublist left p source_h) (sublist left p source_i) ++
          [(Znth p source_h 0, Znth p source_i 0)]).
    {
      rewrite (sublist_split left (p + 1) p source_h) by lia.
      rewrite (sublist_split left (p + 1) p source_i) by
        (rewrite ?Hsource_i; lia).
      rewrite (sublist_single 0 p source_h) by lia.
      rewrite (sublist_single 0 p source_i) by
        (rewrite ?Hsource_i; lia).
      rewrite combine_app.
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct.
        rewrite !Zlength_sublist by (rewrite ?Hsource_i; lia). lia.
    }
      rewrite Hdest_pairs, Hsource_pairs.
      eapply Permutation_trans with
        (l' :=
          (combine (sublist left p source_h) (sublist left p source_i) ++
           combine (sublist middle q source_h) (sublist middle q source_i)) ++
          [(Znth p source_h 0, Znth p source_i 0)]).
      * apply Permutation_app_tail. exact Hperm.
      * assert (Hswap : Permutation
            (combine (sublist middle q source_h) (sublist middle q source_i) ++
             [(Znth p source_h 0, Znth p source_i 0)])
            ([(Znth p source_h 0, Znth p source_i 0)] ++
             combine (sublist middle q source_h) (sublist middle q source_i))).
        { apply Permutation_app_comm. }
        pose proof
          (Permutation_app_head
            (combine (sublist left p source_h) (sublist left p source_i))
            Hswap) as Hmove.
        repeat rewrite app_assoc in Hmove.
        exact Hmove.
    + split.
      * intros u v Hu Huv Hv.
        destruct (Z.eq_dec v output) as [-> | Hvo].
        -- destruct (Z.eq_dec u output) as [-> | Huo].
           ++ rewrite !Znth_replace_Znth_Same by exact Hout. lia.
           ++ rewrite Znth_replace_Znth_Same by exact Hout.
              rewrite Znth_replace_Znth_Diff by lia.
              apply (Hpending u p); lia.
        -- rewrite !Znth_replace_Znth_Diff by lia.
           apply Hdescending; lia.
      * intros u v Hu Hremaining.
        destruct (Z.eq_dec u output) as [-> | Huo].
        -- rewrite Znth_replace_Znth_Same by exact Hout.
           destruct Hremaining as [Hrem_left | Hrem_right].
           ++ apply Hleft_order; lia.
           ++ destruct Hchoice as [-> | Hchosen].
              ** lia.
              ** eapply Z.le_trans with (m := Znth q source_h 0).
                 --- apply Hright_order; lia.
                 --- exact Hchosen.
        -- rewrite Znth_replace_Znth_Diff by lia.
           apply (Hpending u v); lia.
Qed.
Lemma merge_prefix_take_right__merge_core :
  forall source_h source_i dest0_h dest0_i dest_h dest_i
         left middle right p q output,
    Zlength source_i = Zlength source_h ->
    Zlength dest0_h = Zlength source_h ->
    Zlength dest0_i = Zlength source_h ->
    Zlength dest_h = Zlength dest0_h ->
    Zlength dest_i = Zlength dest0_i ->
    0 <= left ->
    left <= p ->
    p <= middle ->
    middle <= q ->
    q < right ->
    right <= Zlength source_h ->
    output = left + (p - left) + (q - middle) ->
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      dest_h dest_i left middle right p q output ->
    (p = middle \/ Znth p source_h 0 < Znth q source_h 0) ->
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      (replace_Znth output (Znth q source_h 0) dest_h)
      (replace_Znth output (Znth q source_i 0) dest_i)
      left middle right p (q + 1) (output + 1).
Proof.
  intros source_h source_i dest0_h dest0_i dest_h dest_i
    left middle right p q output
    Hsource_i Hdest0_h Hdest0_i Hdest_h Hdest_i
    Hleft Hleft_p Hp_middle Hmiddle_q Hq_right Hright_len Houtput
    Hstate Hchoice.
  assert (Hout : 0 <= output < Zlength dest_h).
  { rewrite Hdest_h, Hdest0_h. lia. }
  assert (Hout_i : 0 <= output < Zlength dest_i).
  { rewrite Hdest_i, Hdest0_i. lia. }
  rewrite MergePrefixStateNLogN_unfold in Hstate.
  destruct Hstate as
      [Hdesc_left [Hdesc_right [Houtside [Hperm [Hdescending Hpending]]]]].
  pose proof Hdesc_left as Hdesc_left_parts.
  pose proof Hdesc_right as Hdesc_right_parts.
  pose proof Hdesc_left_parts as Hleft_order.
  pose proof Hdesc_right_parts as Hright_order.
  rewrite MergePrefixStateNLogN_unfold.
  split; [exact Hdesc_left |].
  split; [exact Hdesc_right |].
  split.
  - intros t Ht Hregion.
    assert (Hold_region : t < left \/ output <= t) by lia.
    specialize (Houtside t Ht Hold_region) as [Hoh Hoi].
    split.
    + rewrite (Znth_replace_Znth_Diff 0 dest_h output t
          (Znth q source_h 0)) by (rewrite ?Hdest_h; lia).
      exact Hoh.
    + rewrite (Znth_replace_Znth_Diff 0 dest_i output t
          (Znth q source_i 0)) by (rewrite ?Hdest_i; lia).
      exact Hoi.
  - split.
    + assert (Hdest_pairs :
        combine
          (sublist left (output + 1)
            (replace_Znth output (Znth q source_h 0) dest_h))
          (sublist left (output + 1)
            (replace_Znth output (Znth q source_i 0) dest_i)) =
        combine (sublist left output dest_h) (sublist left output dest_i) ++
          [(Znth q source_h 0, Znth q source_i 0)]).
    {
      rewrite (sublist_replace_Znth_extend__merge_core Z 0 dest_h
        left output (Znth q source_h 0)) by lia.
      rewrite (sublist_replace_Znth_extend__merge_core Z 0 dest_i
        left output (Znth q source_i 0)) by lia.
      rewrite combine_app.
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct.
        rewrite !Zlength_sublist by lia. lia.
    }
    assert (Hsource_pairs :
        combine (sublist middle (q + 1) source_h)
                (sublist middle (q + 1) source_i) =
        combine (sublist middle q source_h) (sublist middle q source_i) ++
          [(Znth q source_h 0, Znth q source_i 0)]).
    {
      rewrite (sublist_split middle (q + 1) q source_h) by lia.
      rewrite (sublist_split middle (q + 1) q source_i) by
        (rewrite ?Hsource_i; lia).
      rewrite (sublist_single 0 q source_h) by lia.
      rewrite (sublist_single 0 q source_i) by
        (rewrite ?Hsource_i; lia).
      rewrite combine_app.
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct.
        rewrite !Zlength_sublist by (rewrite ?Hsource_i; lia). lia.
    }
      rewrite Hdest_pairs, Hsource_pairs.
      eapply Permutation_trans with
        (l' :=
          (combine (sublist left p source_h) (sublist left p source_i) ++
           combine (sublist middle q source_h) (sublist middle q source_i)) ++
          [(Znth q source_h 0, Znth q source_i 0)]).
      * apply Permutation_app_tail. exact Hperm.
      * repeat rewrite app_assoc. apply Permutation_refl.
    + split.
      * intros u v Hu Huv Hv.
        destruct (Z.eq_dec v output) as [-> | Hvo].
        -- destruct (Z.eq_dec u output) as [-> | Huo].
           ++ rewrite !Znth_replace_Znth_Same by exact Hout. lia.
           ++ rewrite Znth_replace_Znth_Same by exact Hout.
              rewrite Znth_replace_Znth_Diff by lia.
              apply (Hpending u q); lia.
        -- rewrite !Znth_replace_Znth_Diff by lia.
           apply Hdescending; lia.
      * intros u v Hu Hremaining.
        destruct (Z.eq_dec u output) as [-> | Huo].
        -- rewrite Znth_replace_Znth_Same by exact Hout.
           destruct Hremaining as [Hrem_left | Hrem_right].
           ++ destruct Hchoice as [-> | Hchosen].
              ** lia.
              ** eapply Z.le_trans with (m := Znth p source_h 0).
                 --- apply Hleft_order; lia.
                 --- lia.
           ++ apply Hright_order; lia.
        -- rewrite Znth_replace_Znth_Diff by lia.
           apply (Hpending u v); lia.
Qed.
Lemma merge_prefix_finish__merge_core :
  forall source_h source_i dest0_h dest0_i dest_h dest_i
         left middle right,
    Zlength source_i = Zlength source_h ->
    Zlength dest0_h = Zlength source_h ->
    Zlength dest0_i = Zlength source_h ->
    Zlength dest_h = Zlength dest0_h ->
    Zlength dest_i = Zlength dest0_i ->
    0 <= left ->
    left <= middle ->
    middle <= right ->
    right <= Zlength source_h ->
    MergePrefixStateNLogN source_h source_i dest0_h dest0_i
      dest_h dest_i left middle right middle right right ->
    HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i
      dest_h dest_i left middle right.
Proof.
  intros source_h source_i dest0_h dest0_i dest_h dest_i
    left middle right Hsource_i Hdest0_h Hdest0_i Hdest_h Hdest_i
    Hleft Hleft_middle Hmiddle_right Hright_len Hstate.
  rewrite MergePrefixStateNLogN_unfold in Hstate.
  destruct Hstate as
      [Hdesc_left [Hdesc_right [Houtside [Hperm [Hdescending _]]]]].
  unfold HeightIndexRangeMergeResultNLogN.
  split.
  - rewrite SameHeightIndexOutsideNLogN_unfold.
    split; [exact Hdest_h |].
    split; [exact Hdest_i |].
    exact Houtside.
  - split.
    + assert (Hsource_pairs :
        combine (sublist left right source_h) (sublist left right source_i) =
        combine (sublist left middle source_h) (sublist left middle source_i) ++
        combine (sublist middle right source_h) (sublist middle right source_i)).
    {
      rewrite (sublist_split left right middle source_h) by lia.
      rewrite (sublist_split left right middle source_i) by
        (rewrite ?Hsource_i; lia).
      rewrite combine_app.
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct.
        rewrite !Zlength_sublist by (rewrite ?Hsource_i; lia). lia.
    }
      rewrite Hsource_pairs. exact Hperm.
    + exact Hdescending.
Qed.
Lemma range_sort_left_desc__sort_recursion :
  forall work0_h work0_i work_mid_h work_mid_i work_h work_i
         left middle right,
    HeightIndexRangeSortResultNLogN
      work0_h work0_i work_mid_h work_mid_i left middle ->
    HeightIndexRangeSortResultNLogN
      work_mid_h work_mid_i work_h work_i middle right ->
    0 <= left /\ left <= middle /\ middle <= right /\ right <= Zlength work0_h ->
    HeightIndexRangeDescendingNLogN work_h left middle.
Proof.
  intros work0_h work0_i work_mid_h work_mid_i work_h work_i
    left middle right Hleft Hright Hbounds.
  unfold HeightIndexRangeSortResultNLogN in Hleft, Hright.
  destruct Hleft as
    [Hbefore_len [Hafter_len [Hsame_left [Hperm_left Hdesc]]]].
  try rewrite SameHeightIndexOutsideNLogN_unfold in Hsame_left.
  destruct Hsame_left as [Hmidlenh [Hmidleni Houtsideleft]].
  destruct Hright as
    [Hmid_pair_len [Hwork_pair_len [Hsame [Hperm_right Hdesc_right]]]].
  rewrite SameHeightIndexOutsideNLogN_unfold in Hsame.
  destruct Hsame as [Hhlen [_ Houtside]].
  unfold HeightIndexRangeDescendingNLogN in Hdesc |- *.
  pose proof Hdesc as Hordered.
  intros p q Hlp Hpq Hqm.
  assert (Hp : 0 <= p < Zlength work_mid_h) by lia.
  assert (Hq : 0 <= q < Zlength work_mid_h) by lia.
  assert (Houtp : p < middle \/ right <= p) by lia.
  assert (Houtq : q < middle \/ right <= q) by lia.
  destruct (Houtside p Hp Houtp) as [Hph _].
  destruct (Houtside q Hq Houtq) as [Hqh _].
  rewrite Hph, Hqh.
  apply Hordered; lia.
Qed.
Lemma sublist_eq_by_Znth__sort_copy :
  forall (A : Type) (l1 l2 : list A) lo hi (d : A),
    Zlength l1 = Zlength l2 ->
    0 <= lo <= hi ->
    hi <= Zlength l1 ->
    (forall k, lo <= k < hi -> Znth k l1 d = Znth k l2 d) ->
    sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros A l1 l2 lo hi d Hlen Hlohi Hhi Hpoint.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2) d)).
  split.
  - rewrite !Zlength_sublist by lia. lia.
  - intros i Hi.
    assert (Hi' : 0 <= i < hi - lo).
    { rewrite Zlength_sublist in Hi by lia. exact Hi. }
    rewrite (@Znth_sublist_lt A d lo hi l1 i).
    2: exact Hlohi.
    2: exact Hhi.
    2: exact Hi'.
    rewrite (@Znth_sublist_lt A d lo hi l2 i).
    2: exact Hlohi.
    2: { rewrite <- Hlen. exact Hhi. }
    2: exact Hi'.
    apply Hpoint. lia.
Qed.
Lemma combine_sublist_split__sort_copy :
  forall (xs ys : list Z) left middle right,
    Zlength xs = Zlength ys ->
    0 <= left <= middle ->
    middle <= right ->
    right <= Zlength xs ->
    combine (sublist left right xs) (sublist left right ys) =
      combine (sublist left middle xs) (sublist left middle ys) ++
      combine (sublist middle right xs) (sublist middle right ys).
Proof.
  intros xs ys left middle right Hlen Hleft Hmiddle Hright.
  rewrite (sublist_split left right middle xs) by lia.
  rewrite (sublist_split left right middle ys) by lia.
  rewrite combine_app.
  - reflexivity.
  - rewrite !sublist_length by lia. reflexivity.
Qed.
Lemma sort_range_after_merge_copy__sort_copy :
  forall before_h before_i mid_h mid_i work_h work_i
         buffer0_h buffer0_i buffer_h buffer_i out_h out_i
         left middle right,
    Zlength out_h = Zlength before_h ->
    Zlength out_i = Zlength before_i ->
    Zlength buffer_h = Zlength out_h ->
    Zlength buffer_i = Zlength out_i ->
    HeightIndexRangeSortResultNLogN
      before_h before_i mid_h mid_i left middle ->
    HeightIndexRangeSortResultNLogN
      mid_h mid_i work_h work_i middle right ->
    HeightIndexRangeMergeResultNLogN
      work_h work_i buffer0_h buffer0_i buffer_h buffer_i
      left middle right ->
    CopyHeightIndexPrefixNLogN
      buffer_h buffer_i work_h work_i out_h out_i left right right ->
    0 <= left /\ left <= middle /\ middle <= right /\ right <= Zlength before_h ->
    HeightIndexRangeSortResultNLogN
      before_h before_i out_h out_i left right.
Proof.
  intros before_h before_i mid_h mid_i work_h work_i
    buffer0_h buffer0_i buffer_h buffer_i out_h out_i
    left middle right HoutH HoutI HBufferH HBufferI
    Hleft Hright Hmerge Hcopy Hbounds.
  destruct Hbounds as [Hleft0 [HleftMiddle [HmiddleRight HrightBefore]]].
  destruct Hleft as
    [HbeforeLen [HmidLen [HoutsideLeft [HpermLeft HdescLeft]]]].
  try rewrite SameHeightIndexOutsideNLogN_unfold in HoutsideLeft.
  destruct HoutsideLeft as [HmidHLen [HmidILen HoutsideLeft]].
  destruct Hright as
    [HmidLen' [HworkLen [HoutsideRight [HpermRight HdescRight]]]].
  try rewrite SameHeightIndexOutsideNLogN_unfold in HoutsideRight.
  destruct HoutsideRight as [HworkHLen [HworkILen HoutsideRight]].
  destruct Hmerge as
    [HoutsideMerge [HpermMerge HdescMerge]].
  rewrite CopyHeightIndexPrefixNLogN_unfold in Hcopy.
  destruct Hcopy as [HcopyInside HcopyOutside].


  assert (HrightOut : right <= Zlength out_h) by lia.
  assert (HrightOutI : right <= Zlength out_i) by lia.

  assert (HoutBufferH :
    sublist left right out_h = sublist left right buffer_h).
  {
    eapply sublist_eq_by_Znth__sort_copy with (d := 0).
    - lia.
    - lia.
    - exact HrightOut.
    - intros p Hp. apply (proj1 (HcopyInside p Hp)).
  }
  assert (HOutBufferI :
    sublist left right out_i = sublist left right buffer_i).
  {
    eapply sublist_eq_by_Znth__sort_copy with (d := 0).
    - lia.
    - lia.
    - exact HrightOutI.
    - intros p Hp. apply (proj2 (HcopyInside p Hp)).
  }

  assert (HworkMidLeftH :
    sublist left middle work_h = sublist left middle mid_h).
  {
    eapply sublist_eq_by_Znth__sort_copy with (d := 0).
    - exact HworkHLen.
    - lia.
    - lia.
    - intros p Hp.
      destruct (HoutsideRight p ltac:(lia) ltac:(lia)) as [HH _].
      exact HH.
  }
  assert (HworkMidLeftI :
    sublist left middle work_i = sublist left middle mid_i).
  {
    eapply sublist_eq_by_Znth__sort_copy with (d := 0).
    - exact HworkILen.
    - lia.
    - lia.
    - intros p Hp.
      destruct (HoutsideRight p ltac:(lia) ltac:(lia)) as [_ HI].
      exact HI.
  }
  assert (HmidBeforeRightH :
    sublist middle right mid_h = sublist middle right before_h).
  {
    eapply sublist_eq_by_Znth__sort_copy with (d := 0).
    - exact HmidHLen.
    - lia.
    - lia.
    - intros p Hp.
      destruct (HoutsideLeft p ltac:(lia) ltac:(lia)) as [HH _].
      exact HH.
  }
  assert (HmidBeforeRightI :
    sublist middle right mid_i = sublist middle right before_i).
  {
    eapply sublist_eq_by_Znth__sort_copy with (d := 0).
    - exact HmidILen.
    - lia.
    - lia.
    - intros p Hp.
      destruct (HoutsideLeft p ltac:(lia) ltac:(lia)) as [_ HI].
      exact HI.
  }

  assert (HworkBeforePerm :
    Permutation
      (combine (sublist left right work_h) (sublist left right work_i))
      (combine (sublist left right before_h) (sublist left right before_i))).
  {
    rewrite (combine_sublist_split__sort_copy
      work_h work_i left middle right) by lia.
    rewrite (combine_sublist_split__sort_copy
      before_h before_i left middle right) by lia.
    apply Permutation_app.
    - rewrite HworkMidLeftH, HworkMidLeftI. exact HpermLeft.
    - rewrite <- HmidBeforeRightH, <- HmidBeforeRightI. exact HpermRight.
  }

  pose proof HdescMerge as HdMono.

  unfold HeightIndexRangeSortResultNLogN,
    HeightIndexRangePermutationNLogN, HeightIndexRangeDescendingNLogN.
  rewrite SameHeightIndexOutsideNLogN_unfold.
  split; [exact HbeforeLen |].
  split; [lia |].
  split.
  - split; [exact HoutH |].
    split; [exact HoutI |].
    intros p Hp Houtside.
    assert (HpWork : 0 <= p < Zlength work_h) by lia.
    specialize (HcopyOutside p HpWork Houtside).
    assert (HoutsideR : p < middle \/ right <= p) by lia.
    specialize (HoutsideRight p ltac:(lia) HoutsideR).
    assert (HoutsideL : p < left \/ middle <= p) by lia.
    specialize (HoutsideLeft p Hp HoutsideL).
    destruct HcopyOutside as [HcopyH HcopyI].
    try rewrite SameHeightIndexOutsideNLogN_unfold in HoutsideRight.
    destruct HoutsideRight as [HrightH HrightI].
    try rewrite SameHeightIndexOutsideNLogN_unfold in HoutsideLeft.
    destruct HoutsideLeft as [HleftH HleftI].
    split; congruence.
  - split.
    + rewrite HoutBufferH, HOutBufferI.
      eapply Permutation_trans; eauto.
    + intros p q Hp Hpq Hq.
      destruct (HcopyInside p ltac:(lia)) as [HpH HpI].
      destruct (HcopyInside q ltac:(lia)) as [HqH HqI].
      rewrite HpH, HqH.
      apply HdMono; lia.
Qed.
Lemma workspace_prefix_snoc__max_init :
  forall l heights indices k,
    Zlength heights = k ->
    Zlength indices = k ->
    WorkspacePrefixNLogN l heights indices k ->
    0 <= k < Zlength l ->
    Zlength (heights ++ [Znth k l 0]) = k + 1 /\
    Zlength (indices ++ [k]) = k + 1 /\
    WorkspacePrefixNLogN
      l (heights ++ [Znth k l 0]) (indices ++ [k]) (k + 1).
Proof.
  intros l heights indices k Hlen_h Hlen_i Hprefix Hk.
  assert (Hnat_h : length heights = Z.to_nat k).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    exact Hlen_h.
  }
  assert (Hnat_i : length indices = Z.to_nat k).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    exact Hlen_i.
  }
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + rewrite WorkspacePrefixNLogN_unfold in Hprefix.
    destruct Hprefix as [Hheights Hindices].
      rewrite WorkspacePrefixNLogN_unfold.
      split.
      * intros p Hp.
        destruct (Z_lt_ge_dec p k) as [Hpk | Hpk].
        -- unfold Znth at 1.
           rewrite app_nth1.
           ++ apply Hheights. lia.
           ++ rewrite Hnat_h.
              apply (proj1 (Z2Nat.inj_lt p k ltac:(lia) ltac:(lia))).
              lia.
        -- assert (p = k) by lia. subst p.
           unfold Znth at 1.
           rewrite app_nth2 by lia.
           replace (Z.to_nat k - length heights)%nat with O by lia.
           reflexivity.
      * intros p Hp.
        destruct (Z_lt_ge_dec p k) as [Hpk | Hpk].
        -- unfold Znth at 1.
           rewrite app_nth1.
           ++ apply Hindices. lia.
           ++ rewrite Hnat_i.
              apply (proj1 (Z2Nat.inj_lt p k ltac:(lia) ltac:(lia))).
              lia.
        -- assert (p = k) by lia. subst p.
           unfold Znth at 1.
           rewrite app_nth2 by lia.
           replace (Z.to_nat k - length indices)%nat with O by lia.
           reflexivity.
Qed.
Lemma sorted_index_bounds__max_init :
  forall l heights indices k,
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    0 <= k < Zlength l ->
    0 <= Znth k indices 0 < Zlength l.
Proof.
  intros l heights indices k Hworkspace Hk.
  destruct Hworkspace as [[Hlen_h [Hlen_i Hperm]] Hdescending].
  assert (Hnat_len : length heights = length indices).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
  assert (Hknat : (Z.to_nat k < length heights)%nat).
  {
    rewrite <- (Nat2Z.id (length heights)).
    apply (proj1
      (Z2Nat.inj_lt k (Z.of_nat (length heights))
        ltac:(lia) ltac:(lia))).
    rewrite <- Zlength_correct.
    lia.
  }
  assert (Hin_pair :
    In (Znth k heights 0, Znth k indices 0)
       (combine heights indices)).
  {
    unfold Znth.
    rewrite <- (combine_nth heights indices (Z.to_nat k) 0 0 Hnat_len).
    apply nth_In.
    rewrite length_combine, <- Hnat_len, Nat.min_id.
    exact Hknat.
  }
  assert (Hin_indexed :
    In (Znth k heights 0, Znth k indices 0)
       (IndexedHeightsNLogN l)).
  { eapply Permutation_in; [exact Hperm | exact Hin_pair]. }
  rewrite IndexedHeightsNLogN_legacy in Hin_indexed.
  apply in_map_iff in Hin_indexed.
  destruct Hin_indexed as [m [Hpair Hm]].
  apply in_seq in Hm.
  inversion Hpair; subst.
  rewrite Zlength_correct. lia.
Qed.
Lemma workspace_prefix_complete__max_sort_boundary :
  forall l heights indices k heightSize,
    k >= heightSize ->
    k <= heightSize ->
    Zlength heights = k ->
    Zlength indices = k ->
    WorkspacePrefixNLogN l heights indices k ->
    Zlength heights = heightSize /\
    Zlength indices = heightSize /\
    WorkspacePrefixNLogN l heights indices heightSize.
Proof.
  intros l heights indices k heightSize Hlower Hupper
    Hheight_len Hindex_len Hprefix.
  assert (Hk : k = heightSize) by lia.
  rewrite <- Hk.
  split; [exact Hheight_len |].
  split; [exact Hindex_len | exact Hprefix].
Qed.
Lemma workspace_prefix_indexed__max_loop_setup :
  forall l heights indices n,
    Zlength l = n ->
    Zlength heights = n ->
    Zlength indices = n ->
    WorkspacePrefixNLogN l heights indices n ->
    combine heights indices = IndexedHeightsNLogN l.
Proof.
  intros l heights indices n Hl Hh Hi Hprefix.
  rewrite WorkspacePrefixNLogN_unfold in Hprefix.
    destruct Hprefix as [Hheights Hindices].
  assert (Hlen_h : length heights = length l).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
  assert (Hlen_i : length indices = length l).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
  rewrite IndexedHeightsNLogN_legacy.
  apply List.nth_ext with
      (d := (0, 0)) (d' := (nth 0 l 0, 0)).
  - rewrite length_combine, length_map, length_seq.
    rewrite Hlen_h, Hlen_i, Nat.min_id. reflexivity.
  - intros k Hk.
    assert (Hk_l : (k < length l)%nat).
    {
      rewrite length_combine, Hlen_h, Hlen_i, Nat.min_id in Hk.
      exact Hk.
    }
    rewrite combine_nth by lia.
    match goal with
    | |- _ = ?rhs =>
        replace rhs with
          ((fun k0 : nat => (nth k0 l 0, Z.of_nat k0))
             (nth k (seq Nat.zero (length l)) Nat.zero))
    end.
    2: {
      symmetry.
      transitivity
        (nth k
          (map (fun k0 : nat => (nth k0 l 0, Z.of_nat k0))
               (seq Nat.zero (length l)))
          (nth Nat.zero l 0, Z.of_nat Nat.zero)).
      - apply nth_indep. rewrite length_map, length_seq. exact Hk_l.
      - apply (@map_nth nat (Z * Z)
          (fun k0 : nat => (nth k0 l 0, Z.of_nat k0))).
    }
    rewrite seq_nth by exact Hk_l.
    specialize (Hheights (Z.of_nat k) ltac:(rewrite Zlength_correct in Hl; lia)).
    specialize (Hindices (Z.of_nat k) ltac:(rewrite Zlength_correct in Hl; lia)).
    unfold Znth in Hheights, Hindices.
    replace (Z.to_nat (Z.of_nat k)) with k in Hheights by lia.
    replace (Z.to_nat (Z.of_nat k)) with k in Hindices by lia.
    simpl. f_equal; assumption.
Qed.
Lemma full_sort_workspace__max_loop_setup :
  forall l work0_h work0_i work_h work_i n,
    Zlength l = n ->
    Zlength work0_h = n ->
    Zlength work0_i = n ->
    WorkspacePrefixNLogN l work0_h work0_i n ->
    HeightIndexRangeSortResultNLogN
      work0_h work0_i work_h work_i 0 n ->
    SortedHeightIndexWorkspaceNLogN l work_h work_i.
Proof.
  intros l work0_h work0_i work_h work_i n
    Hl Hwork0_h Hwork0_i Hprefix Hsort.
  destruct Hsort as
    [Hbefore_len [Hafter_len [Houtside [Hrange_perm Hdescending]]]].
  try rewrite SameHeightIndexOutsideNLogN_unfold in Houtside.
  destruct Houtside as [Hwork_h [Hwork_i Hframe]].
  unfold HeightIndexRangePermutationNLogN in Hrange_perm.
  rewrite (sublist_self work_h n) in Hrange_perm by lia.
  rewrite (sublist_self work_i n) in Hrange_perm by lia.
  rewrite (sublist_self work0_h n) in Hrange_perm by lia.
  rewrite (sublist_self work0_i n) in Hrange_perm by lia.
  pose proof
    (workspace_prefix_indexed__max_loop_setup
      l work0_h work0_i n Hl Hwork0_h Hwork0_i Hprefix) as Hindexed.
  rewrite Hindexed in Hrange_perm.
  unfold SortedHeightIndexWorkspaceNLogN.
  split.
  - unfold HeightIndexPermutationNLogN.
    split; [lia |].
    split; [lia | exact Hrange_perm].
  - replace (Zlength work_h) with n by lia.
    exact Hdescending.
Qed.
Lemma sorted_workspace_lookup__max_loop_setup :
  forall l sorted_h sorted_i k,
    SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ->
    0 <= k < Zlength l ->
    0 <= Znth k sorted_i 0 < Zlength l /\
    Znth k sorted_h 0 = Znth (Znth k sorted_i 0) l 0.
Proof.
  intros l sorted_h sorted_i k Hworkspace Hk.
  destruct Hworkspace as [Hperm Hdescending].
  destruct Hperm as [Hlen_h [Hlen_i Hperm]].
  assert (Hnat_len : length sorted_h = length sorted_i).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
  assert (Hin_pair :
    In (Znth k sorted_h 0, Znth k sorted_i 0)
       (combine sorted_h sorted_i)).
  {
    unfold Znth.
    rewrite <- (combine_nth sorted_h sorted_i (Z.to_nat k) 0 0 Hnat_len).
    apply nth_In.
    rewrite length_combine, Hnat_len, Nat.min_id.
    rewrite !Zlength_correct in Hlen_h, Hk.
    rewrite <- (Nat2Z.id (length sorted_i)).
    apply (proj1
      (Z2Nat.inj_lt k (Z.of_nat (length sorted_i))
        ltac:(lia) ltac:(lia))).
    rewrite <- Hnat_len, Hlen_h.
    rewrite Zlength_correct.
    exact (proj2 Hk).
  }
  assert (Hin_indexed :
    In (Znth k sorted_h 0, Znth k sorted_i 0)
       (IndexedHeightsNLogN l)).
  { eapply Permutation_in; [exact Hperm | exact Hin_pair]. }
  rewrite IndexedHeightsNLogN_legacy in Hin_indexed.
  apply in_map_iff in Hin_indexed.
  destruct Hin_indexed as [m [Hpair Hm]].
  apply in_seq in Hm.
  inversion Hpair; subst.
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma processed_maximum_initial__max_loop_setup :
  forall l indices,
    1 <= Zlength indices ->
    ProcessedContainerMaximumNLogN l indices 1 0.
Proof.
  intros l indices Hlen.
  unfold ProcessedContainerMaximumNLogN.
  apply max_default_default.
  intros [i j] Hpair.
  unfold ProcessedContainerPairNLogN in Hpair.
  destruct Hpair as [Hcontainer [Hi Hj]].
  unfold ContainerPairNLogN in Hcontainer.
  replace 1 with (0 + 1) in Hi by lia.
  replace 1 with (0 + 1) in Hj by lia.
  rewrite (sublist_single 0 0 indices) in Hi by lia.
  rewrite (sublist_single 0 0 indices) in Hj by lia.
  destruct Hi as [Hi | Hi]; [| contradiction].
  destruct Hj as [Hj | Hj]; [| contradiction].
  destruct Hcontainer as [_ [Hij _]].
  inversion Hi. inversion Hj. subst.
  lia.
Qed.
Lemma processed_endpoint_bounds__max_width_selection :
  forall indices k minimum maximum n,
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    (forall p, 0 <= p < k -> 0 <= Znth p indices 0 < n) ->
    0 <= minimum /\ minimum <= maximum /\ maximum < n.
Proof.
  intros indices k minimum maximum n Hendpoints Hindex_bounds.
  rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  destruct Hendpoints as [[p [Hp Hminimum]]
    [[q [Hq Hmaximum]] Hordered]].
  pose proof (Hindex_bounds p Hp) as Hp_bound.
  pose proof (Hindex_bounds q Hq) as Hq_bound.
  pose proof (Hordered p Hp) as Hp_ordered.
  pose proof (Hordered q Hq) as Hq_ordered.
  lia.
Qed.
Lemma sorted_workspace_lookup__max_width_selection :
  forall l heights indices k,
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    0 <= k < Zlength l ->
    0 <= Znth k indices 0 < Zlength l /\
    Znth k heights 0 = Znth (Znth k indices 0) l 0.
Proof.
  intros l heights indices k Hsorted Hk.
  unfold SortedHeightIndexWorkspaceNLogN in Hsorted.
  destruct Hsorted as [[Hheights [Hindices Hperm]] Hdescending].
  assert (Hsame : length heights = length indices).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
  assert (Hk_indices : 0 <= k < Zlength indices) by lia.
  assert (Hpair_in :
    In (Znth k heights 0, Znth k indices 0) (combine heights indices)).
  {
    unfold Znth.
    assert (Hin : In
      (nth (Z.to_nat k) (combine heights indices) (0, 0))
      (combine heights indices)).
    {
      apply nth_In.
      rewrite length_combine, Hsame, Nat.min_id.
      rewrite Zlength_correct in Hk_indices.
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia. lia.
    }
    rewrite combine_nth in Hin by exact Hsame.
    exact Hin.
  }
  assert (Hindexed :
    In (Znth k heights 0, Znth k indices 0) (IndexedHeightsNLogN l)).
  { eapply Permutation_in; [exact Hperm | exact Hpair_in]. }
  rewrite IndexedHeightsNLogN_legacy in Hindexed.
  apply in_map_iff in Hindexed.
  destruct Hindexed as [position [Heq Hposition]].
  apply in_seq in Hposition.
  inversion Heq; subst.
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma processed_pair_extend__max_area_update_a :
  forall (l indices : list Z) (k : Z) (ij : Z * Z),
    0 <= k ->
    k < Zlength indices ->
    ProcessedContainerPairNLogN l indices (k + 1) ij <->
    ContainerPairNLogN l (fst ij) (snd ij) /\
    (In (fst ij) (sublist 0 k indices) \/ fst ij = Znth k indices 0) /\
    (In (snd ij) (sublist 0 k indices) \/ snd ij = Znth k indices 0).
Proof.
  intros l indices k ij Hk0 Hklen.
  unfold ProcessedContainerPairNLogN.
  repeat rewrite (sublist_split 0 (k + 1) k) by lia.
  repeat rewrite (sublist_single 0 k indices) by lia.
  repeat rewrite in_app_iff.
  simpl.
  firstorder.
Qed.
Lemma sorted_workspace_lookup__max_endpoint_a :
  forall (l heights indices : list Z) (q : Z),
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    0 <= q < Zlength heights ->
    0 <= Znth q indices 0 < Zlength l /\
    Znth q heights 0 = Znth (Znth q indices 0) l 0.
Proof.
  intros l heights indices q Hsorted Hq.
  destruct Hsorted as [[Hheights [Hindices Hperm]] Hdescending].
  assert (Hlengths : length heights = length indices).
  { rewrite !Zlength_correct in Hheights, Hindices. lia. }
  set (nq := Z.to_nat q).
  assert (Hnq : (nq < length heights)%nat).
  { unfold nq. rewrite Zlength_correct in Hq. lia. }
  assert (Hin_combined :
    In (nth nq heights 0, nth nq indices 0) (combine heights indices)).
  { rewrite <- (combine_nth heights indices nq 0 0 Hlengths).
    apply nth_In.
    rewrite length_combine, <- Hlengths, Nat.min_id.
    exact Hnq. }
  assert (Hin_indexed :
    In (nth nq heights 0, nth nq indices 0) (IndexedHeightsNLogN l)).
  { eapply Permutation_in; eauto. }
  rewrite IndexedHeightsNLogN_legacy in Hin_indexed.
  apply in_map_iff in Hin_indexed.
  destruct Hin_indexed as [n [Heq Hin_seq]].
  apply in_seq in Hin_seq.
  injection Heq as Hheight Hindex.
  split.
  - change (0 <= nth nq indices 0 < Zlength l)%Z.
    rewrite <- Hindex, Zlength_correct.
    lia.
  - change (nth nq heights 0 = Znth (nth nq indices 0) l 0)%Z.
    rewrite <- Hheight, <- Hindex.
    unfold Znth.
    rewrite Nat2Z.id.
    reflexivity.
Qed.
Lemma processed_endpoints_extend__max_endpoint_a :
  forall (indices : list Z) (k minimum maximum index new_min new_max : Z),
    1 <= k ->
    k < Zlength indices ->
    index = Znth k indices 0 ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ((index < minimum /\ new_min = index /\ new_max = maximum) \/
     (maximum < index /\ new_min = minimum /\ new_max = index) \/
     (minimum <= index <= maximum /\ new_min = minimum /\ new_max = maximum)) ->
    ProcessedIndexEndpointsNLogN indices (k + 1) new_min new_max.
Proof.
  intros indices k minimum maximum index new_min new_max
    Hk Hklen Hindex Hends Hcase.
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hends.
  destruct Hends as [[pmin [Hpmin Hmin]]
                     [[pmax [Hpmax Hmax]] Hall]].
  assert (Hminmax : minimum <= maximum).
  { pose proof (Hall pmin Hpmin). lia. }
  destruct Hcase as [[Hbelow [-> ->]] |
                     [[Habove [-> ->]] | [Hinside [-> ->]]]].
  - rewrite ProcessedIndexEndpointsNLogN_unfold.
    split.
    + exists k. split; [lia | symmetry; exact Hindex].
    + split.
      * exists pmax. split; [lia | exact Hmax].
      * intros p Hp.
        destruct (Z_lt_ge_dec p k) as [Hpk | Hpk].
        -- specialize (Hall p ltac:(lia)). lia.
        -- assert (p = k) by lia. subst p. rewrite <- Hindex. lia.
  - rewrite ProcessedIndexEndpointsNLogN_unfold.
    split.
    + exists pmin. split; [lia | exact Hmin].
    + split.
      * exists k. split; [lia | symmetry; exact Hindex].
      * intros p Hp.
        destruct (Z_lt_ge_dec p k) as [Hpk | Hpk].
        -- specialize (Hall p ltac:(lia)). lia.
        -- assert (p = k) by lia. subst p. rewrite <- Hindex. lia.
  - rewrite ProcessedIndexEndpointsNLogN_unfold.
    split.
    + exists pmin. split; [lia | exact Hmin].
    + split.
      * exists pmax. split; [lia | exact Hmax].
      * intros p Hp.
        destruct (Z_lt_ge_dec p k) as [Hpk | Hpk].
        -- apply Hall. lia.
        -- assert (p = k) by lia. subst p. rewrite <- Hindex. lia.
Qed.
Lemma processed_max_extend__max_endpoint_a :
  forall (l heights indices : list Z)
         (k index currentHeight minimum maximum width oldMaximum : Z),
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ProcessedContainerMaximumNLogN l indices k oldMaximum ->
    1 <= k ->
    k < Zlength l ->
    index = Znth k indices 0 ->
    currentHeight = Znth k heights 0 ->
    0 <= currentHeight ->
    ((maximum < index /\ width = index - minimum) \/
     (index < minimum /\ width = maximum - index)) ->
    ProcessedContainerMaximumNLogN l indices (k + 1)
      (Z.max oldMaximum (width * currentHeight)).
Proof.
  intros l heights indices k index currentHeight minimum maximum width oldMaximum
    Hsorted Hends Hold Hk Hklength Hindex Hcurrent Hcurrent_nonneg Hside.
  destruct Hsorted as [Hpermutation Hdescending].
  destruct Hpermutation as [Hheight_len [Hindex_len Hperm]].
  assert (Hsorted_full : SortedHeightIndexWorkspaceNLogN l heights indices).
  { split.
    - unfold HeightIndexPermutationNLogN. repeat split; assumption.
    - exact Hdescending. }
  assert (Hkheight : 0 <= k < Zlength heights) by lia.
  assert (Hkindex : 0 <= k < Zlength indices) by lia.
  assert (Hnew_lookup :=
      sorted_workspace_lookup__max_endpoint_a l heights indices k
      Hsorted_full Hkheight).
  rewrite <- Hindex, <- Hcurrent in Hnew_lookup.
  destruct Hnew_lookup as [Hindex_bounds Hcurrent_original].
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hends.
  destruct Hends as [[pmin [Hpmin Hmin]]
                     [[pmax [Hpmax Hmax]] Hall]].
  assert (Hprefix_member : forall p,
    0 <= p < k -> In (Znth p indices 0) (sublist 0 k indices)).
  { intros p Hp.
    rewrite <- (Znth_sublist0 0 p k indices) by lia.
    unfold Znth.
    apply nth_In.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    rewrite Zlength_sublist by lia.
    lia. }
  assert (Hmember_lookup : forall a,
    In a (sublist 0 k indices) ->
    exists q,
      0 <= q < k /\
      Znth q indices 0 = a /\
      0 <= a < Zlength l /\
      Znth q heights 0 = Znth a l 0).
  { intros a Ha.
    destruct (In_nth (sublist 0 k indices) a 0 Ha)
      as [n [Hn Hnth]].
    exists (Z.of_nat n).
    assert (Hqn : 0 <= Z.of_nat n < k).
    { split; [lia |].
      apply Nat2Z.inj_lt in Hn.
      rewrite <- Zlength_correct in Hn.
      rewrite Zlength_sublist in Hn by lia.
      lia. }
    assert (Hqvalue : Znth (Z.of_nat n) indices 0 = a).
    { rewrite <- (Znth_sublist0 0 (Z.of_nat n) k indices) by lia.
      unfold Znth. rewrite Nat2Z.id. exact Hnth. }
    assert (Hlookup :=
      sorted_workspace_lookup__max_endpoint_a l heights indices
        (Z.of_nat n) Hsorted_full ltac:(lia)).
    rewrite Hqvalue in Hlookup.
    destruct Hlookup as [Habounds Hheight].
    split; [exact Hqn |].
    split; [exact Hqvalue |].
    split; assumption. }
  assert (Hminimum_member : In minimum (sublist 0 k indices)).
  { rewrite <- Hmin. apply Hprefix_member. exact Hpmin. }
  assert (Hmaximum_member : In maximum (sublist 0 k indices)).
  { rewrite <- Hmax. apply Hprefix_member. exact Hpmax. }
  assert (Hminmax : minimum <= maximum).
  { pose proof (Hall pmin Hpmin). lia. }
  assert (Hcandidate_pair :
    exists ij,
      ProcessedContainerPairNLogN l indices (k + 1) ij /\
      ContainerAreaNLogN l (fst ij) (snd ij) = width * currentHeight).
  { destruct Hside as [[Habove Hwidth] | [Hbelow Hwidth]].
    - exists (minimum, index). split.
      + apply (proj2 (processed_pair_extend__max_area_update_a
          l indices k (minimum, index) ltac:(lia) ltac:(lia))).
        simpl. split.
        * destruct (Hmember_lookup minimum Hminimum_member)
            as [q [Hq [Hqvalue [Hminimum_bounds Hminimum_height]]]].
          unfold ContainerPairNLogN. lia.
        * split; [left; exact Hminimum_member | right; exact Hindex].
      + destruct (Hmember_lookup minimum Hminimum_member)
          as [q [Hq [Hqvalue [Hminimum_bounds Hminimum_height]]]].
        assert (Hheight_order : currentHeight <= Znth minimum l 0).
        { rewrite <- Hminimum_height, Hcurrent.
          apply Hdescending; lia. }
        unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
        rewrite Z.min_r by lia. lia.
    - exists (index, maximum). split.
      + apply (proj2 (processed_pair_extend__max_area_update_a
          l indices k (index, maximum) ltac:(lia) ltac:(lia))).
        simpl. split.
        * destruct (Hmember_lookup maximum Hmaximum_member)
            as [q [Hq [Hqvalue [Hmaximum_bounds Hmaximum_height]]]].
          unfold ContainerPairNLogN. lia.
        * split; [right; exact Hindex | left; exact Hmaximum_member].
      + destruct (Hmember_lookup maximum Hmaximum_member)
          as [q [Hq [Hqvalue [Hmaximum_bounds Hmaximum_height]]]].
        assert (Hheight_order : currentHeight <= Znth maximum l 0).
        { rewrite <- Hmaximum_height, Hcurrent.
          apply Hdescending; lia. }
        unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
        rewrite Z.min_l by lia. lia. }
  assert (Hnew_bound : forall ij,
    ProcessedContainerPairNLogN l indices (k + 1) ij ->
    ProcessedContainerPairNLogN l indices k ij \/
    ContainerAreaNLogN l (fst ij) (snd ij) <= width * currentHeight).
  { intros [i j] Hpair.
    apply (proj1 (processed_pair_extend__max_area_update_a
      l indices k (i, j) ltac:(lia) ltac:(lia))) in Hpair.
    simpl in Hpair.
    destruct Hpair as [Hlegal [Hi Hj]].
    destruct Hi as [Hi | Hi]; destruct Hj as [Hj | Hj].
    - left. unfold ProcessedContainerPairNLogN. simpl. tauto.
    - right. simpl in Hi, Hj. subst j.
      destruct (Hmember_lookup i Hi)
        as [q [Hq [Hqvalue [Hi_bounds Hi_height]]]].
      assert (Hheight_order : currentHeight <= Znth i l 0).
      { rewrite <- Hi_height, Hcurrent. apply Hdescending; lia. }
      unfold ContainerPairNLogN in Hlegal.
      unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
      rewrite <- Hindex.
      rewrite <- Hcurrent_original.
      rewrite Z.min_r by lia.
      destruct Hside as [[Habove Hwidth] | [Hbelow Hwidth]].
      + specialize (Hall q Hq). rewrite Hqvalue in Hall.
        apply Z.mul_le_mono_nonneg_r; lia.
      + specialize (Hall q Hq). rewrite Hqvalue in Hall. lia.
    - right. simpl in Hi, Hj. subst i.
      destruct (Hmember_lookup j Hj)
        as [q [Hq [Hqvalue [Hj_bounds Hj_height]]]].
      assert (Hheight_order : currentHeight <= Znth j l 0).
      { rewrite <- Hj_height, Hcurrent. apply Hdescending; lia. }
      unfold ContainerPairNLogN in Hlegal.
      unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
      rewrite <- Hindex.
      rewrite <- Hcurrent_original.
      rewrite Z.min_l by lia.
      destruct Hside as [[Habove Hwidth] | [Hbelow Hwidth]].
      + specialize (Hall q Hq). rewrite Hqvalue in Hall. lia.
      + specialize (Hall q Hq). rewrite Hqvalue in Hall.
        apply Z.mul_le_mono_nonneg_r; lia.
    - simpl in Hi, Hj. subst i j.
      unfold ContainerPairNLogN in Hlegal. lia. }
  destruct Hcandidate_pair as [candidate [Hcandidate_pair Hcandidate_area]].
  unfold ProcessedContainerMaximumNLogN in Hold |- *.
  destruct Hold as [[Hold_max Hold_nonneg] | [Hold_bound Hold_eq]].
  - destruct Hold_max as [old_pair [[Hold_pair Hold_bound] Hold_area]].
    destruct (Z_le_gt_dec oldMaximum (width * currentHeight)) as [Hchoose_new | Hkeep_old].
    + left. split.
      * exists candidate. split.
        -- split; [exact Hcandidate_pair |].
           intros ij Hij.
           destruct (Hnew_bound ij Hij) as [Hij_old | Hij_new].
           ++ specialize (Hold_bound ij Hij_old).
              rewrite Hcandidate_area. lia.
           ++ rewrite Hcandidate_area. exact Hij_new.
        -- rewrite Hcandidate_area, Z.max_r by lia. reflexivity.
      * rewrite Z.max_r by lia. lia.
    + left. split.
      * exists old_pair. split.
        -- split.
           ++ apply (proj2 (processed_pair_extend__max_area_update_a
                l indices k old_pair ltac:(lia) ltac:(lia))).
              destruct Hold_pair as [Hold_legal [Hold_left Hold_right]].
              split; [exact Hold_legal |].
              split; [left; exact Hold_left | left; exact Hold_right].
           ++ intros ij Hij.
              destruct (Hnew_bound ij Hij) as [Hij_old | Hij_new].
              ** specialize (Hold_bound ij Hij_old). exact Hold_bound.
              ** rewrite Hold_area. lia.
        -- rewrite Hold_area, Z.max_l by lia. reflexivity.
      * rewrite Z.max_l by lia. exact Hold_nonneg.
  - subst oldMaximum.
    left. split.
    + exists candidate. split.
      * split; [exact Hcandidate_pair |].
        intros ij Hij.
        destruct (Hnew_bound ij Hij) as [Hij_old | Hij_new].
        -- specialize (Hold_bound ij Hij_old).
           rewrite Hcandidate_area. nia.
        -- rewrite Hcandidate_area. exact Hij_new.
      * rewrite Hcandidate_area, Z.max_r by
          (destruct Hside as [[? ?] | [? ?]]; nia).
        reflexivity.
    + rewrite Z.max_r by
        (destruct Hside as [[? ?] | [? ?]]; nia).
      destruct Hside as [[? ?] | [? ?]]; nia.
Qed.
Lemma in_prefix_iff_position__max_endpoint_b :
  forall (A : Type) (l : list A) (d x : A) k,
    0 <= k <= Zlength l ->
    (In x (sublist 0 k l) <->
     exists p, 0 <= p < k /\ Znth p l d = x).
Proof.
  intros A l d x k Hk.
  split.
  - intros Hin.
    apply In_nth with (d := d) in Hin as [n [Hn Hnth]].
    assert (Hsub : Zlength (sublist 0 k l) = k).
    { rewrite Zlength_sublist by lia. lia. }
    assert (Hp : 0 <= Z.of_nat n < k).
    { rewrite Zlength_correct in Hsub. lia. }
    exists (Z.of_nat n). split; [exact Hp |].
    rewrite <- Hnth.
    replace (Z.of_nat n) with (Z.of_nat n + 0) at 1 by lia.
    rewrite <- (Znth_sublist d 0 (Z.of_nat n) k l) by lia.
    unfold Znth. rewrite Nat2Z.id. reflexivity.
  - intros [p [Hp Hpx]].
    rewrite <- Hpx.
    replace p with (p + 0) at 1 by lia.
    rewrite <- (Znth_sublist d 0 p k l) by lia.
    unfold Znth.
    apply nth_In.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    rewrite Zlength_sublist by lia.
    lia.
Qed.
Lemma sorted_workspace_lookup__max_endpoint_b :
  forall l heights indices p k,
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    0 <= p <= k ->
    k < Zlength l ->
    0 <= Znth p indices 0 < Zlength l /\
    Znth p heights 0 = Znth (Znth p indices 0) l 0 /\
    Znth k heights 0 <= Znth p heights 0.
Proof.
  intros l heights indices p k Hsorted Hpk Hk.
  pose proof Hsorted as Hsorted_copy.
  unfold SortedHeightIndexWorkspaceNLogN in Hsorted_copy.
  destruct Hsorted_copy as [Hperm Hdescending].
  unfold HeightIndexPermutationNLogN in Hperm.
  destruct Hperm as [Hheights [Hindices Hpermutation]].
  unfold HeightIndexRangeDescendingNLogN in Hdescending.
  pose proof Hdescending as Hmono.
  assert (Hpheight : p < Zlength heights) by lia.
  assert (Hlen_nat : length heights = length indices).
  { rewrite !Zlength_correct in Hheights, Hindices. lia. }
  assert (Hin_combined :
      In (Znth p heights 0, Znth p indices 0) (combine heights indices)).
  {
    replace (Znth p heights 0, Znth p indices 0)
      with (nth (Z.to_nat p) (combine heights indices) (0, 0)).
    - apply nth_In.
      rewrite length_combine, <- Hlen_nat, Nat.min_id.
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      exact Hpheight.
    - rewrite (combine_nth heights indices (Z.to_nat p) 0 0 Hlen_nat).
      unfold Znth. reflexivity.
  }
  assert (Hin_indexed :
      In (Znth p heights 0, Znth p indices 0) (IndexedHeightsNLogN l)).
  { eapply Permutation_in; eauto. }
  rewrite IndexedHeightsNLogN_legacy in Hin_indexed.
  apply in_map_iff in Hin_indexed.
  destruct Hin_indexed as [n [Heq Hn]].
  apply in_seq in Hn.
  injection Heq as Hheight Hindex.
  split.
  - rewrite <- Hindex, Zlength_correct. lia.
  - split.
    + rewrite <- Hheight, <- Hindex.
      unfold Znth. rewrite Nat2Z.id. reflexivity.
    + apply Hmono; lia.
Qed.
Lemma processed_endpoints_extend__max_endpoint_b :
  forall indices k minimum maximum,
    0 <= k ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ProcessedIndexEndpointsNLogN indices (k + 1)
      (Z.min minimum (Znth k indices 0))
      (Z.max maximum (Znth k indices 0)).
Proof.
  intros indices k minimum maximum Hk Hendpoints.
  rewrite ProcessedIndexEndpointsNLogN_unfold in *.
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  destruct Hendpoints as
      [[pmin [Hpmin Hmin]] [[pmax [Hpmax Hmax]] Hall]].
  destruct (Z_le_gt_dec minimum (Znth k indices 0)) as [Hminle | Hminlt];
  destruct (Z_le_gt_dec maximum (Znth k indices 0)) as [Hmaxle | Hmaxlt].
  - rewrite Z.min_l by lia. rewrite Z.max_r by lia.
    split.
    + exists pmin. lia.
    + split.
      * exists k. lia.
      * intros p Hp. destruct (Z.eq_dec p k) as [-> | Hneq].
        -- lia.
        -- specialize (Hall p ltac:(lia)). lia.
  - rewrite Z.min_l by lia. rewrite Z.max_l by lia.
    split.
    + exists pmin. lia.
    + split.
      * exists pmax. lia.
      * intros p Hp. destruct (Z.eq_dec p k) as [-> | Hneq].
        -- lia.
        -- specialize (Hall p ltac:(lia)). lia.
  - rewrite Z.min_r by lia. rewrite Z.max_r by lia.
    split.
    + exists k. lia.
    + split.
      * exists k. lia.
      * intros p Hp. destruct (Z.eq_dec p k) as [-> | Hneq].
        -- lia.
        -- specialize (Hall p ltac:(lia)). lia.
  - rewrite Z.min_r by lia. rewrite Z.max_l by lia.
    split.
    + exists k. lia.
    + split.
      * exists pmax. lia.
      * intros p Hp. destruct (Z.eq_dec p k) as [-> | Hneq].
        -- lia.
        -- specialize (Hall p ltac:(lia)). lia.
Qed.
Lemma processed_max_extend__max_endpoint_b :
  forall l heights indices k index currentHeight minimum maximum old width,
    1 <= k ->
    k < Zlength l ->
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ProcessedContainerMaximumNLogN l indices k old ->
    index = Znth k indices 0 ->
    currentHeight = Znth k heights 0 ->
    currentHeight = Znth index l 0 ->
    0 <= currentHeight ->
    0 <= width ->
    (forall x, minimum <= x <= maximum -> Z.abs (x - index) <= width) ->
    (width = Z.abs (minimum - index) \/
     width = Z.abs (maximum - index)) ->
    ProcessedContainerMaximumNLogN l indices (k + 1)
      (Z.max old (width * currentHeight)).
Proof.
  intros l heights indices k index currentHeight minimum maximum old width
    Hkpos Hklen Hsorted Hendpoints Hold Hindex Hheight Hcurrent
    Hcurrent_nonneg Hwidth_nonneg Hwidth_bound Hwidth_attained.
  pose proof Hsorted as Hsorted_lengths.
  unfold SortedHeightIndexWorkspaceNLogN in Hsorted_lengths.
  destruct Hsorted_lengths as [Hperm _].
  unfold HeightIndexPermutationNLogN in Hperm.
  destruct Hperm as [Hheights_len [Hindices_len _]].
  assert (Hkindices : 0 <= k < Zlength indices) by lia.
  assert (Hold_nonneg : 0 <= old).
  {
    unfold ProcessedContainerMaximumNLogN,
      max_value_of_subset_with_default in Hold.
    destruct Hold as [[_ Hnonneg] | [_ Heq]]; lia.
  }
  assert (Hold_bound :
      forall ij, ProcessedContainerPairNLogN l indices k ij ->
        ContainerAreaNLogN l (fst ij) (snd ij) <= old).
  {
    intros ij Hij.
    unfold ProcessedContainerMaximumNLogN,
      max_value_of_subset_with_default in Hold.
    destruct Hold as
        [[Hmaximum _] | [Hall Heq]].
    - destruct Hmaximum as [best [[_ Hbest] Hbest_value]].
      rewrite <- Hbest_value. apply Hbest. exact Hij.
    - subst old. apply Hall. exact Hij.
  }
  assert (Hnew_class :
      forall ij, ProcessedContainerPairNLogN l indices (k + 1) ij ->
        ProcessedContainerPairNLogN l indices k ij \/
        ContainerAreaNLogN l (fst ij) (snd ij) <=
          width * currentHeight).
  {
    intros [a b] Hpair.
    apply (proj1 (processed_pair_extend__max_area_update_a
      l indices k (a, b) ltac:(lia) ltac:(lia))) in Hpair.
    simpl in Hpair.
    destruct Hpair as [Hlegal [[Ha | Ha] [Hb | Hb]]].
    - left. unfold ProcessedContainerPairNLogN. simpl. tauto.
    - right. subst b.
      apply (proj1 (in_prefix_iff_position__max_endpoint_b
        Z indices 0 a k ltac:(lia))) in Ha.
      destruct Ha as [p [Hp Hpa]].
      pose proof (sorted_workspace_lookup__max_endpoint_b
        l heights indices p k Hsorted ltac:(lia) Hklen)
        as [Ha_bounds [Ha_height Hheight_order]].
      rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
      try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
      destruct Hendpoints as [_ [_ Hall]].
      specialize (Hall p Hp).
      rewrite Hpa in Ha_bounds, Ha_height, Hall.
      specialize (Hwidth_bound a Hall).
      unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
      rewrite <- Hindex.
      rewrite <- Hcurrent, <- Ha_height.
      rewrite Z.min_r by (rewrite Hheight; exact Hheight_order).
      rewrite Z.abs_neq in Hwidth_bound by (unfold ContainerPairNLogN in Hlegal; lia).
      unfold ContainerPairNLogN in Hlegal. nia.
    - right. subst a.
      apply (proj1 (in_prefix_iff_position__max_endpoint_b
        Z indices 0 b k ltac:(lia))) in Hb.
      destruct Hb as [p [Hp Hpb]].
      pose proof (sorted_workspace_lookup__max_endpoint_b
        l heights indices p k Hsorted ltac:(lia) Hklen)
        as [Hb_bounds [Hb_height Hheight_order]].
      rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
      try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
      destruct Hendpoints as [_ [_ Hall]].
      specialize (Hall p Hp).
      rewrite Hpb in Hb_bounds, Hb_height, Hall.
      specialize (Hwidth_bound b Hall).
      unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
      rewrite <- Hindex.
      rewrite <- Hcurrent, <- Hb_height.
      rewrite Z.min_l by (rewrite Hheight; exact Hheight_order).
      rewrite Z.abs_eq in Hwidth_bound by (unfold ContainerPairNLogN in Hlegal; lia).
      unfold ContainerPairNLogN in Hlegal. nia.
    - subst a b. unfold ContainerPairNLogN in Hlegal. lia.
  }
  destruct (Z_le_gt_dec (width * currentHeight) old) as [Hretain | Hreplace].
  - rewrite Z.max_l by exact Hretain.
    unfold ProcessedContainerMaximumNLogN,
      max_value_of_subset_with_default in *.
    destruct Hold as [[Hmaximum Hdefault] | [Hall Heq]].
    + left. split; [| exact Hdefault].
      destruct Hmaximum as [best [[Hbest_member Hbest_bound] Hbest_value]].
      exists best. split.
      * split.
        -- unfold ProcessedContainerPairNLogN in *.
           destruct Hbest_member as [Hlegal [Hfst Hsnd]].
           split; [exact Hlegal |].
           split.
           ++ rewrite (sublist_split 0 (k + 1) k) by lia.
              apply in_or_app. left. exact Hfst.
           ++ rewrite (sublist_split 0 (k + 1) k) by lia.
              apply in_or_app. left. exact Hsnd.
        -- intros ij Hij. specialize (Hnew_class ij Hij).
           destruct Hnew_class as [Hold_pair | Hnew_area].
           ++ specialize (Hbest_bound ij Hold_pair).
              exact Hbest_bound.
           ++ rewrite Hbest_value. lia.
      * exact Hbest_value.
    + right. split; [| exact Heq].
      intros ij Hij. specialize (Hnew_class ij Hij).
      destruct Hnew_class as [Hold_pair | Hnew_area].
      * apply Hall. exact Hold_pair.
      * lia.
  - rewrite Z.max_r by lia.
    assert (Hcandidate :
        exists ij,
          ProcessedContainerPairNLogN l indices (k + 1) ij /\
          ContainerAreaNLogN l (fst ij) (snd ij) =
            width * currentHeight).
    {
      rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
      try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
      destruct Hendpoints as
          [[pmin [Hpmin Hmin]] [[pmax [Hpmax Hmax]] Hall]].
      destruct Hwidth_attained as [Hattain | Hattain].
      - assert (Hmin_in : In minimum (sublist 0 k indices)).
        { apply (proj2 (in_prefix_iff_position__max_endpoint_b
            Z indices 0 minimum k ltac:(lia))). eauto. }
        pose proof (sorted_workspace_lookup__max_endpoint_b
          l heights indices pmin k Hsorted ltac:(lia) Hklen)
          as [Hmin_bounds [Hmin_height Hmin_order]].
        rewrite Hmin in Hmin_bounds, Hmin_height.
        pose proof (sorted_workspace_lookup__max_endpoint_b
          l heights indices k k Hsorted ltac:(lia) Hklen)
          as [Hindex_bounds _].
        rewrite <- Hindex in Hindex_bounds.
        assert (Hdistinct : minimum <> index).
        { intros ->. rewrite Z.sub_diag, Z.abs_0 in Hattain.
          subst width. nia. }
        destruct (Z_lt_le_dec minimum index) as [Hlt | Hgt];
          [| assert (index < minimum) by lia].
        + exists (minimum, index). split.
          * apply (proj2 (processed_pair_extend__max_area_update_a
              l indices k (minimum, index) ltac:(lia) ltac:(lia))).
            simpl. split.
            -- unfold ContainerPairNLogN. lia.
            -- split; [left; exact Hmin_in | right; exact Hindex].
          * unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
            rewrite <- Hcurrent, <- Hmin_height.
            rewrite Z.min_r by (rewrite Hheight; exact Hmin_order).
            rewrite Z.abs_neq in Hattain by lia. nia.
        + exists (index, minimum). split.
          * apply (proj2 (processed_pair_extend__max_area_update_a
              l indices k (index, minimum) ltac:(lia) ltac:(lia))).
            simpl. split.
            -- unfold ContainerPairNLogN. lia.
            -- split; [right; exact Hindex | left; exact Hmin_in].
          * unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
            rewrite <- Hcurrent, <- Hmin_height.
            rewrite Z.min_l by (rewrite Hheight; exact Hmin_order).
            rewrite Z.abs_eq in Hattain by lia. nia.
      - assert (Hmax_in : In maximum (sublist 0 k indices)).
        { apply (proj2 (in_prefix_iff_position__max_endpoint_b
            Z indices 0 maximum k ltac:(lia))). eauto. }
        pose proof (sorted_workspace_lookup__max_endpoint_b
          l heights indices pmax k Hsorted ltac:(lia) Hklen)
          as [Hmax_bounds [Hmax_height Hmax_order]].
        rewrite Hmax in Hmax_bounds, Hmax_height.
        pose proof (sorted_workspace_lookup__max_endpoint_b
          l heights indices k k Hsorted ltac:(lia) Hklen)
          as [Hindex_bounds _].
        rewrite <- Hindex in Hindex_bounds.
        assert (Hdistinct : maximum <> index).
        { intros ->. rewrite Z.sub_diag, Z.abs_0 in Hattain.
          subst width. nia. }
        destruct (Z_lt_le_dec maximum index) as [Hlt | Hgt];
          [| assert (index < maximum) by lia].
        + exists (maximum, index). split.
          * apply (proj2 (processed_pair_extend__max_area_update_a
              l indices k (maximum, index) ltac:(lia) ltac:(lia))).
            simpl. split.
            -- unfold ContainerPairNLogN. lia.
            -- split; [left; exact Hmax_in | right; exact Hindex].
          * unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
            rewrite <- Hcurrent, <- Hmax_height.
            rewrite Z.min_r by (rewrite Hheight; exact Hmax_order).
            rewrite Z.abs_neq in Hattain by lia. nia.
        + exists (index, maximum). split.
          * apply (proj2 (processed_pair_extend__max_area_update_a
              l indices k (index, maximum) ltac:(lia) ltac:(lia))).
            simpl. split.
            -- unfold ContainerPairNLogN. lia.
            -- split; [right; exact Hindex | left; exact Hmax_in].
          * unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
            rewrite <- Hcurrent, <- Hmax_height.
            rewrite Z.min_l by (rewrite Hheight; exact Hmax_order).
            rewrite Z.abs_eq in Hattain by lia. nia.
    }
    unfold ProcessedContainerMaximumNLogN,
      max_value_of_subset_with_default.
    left. split; [| nia].
    destruct Hcandidate as [candidate [Hcandidate_member Hcandidate_area]].
    exists candidate. split.
    + split; [exact Hcandidate_member |].
      intros ij Hij. specialize (Hnew_class ij Hij).
      destruct Hnew_class as [Hold_pair | Hnew_area].
      * specialize (Hold_bound ij Hold_pair).
        rewrite Hcandidate_area. lia.
      * rewrite Hcandidate_area. exact Hnew_area.
    + exact Hcandidate_area.
Qed.
Lemma map_snd_combine__max_final_result : forall (xs ys : list Z),
  Zlength xs = Zlength ys ->
  map snd (combine xs ys) = ys.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys; [reflexivity |].
    rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma sorted_workspace_lookup__max_endpoint_c :
  forall l heights indices,
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    NoDup indices.
Proof.
  intros l heights indices Hsorted.
  destruct Hsorted as [[Hheights [Hindices Hperm]] _].
  assert (Hsame : Zlength heights = Zlength indices) by lia.
  pose proof (Permutation_map snd Hperm) as Hmap.
  rewrite (map_snd_combine__max_final_result heights indices Hsame) in Hmap.
  rewrite IndexedHeightsNLogN_legacy in Hmap.
  rewrite map_map in Hmap. simpl in Hmap.
  apply (Permutation_NoDup (Permutation_sym Hmap)).
  apply NoDup_map_NoDup_ForallPairs.
  - unfold ForallPairs. intros a b _ _ Heq.
    apply Nat2Z.inj in Heq. exact Heq.
  - apply seq_NoDup.
Qed.
Lemma processed_endpoint_fresh__max_endpoint_c :
  forall indices k minimum maximum index,
    0 <= k ->
    k < Zlength indices ->
    NoDup indices ->
    index = Znth k indices 0 ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    index <> minimum /\ index <> maximum.
Proof.
  intros indices k minimum maximum index Hk0 Hklen Hnodup Hindex Hendpoints.
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  destruct Hendpoints as [[p [[Hp0 Hpk] Hpmin]]
                         [[q [[Hq0 Hqk] Hqmax]] _]].
  split; intro Heq.
  - assert (Hz : Znth p indices 0 = Znth k indices 0) by lia.
    unfold Znth in Hz.
    assert (Hpn : (Z.to_nat p < length indices)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia. }
    assert (Hkn : (Z.to_nat k < length indices)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia. }
    pose proof ((proj1 (NoDup_nth indices 0) Hnodup)
                  (Z.to_nat p) (Z.to_nat k) Hpn Hkn Hz) as Hnat.
    pose proof (Z2Nat.inj p k ltac:(lia) ltac:(lia) Hnat) as Hpq.
    lia.
  - assert (Hz : Znth q indices 0 = Znth k indices 0) by lia.
    unfold Znth in Hz.
    assert (Hqn : (Z.to_nat q < length indices)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia. }
    assert (Hkn : (Z.to_nat k < length indices)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia. }
    pose proof ((proj1 (NoDup_nth indices 0) Hnodup)
                  (Z.to_nat q) (Z.to_nat k) Hqn Hkn Hz) as Hnat.
    pose proof (Z2Nat.inj q k ltac:(lia) ltac:(lia) Hnat) as Hqeq.
    lia.
Qed.
Lemma processed_endpoints_extend__max_endpoint_c :
  forall l heights indices k minimum maximum index,
    0 <= k ->
    k < Zlength l ->
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    index = Znth k indices 0 ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    (index = minimum \/ index = maximum) ->
    ProcessedIndexEndpointsNLogN indices (k + 1) minimum maximum.
Proof.
  intros l heights indices k minimum maximum index
         Hk0 Hkl Hsorted Hindex Hendpoints Heq.
  pose proof (sorted_workspace_lookup__max_endpoint_c
                l heights indices Hsorted) as Hnodup.
  assert (Hklen : k < Zlength indices).
  { destruct Hsorted as [[_ [Hindices _]] _]. lia. }
  pose proof (processed_endpoint_fresh__max_endpoint_c
                indices k minimum maximum index Hk0 Hklen Hnodup
                Hindex Hendpoints) as [Hne_minimum Hne_maximum].
  destruct Heq; contradiction.
Qed.
Lemma processed_max_extend__max_endpoint_c :
  forall l heights indices k minimum maximum index oldans newans,
    0 <= k ->
    k < Zlength l ->
    SortedHeightIndexWorkspaceNLogN l heights indices ->
    index = Znth k indices 0 ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ProcessedContainerMaximumNLogN l indices k oldans ->
    (index = minimum \/ index = maximum) ->
    ProcessedContainerMaximumNLogN l indices (k + 1) newans.
Proof.
  intros l heights indices k minimum maximum index oldans newans
         Hk0 Hkl Hsorted Hindex Hendpoints _ Heq.
  pose proof (sorted_workspace_lookup__max_endpoint_c
                l heights indices Hsorted) as Hnodup.
  assert (Hklen : k < Zlength indices).
  { destruct Hsorted as [[_ [Hindices _]] _]. lia. }
  pose proof (processed_endpoint_fresh__max_endpoint_c
                indices k minimum maximum index Hk0 Hklen Hnodup
                Hindex Hendpoints) as [Hne_minimum Hne_maximum].
  destruct Heq; contradiction.
Qed.
Lemma sorted_workspace_lookup__max_endpoint_d :
  forall indices k minimum maximum x,
    0 <= k <= Zlength indices ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    In x (sublist 0 k indices) ->
    minimum <= x <= maximum.
Proof.
  intros indices k minimum maximum x Hk Hendpoints Hin.
  rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  destruct Hendpoints as [_ [_ Hall]].
  pose proof (In_nth (sublist 0 k indices) x 0 Hin) as [n [Hn Hnth]].
  rewrite sublist_length in Hn by lia.
  specialize (Hall (Z.of_nat n)).
  assert (Hp : 0 <= Z.of_nat n < k) by lia.
  specialize (Hall Hp).
  replace x with (Znth (Z.of_nat n) indices 0).
  - exact Hall.
  - rewrite <- Hnth.
    unfold Znth, sublist.
    rewrite skipn_O.
    replace (Z.to_nat (Z.of_nat n)) with n by lia.
    rewrite nth_firstn by lia.
    reflexivity.
Qed.
Lemma processed_endpoints_extend__max_endpoint_d :
  forall indices k index minimum maximum,
    0 <= k ->
    index = Znth k indices 0 ->
    minimum <= index <= maximum ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ProcessedIndexEndpointsNLogN indices (k + 1) minimum maximum.
Proof.
  intros indices k index minimum maximum Hk Hindex Hbetween Hendpoints.
  rewrite ProcessedIndexEndpointsNLogN_unfold in *.
  try rewrite ProcessedIndexEndpointsNLogN_unfold in Hendpoints.
  destruct Hendpoints as [[pmin [Hpmin Hmin]]
                           [[pmax [Hpmax Hmax]] Hall]].
  split.
  - exists pmin. split; [lia | exact Hmin].
  - split.
    + exists pmax. split; [lia | exact Hmax].
    + intros p Hp.
      destruct (Z.eq_dec p k) as [-> | Hne].
      * rewrite <- Hindex. exact Hbetween.
      * apply Hall. lia.
Qed.
Lemma processed_max_extend__max_endpoint_d :
  forall l indices k index currentHeight minimum maximum width maximumArea,
    0 <= k < Zlength indices ->
    index = Znth k indices 0 ->
    currentHeight = Znth index l 0 ->
    0 <= currentHeight ->
    0 <= width ->
    minimum <= index <= maximum ->
    index - minimum <= width ->
    maximum - index <= width ->
    ProcessedIndexEndpointsNLogN indices k minimum maximum ->
    ProcessedContainerMaximumNLogN l indices k maximumArea ->
    width * currentHeight <= maximumArea ->
    ProcessedContainerMaximumNLogN l indices (k + 1) maximumArea.
Proof.
  intros l indices k index currentHeight minimum maximum width maximumArea
    Hk Hindex Hheight Hcurrent_nonneg Hwidth_nonneg Hindex_between
    Hleft_width Hright_width Hendpoints Hmaximum Hnew_bound.
  assert (Hold_to_new :
    forall ij,
      ProcessedContainerPairNLogN l indices k ij ->
      ProcessedContainerPairNLogN l indices (k + 1) ij).
  {
    intros ij Hold.
    apply (proj2 (processed_pair_extend__max_area_update_a
      l indices k ij (proj1 Hk) (proj2 Hk))).
    unfold ProcessedContainerPairNLogN in Hold.
    destruct Hold as [Hpair [Hfst Hsnd]].
    split; [exact Hpair |].
    split; [left; exact Hfst | left; exact Hsnd].
  }
  assert (Hnew_candidate_bound :
    forall ij,
      ProcessedContainerPairNLogN l indices (k + 1) ij ->
      ProcessedContainerPairNLogN l indices k ij \/
      ContainerAreaNLogN l (fst ij) (snd ij) <= width * currentHeight).
  {
    intros [i j] Hnew.
    simpl in *.
    apply (proj1 (processed_pair_extend__max_area_update_a
      l indices k (i, j) (proj1 Hk) (proj2 Hk))) in Hnew.
    simpl in Hnew.
    destruct Hnew as [Hpair [[Hiold | Hiindex] [Hjold | Hjindex]]].
    - left. unfold ProcessedContainerPairNLogN. simpl.
      split; [exact Hpair |].
      split; assumption.
    - right.
      unfold ContainerPairNLogN in Hpair. simpl in Hpair.
      assert (Hibounds : minimum <= i <= maximum).
      { eapply sorted_workspace_lookup__max_endpoint_d; eauto; lia. }
      assert (Hj : j = index) by congruence.
      replace j with index by (symmetry; exact Hj).
      unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
      rewrite <- Hheight.
      eapply Z.le_trans.
      + apply Z.mul_le_mono_nonneg_l; [lia | apply Z.le_min_r].
      + apply Z.mul_le_mono_nonneg_r; lia.
    - right.
      unfold ContainerPairNLogN in Hpair. simpl in Hpair.
      assert (Hjbounds : minimum <= j <= maximum).
      { eapply sorted_workspace_lookup__max_endpoint_d; eauto; lia. }
      assert (Hi : i = index) by congruence.
      replace i with index by (symmetry; exact Hi).
      unfold ContainerAreaNLogN, ContainerHeightNLogN. simpl.
      rewrite <- Hheight.
      eapply Z.le_trans.
      + apply Z.mul_le_mono_nonneg_l; [lia | apply Z.le_min_l].
      + apply Z.mul_le_mono_nonneg_r; lia.
    - subst i j. unfold ContainerPairNLogN in Hpair. simpl in Hpair. lia.
  }
  unfold ProcessedContainerMaximumNLogN in *.
  unfold MaxMin.max_value_of_subset_with_default in *.
  destruct Hmaximum as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - left. split; [| exact Hdefault].
    unfold MaxMin.max_value_of_subset in *.
    destruct Hmaximum as [best [[Hbest Hupper] Hbest_value]].
    exists best. split; [| exact Hbest_value].
    split.
    + apply Hold_to_new. exact Hbest.
    + intros candidate Hcandidate.
      destruct (Hnew_candidate_bound candidate Hcandidate) as [Hold | Hnew].
      * apply Hupper. exact Hold.
      * rewrite Hbest_value. lia.
  - right. split; [| exact Hdefault].
    intros candidate Hcandidate.
    destruct (Hnew_candidate_bound candidate Hcandidate) as [Hold | Hnew].
    + apply Hall. exact Hold.
    + lia.
Qed.
Lemma original_pair_in_indexed__max_final_result : forall (l : list Z) p,
  0 <= p < Zlength l ->
  In (Znth p l 0, p) (IndexedHeightsNLogN l).
Proof.
  intros l p Hp. rewrite IndexedHeightsNLogN_legacy.
  apply in_map_iff. exists (Z.to_nat p). split.
  - unfold Znth. rewrite Z2Nat.id by lia. reflexivity.
  - apply in_seq. rewrite Zlength_correct in Hp. lia.
Qed.
Lemma original_index_in_indices__max_final_result : forall l heights indices p,
  HeightIndexPermutationNLogN l heights indices ->
  0 <= p < Zlength l ->
  In p indices.
Proof.
  intros l heights indices p Hperm Hp.
  destruct Hperm as [Hheights [Hindices Hperm]].
  assert (Hsame : Zlength heights = Zlength indices) by lia.
  assert (Horiginal : In (Znth p l 0, p) (IndexedHeightsNLogN l)).
  { apply original_pair_in_indexed__max_final_result. exact Hp. }
  assert (Hcombined : In (Znth p l 0, p) (combine heights indices)).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Horiginal]. }
  apply in_map with (f := snd) in Hcombined.
  rewrite (map_snd_combine__max_final_result heights indices Hsame) in Hcombined.
  simpl in Hcombined. exact Hcombined.
Qed.
Lemma in_sublist_full__max_final_result : forall (A : Type) (l : list A) n x,
  Zlength l = n ->
  In x l ->
  In x (sublist 0 n l).
Proof.
  intros A l n x Hn Hin. subst n.
  rewrite sublist_self by reflexivity. exact Hin.
Qed.
Lemma original_pair_processed_full__max_final_result : forall l heights indices i j,
  HeightIndexPermutationNLogN l heights indices ->
  ContainerPairNLogN l i j ->
  ProcessedContainerPairNLogN l indices (Zlength l) (i, j).
Proof.
  intros l heights indices i j Hperm Hpair.
  destruct Hperm as [Hheights [Hindices Hperm]].
  unfold ProcessedContainerPairNLogN. simpl. split; [exact Hpair |]. split.
  - apply in_sublist_full__max_final_result with (n := Zlength l).
    + exact Hindices.
    + eapply original_index_in_indices__max_final_result with
        (l := l) (heights := heights) (indices := indices) (p := i).
      * repeat split; assumption.
      * destruct Hpair as [Hi [Hij Hj]]. lia.
  - apply in_sublist_full__max_final_result with (n := Zlength l).
    + exact Hindices.
    + eapply original_index_in_indices__max_final_result with
        (l := l) (heights := heights) (indices := indices) (p := j).
      * repeat split; assumption.
      * destruct Hpair as [Hi [Hij Hj]]. lia.
Qed.
Lemma processed_full_prefix_maximum__max_final_result :
  forall l heights indices ans,
    2 <= Zlength l ->
    HeightIndexPermutationNLogN l heights indices ->
    ProcessedContainerMaximumNLogN l indices (Zlength l) ans ->
    (forall p, 0 <= p < Zlength l -> 0 <= Znth p l 0) ->
    MaximumContainerArea l ans.
Proof.
  intros l heights indices ans Hlen Hperm Hprocessed Hnonneg.
  unfold ProcessedContainerMaximumNLogN in Hprocessed.
  apply MaximumContainerArea_unfold.
  destruct Hprocessed as [[Hmaximum Hans_nonneg] | [Hall Hans]].
  - destruct Hmaximum as [[i j] [[Hmember Hbound] Harea]].
    unfold ProcessedContainerPairNLogN in Hmember. simpl in Hmember.
    destruct Hmember as [Hpair _]. simpl in Hpair, Hbound, Harea.
    destruct Hpair as [Hi [Hij Hj]].
    exists i, j. repeat split; try assumption.
    + unfold ContainerAreaNLogN in Harea. symmetry. exact Harea.
    + intros p q Hp Hpq Hq.
      specialize (Hbound (p, q)).
      assert (Hprocessed_pair :
        ProcessedContainerPairNLogN l indices (Zlength l) (p, q)).
      { eapply original_pair_processed_full__max_final_result with
          (heights := heights); [exact Hperm |].
        unfold ContainerPairNLogN. repeat split; assumption. }
      specialize (Hbound Hprocessed_pair).
      unfold ContainerAreaNLogN in Hbound, Harea. rewrite Harea in Hbound.
      exact Hbound.
  - assert (Hans0 : ans = 0) by lia. subst ans.
    exists 0, 1. repeat split; try lia.
    + assert (Hzero_pair :
        ProcessedContainerPairNLogN l indices (Zlength l) (0, 1)).
      { eapply original_pair_processed_full__max_final_result with
          (heights := heights); [exact Hperm |].
        unfold ContainerPairNLogN. lia. }
      specialize (Hall (0, 1) Hzero_pair).
      unfold ContainerAreaNLogN in Hall.
      assert (Hheight0 : 0 <= Znth 0 l 0) by (apply Hnonneg; lia).
      assert (Hheight1 : 0 <= Znth 1 l 0) by (apply Hnonneg; lia).
      assert (Hmin : 0 <= Z.min (Znth 0 l 0) (Znth 1 l 0)).
      { destruct (Z_le_gt_dec (Znth 0 l 0) (Znth 1 l 0)) as [Hle | Hgt].
        - rewrite Z.min_l by lia. exact Hheight0.
        - rewrite Z.min_r by lia. exact Hheight1. }
      unfold ContainerHeightNLogN in Hall.
      unfold ContainerHeightNLogN.
      change ((1 - 0) * Z.min (Znth 0 l 0) (Znth 1 l 0) <= 0) in Hall.
      change (0 = (1 - 0) * Z.min (Znth 0 l 0) (Znth 1 l 0)).
      rewrite Z.sub_0_r in Hall.
      rewrite Z.mul_1_l in Hall.
      rewrite Z.sub_0_r.
      rewrite Z.mul_1_l.
      apply Z.le_antisymm; [exact Hmin | exact Hall].
    + intros p q Hp Hpq Hq.
      assert (Hprocessed_pair :
        ProcessedContainerPairNLogN l indices (Zlength l) (p, q)).
      { eapply original_pair_processed_full__max_final_result with
          (heights := heights); [exact Hperm |].
        unfold ContainerPairNLogN. repeat split; assumption. }
      specialize (Hall (p, q) Hprocessed_pair).
      unfold ContainerAreaNLogN in Hall. exact Hall.
Qed.
