Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SumLib.ZRect.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition OnStreet (xs ys : list Z) (p : Z * Z) : Prop := In (fst p) xs \/ In (snd p) ys.
Definition StreetSegment (xs ys : list Z) (p q : Z * Z) : Prop :=
  (fst p = fst q /\ In (fst p) xs) \/ (snd p = snd q /\ In (snd p) ys).
(* The distance between two points when travelling in a straight line. *)
Definition Manhattan (p q : Z * Z) : Z :=
  Z.abs (fst p - fst q) + Z.abs (snd p - snd q).

(* [path] runs from [p] to [q], every step along one street. *)
Definition StreetWalk (xs ys : list Z) (p q : Z * Z) (path : list (Z * Z)) : Prop :=
  path <> [] /\
  Znth 0 path (0, 0) = p /\
  Znth (Zlength path - 1) path (0, 0) = q /\
  forall i, 0 <= i < Zlength path - 1 ->
    StreetSegment xs ys (Znth i path (0, 0)) (Znth (i + 1) path (0, 0)).

(* How far one walks along it. *)
Definition WalkLength (path : list (Z * Z)) : Z :=
  sum_range 0 (Zlength path - 2)
    (fun i => Manhattan (Znth i path (0, 0)) (Znth (i + 1) path (0, 0))).

Definition StreetDistance (xs ys : list Z) (p q : Z * Z) (d : Z) : Prop :=
  min_value_of_subset Z.le
    (fun v => exists path, StreetWalk xs ys p q path /\ v = WalkLength path)
    (fun x => x) d.
Definition Pre (xs ys : list Z) (people : list (Z * Z)) : Prop :=
  (* Stated explicitly in the P063 solver Require, so dropped here:
       2 <= Zlength xs <= 200000 /\
       2 <= Zlength ys <= 200000 /\
       2 <= Zlength people <= 300000 /\
     and the coordinate half of the clause below, whose on-a-street half stays:
       Forall (fun p => 0 <= fst p <= 1000000 /\ 0 <= snd p <= 1000000 /\ OnStreet xs ys p) people *)
  Forall (fun p => OnStreet xs ys p) people /\
  mono_inc xs /\
  mono_inc ys /\
  Znth 0 xs 0 = 0 /\
  Znth (Zlength xs - 1) xs 0 = 1000000 /\
  Znth 0 ys 0 = 0 /\
  Znth (Zlength ys - 1) ys 0 = 1000000 /\
  NoDup people.

(* A pair is inconvenient when the shortest way along the streets is strictly
   longer than going straight. *)
Definition Inconvenient (xs ys : list Z) (p q : Z * Z) : Prop :=
  exists d, StreetDistance xs ys p q d /\ d > Manhattan p q.

(* Count the unordered pairs of persons that are inconvenient. *)
Definition Spec (xs ys : list Z) (people : list (Z * Z)) (out : Z) : Prop :=
  out = #(fun ij : Z * Z =>
            0 <= fst ij < Zlength people /\
            0 <= snd ij < Zlength people /\
            fst ij < snd ij /\
            Inconvenient xs ys
              (Znth (fst ij) people (0, 0)) (Znth (snd ij) people (0, 0))).

(* Mathematical interfaces used by the normalized implementation.  They
   describe the order, the selected street strips, and the finite pair sets;
   none of them executes the C loops. *)
Definition StripIndex (streets : list Z) (v r : Z) : Prop :=
  (r = -1 /\ In v streets) \/
  (0 <= r < Zlength streets - 1 /\
   Znth r streets 0 < v < Znth (r + 1) streets 0).

Definition ItemLe (a b : Z * Z) : Prop :=
  fst a < fst b \/ (fst a = fst b /\ snd a <= snd b).

Definition ItemLe4 (g1 k1 g2 k2 : Z) : Prop :=
  g1 < g2 \/ (g1 = g2 /\ k1 <= k2).

Definition ParallelPermutation
    (groups keys groups' keys' : list Z) : Prop :=
  Permutation (combine groups keys) (combine groups' keys').

Definition ItemsIncreasing (groups keys : list Z) : Prop :=
  Zlength groups = Zlength keys /\
  forall i j, 0 <= i /\ i <= j /\ j < Zlength groups ->
    ItemLe (Znth i (combine groups keys) (0, 0))
           (Znth j (combine groups keys) (0, 0)).

Definition HeapParentsFromItems
    (groups keys : list Z) (lo hi : Z) : Prop :=
  forall child,
    1 <= child <= hi -> lo <= (child - 1) / 2 ->
    ItemLe (Znth child (combine groups keys) (0, 0))
           (Znth ((child - 1) / 2) (combine groups keys) (0, 0)).

Definition HeapOrderedExceptAtFromItems
    (groups keys : list Z) (lo hi bad : Z) : Prop :=
  forall child,
    1 <= child <= hi -> lo <= (child - 1) / 2 ->
    (child - 1) / 2 <> bad ->
    ItemLe (Znth child (combine groups keys) (0, 0))
           (Znth ((child - 1) / 2) (combine groups keys) (0, 0)).

Definition SelectedLargerChildItems
    (groups keys : list Z) (root hi child : Z) : Prop :=
  (child = 2 * root + 1 \/ child = 2 * root + 2) /\ child <= hi /\
  (2 * root + 1 <= hi ->
     ItemLe (Znth (2 * root + 1) (combine groups keys) (0, 0))
            (Znth child (combine groups keys) (0, 0))) /\
  (2 * root + 2 <= hi ->
     ItemLe (Znth (2 * root + 2) (combine groups keys) (0, 0))
            (Znth child (combine groups keys) (0, 0))).

Definition HeapSortItemsState
    (groups0 keys0 groups keys : list Z) (hi : Z) : Prop :=
  Zlength groups = Zlength groups0 /\ Zlength keys = Zlength keys0 /\
  ParallelPermutation groups0 keys0 groups keys /\
  HeapParentsFromItems groups keys 0 hi /\
  ItemsIncreasing (sublist (hi + 1) (Zlength groups) groups)
                  (sublist (hi + 1) (Zlength keys) keys) /\
  (forall p q, 0 <= p <= hi -> hi < q < Zlength groups ->
     ItemLe (Znth p (combine groups keys) (0, 0))
            (Znth q (combine groups keys) (0, 0))).

Definition PairCountPrefix (groups keys : list Z) (hi out : Z) : Prop :=
  out = #(fun ij : Z * Z =>
            0 <= fst ij < hi /\ 0 <= snd ij < hi /\ fst ij < snd ij /\
            Znth (fst ij) groups 0 = Znth (snd ij) groups 0 /\
            Znth (fst ij) keys 0 <> Znth (snd ij) keys 0).

Definition SameKeyCountRange (keys : list Z) (lo hi : Z) : Z :=
  #(fun ij : Z * Z =>
      lo <= fst ij < hi /\ lo <= snd ij < hi /\ fst ij < snd ij /\
      Znth (fst ij) keys 0 = Znth (snd ij) keys 0).

Definition CountGroupPhase
    (groups keys : list Z) (i j p total : Z) : Prop :=
  exists before,
    PairCountPrefix groups keys i before /\
    total = before + (j - i) * (j - i - 1) / 2 -
                     SameKeyCountRange keys i p.

Definition SameValueRange (l : list Z) (lo hi : Z) : Prop :=
  forall q, lo <= q < hi -> Znth q l 0 = Znth lo l 0.

Definition VerticalEntry (xs ys : list Z) (person : Z * Z)
    (group key : Z) : Prop :=
  StripIndex ys (snd person) group /\ 0 <= group /\ key = fst person.

Definition HorizontalEntry (xs ys : list Z) (person : Z * Z)
    (group key : Z) : Prop :=
  StripIndex ys (snd person) (-1) /\
  StripIndex xs (fst person) group /\ 0 <= group /\ key = snd person.

Definition EnumeratesEntries
    (Entry : (Z * Z) -> Z -> Z -> Prop)
    (people : list (Z * Z)) (done : Z) (groups keys : list Z) : Prop :=
  exists indices : list Z,
    Zlength indices = Zlength groups /\
    Zlength groups = Zlength keys /\ mono_inc indices /\
    (forall t, 0 <= t < Zlength indices ->
       0 <= Znth t indices 0 < done /\
       Entry (Znth (Znth t indices 0) people (0, 0))
             (Znth t groups 0) (Znth t keys 0)) /\
    (forall q, 0 <= q < done ->
       (exists group key,
          Entry (Znth q people (0, 0)) group key) -> In q indices).

Definition ClassifiedPrefix
    (xs ys : list Z) (people : list (Z * Z)) (done : Z)
    (vg vk hg hk : list Z) : Prop :=
  EnumeratesEntries (VerticalEntry xs ys) people done vg vk /\
  EnumeratesEntries (HorizontalEntry xs ys) people done hg hk.

Definition ClassifiedPairCounts
    (xs ys : list Z) (people : list (Z * Z))
    (vg vk hg hk : list Z) (out : Z) : Prop :=
  ClassifiedPrefix xs ys people (Zlength people) vg vk hg hk /\
  exists vertical horizontal,
    PairCountPrefix vg vk (Zlength vg) vertical /\
    PairCountPrefix hg hk (Zlength hg) horizontal /\
    out = vertical + horizontal.

Definition StreetCoordinateBounds (streets : list Z) : Prop :=
  forall i, 0 <= i < Zlength streets -> 0 <= Znth i streets 0 <= 1000000.

Definition PeopleCoordinateBounds (people : list (Z * Z)) : Prop :=
  forall i, 0 <= i < Zlength people ->
    0 <= fst (Znth i people (0, 0)) <= 1000000 /\
    0 <= snd (Znth i people (0, 0)) <= 1000000.

(* Stable boundary facts used by the normalized heap and run scans. *)
Definition SiftChildrenBelowParentItems
    (groups keys : list Z) (start hi root : Z) : Prop :=
  root = start \/
  forall child,
    (child = 2 * root + 1 \/ child = 2 * root + 2) -> child <= hi ->
    ItemLe (Znth child (combine groups keys) (0, 0))
           (Znth ((root - 1) / 2) (combine groups keys) (0, 0)).

Definition ValueRunBoundary (l : list Z) (i : Z) : Prop :=
  i = 0 \/ i = Zlength l \/
  (0 < i < Zlength l /\ Znth (i - 1) l 0 <> Znth i l 0).

Definition RangeRunBoundary (l : list Z) (lo hi p : Z) : Prop :=
  p = lo \/ p = hi \/
  (lo < p < hi /\ Znth (p - 1) l 0 <> Znth p l 0).

(* A semantic, implementation-independent correspondence for a processed prefix:
   counting the two normalized entry lists gives exactly the inconvenient pairs
   whose two people lie in that prefix. *)
Definition ClassifiedCountsCorrect
    (xs ys : list Z) (people : list (Z * Z)) (done : Z)
    (vg vk hg hk : list Z) : Prop :=
  forall vertical horizontal,
    PairCountPrefix vg vk (Zlength vg) vertical ->
    PairCountPrefix hg hk (Zlength hg) horizontal ->
    vertical + horizontal =
      #(fun ij : Z * Z =>
          0 <= fst ij < done /\
          0 <= snd ij < done /\
          fst ij < snd ij /\
          Inconvenient xs ys
            (Znth (fst ij) people (0, 0))
            (Znth (snd ij) people (0, 0))).

Lemma ClassifiedCountsCorrect_full_Spec :
  forall xs ys people vg vk hg hk vertical horizontal,
    ClassifiedCountsCorrect xs ys people (Zlength people) vg vk hg hk ->
    PairCountPrefix vg vk (Zlength vg) vertical ->
    PairCountPrefix hg hk (Zlength hg) horizontal ->
    Spec xs ys people (vertical + horizontal).
Proof.
  intros xs ys people vg vk hg hk vertical horizontal Hcorrect Hv Hh.
  unfold ClassifiedCountsCorrect in Hcorrect.
  unfold Spec.
  exact (Hcorrect vertical horizontal Hv Hh).
Qed.

(* The stable part of a heap-extraction state.  The prefix may be permuted by
   sifting, while the suffix remains sorted and above every prefix item. *)
Definition ExtractionFrameItems
    (groups keys : list Z) (split : Z) : Prop :=
  ItemsIncreasing (sublist split (Zlength groups) groups)
                  (sublist split (Zlength keys) keys) /\
  (forall p q,
      0 <= p < split -> split <= q < Zlength groups ->
      ItemLe (Znth p (combine groups keys) (0, 0))
             (Znth q (combine groups keys) (0, 0))).

(* The completed-run transition used by [count_pairs].  The supporting facts
   below deliberately expose the finite-cardinality argument in the case
   library: the generated VC can apply the final theorem directly instead of
   rebuilding the old-prefix/new-run partition. *)
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.setoid_ring.Ring.

Lemma set_card_Z_rect_filter_as_nested_sum__count_result :
  forall (xl xh yl yh : Z) (P : Z * Z -> Prop),
    #(fun p : Z * Z =>
        xl <= fst p < xh /\ yl <= snd p < yh /\ P p) =
    SumLib.Sum.sum (fun x : Z => xl <= x < xh)
      (fun x => SumLib.Sum.sum (fun y : Z => yl <= y < yh)
        (fun y => if prop_dec (P (x, y)) then 1 else 0)).
Proof.
  intros xl xh yl yh P.
  transitivity
    (@SumLib.Sum.sum (Z * Z)
      (fun p : Z * Z => xl <= fst p < xh /\ yl <= snd p < yh)
      (finite_Z_rect xl xh yl yh)
      (fun p => if prop_dec (P p) then 1 else 0)).
  - unfold set_card, SumLib.Sum.sum. simpl.
    induction (Zrect xl xh yl yh) as [|p ps IH]; simpl.
    + reflexivity.
    + destruct (prop_dec (P p)); simpl; rewrite IH; reflexivity.
  - set (f := fun x y : Z => if prop_dec (P (x, y)) then 1 else 0).
    replace (fun p : Z * Z => if prop_dec (P p) then 1 else 0)
      with (fun p : Z * Z => f (fst p) (snd p)).
    2: {
      apply functional_extensionality. intros [x y]. reflexivity.
    }
    change
      (SumLib.Sum.sum
         (fun p : Z * Z => xl <= fst p < xh /\ yl <= snd p < yh)
         (fun p => f (fst p) (snd p)) =
       SumLib.Sum.sum (fun x : Z => xl <= x < xh)
         (fun x => SumLib.Sum.sum (fun y : Z => yl <= y < yh) (f x))).
    apply sum_Z_rect_nested.
Qed.

Lemma set_card_Z_rect_partition__count_result :
  forall (xl xh yl yh : Z) (P Q : Z * Z -> Prop),
    #(fun p : Z * Z =>
        xl <= fst p < xh /\ yl <= snd p < yh /\ P p) =
    #(fun p : Z * Z =>
        xl <= fst p < xh /\ yl <= snd p < yh /\ P p /\ Q p) +
    #(fun p : Z * Z =>
        xl <= fst p < xh /\ yl <= snd p < yh /\ P p /\ ~ Q p).
Proof.
  intros xl xh yl yh P Q.
  rewrite !set_card_Z_rect_filter_as_nested_sum__count_result.
  rewrite <- SumLib.Sum.sum_add.
  apply SumLib.Sum.sum_ext. intros x Hx.
  rewrite <- SumLib.Sum.sum_add.
  apply SumLib.Sum.sum_ext. intros y Hy.
  destruct (prop_dec (P (x, y))) as [HP | HnP];
    destruct (prop_dec (Q (x, y))) as [HQ | HnQ];
    repeat match goal with
    | |- context [prop_dec ?R] => destruct (prop_dec R)
    end; try reflexivity; tauto.
Qed.

Lemma Znth_combine__count_result :
  forall {A B : Type} (xs : list A) (ys : list B) i dx dy,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (dx, dy) = (Znth i xs dx, Znth i ys dy).
Proof.
  intros A B xs. induction xs as [|x xs IH];
    intros ys i dx dy Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
      * rewrite !Znth0_cons. reflexivity.
      * rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.

Lemma ItemsIncreasing_group_monotone__count_result :
  forall groups keys x y,
    ItemsIncreasing groups keys ->
    0 <= x -> x <= y -> y < Zlength groups ->
    Znth x groups 0 <= Znth y groups 0.
Proof.
  intros groups keys x y [Hlens Hinc] Hx Hxy Hy.
  specialize (Hinc x y ltac:(lia)).
  rewrite !Znth_combine__count_result in Hinc by lia.
  unfold ItemLe in Hinc. simpl in Hinc. lia.
Qed.

Lemma ItemsIncreasing_groups_separated_at_boundary__count_result :
  forall groups keys i x y,
    ItemsIncreasing groups keys ->
    ValueRunBoundary groups i ->
    0 <= x < i -> i <= y < Zlength groups ->
    Znth x groups 0 <> Znth y groups 0.
Proof.
  intros groups keys i x y Hinc Hboundary Hx Hy.
  unfold ValueRunBoundary in Hboundary.
  destruct Hboundary as [-> | [Hiend | [Hi Hneq]]].
  - lia.
  - lia.
  - pose proof (ItemsIncreasing_group_monotone__count_result
      groups keys x (i - 1) Hinc ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft.
    pose proof (ItemsIncreasing_group_monotone__count_result
      groups keys i y Hinc ltac:(lia) ltac:(lia) ltac:(lia)) as Hright.
    pose proof (ItemsIncreasing_group_monotone__count_result
      groups keys (i - 1) i Hinc ltac:(lia) ltac:(lia) ltac:(lia)) as Hmiddle.
    lia.
Qed.

Lemma PairCountPrefix_split_completed_run__count_result :
  forall groups keys i j before,
    0 <= i < j ->
    j <= Zlength groups ->
    ItemsIncreasing groups keys ->
    ValueRunBoundary groups i ->
    SameValueRange groups i j ->
    PairCountPrefix groups keys i before ->
    before +
      #(fun ij : Z * Z =>
          i <= fst ij < j /\ i <= snd ij < j /\ fst ij < snd ij /\
          Znth (fst ij) keys 0 <> Znth (snd ij) keys 0) =
    #(fun ij : Z * Z =>
        0 <= fst ij < j /\ 0 <= snd ij < j /\ fst ij < snd ij /\
        Znth (fst ij) groups 0 = Znth (snd ij) groups 0 /\
        Znth (fst ij) keys 0 <> Znth (snd ij) keys 0).
Proof.
  intros groups keys i j before Hij Hj Hinc Hboundary Hsame Hbefore.
  unfold PairCountPrefix in Hbefore. subst before.
  rewrite !set_card_Z_rect_filter_as_nested_sum__count_result.
  set (F := fun x y : Z =>
    if prop_dec
      (x < y /\ Znth x groups 0 = Znth y groups 0 /\
       Znth x keys 0 <> Znth y keys 0)
    then 1 else 0).
  set (G := fun x y : Z =>
    if prop_dec (x < y /\ Znth x keys 0 <> Znth y keys 0)
    then 1 else 0).
  change
    (SumLib.Sum.sum (fun x : Z => 0 <= x < i)
       (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < i) (F x)) +
     SumLib.Sum.sum (fun x : Z => i <= x < j)
       (fun x => SumLib.Sum.sum (fun y : Z => i <= y < j) (G x)) =
     SumLib.Sum.sum (fun x : Z => 0 <= x < j)
       (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < j) (F x))).
  rewrite (sum_Z_range_split 0 i j) by lia.
  assert (Hold :
    SumLib.Sum.sum (fun x : Z => 0 <= x < i)
      (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < j) (F x)) =
    SumLib.Sum.sum (fun x : Z => 0 <= x < i)
      (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < i) (F x))).
  {
    apply SumLib.Sum.sum_ext. intros x Hx.
    rewrite (sum_Z_range_split 0 i j) by lia.
    assert (Hzero :
      SumLib.Sum.sum (fun y : Z => i <= y < j) (F x) = 0).
    {
      apply sum_Z_range_eq_zero. intros y Hy.
      unfold F.
      destruct (prop_dec
        (x < y /\ Znth x groups 0 = Znth y groups 0 /\
         Znth x keys 0 <> Znth y keys 0)) as [Hbad | Hnot];
        [| reflexivity].
      exfalso.
      apply (ItemsIncreasing_groups_separated_at_boundary__count_result
        groups keys i x y Hinc Hboundary); try lia.
    }
    rewrite Hzero. lia.
  }
  assert (Hnew :
    SumLib.Sum.sum (fun x : Z => i <= x < j)
      (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < j) (F x)) =
    SumLib.Sum.sum (fun x : Z => i <= x < j)
      (fun x => SumLib.Sum.sum (fun y : Z => i <= y < j) (G x))).
  {
    apply SumLib.Sum.sum_ext. intros x Hx.
    rewrite (sum_Z_range_split 0 i j) by lia.
    assert (Hzero :
      SumLib.Sum.sum (fun y : Z => 0 <= y < i) (F x) = 0).
    {
      apply sum_Z_range_eq_zero. intros y Hy.
      unfold F.
      destruct (prop_dec
        (x < y /\ Znth x groups 0 = Znth y groups 0 /\
         Znth x keys 0 <> Znth y keys 0)); [lia | reflexivity].
    }
    rewrite Hzero, Z.add_0_l.
    apply SumLib.Sum.sum_ext. intros y Hy.
    unfold F, G.
    assert (Hgx : Znth x groups 0 = Znth i groups 0) by
      (apply Hsame; lia).
    assert (Hgy : Znth y groups 0 = Znth i groups 0) by
      (apply Hsame; lia).
    assert (Hgxy : Znth x groups 0 = Znth y groups 0) by congruence.
    destruct (prop_dec
      (x < y /\ Znth x groups 0 = Znth y groups 0 /\
       Znth x keys 0 <> Znth y keys 0));
      destruct (prop_dec (x < y /\ Znth x keys 0 <> Znth y keys 0));
      try reflexivity; tauto.
  }
  rewrite Hold, Hnew. lia.
Qed.

Lemma fold_Zrange_aux_descending_twice__count_result :
  forall (n : nat) (lo : Z),
    2 * fold_right
      (fun x acc => (lo + Z.of_nat n - x - 1) + acc) 0
      (Zrange_aux lo n) =
    Z.of_nat n * (Z.of_nat n - 1).
Proof.
  induction n as [|n IH]; intros lo.
  - cbn [Zrange_aux fold_right]. reflexivity.
  - cbn [Zrange_aux fold_right].
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) in * by lia.
    replace
      (fun x acc : Z => lo + (Z.of_nat n + 1) - x - 1 + acc)
      with
      (fun x acc : Z => lo + 1 + Z.of_nat n - x - 1 + acc) by
      (apply functional_extensionality; intro x;
       apply functional_extensionality; intro acc; f_equal; lia).
    replace (lo + (Z.of_nat n + 1) - lo - 1) with (Z.of_nat n) by lia.
    replace (Z.of_nat n + 1 - 1) with (Z.of_nat n) by lia.
    pose proof (IH (lo + 1)) as Htail.
    set (tail := fold_right
      (fun x acc : Z => lo + 1 + Z.of_nat n - x - 1 + acc) 0
      (Zrange_aux (lo + 1) n)) in *.
    nia.
Qed.

Lemma sum_Z_range_descending__count_result :
  forall lo hi,
    lo <= hi ->
    SumLib.Sum.sum (fun x : Z => lo <= x < hi)
      (fun x => hi - x - 1) =
    (hi - lo) * (hi - lo - 1) / 2.
Proof.
  intros lo hi Hrange.
  rewrite sum_range_unfold. unfold Zrange.
  set (n := Z.to_nat (hi - lo)).
  assert (Hn : Z.of_nat n = hi - lo) by (unfold n; lia).
  assert (Htwice := fold_Zrange_aux_descending_twice__count_result n lo).
  replace (fun x acc : Z => hi - x - 1 + acc)
    with (fun x acc : Z => lo + Z.of_nat n - x - 1 + acc) by
    (apply functional_extensionality; intro x;
     apply functional_extensionality; intro acc; f_equal; lia).
  replace ((hi - lo) * (hi - lo - 1))
    with (2 * fold_right
      (fun x acc : Z => lo + Z.of_nat n - x - 1 + acc) 0
      (Zrange_aux lo n)) by lia.
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma unordered_pair_range_card__count_result :
  forall lo hi,
    lo <= hi ->
    #(fun ij : Z * Z =>
        lo <= fst ij < hi /\ lo <= snd ij < hi /\ fst ij < snd ij) =
    (hi - lo) * (hi - lo - 1) / 2.
Proof.
  intros lo hi Hrange.
  rewrite set_card_Z_rect_filter_as_nested_sum__count_result.
  transitivity
    (SumLib.Sum.sum (fun x : Z => lo <= x < hi)
      (fun x => hi - x - 1)).
  - apply SumLib.Sum.sum_ext. intros x Hx.
    rewrite (sum_Z_range_split lo (x + 1) hi) by lia.
    rewrite (sum_Z_range_eq_zero lo (x + 1)).
    2: {
      intros y Hy.
      change ((if prop_dec (x < y) then 1 else 0) = 0).
      destruct (prop_dec (x < y)); [lia | reflexivity].
    }
    rewrite Z.add_0_l.
    transitivity
      (SumLib.Sum.sum (fun y : Z => x + 1 <= y < hi) (fun _ => 1)).
    + apply SumLib.Sum.sum_ext. intros y Hy.
      change ((if prop_dec (x < y) then 1 else 0) = 1).
      destruct (prop_dec (x < y)); [reflexivity | lia].
    + rewrite sum_Z_range_const by lia. lia.
  - apply sum_Z_range_descending__count_result. exact Hrange.
Qed.

Lemma unequal_pair_range_card__count_result :
  forall keys lo hi,
    lo <= hi ->
    #(fun ij : Z * Z =>
        lo <= fst ij < hi /\ lo <= snd ij < hi /\ fst ij < snd ij /\
        Znth (fst ij) keys 0 <> Znth (snd ij) keys 0) =
    (hi - lo) * (hi - lo - 1) / 2 - SameKeyCountRange keys lo hi.
Proof.
  intros keys lo hi Hrange.
  pose proof (set_card_Z_rect_partition__count_result lo hi lo hi
    (fun ij : Z * Z => fst ij < snd ij)
    (fun ij : Z * Z => Znth (fst ij) keys 0 = Znth (snd ij) keys 0)) as Hpart.
  rewrite unordered_pair_range_card__count_result in Hpart by exact Hrange.
  unfold SameKeyCountRange.
  replace
    (fun ij : Z * Z =>
       lo <= fst ij < hi /\ lo <= snd ij < hi /\ fst ij < snd ij /\
       ~ Znth (fst ij) keys 0 = Znth (snd ij) keys 0)
    with
    (fun ij : Z * Z =>
       lo <= fst ij < hi /\ lo <= snd ij < hi /\ fst ij < snd ij /\
       Znth (fst ij) keys 0 <> Znth (snd ij) keys 0) in Hpart by
    (apply functional_extensionality; intro ij; apply propositional_extensionality; tauto).
  lia.
Qed.

Lemma CountGroupPhase_complete__count_result :
  forall groups keys i j total,
    0 <= i < j ->
    j <= Zlength groups ->
    ItemsIncreasing groups keys ->
    ValueRunBoundary groups i ->
    SameValueRange groups i j ->
    CountGroupPhase groups keys i j j total ->
    PairCountPrefix groups keys j total.
Proof.
  intros groups keys i j total Hij Hj Hinc Hboundary Hsame Hphase.
  unfold CountGroupPhase in Hphase.
  destruct Hphase as [before [Hbefore Htotal]].
  unfold PairCountPrefix.
  pose proof (PairCountPrefix_split_completed_run__count_result
    groups keys i j before Hij Hj Hinc Hboundary Hsame Hbefore) as Hsplit.
  rewrite unequal_pair_range_card__count_result in Hsplit by lia.
  lia.
Qed.

(* Street-geometry support for the classification/count correspondence.  The
   recursive presentation is proof-facing only; [WalkLength] remains the
   mathematical specification used by [StreetDistance]. *)
Fixpoint WalkLengthList__classification
    (path : list (Z * Z)) : Z :=
  match path with
  | a :: ((b :: tl) as rest) =>
      Manhattan a b + WalkLengthList__classification rest
  | _ => 0
  end.

Lemma WalkLength_eq_WalkLengthList__classification :
  forall path,
    WalkLength path = WalkLengthList__classification path.
Proof.
  induction path as [|a [|b tl] IH].
  - unfold WalkLength, SpecHelpers.sum_range.
    rewrite sum_Z_range_empty by (rewrite Zlength_nil; lia).
    reflexivity.
  - unfold WalkLength, SpecHelpers.sum_range.
    rewrite sum_Z_range_empty by (rewrite Zlength_cons, Zlength_nil; lia).
    reflexivity.
  - change (WalkLength (a :: b :: tl) =
      Manhattan a b + WalkLengthList__classification (b :: tl)).
    unfold WalkLength, SpecHelpers.sum_range.
    replace (Zlength (a :: b :: tl) - 2 + 1)
      with (Zlength (b :: tl)) by (rewrite !Zlength_cons; lia).
    rewrite sum_Z_range_cons by
      (pose proof (Zlength_nonneg tl); rewrite Zlength_cons; lia).
    replace (Znth 0 (a :: b :: tl) (0, 0)) with a by reflexivity.
    replace (Znth (0 + 1) (a :: b :: tl) (0, 0)) with b by reflexivity.
    f_equal. rewrite <- IH.
    unfold WalkLength, SpecHelpers.sum_range.
    rewrite !sum_range_unfold. unfold Zrange.
    rewrite fold_Zrange_aux_shift.
    replace (Z.to_nat (Zlength (b :: tl) - (0 + 1)))
      with (Z.to_nat (Zlength (b :: tl) - 2 + 1 - 0)) by
      (f_equal; lia).
    apply fold_Zsum_ext_in. intros x Hx.
    apply In_Zrange_aux_lb in Hx.
    replace (Znth (x + 1) (a :: b :: tl) (0, 0))
      with (Znth x (b :: tl) (0, 0)) by
      (rewrite (Znth_cons (0, 0) (x + 1) a (b :: tl)) by lia;
       replace (x + 1 - 1) with x by lia; reflexivity).
    replace (Znth (x + 1 + 1) (a :: b :: tl) (0, 0))
      with (Znth (x + 1) (b :: tl) (0, 0)) by
      (rewrite (Znth_cons (0, 0) (x + 1 + 1) a (b :: tl)) by lia;
       replace (x + 1 + 1 - 1) with (x + 1) by lia; reflexivity).
    reflexivity.
Qed.

Fixpoint CoordinateVariation__classification
    (coord : (Z * Z) -> Z) (path : list (Z * Z)) : Z :=
  match path with
  | a :: ((b :: tl) as rest) =>
      Z.abs (coord a - coord b) +
      CoordinateVariation__classification coord rest
  | _ => 0
  end.

Lemma WalkLengthList_coordinate_split__classification :
  forall path,
    WalkLengthList__classification path =
      CoordinateVariation__classification fst path +
      CoordinateVariation__classification snd path.
Proof.
  induction path as [|a [|b tl] IH]; try reflexivity.
  change
    (Manhattan a b + WalkLengthList__classification (b :: tl) =
     (Z.abs (fst a - fst b) +
        CoordinateVariation__classification fst (b :: tl)) +
     (Z.abs (snd a - snd b) +
        CoordinateVariation__classification snd (b :: tl))).
  rewrite IH. unfold Manhattan. lia.
Qed.

Lemma CoordinateVariation_nonnegative__classification :
  forall coord path,
    0 <= CoordinateVariation__classification coord path.
Proof.
  intros coord path. induction path as [|a [|b tl] IH]; try reflexivity.
  change (0 <= Z.abs (coord a - coord b) +
    CoordinateVariation__classification coord (b :: tl)).
  pose proof (Z.abs_nonneg (coord a - coord b)). lia.
Qed.

Lemma last_nonempty_default__classification :
  forall {A : Type} (path : list A) d1 d2,
    path <> [] -> last path d1 = last path d2.
Proof.
  intros A path. induction path as [|a [|b tl] IH];
    intros d1 d2 Hne; try contradiction; try reflexivity.
  change (last (b :: tl) d1 = last (b :: tl) d2).
  apply IH. discriminate.
Qed.

Lemma CoordinateVariation_endpoint_bound__classification :
  forall coord a rest,
    Z.abs (coord a - coord (last (a :: rest) a)) <=
    CoordinateVariation__classification coord (a :: rest).
Proof.
  intros coord a rest. revert a.
  induction rest as [|b tl IH]; intro a.
  - cbn [CoordinateVariation__classification last].
    rewrite Z.sub_diag, Z.abs_0. lia.
  - change
      (Z.abs (coord a - coord (last (a :: b :: tl) a)) <=
       Z.abs (coord a - coord b) +
       CoordinateVariation__classification coord (b :: tl)).
    assert (Hlast : last (a :: b :: tl) a = last (b :: tl) b).
    {
      transitivity (last (b :: tl) a); [reflexivity |].
      apply last_nonempty_default__classification. discriminate.
    }
    rewrite Hlast.
    pose proof (IH b) as Htail.
    pose proof (Z.abs_triangle
      (coord a - coord b)
      (coord b - coord (last (b :: tl) b))) as Htriangle.
    replace
      (coord a - coord b + (coord b - coord (last (b :: tl) b)))
      with (coord a - coord (last (b :: tl) b)) in Htriangle by ring.
    lia.
Qed.

Lemma CoordinateVariation_via_bound__classification :
  forall coord a rest r,
    In r (a :: rest) ->
    Z.abs (coord a - coord r) +
      Z.abs (coord r - coord (last (a :: rest) a)) <=
    CoordinateVariation__classification coord (a :: rest).
Proof.
  intros coord a rest. revert a.
  induction rest as [|b tl IH]; intros a r Hin.
  - simpl in Hin. destruct Hin as [-> | []].
    cbn [CoordinateVariation__classification last].
    rewrite !Z.sub_diag, !Z.abs_0. lia.
  - change
      (Z.abs (coord a - coord r) +
         Z.abs (coord r - coord (last (a :: b :: tl) a)) <=
       Z.abs (coord a - coord b) +
         CoordinateVariation__classification coord (b :: tl)).
    assert (Hlast : last (a :: b :: tl) a = last (b :: tl) b).
    {
      transitivity (last (b :: tl) a); [reflexivity |].
      apply last_nonempty_default__classification. discriminate.
    }
    rewrite Hlast.
    simpl in Hin. destruct Hin as [-> | Hin].
    + rewrite Z.sub_diag, Z.abs_0, Z.add_0_l.
      pose proof
        (CoordinateVariation_endpoint_bound__classification
          coord r (b :: tl)) as Hendpoint.
      rewrite Hlast in Hendpoint. exact Hendpoint.
    + pose proof (IH b r Hin) as Htail.
      pose proof (Z.abs_triangle
        (coord a - coord b) (coord b - coord r)) as Htriangle.
      replace (coord a - coord b + (coord b - coord r))
        with (coord a - coord r) in Htriangle by ring.
      lia.
Qed.

Lemma Znth_last_nonempty__classification :
  forall {A : Type} (path : list A) default,
    path <> [] ->
    Znth (Zlength path - 1) path default = last path default.
Proof.
  intros A path. induction path as [|a [|b tl] IH]; intros default Hne.
  - contradiction.
  - reflexivity.
  - rewrite (Znth_cons default (Zlength (a :: b :: tl) - 1)
      a (b :: tl)) by
      (pose proof (Zlength_nonneg tl); rewrite !Zlength_cons; lia).
    replace (Zlength (a :: b :: tl) - 1 - 1)
      with (Zlength (b :: tl) - 1) by (rewrite !Zlength_cons; lia).
    replace (last (a :: b :: tl) default)
      with (last (b :: tl) default) by (destruct tl; reflexivity).
    apply IH. discriminate.
Qed.

Lemma WalkLength_Manhattan_lower_bound__classification :
  forall xs ys p q path,
    StreetWalk xs ys p q path ->
    Manhattan p q <= WalkLength path.
Proof.
  intros xs ys p q path [Hne [Hfirst [Hlast Hsteps]]].
  rewrite WalkLength_eq_WalkLengthList__classification.
  rewrite WalkLengthList_coordinate_split__classification.
  destruct path as [|a rest]; [contradiction |].
  rewrite Znth0_cons in Hfirst. subst a.
  rewrite Znth_last_nonempty__classification in Hlast by discriminate.
  pose proof (CoordinateVariation_endpoint_bound__classification fst p rest) as Hx.
  pose proof (CoordinateVariation_endpoint_bound__classification snd p rest) as Hy.
  assert (Hlastp : last (p :: rest) p = q).
  { rewrite (last_nonempty_default__classification
      (p :: rest) p (0, 0)) by discriminate.
    exact Hlast. }
  rewrite Hlastp in Hx, Hy. unfold Manhattan. lia.
Qed.

Lemma WalkLength_nonnegative__classification :
  forall path, 0 <= WalkLength path.
Proof.
  intro path. rewrite WalkLength_eq_WalkLengthList__classification.
  rewrite WalkLengthList_coordinate_split__classification.
  pose proof (CoordinateVariation_nonnegative__classification fst path).
  pose proof (CoordinateVariation_nonnegative__classification snd path). lia.
Qed.

Lemma StreetDistance_exists__classification :
  forall xs ys p q path,
    StreetWalk xs ys p q path ->
    exists d, StreetDistance xs ys p q d.
Proof.
  intros xs ys p q path Hpath.
  set (Q := fun v : Z =>
    exists walk, StreetWalk xs ys p q walk /\ v = WalkLength walk).
  set (K := WalkLength path).
  assert (HK : 0 <= K) by
    (unfold K; apply WalkLength_nonnegative__classification).
  assert (HQK : Q K) by
    (unfold Q, K; exists path; split; [exact Hpath | reflexivity]).
  assert (Hexrange : exists n, 0 <= n <= K /\ Q n).
  { exists K. split; [lia | exact HQK]. }
  destruct (min_n_in_range Q K HK Hexrange) as
      [m [HQm [[Hm0 HmK] Hmin]]].
  exists m. unfold StreetDistance, min_value_of_subset.
  exists m. split; [|reflexivity].
  split; [exact HQm |].
  intros k HQk. destruct HQk as [walk [Hwalk ->]].
  pose proof (WalkLength_nonnegative__classification walk) as Hk0.
  destruct (Z_le_gt_dec (WalkLength walk) K) as [HkK | HkK].
  - apply Hmin; [lia |]. unfold Q. exists walk. auto.
  - lia.
Qed.

Lemma all_walks_strict_implies_Inconvenient__classification :
  forall xs ys p q path,
    StreetWalk xs ys p q path ->
    (forall walk, StreetWalk xs ys p q walk ->
       Manhattan p q < WalkLength walk) ->
    Inconvenient xs ys p q.
Proof.
  intros xs ys p q path Hpath Hstrict.
  destruct (StreetDistance_exists__classification
    xs ys p q path Hpath) as [d Hd].
  exists d. split; [exact Hd |].
  unfold StreetDistance, min_value_of_subset, min_object_of_subset in Hd.
  destruct Hd as [v [[[walk [Hwalk Hv]] Hminimal] Hvd]].
  subst v d. pose proof (Hstrict walk Hwalk). lia.
Qed.

Lemma Manhattan_walk_implies_not_Inconvenient__classification :
  forall xs ys p q path,
    StreetWalk xs ys p q path ->
    WalkLength path = Manhattan p q ->
    ~ Inconvenient xs ys p q.
Proof.
  intros xs ys p q path Hpath Hlength [d [Hd Hgreater]].
  unfold StreetDistance, min_value_of_subset, min_object_of_subset in Hd.
  destruct Hd as [v [Hobject Hvd]].
  destruct Hobject as [Hmember Hminimal].
  specialize (Hminimal (WalkLength path)).
  assert (Hex : exists walk,
      StreetWalk xs ys p q walk /\ WalkLength path = WalkLength walk).
  { exists path. auto. }
  specialize (Hminimal Hex). lia.
Qed.

Fixpoint StreetSegments__classification
    (xs ys : list Z) (path : list (Z * Z)) : Prop :=
  match path with
  | a :: ((b :: tl) as rest) =>
      StreetSegment xs ys a b /\
      StreetSegments__classification xs ys rest
  | _ => True
  end.

Lemma indexed_steps_imply_StreetSegments__classification :
  forall xs ys path,
    (forall i, 0 <= i < Zlength path - 1 ->
      StreetSegment xs ys (Znth i path (0, 0))
        (Znth (i + 1) path (0, 0))) ->
    StreetSegments__classification xs ys path.
Proof.
  intros xs ys path. induction path as [|a [|b tl] IH]; intro Hsteps;
    simpl; auto.
  split.
  - specialize (Hsteps 0 ltac:(rewrite !Zlength_cons; pose proof
      (Zlength_nonneg tl); lia)).
    rewrite Znth0_cons in Hsteps.
    replace (0 + 1) with 1 in Hsteps by lia.
    rewrite Znth_cons in Hsteps by lia.
    replace (1 - 1) with 0 in Hsteps by lia.
    rewrite Znth0_cons in Hsteps. exact Hsteps.
  - apply IH. intros i Hi.
    specialize (Hsteps (i + 1)).
    assert (Hrange : 0 <= i + 1 < Zlength (a :: b :: tl) - 1).
    { rewrite !Zlength_cons in *. pose proof (Zlength_nonneg tl). lia. }
    specialize (Hsteps Hrange).
    rewrite Znth_cons in Hsteps by lia.
    replace (i + 1 - 1) with i in Hsteps by lia.
    assert (Hz : Znth (i + 1 + 1) (a :: b :: tl) (0, 0) =
        Znth (i + 1) (b :: tl) (0, 0)).
    { rewrite Znth_cons by lia. f_equal. lia. }
    rewrite Hz in Hsteps.
    exact Hsteps.
Qed.

Lemma StreetSegments_no_horizontal_fst_constant__classification :
  forall xs ys a rest,
    StreetSegments__classification xs ys (a :: rest) ->
    (forall r, In r (a :: rest) -> ~ In (snd r) ys) ->
    forall r, In r (a :: rest) -> fst r = fst a.
Proof.
  intros xs ys a rest. revert a.
  induction rest as [|b tl IH]; intros a Hsegments Hnone r Hin.
  - simpl in Hin. destruct Hin as [-> | []]. reflexivity.
  - simpl in Hsegments. destruct Hsegments as [Hab Htail].
    assert (Hfst : fst b = fst a).
    { unfold StreetSegment in Hab. destruct Hab as [[Hsame _] | [Hsame Hstreet]].
      - symmetry. exact Hsame.
      - exfalso. apply (Hnone a); [simpl; auto |].
        exact Hstreet. }
    simpl in Hin. destruct Hin as [-> | Hin]; [reflexivity |].
    specialize (IH b Htail).
    assert (Hnone_tail : forall u, In u (b :: tl) -> ~ In (snd u) ys).
    { intros u Hu. apply Hnone. simpl. auto. }
    specialize (IH Hnone_tail r Hin). lia.
Qed.

Lemma last_in_nonempty__classification :
  forall {A : Type} (path : list A) d,
    path <> [] -> In (last path d) path.
Proof.
  intros A path. induction path as [|a [|b tl] IH]; intros d Hne.
  - contradiction.
  - simpl. auto.
  - change (In (last (b :: tl) d) (a :: b :: tl)).
    right. apply IH. discriminate.
Qed.

Lemma StreetWalk_x_change_hits_horizontal__classification :
  forall xs ys p q path,
    StreetWalk xs ys p q path ->
    fst p <> fst q ->
    exists r, In r path /\ In (snd r) ys.
Proof.
  intros xs ys p q path [Hne [Hfirst [Hlast Hsteps]]] Hchange.
  destruct (classic (exists r, In r path /\ In (snd r) ys)) as [Hex | Hnone];
    [exact Hex | exfalso].
  destruct path as [|a rest]; [contradiction |].
  rewrite Znth0_cons in Hfirst. subst a.
  rewrite Znth_last_nonempty__classification in Hlast by discriminate.
  assert (Hsegments : StreetSegments__classification xs ys (p :: rest)).
  { apply indexed_steps_imply_StreetSegments__classification. exact Hsteps. }
  assert (Hnone' : forall r, In r (p :: rest) -> ~ In (snd r) ys).
  { intros r Hr Hry. apply Hnone. exists r. auto. }
  assert (Hinlast : In (last (p :: rest) (0, 0)) (p :: rest)).
  { apply last_in_nonempty__classification. congruence. }
  pose proof (StreetSegments_no_horizontal_fst_constant__classification
    xs ys p rest Hsegments Hnone'
    (last (p :: rest) (0, 0)) Hinlast) as Hconstant.
  rewrite Hlast in Hconstant. apply Hchange. symmetry. exact Hconstant.
Qed.

Lemma In_as_Znth__classification :
  forall {A : Type} (l : list A) (v d : A),
    In v l -> exists i, 0 <= i < Zlength l /\ Znth i l d = v.
Proof.
  intros A l. induction l as [|a tl IH]; intros v d Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [<- | Hin].
    + exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg tl). lia.
      * rewrite Znth0_cons. reflexivity.
    + destruct (IH v d Hin) as [i [Hi Hiv]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia. exact Hiv.
Qed.

Lemma mono_inc_member_outside_gap__classification :
  forall streets g v,
    mono_inc streets ->
    0 <= g < Zlength streets - 1 ->
    In v streets ->
    v <= Znth g streets 0 \/ Znth (g + 1) streets 0 <= v.
Proof.
  intros streets g v Hmono Hg Hin.
  unfold mono_inc in Hmono.
  destruct (In_as_Znth__classification streets v 0 Hin)
    as [i [[Hi0 Hil] Hiv]].
  destruct (Z_le_gt_dec i g) as [Hig | Hig].
  - left. destruct (Z.eq_dec i g) as [-> | Hne]; [lia |].
    rewrite <- Hiv. pose proof (Hmono i g ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - right. destruct (Z.eq_dec i (g + 1)) as [-> | Hne]; [lia |].
    rewrite <- Hiv.
    pose proof (Hmono (g + 1) i ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma abs_via_outside_open_interval__classification :
  forall lo hi a b r,
    lo < a < hi -> lo < b < hi ->
    (r <= lo \/ hi <= r) ->
    Z.abs (a - b) < Z.abs (a - r) + Z.abs (r - b).
Proof.
  intros lo hi a b r Ha Hb Hr.
  destruct Hr as [Hr | Hr];
    destruct (Z_le_gt_dec a b) as [Hab | Hab].
  - rewrite Z.abs_neq by lia.
    rewrite Z.abs_eq by lia.
    rewrite Z.abs_neq by lia. lia.
  - rewrite Z.abs_eq by lia.
    rewrite Z.abs_eq by lia.
    rewrite Z.abs_neq by lia. lia.
  - rewrite Z.abs_neq by lia.
    rewrite Z.abs_neq by lia.
    rewrite Z.abs_eq by lia. lia.
  - rewrite Z.abs_eq by lia.
    rewrite Z.abs_neq by lia.
    rewrite Z.abs_eq by lia. lia.
Qed.

Lemma StreetWalk_coordinate_endpoint_bound__classification :
  forall xs ys p q path coord,
    StreetWalk xs ys p q path ->
    Z.abs (coord p - coord q) <=
      CoordinateVariation__classification coord path.
Proof.
  intros xs ys p q path coord [Hne [Hfirst [Hlast Hsteps]]].
  destruct path as [|a rest]; [contradiction |].
  rewrite Znth0_cons in Hfirst. subst a.
  rewrite Znth_last_nonempty__classification in Hlast by discriminate.
  pose proof (CoordinateVariation_endpoint_bound__classification
    coord p rest) as Hbound.
  assert (Hlastp : last (p :: rest) p = q).
  { rewrite (last_nonempty_default__classification
      (p :: rest) p (0, 0)) by discriminate. exact Hlast. }
  rewrite Hlastp in Hbound. exact Hbound.
Qed.

Lemma StreetWalk_coordinate_via_bound__classification :
  forall xs ys p q path coord r,
    StreetWalk xs ys p q path -> In r path ->
    Z.abs (coord p - coord r) + Z.abs (coord r - coord q) <=
      CoordinateVariation__classification coord path.
Proof.
  intros xs ys p q path coord r [Hne [Hfirst [Hlast Hsteps]]] Hin.
  destruct path as [|a rest]; [contradiction |].
  rewrite Znth0_cons in Hfirst. subst a.
  rewrite Znth_last_nonempty__classification in Hlast by discriminate.
  pose proof (CoordinateVariation_via_bound__classification
    coord p rest r Hin) as Hbound.
  assert (Hlastp : last (p :: rest) p = q).
  { rewrite (last_nonempty_default__classification
      (p :: rest) p (0, 0)) by discriminate. exact Hlast. }
  rewrite Hlastp in Hbound. exact Hbound.
Qed.

Lemma StreetWalk_four_segments__classification :
  forall xs ys a b c d,
    StreetSegment xs ys a b ->
    StreetSegment xs ys b c ->
    StreetSegment xs ys c d ->
    StreetWalk xs ys a d [a; b; c; d].
Proof.
  intros xs ys a b c d Hab Hbc Hcd.
  unfold StreetWalk.
  split; [discriminate |].
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  - intros i Hi. change (0 <= i < 3) in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct H as [-> | [-> | ->]]; vm_compute; assumption.
Qed.

Lemma vertical_same_strip_different_key_Inconvenient__classification :
  forall xs ys a b g,
    mono_inc ys ->
    StripIndex ys (snd a) g ->
    StripIndex ys (snd b) g ->
    0 <= g ->
    In (fst a) xs -> In (fst b) xs ->
    fst a <> fst b ->
    Inconvenient xs ys a b.
Proof.
  intros xs ys a b g Hmono Ha Hb Hg Hxa Hxb Hxne.
  unfold StripIndex in Ha, Hb.
  destruct Ha as [[Hgm _] | [Hgbound Hay]]; [lia |].
  destruct Hb as [[Hgm _] | [_ Hby]]; [lia |].
  set (lo := Znth g ys 0).
  set (hi := Znth (g + 1) ys 0).
  assert (Hlo_in : In lo ys).
  { unfold lo. apply Znth_In_Zlength. lia. }
  set (path := [a; (fst a, lo); (fst b, lo); b]).
  assert (Hpath : StreetWalk xs ys a b path).
  { unfold path. apply StreetWalk_four_segments__classification.
    - left. simpl. auto.
    - right. simpl. auto.
    - left. simpl. auto. }
  apply (all_walks_strict_implies_Inconvenient__classification
    xs ys a b path Hpath).
  intros walk Hwalk.
  destruct (StreetWalk_x_change_hits_horizontal__classification
    xs ys a b walk Hwalk Hxne) as [r [Hrin Hrstreet]].
  assert (Hrout : snd r <= lo \/ hi <= snd r).
  { unfold lo, hi. apply mono_inc_member_outside_gap__classification;
      auto; lia. }
  assert (Hystrict : Z.abs (snd a - snd b) <
      Z.abs (snd a - snd r) + Z.abs (snd r - snd b)).
  { apply (abs_via_outside_open_interval__classification
      lo hi (snd a) (snd b) (snd r)); auto. }
  pose proof (StreetWalk_coordinate_via_bound__classification
    xs ys a b walk snd r Hwalk Hrin) as Hywalk.
  pose proof (StreetWalk_coordinate_endpoint_bound__classification
    xs ys a b walk fst Hwalk) as Hxwalk.
  rewrite WalkLength_eq_WalkLengthList__classification.
  rewrite WalkLengthList_coordinate_split__classification.
  unfold Manhattan. lia.
Qed.

Lemma StreetSegments_no_vertical_snd_constant__classification :
  forall xs ys a rest,
    StreetSegments__classification xs ys (a :: rest) ->
    (forall r, In r (a :: rest) -> ~ In (fst r) xs) ->
    forall r, In r (a :: rest) -> snd r = snd a.
Proof.
  intros xs ys a rest. revert a.
  induction rest as [|b tl IH]; intros a Hsegments Hnone r Hin.
  - simpl in Hin. destruct Hin as [-> | []]. reflexivity.
  - simpl in Hsegments. destruct Hsegments as [Hab Htail].
    assert (Hsnd : snd b = snd a).
    { unfold StreetSegment in Hab. destruct Hab as [[Hsame Hstreet] | [Hsame _]].
      - exfalso. apply (Hnone a); [simpl; auto |]. exact Hstreet.
      - symmetry. exact Hsame. }
    simpl in Hin. destruct Hin as [-> | Hin]; [reflexivity |].
    specialize (IH b Htail).
    assert (Hnone_tail : forall u, In u (b :: tl) -> ~ In (fst u) xs).
    { intros u Hu. apply Hnone. simpl. auto. }
    specialize (IH Hnone_tail r Hin). lia.
Qed.

Lemma StreetWalk_y_change_hits_vertical__classification :
  forall xs ys p q path,
    StreetWalk xs ys p q path ->
    snd p <> snd q ->
    exists r, In r path /\ In (fst r) xs.
Proof.
  intros xs ys p q path [Hne [Hfirst [Hlast Hsteps]]] Hchange.
  destruct (classic (exists r, In r path /\ In (fst r) xs)) as [Hex | Hnone];
    [exact Hex | exfalso].
  destruct path as [|a rest]; [contradiction |].
  rewrite Znth0_cons in Hfirst. subst a.
  rewrite Znth_last_nonempty__classification in Hlast by discriminate.
  assert (Hsegments : StreetSegments__classification xs ys (p :: rest)).
  { apply indexed_steps_imply_StreetSegments__classification. exact Hsteps. }
  assert (Hnone' : forall r, In r (p :: rest) -> ~ In (fst r) xs).
  { intros r Hr Hrx. apply Hnone. exists r. auto. }
  assert (Hinlast : In (last (p :: rest) (0, 0)) (p :: rest)).
  { apply last_in_nonempty__classification. congruence. }
  pose proof (StreetSegments_no_vertical_snd_constant__classification
    xs ys p rest Hsegments Hnone'
    (last (p :: rest) (0, 0)) Hinlast) as Hconstant.
  rewrite Hlast in Hconstant. apply Hchange. symmetry. exact Hconstant.
Qed.

Lemma horizontal_same_strip_different_key_Inconvenient__classification :
  forall xs ys a b g,
    mono_inc xs ->
    StripIndex xs (fst a) g ->
    StripIndex xs (fst b) g ->
    0 <= g ->
    In (snd a) ys -> In (snd b) ys ->
    snd a <> snd b ->
    Inconvenient xs ys a b.
Proof.
  intros xs ys a b g Hmono Ha Hb Hg Hya Hyb Hyne.
  unfold StripIndex in Ha, Hb.
  destruct Ha as [[Hgm _] | [Hgbound Hax]]; [lia |].
  destruct Hb as [[Hgm _] | [_ Hbx]]; [lia |].
  set (lo := Znth g xs 0).
  set (hi := Znth (g + 1) xs 0).
  assert (Hlo_in : In lo xs).
  { unfold lo. apply Znth_In_Zlength. lia. }
  set (path := [a; (lo, snd a); (lo, snd b); b]).
  assert (Hpath : StreetWalk xs ys a b path).
  { unfold path. apply StreetWalk_four_segments__classification.
    - right. simpl. auto.
    - left. simpl. auto.
    - right. simpl. auto. }
  apply (all_walks_strict_implies_Inconvenient__classification
    xs ys a b path Hpath).
  intros walk Hwalk.
  destruct (StreetWalk_y_change_hits_vertical__classification
    xs ys a b walk Hwalk Hyne) as [r [Hrin Hrstreet]].
  assert (Hrout : fst r <= lo \/ hi <= fst r).
  { unfold lo, hi. apply mono_inc_member_outside_gap__classification;
      auto; lia. }
  assert (Hxstrict : Z.abs (fst a - fst b) <
      Z.abs (fst a - fst r) + Z.abs (fst r - fst b)).
  { apply (abs_via_outside_open_interval__classification
      lo hi (fst a) (fst b) (fst r)); auto. }
  pose proof (StreetWalk_coordinate_via_bound__classification
    xs ys a b walk fst r Hwalk Hrin) as Hxwalk.
  pose proof (StreetWalk_coordinate_endpoint_bound__classification
    xs ys a b walk snd Hwalk) as Hywalk.
  rewrite WalkLength_eq_WalkLengthList__classification.
  rewrite WalkLengthList_coordinate_split__classification.
  unfold Manhattan. lia.
Qed.

Lemma StreetWalk_two_segment__classification :
  forall xs ys a b,
    StreetSegment xs ys a b -> StreetWalk xs ys a b [a; b].
Proof.
  intros xs ys a b Hab. unfold StreetWalk.
  split; [discriminate |].
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  intros i Hi. change (0 <= i < 1) in Hi.
  assert (i = 0) by lia. subst. vm_compute. exact Hab.
Qed.

Lemma StreetWalk_three_segments__classification :
  forall xs ys a b c,
    StreetSegment xs ys a b -> StreetSegment xs ys b c ->
    StreetWalk xs ys a c [a; b; c].
Proof.
  intros xs ys a b c Hab Hbc. unfold StreetWalk.
  split; [discriminate |].
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  intros i Hi. change (0 <= i < 2) in Hi.
  assert (i = 0 \/ i = 1) by lia.
  destruct H as [-> | ->]; vm_compute; assumption.
Qed.

Lemma shared_vertical_not_Inconvenient__classification :
  forall xs ys a b,
    fst a = fst b -> In (fst a) xs -> ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b Hx Hstreet.
  assert (Hwalk : StreetWalk xs ys a b [a; b]).
  { apply StreetWalk_two_segment__classification. left. auto. }
  apply (Manhattan_walk_implies_not_Inconvenient__classification
    xs ys a b [a; b] Hwalk).
  rewrite WalkLength_eq_WalkLengthList__classification. simpl.
  unfold Manhattan. ring.
Qed.

Lemma shared_horizontal_not_Inconvenient__classification :
  forall xs ys a b,
    snd a = snd b -> In (snd a) ys -> ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b Hy Hstreet.
  assert (Hwalk : StreetWalk xs ys a b [a; b]).
  { apply StreetWalk_two_segment__classification. right. auto. }
  apply (Manhattan_walk_implies_not_Inconvenient__classification
    xs ys a b [a; b] Hwalk).
  rewrite WalkLength_eq_WalkLengthList__classification. simpl.
  unfold Manhattan. ring.
Qed.

Lemma vertical_horizontal_not_Inconvenient__classification :
  forall xs ys a b,
    In (fst a) xs -> In (snd b) ys -> ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b Hxa Hyb.
  set (corner := (fst a, snd b)).
  assert (Hwalk : StreetWalk xs ys a b [a; corner; b]).
  { apply StreetWalk_three_segments__classification.
    - left. unfold corner. simpl. auto.
    - right. unfold corner. simpl. auto. }
  apply (Manhattan_walk_implies_not_Inconvenient__classification
    xs ys a b [a; corner; b] Hwalk).
  rewrite WalkLength_eq_WalkLengthList__classification.
  destruct a as [ax ay]. destruct b as [bx by0]. simpl in *.
  unfold corner, Manhattan. simpl.
  rewrite !Z.sub_diag, !Z.abs_0. lia.
Qed.

Lemma horizontal_vertical_not_Inconvenient__classification :
  forall xs ys a b,
    In (snd a) ys -> In (fst b) xs -> ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b Hya Hxb.
  set (corner := (fst b, snd a)).
  assert (Hwalk : StreetWalk xs ys a b [a; corner; b]).
  { apply StreetWalk_three_segments__classification.
    - right. unfold corner. simpl. auto.
    - left. unfold corner. simpl. auto. }
  apply (Manhattan_walk_implies_not_Inconvenient__classification
    xs ys a b [a; corner; b] Hwalk).
  rewrite WalkLength_eq_WalkLengthList__classification.
  destruct a as [ax ay]. destruct b as [bx by0]. simpl in *.
  unfold corner, Manhattan. simpl.
  rewrite !Z.sub_diag, !Z.abs_0. lia.
Qed.

Lemma vertical_via_horizontal_not_Inconvenient__classification :
  forall xs ys a b y,
    In (fst a) xs -> In (fst b) xs -> In y ys ->
    (snd a <= y <= snd b \/ snd b <= y <= snd a) ->
    ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b y Hxa Hxb Hy Hbetween.
  set (path := [a; (fst a, y); (fst b, y); b]).
  assert (Hwalk : StreetWalk xs ys a b path).
  { unfold path. apply StreetWalk_four_segments__classification.
    - left. simpl. auto.
    - right. simpl. auto.
    - left. simpl. auto. }
  apply (Manhattan_walk_implies_not_Inconvenient__classification
    xs ys a b path Hwalk).
  destruct a as [ax ay]. destruct b as [bx by0].
  cbn [fst snd] in Hbetween.
  unfold path. rewrite WalkLength_eq_WalkLengthList__classification.
  cbn [WalkLengthList__classification Manhattan fst snd].
  unfold Manhattan. cbn [fst snd].
  destruct Hbetween as [Hbetween | Hbetween].
  - rewrite (Z.abs_neq (ay - y)) by lia.
    rewrite (Z.abs_neq (y - by0)) by lia.
    rewrite (Z.abs_neq (ay - by0)) by lia. lia.
  - rewrite (Z.abs_eq (ay - y)) by lia.
    rewrite (Z.abs_eq (y - by0)) by lia.
    rewrite (Z.abs_eq (ay - by0)) by lia. lia.
Qed.

Lemma horizontal_via_vertical_not_Inconvenient__classification :
  forall xs ys a b x,
    In (snd a) ys -> In (snd b) ys -> In x xs ->
    (fst a <= x <= fst b \/ fst b <= x <= fst a) ->
    ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b x Hya Hyb Hx Hbetween.
  set (path := [a; (x, snd a); (x, snd b); b]).
  assert (Hwalk : StreetWalk xs ys a b path).
  { unfold path. apply StreetWalk_four_segments__classification.
    - right. simpl. auto.
    - left. simpl. auto.
    - right. simpl. auto. }
  apply (Manhattan_walk_implies_not_Inconvenient__classification
    xs ys a b path Hwalk).
  destruct a as [ax ay]. destruct b as [bx by0].
  cbn [fst snd] in Hbetween.
  unfold path. rewrite WalkLength_eq_WalkLengthList__classification.
  cbn [WalkLengthList__classification Manhattan fst snd].
  unfold Manhattan. cbn [fst snd].
  destruct Hbetween as [Hbetween | Hbetween].
  - rewrite (Z.abs_neq (ax - x)) by lia.
    rewrite (Z.abs_neq (x - bx)) by lia.
    rewrite (Z.abs_neq (ax - bx)) by lia. lia.
  - rewrite (Z.abs_eq (ax - x)) by lia.
    rewrite (Z.abs_eq (x - bx)) by lia.
    rewrite (Z.abs_eq (ax - bx)) by lia. lia.
Qed.

Lemma StripIndex_nonnegative_not_member__classification :
  forall streets v g,
    mono_inc streets -> StripIndex streets v g -> 0 <= g ->
    ~ In v streets.
Proof.
  intros streets v g Hmono Hstrip Hg Hin.
  unfold StripIndex in Hstrip.
  destruct Hstrip as [[Hgm _] | [Hgbound Hv]]; [lia |].
  pose proof (mono_inc_member_outside_gap__classification
    streets g v Hmono Hgbound Hin). lia.
Qed.

Lemma different_Strips_has_member_between__classification :
  forall streets v1 v2 g1 g2,
    mono_inc streets ->
    StripIndex streets v1 g1 -> 0 <= g1 ->
    StripIndex streets v2 g2 -> 0 <= g2 ->
    g1 <> g2 ->
    exists c, In c streets /\
      (v1 <= c <= v2 \/ v2 <= c <= v1).
Proof.
  intros streets v1 v2 g1 g2 Hmono Hs1 Hg1 Hs2 Hg2 Hne.
  unfold StripIndex in Hs1, Hs2.
  destruct Hs1 as [[Hm1 _] | [Hb1 Hv1]]; [lia |].
  destruct Hs2 as [[Hm2 _] | [Hb2 Hv2]]; [lia |].
  unfold mono_inc in Hmono.
  destruct (Z_lt_dec g1 g2) as [Hlt | Hgt].
  - exists (Znth (g1 + 1) streets 0). split.
    + apply Znth_In_Zlength. lia.
    + left. split; [lia |].
      destruct (Z.eq_dec (g1 + 1) g2) as [Heq | Hneq].
      * subst g2. lia.
      * pose proof (Hmono (g1 + 1) g2 ltac:(lia)
          ltac:(lia) ltac:(lia)). lia.
  - exists (Znth (g2 + 1) streets 0). split.
    + apply Znth_In_Zlength. lia.
    + right. split; [lia |].
      assert (Hg21 : g2 < g1) by lia.
      destruct (Z.eq_dec (g2 + 1) g1) as [Heq | Hneq].
      * subst g1. lia.
      * pose proof (Hmono (g2 + 1) g1 ltac:(lia)
          ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma vertical_entry_on_vertical_street__classification :
  forall xs ys a g k,
    mono_inc ys -> OnStreet xs ys a -> VerticalEntry xs ys a g k ->
    In (fst a) xs.
Proof.
  intros xs ys a g k Hmono [Hx | Hy] Hentry; [exact Hx |].
  unfold VerticalEntry in Hentry.
  destruct Hentry as [Hstrip [Hg Hkey]].
  exfalso. exact (StripIndex_nonnegative_not_member__classification
    ys (snd a) g Hmono Hstrip Hg Hy).
Qed.

Lemma vertical_entries_Inconvenient_iff__classification :
  forall xs ys a b ga ka gb kb,
    mono_inc ys -> OnStreet xs ys a -> OnStreet xs ys b ->
    VerticalEntry xs ys a ga ka -> VerticalEntry xs ys b gb kb ->
    (Inconvenient xs ys a b <-> ga = gb /\ ka <> kb).
Proof.
  intros xs ys a b ga ka gb kb Hmono Hona Honb Hea Heb.
  assert (Hxa : In (fst a) xs) by
    (eapply vertical_entry_on_vertical_street__classification; eauto).
  assert (Hxb : In (fst b) xs) by
    (eapply vertical_entry_on_vertical_street__classification; eauto).
  unfold VerticalEntry in Hea, Heb.
  destruct Hea as [Hsa [Hga Hka]].
  destruct Heb as [Hsb [Hgb Hkb]]. subst ka kb.
  split.
  - intro Hinc. split.
    + destruct (Z.eq_dec ga gb); auto.
      exfalso.
      destruct (different_Strips_has_member_between__classification
        ys (snd a) (snd b) ga gb Hmono Hsa Hga Hsb Hgb n)
        as [c [Hcin Hbetween]].
      pose proof (vertical_via_horizontal_not_Inconvenient__classification
        xs ys a b c Hxa Hxb Hcin Hbetween) as Hnot. exact (Hnot Hinc).
    + intro Hkey. exfalso.
      pose proof (shared_vertical_not_Inconvenient__classification
        xs ys a b Hkey Hxa) as Hnot. exact (Hnot Hinc).
  - intros [-> Hkey].
    eapply vertical_same_strip_different_key_Inconvenient__classification;
      eauto.
Qed.

Lemma horizontal_entries_Inconvenient_iff__classification :
  forall xs ys a b ga ka gb kb,
    mono_inc xs ->
    HorizontalEntry xs ys a ga ka -> HorizontalEntry xs ys b gb kb ->
    (Inconvenient xs ys a b <-> ga = gb /\ ka <> kb).
Proof.
  intros xs ys a b ga ka gb kb Hmono Hea Heb.
  unfold HorizontalEntry in Hea, Heb.
  destruct Hea as [Hya [Hsa [Hga Hka]]].
  destruct Heb as [Hyb [Hsb [Hgb Hkb]]].
  unfold StripIndex in Hya, Hyb.
  destruct Hya as [[_ Hya] | [Hbad _]]; [|lia].
  destruct Hyb as [[_ Hyb] | [Hbad _]]; [|lia].
  subst ka kb. split.
  - intro Hinc. split.
    + destruct (Z.eq_dec ga gb); auto.
      exfalso.
      destruct (different_Strips_has_member_between__classification
        xs (fst a) (fst b) ga gb Hmono Hsa Hga Hsb Hgb n)
        as [c [Hcin Hbetween]].
      pose proof (horizontal_via_vertical_not_Inconvenient__classification
        xs ys a b c Hya Hyb Hcin Hbetween) as Hnot. exact (Hnot Hinc).
    + intro Hkey. exfalso.
      pose proof (shared_horizontal_not_Inconvenient__classification
        xs ys a b Hkey Hya) as Hnot. exact (Hnot Hinc).
  - intros [-> Hkey].
    eapply horizontal_same_strip_different_key_Inconvenient__classification;
      eauto.
Qed.

Lemma vertical_horizontal_entries_not_Inconvenient__classification :
  forall xs ys a b ga ka gb kb,
    mono_inc ys -> OnStreet xs ys a ->
    VerticalEntry xs ys a ga ka -> HorizontalEntry xs ys b gb kb ->
    ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b ga ka gb kb Hmono Hona Hea Heb.
  assert (Hxa : In (fst a) xs) by
    (eapply vertical_entry_on_vertical_street__classification; eauto).
  unfold HorizontalEntry, StripIndex in Heb.
  destruct Heb as [Hyb _]. destruct Hyb as [[_ Hyb] | [Hbad _]]; [|lia].
  apply vertical_horizontal_not_Inconvenient__classification; auto.
Qed.

Lemma horizontal_vertical_entries_not_Inconvenient__classification :
  forall xs ys a b ga ka gb kb,
    mono_inc ys -> OnStreet xs ys b ->
    HorizontalEntry xs ys a ga ka -> VerticalEntry xs ys b gb kb ->
    ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b ga ka gb kb Hmono Honb Hea Heb.
  assert (Hxb : In (fst b) xs) by
    (eapply vertical_entry_on_vertical_street__classification; eauto).
  unfold HorizontalEntry, StripIndex in Hea.
  destruct Hea as [Hya _]. destruct Hya as [[_ Hya] | [Hbad _]]; [|lia].
  apply horizontal_vertical_not_Inconvenient__classification; auto.
Qed.

Lemma intersection_second_not_Inconvenient__classification :
  forall xs ys a b,
    OnStreet xs ys a -> In (fst b) xs -> In (snd b) ys ->
    ~ Inconvenient xs ys a b.
Proof.
  intros xs ys a b [Hxa | Hya] Hxb Hyb.
  - apply vertical_horizontal_not_Inconvenient__classification; auto.
  - apply horizontal_vertical_not_Inconvenient__classification; auto.
Qed.

Definition PrefixPairCard__classification
    (n : Z) (P : Z -> Z -> Prop) : Z :=
  #(fun ij : Z * Z =>
      0 <= fst ij < n /\ 0 <= snd ij < n /\ fst ij < snd ij /\
      P (fst ij) (snd ij)).

Definition NewEndpointCard__classification
    (n : Z) (P : Z -> Z -> Prop) : Z :=
  #(fun i : Z => 0 <= i < n /\ P i n).

Lemma set_card_Z_range_filter_as_sum__classification :
  forall (lo hi : Z) (P : Z -> Prop),
    #(fun x : Z => lo <= x < hi /\ P x) =
    SumLib.Sum.sum (fun x : Z => lo <= x < hi)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros lo hi P.
  transitivity
    (@SumLib.Sum.sum Z (fun x : Z => lo <= x < hi)
      (finite_Z_range lo hi)
      (fun x => if prop_dec (P x) then 1 else 0)).
  - unfold set_card, SumLib.Sum.sum. simpl.
    induction (Zrange lo hi) as [|x tl IH]; simpl.
    + reflexivity.
    + destruct (prop_dec (P x)); simpl; rewrite IH; reflexivity.
  - reflexivity.
Qed.

Lemma PrefixPairCard_extend__classification :
  forall n P,
    0 <= n ->
    PrefixPairCard__classification (n + 1) P =
    PrefixPairCard__classification n P +
    NewEndpointCard__classification n P.
Proof.
  intros n P Hn.
  unfold PrefixPairCard__classification, NewEndpointCard__classification.
  rewrite !set_card_Z_rect_filter_as_nested_sum__count_result.
  rewrite set_card_Z_range_filter_as_sum__classification.
  set (F := fun x y : Z =>
    if prop_dec (x < y /\ P x y) then 1 else 0).
  change
    (SumLib.Sum.sum (fun x : Z => 0 <= x < n + 1)
       (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < n + 1) (F x)) =
     SumLib.Sum.sum (fun x : Z => 0 <= x < n)
       (fun x => SumLib.Sum.sum (fun y : Z => 0 <= y < n) (F x)) +
     SumLib.Sum.sum (fun x : Z => 0 <= x < n)
       (fun x => if prop_dec (P x n) then 1 else 0)).
  rewrite (sum_Z_range_extend_right 0 n) by lia.
  assert (Hrow :
    SumLib.Sum.sum (fun y : Z => 0 <= y < n + 1) (F n) = 0).
  { apply sum_Z_range_eq_zero. intros y Hy. unfold F.
    destruct (prop_dec (n < y /\ P n y)); [lia | reflexivity]. }
  rewrite Hrow, Z.add_0_r.
  transitivity
    (SumLib.Sum.sum (fun x : Z => 0 <= x < n)
      (fun x =>
        SumLib.Sum.sum (fun y : Z => 0 <= y < n) (F x) +
        (if prop_dec (P x n) then 1 else 0))).
  - apply SumLib.Sum.sum_ext. intros x Hx.
    rewrite (sum_Z_range_extend_right 0 n) by lia.
    unfold F. destruct (prop_dec (x < n /\ P x n));
      destruct (prop_dec (P x n)); try reflexivity; tauto.
  - rewrite SumLib.Sum.sum_add. reflexivity.
Qed.

Require Import Coq.Logic.ProofIrrelevance.

Lemma set_card_bijection__classification :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
         (FP : Finite P) (FQ : Finite Q) (f : A -> B) (g : B -> A),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> P (g y)) ->
    (forall x, P x -> g (f x) = x) ->
    (forall y, Q y -> f (g y) = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f g Hf Hg Hgf Hfg.
  unfold set_card, SumLib.Sum.sum.
  assert (Hnodup_map : NoDup (map f (@enum A P FP))).
  { assert (Hgeneral : forall xs : list A,
      NoDup xs -> (forall x, In x xs -> P x) -> NoDup (map f xs)).
    { intros xs Hnodup. induction Hnodup as [|x xs Hnotin Hnodup IH];
        intros Hall; simpl.
      - constructor.
      - constructor.
        + intro Hin. apply in_map_iff in Hin.
          destruct Hin as [y [Hfy Hy]]. apply Hnotin.
          assert (HPx : P x) by (apply Hall; left; reflexivity).
          assert (HPy : P y) by (apply Hall; right; exact Hy).
          assert (Hxy : x = y).
          { rewrite <- (Hgf x HPx), <- (Hgf y HPy). congruence. }
          rewrite Hxy. exact Hy.
        + apply IH. intros y Hy. apply Hall. right. exact Hy. }
    apply Hgeneral.
    - exact (@enum_nodup A P FP).
    - intros x Hx. apply (proj2 (@enum_ok A P FP x)). exact Hx. }
  assert (Hperm : Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  { apply NoDup_Permutation.
    - exact Hnodup_map.
    - exact (@enum_nodup B Q FQ).
    - intros y. rewrite <- (@enum_ok B Q FQ y). split.
      + intros Hin. apply in_map_iff in Hin.
        destruct Hin as [x [Hxy Hx]]. subst y.
        apply Hf. apply (proj2 (@enum_ok A P FP x)). exact Hx.
      + intros HyQ. apply in_map_iff. exists (g y). split.
        * apply Hfg. exact HyQ.
        * apply (proj1 (@enum_ok A P FP (g y))). apply Hg. exact HyQ. }
  assert (Hfold_count : forall (C : Type) (l : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  { intros C l. induction l as [|x xs IH].
    - reflexivity.
    - cbn [fold_right length]. rewrite IH, Nat2Z.inj_succ. lia. }
  rewrite !Hfold_count.
  rewrite <- (Permutation_length Hperm), length_map. reflexivity.
Qed.

Lemma set_card_ext__classification :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Heq.
  eapply set_card_bijection__classification
    with (f := fun x => x) (g := fun x => x).
  - intros x Hx. apply Heq. exact Hx.
  - intros x Hx. apply Heq. exact Hx.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

Lemma Znth_app_left__classification :
  forall {A : Type} (l1 l2 : list A) d i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A l1 l2 d i Hi. unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi. lia.
Qed.

Lemma Znth_app_last__classification :
  forall {A : Type} (l : list A) d x,
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros A l d x. unfold Znth. rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct. lia.
Qed.

Definition EntryPairRel__classification
    (groups keys : list Z) (i j : Z) : Prop :=
  Znth i groups 0 = Znth j groups 0 /\
  Znth i keys 0 <> Znth j keys 0.

Lemma PairCountPrefix_append__classification :
  forall groups keys g k old,
    Zlength groups = Zlength keys ->
    PairCountPrefix groups keys (Zlength groups) old ->
    PairCountPrefix (groups ++ [g]) (keys ++ [k])
      (Zlength (groups ++ [g]))
      (old + #(fun i : Z =>
        0 <= i < Zlength groups /\
        Znth i groups 0 = g /\ Znth i keys 0 <> k)).
Proof.
  intros groups keys g k old Hlen Hold.
  unfold PairCountPrefix in Hold |- *.
  set (Papp := EntryPairRel__classification (groups ++ [g]) (keys ++ [k])).
  set (Pold := EntryPairRel__classification groups keys).
  assert (Hn : 0 <= Zlength groups) by apply Zlength_nonneg.
  pose proof (PrefixPairCard_extend__classification
    (Zlength groups) Papp Hn) as Hextend.
  assert (Hlength_app : Zlength (groups ++ [g]) = Zlength groups + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Holdcard :
    PrefixPairCard__classification (Zlength groups) Papp =
    PrefixPairCard__classification (Zlength groups) Pold).
  { unfold PrefixPairCard__classification. apply set_card_ext__classification.
    intros [i j]. unfold Papp, Pold, EntryPairRel__classification. simpl.
    split; intros [Hi [Hj [Hij [Hg Hk]]]].
    - repeat split; try lia; try assumption.
      + rewrite !Znth_app_left__classification in Hg by lia. exact Hg.
      + rewrite !Znth_app_left__classification in Hk by lia. exact Hk.
    - repeat split; try lia; try assumption.
      + rewrite !Znth_app_left__classification by lia. exact Hg.
      + rewrite !Znth_app_left__classification by lia. exact Hk. }
  assert (Hnewcard :
    NewEndpointCard__classification (Zlength groups) Papp =
    #(fun i : Z => 0 <= i < Zlength groups /\
      Znth i groups 0 = g /\ Znth i keys 0 <> k)).
  { unfold NewEndpointCard__classification. apply set_card_ext__classification.
    intro i. unfold Papp, EntryPairRel__classification.
    split.
    - intros [Hi [Hg Hk]]. split; [exact Hi |].
      rewrite Znth_app_left__classification in Hg by lia.
      rewrite Znth_app_last__classification in Hg.
      rewrite Znth_app_left__classification in Hk by (rewrite <- Hlen; lia).
      replace (Zlength groups) with (Zlength keys) in Hk by lia.
      rewrite Znth_app_last__classification in Hk. auto.
    - intros [Hi [Hg Hk]]. split; [exact Hi |].
      rewrite Znth_app_left__classification by lia.
      rewrite Znth_app_last__classification.
      rewrite Znth_app_left__classification by lia.
      replace (Zlength groups) with (Zlength keys) by lia.
      rewrite Znth_app_last__classification. auto. }
  rewrite Hlength_app.
  change (old +
    #(fun i : Z => 0 <= i < Zlength groups /\
      Znth i groups 0 = g /\ Znth i keys 0 <> k) =
    PrefixPairCard__classification (Zlength groups + 1) Papp).
  rewrite Hextend, Holdcard, Hnewcard.
  change (old = PrefixPairCard__classification (Zlength groups) Pold) in Hold.
  rewrite <- Hold. reflexivity.
Qed.

Lemma Inconvenient_with_vertical_entry_iff__classification :
  forall xs ys q cur g k,
    mono_inc ys -> OnStreet xs ys q -> OnStreet xs ys cur ->
    VerticalEntry xs ys cur g k ->
    (Inconvenient xs ys q cur <->
      exists kq, VerticalEntry xs ys q g kq /\ kq <> k).
Proof.
  intros xs ys q cur g k Hmono Honq Honcur Hcur.
  assert (Hxcur : In (fst cur) xs) by
    (eapply vertical_entry_on_vertical_street__classification; eauto).
  unfold VerticalEntry in Hcur.
  destruct Hcur as [Hscur [Hg Hk]]. subst k.
  unfold StripIndex in Hscur.
  destruct Hscur as [[Hbad _] | [Hgbound Hcury]]; [lia |].
  set (lo := Znth g ys 0).
  set (hi := Znth (g + 1) ys 0).
  assert (Hloin : In lo ys) by
    (unfold lo; apply Znth_In_Zlength; lia).
  assert (Hhiin : In hi ys) by
    (unfold hi; apply Znth_In_Zlength; lia).
  split.
  - intro Hinc. destruct Honq as [Hxq | Hyq].
    + assert (Hinside : lo < snd q < hi).
      { destruct (Z_le_gt_dec (snd q) lo) as [Hlow | Hlow].
        - exfalso. apply (vertical_via_horizontal_not_Inconvenient__classification
            xs ys q cur lo Hxq Hxcur Hloin ltac:(left; unfold lo, hi in *; lia)).
          exact Hinc.
        - destruct (Z_le_gt_dec hi (snd q)) as [Hhigh | Hhigh]; [|lia].
          exfalso. apply (vertical_via_horizontal_not_Inconvenient__classification
            xs ys q cur hi Hxq Hxcur Hhiin ltac:(right; unfold lo, hi in *; lia)).
          exact Hinc. }
      exists (fst q). split.
      * unfold VerticalEntry. split.
        -- unfold StripIndex. right. split; [exact Hgbound |].
           unfold lo, hi in Hinside. exact Hinside.
        -- split; [exact Hg | reflexivity].
      * intro Heq. exfalso.
        pose proof (shared_vertical_not_Inconvenient__classification
          xs ys q cur Heq Hxq) as Hnot. exact (Hnot Hinc).
    + exfalso. apply (horizontal_vertical_not_Inconvenient__classification
        xs ys q cur Hyq Hxcur). exact Hinc.
  - intros [kq [Hq Hneq]].
    assert (Hcur' : VerticalEntry xs ys cur g (fst cur)).
    { unfold VerticalEntry. split.
      - unfold StripIndex. right. split; assumption.
      - split; [exact Hg | reflexivity]. }
    pose proof (vertical_entries_Inconvenient_iff__classification
      xs ys q cur g kq g (fst cur) Hmono Honq Honcur Hq Hcur') as Hiff.
    apply (proj2 Hiff). split; [reflexivity |].
    unfold VerticalEntry in Hq. destruct Hq as [_ [_ ->]]. exact Hneq.
Qed.

Lemma Inconvenient_with_horizontal_entry_iff__classification :
  forall xs ys q cur g k,
    mono_inc xs -> OnStreet xs ys q ->
    HorizontalEntry xs ys cur g k ->
    (Inconvenient xs ys q cur <->
      exists kq, HorizontalEntry xs ys q g kq /\ kq <> k).
Proof.
  intros xs ys q cur g k Hmono Honq Hcur.
  unfold HorizontalEntry in Hcur.
  destruct Hcur as [Hycur [Hscur [Hg Hk]]]. subst k.
  unfold StripIndex in Hycur, Hscur.
  destruct Hycur as [[_ Hycur] | [Hbad _]]; [|lia].
  destruct Hscur as [[Hbad _] | [Hgbound Hcurx]]; [lia |].
  set (lo := Znth g xs 0).
  set (hi := Znth (g + 1) xs 0).
  assert (Hloin : In lo xs) by
    (unfold lo; apply Znth_In_Zlength; lia).
  assert (Hhiin : In hi xs) by
    (unfold hi; apply Znth_In_Zlength; lia).
  split.
  - intro Hinc. destruct Honq as [Hxq | Hyq].
    + exfalso. apply (vertical_horizontal_not_Inconvenient__classification
        xs ys q cur Hxq Hycur). exact Hinc.
    + assert (Hinside : lo < fst q < hi).
      { destruct (Z_le_gt_dec (fst q) lo) as [Hlow | Hlow].
        - exfalso. apply (horizontal_via_vertical_not_Inconvenient__classification
            xs ys q cur lo Hyq Hycur Hloin ltac:(left; unfold lo, hi in *; lia)).
          exact Hinc.
        - destruct (Z_le_gt_dec hi (fst q)) as [Hhigh | Hhigh]; [|lia].
          exfalso. apply (horizontal_via_vertical_not_Inconvenient__classification
            xs ys q cur hi Hyq Hycur Hhiin ltac:(right; unfold lo, hi in *; lia)).
          exact Hinc. }
      exists (snd q). split.
      * unfold HorizontalEntry. split.
        -- unfold StripIndex. left. auto.
        -- split.
           ++ unfold StripIndex. right. split; [exact Hgbound |].
              unfold lo, hi in Hinside. exact Hinside.
           ++ split; [exact Hg | reflexivity].
      * intro Heq. exfalso.
        pose proof (shared_horizontal_not_Inconvenient__classification
          xs ys q cur Heq Hyq) as Hnot. exact (Hnot Hinc).
    
  - intros [kq [Hq Hneq]].
    assert (Hcur' : HorizontalEntry xs ys cur g (snd cur)).
    { unfold HorizontalEntry. split.
      - unfold StripIndex. left. split; [reflexivity | exact Hycur].
      - split.
        + unfold StripIndex. right. split; assumption.
        + split; [exact Hg | reflexivity]. }
    pose proof (horizontal_entries_Inconvenient_iff__classification
      xs ys q cur g kq g (snd cur) Hmono Hq Hcur') as Hiff.
    apply (proj2 Hiff). split; [reflexivity |].
    unfold HorizontalEntry in Hq. destruct Hq as [_ [_ [_ ->]]]. exact Hneq.
Qed.

Require Import Coq.Logic.ClassicalEpsilon.

Lemma mono_inc_Znth_injective__classification :
  forall l i j,
    mono_inc l ->
    0 <= i < Zlength l -> 0 <= j < Zlength l ->
    Znth i l 0 = Znth j l 0 -> i = j.
Proof.
  intros l i j Hmono Hi Hj Heq.
  destruct (Z.lt_trichotomy i j) as [Hij | [Hij | Hij]]; [|exact Hij|].
  - exfalso. pose proof (Hmono i j ltac:(lia) Hij ltac:(lia)). lia.
  - exfalso. pose proof (Hmono j i ltac:(lia) Hij ltac:(lia)). lia.
Qed.

Lemma StripIndex_nonnegative_functional__classification :
  forall streets v r s,
    mono_inc streets -> 0 <= r -> 0 <= s ->
    StripIndex streets v r -> StripIndex streets v s -> r = s.
Proof.
  intros streets v r s Hmono Hr Hs Hri Hsi.
  unfold StripIndex in Hri, Hsi.
  destruct Hri as [[Hbad _] | [Hrb Hrv]]; [lia |].
  destruct Hsi as [[Hbad _] | [Hsb Hsv]]; [lia |].
  destruct (Z.lt_trichotomy r s) as [Hrs | [Hrs | Hsr]]; [|exact Hrs|].
  - assert (Hle : Znth (r + 1) streets 0 <= Znth s streets 0).
    { destruct (Z.eq_dec (r + 1) s) as [Heq | Hne].
      - subst s. reflexivity.
      - apply Z.lt_le_incl. apply Hmono; lia. }
    lia.
  - assert (Hle : Znth (s + 1) streets 0 <= Znth r streets 0).
    { destruct (Z.eq_dec (s + 1) r) as [Heq | Hne].
      - subst r. reflexivity.
      - apply Z.lt_le_incl. apply Hmono; lia. }
    lia.
Qed.

Lemma VerticalEntry_functional__classification :
  forall xs ys p g1 k1 g2 k2,
    mono_inc ys ->
    VerticalEntry xs ys p g1 k1 -> VerticalEntry xs ys p g2 k2 ->
    g1 = g2 /\ k1 = k2.
Proof.
  intros xs ys p g1 k1 g2 k2 Hmono H1 H2.
  unfold VerticalEntry in H1, H2.
  destruct H1 as [Hs1 [Hg1 Hk1]], H2 as [Hs2 [Hg2 Hk2]].
  split.
  - eapply StripIndex_nonnegative_functional__classification; eauto.
  - lia.
Qed.

Lemma HorizontalEntry_functional__classification :
  forall xs ys p g1 k1 g2 k2,
    mono_inc xs ->
    HorizontalEntry xs ys p g1 k1 -> HorizontalEntry xs ys p g2 k2 ->
    g1 = g2 /\ k1 = k2.
Proof.
  intros xs ys p g1 k1 g2 k2 Hmono H1 H2.
  unfold HorizontalEntry in H1, H2.
  destruct H1 as [_ [Hs1 [Hg1 Hk1]]], H2 as [_ [Hs2 [Hg2 Hk2]]].
  split.
  - eapply StripIndex_nonnegative_functional__classification; eauto.
  - lia.
Qed.

Definition IndexOf__classification (indices : list Z) (q : Z) : Z :=
  epsilon (inhabits 0)
    (fun t => 0 <= t < Zlength indices /\ Znth t indices 0 = q).

Lemma IndexOf_spec__classification :
  forall indices q,
    In q indices ->
    0 <= IndexOf__classification indices q < Zlength indices /\
    Znth (IndexOf__classification indices q) indices 0 = q.
Proof.
  intros indices q Hin. unfold IndexOf__classification.
  apply epsilon_spec. apply In_as_Znth__classification. exact Hin.
Qed.

Lemma Pre_OnStreet_Znth__classification :
  forall xs ys people i,
    Pre xs ys people -> 0 <= i < Zlength people ->
    OnStreet xs ys (Znth i people (0, 0)).
Proof.
  intros xs ys people i Hpre Hi.
  unfold Pre in Hpre. destruct Hpre as [Hall _].
  apply (proj1 (Forall_Znth (fun p => OnStreet xs ys p) (0, 0) people) Hall).
  exact Hi.
Qed.

Lemma EnumeratesEntries_new_endpoint_card__classification :
  forall (Entry : (Z * Z) -> Z -> Z -> Prop)
         (people : list (Z * Z)) p groups keys g k
         (Inc : Z -> Prop),
    EnumeratesEntries Entry people p groups keys ->
    (forall person g1 k1 g2 k2,
      Entry person g1 k1 -> Entry person g2 k2 ->
      g1 = g2 /\ k1 = k2) ->
    (forall q, 0 <= q < p ->
      (Inc q <-> exists kq,
        Entry (Znth q people (0, 0)) g kq /\ kq <> k)) ->
    #(fun q : Z => 0 <= q < p /\ Inc q) =
    #(fun t : Z => 0 <= t < Zlength groups /\
      Znth t groups 0 = g /\ Znth t keys 0 <> k).
Proof.
  intros Entry people p groups keys g k Inc Henum Hfunctional Hgeom.
  unfold EnumeratesEntries in Henum.
  destruct Henum as
    [indices [Hilen [Hgklen [Hmono [Hindexed Hcomplete]]]]].
  eapply set_card_bijection__classification
    with (f := fun q => IndexOf__classification indices q)
         (g := fun t => Znth t indices 0).
  - intros q [Hq Hinc].
    destruct (proj1 (Hgeom q Hq) Hinc) as [kq [Hentry Hneq]].
    assert (Hinq : In q indices).
    { apply Hcomplete; [exact Hq |]. exists g, kq. exact Hentry. }
    destruct (IndexOf_spec__classification indices q Hinq) as [Ht Htq].
    specialize (Hindexed (IndexOf__classification indices q) Ht).
    destruct Hindexed as [_ Henum_entry].
    rewrite Htq in Henum_entry.
    destruct (Hfunctional (Znth q people (0, 0))
      (Znth (IndexOf__classification indices q) groups 0)
      (Znth (IndexOf__classification indices q) keys 0)
      g kq Henum_entry Hentry) as [Hgroup Hkey].
    rewrite Hilen in Ht. split; [exact Ht |].
    split; [exact Hgroup |].
    intro Heq. apply Hneq. rewrite <- Hkey. exact Heq.
  - intros t [Ht [Hgroup Hneq]].
    assert (Hti : 0 <= t < Zlength indices) by (rewrite Hilen; exact Ht).
    specialize (Hindexed t Hti).
    destruct Hindexed as [Hq Hentry].
    split; [exact Hq |]. apply (proj2 (Hgeom (Znth t indices 0) Hq)).
    exists (Znth t keys 0). split.
    + rewrite Hgroup in Hentry. exact Hentry.
    + exact Hneq.
  - intros q [Hq Hinc].
    destruct (proj1 (Hgeom q Hq) Hinc) as [kq [Hentry _]].
    assert (Hinq : In q indices).
    { apply Hcomplete; [exact Hq |]. exists g, kq. exact Hentry. }
    exact (proj2 (IndexOf_spec__classification indices q Hinq)).
  - intros t [Ht _].
    assert (Hti : 0 <= t < Zlength indices) by (rewrite Hilen; exact Ht).
    assert (Hin : In (Znth t indices 0) indices).
    { apply Znth_In_Zlength. exact Hti. }
    destruct (IndexOf_spec__classification indices (Znth t indices 0) Hin)
      as [Hindex Hvalue].
    apply (mono_inc_Znth_injective__classification indices
      (IndexOf__classification indices (Znth t indices 0)) t Hmono
      Hindex Hti Hvalue).
Qed.

Lemma vertical_new_endpoint_card__classification :
  forall xs ys people p groups keys g k,
    Pre xs ys people -> 0 <= p < Zlength people ->
    VerticalEntry xs ys (Znth p people (0, 0)) g k ->
    EnumeratesEntries (VerticalEntry xs ys) people p groups keys ->
    #(fun q : Z => 0 <= q < p /\
      Inconvenient xs ys (Znth q people (0, 0))
        (Znth p people (0, 0))) =
    #(fun t : Z => 0 <= t < Zlength groups /\
      Znth t groups 0 = g /\ Znth t keys 0 <> k).
Proof.
  intros xs ys people p groups keys g k Hpre Hp Hcur Henum.
  eapply EnumeratesEntries_new_endpoint_card__classification
    with (Entry := VerticalEntry xs ys)
         (Inc := fun q => Inconvenient xs ys
           (Znth q people (0, 0)) (Znth p people (0, 0))).
  - exact Henum.
  - intros person g1 k1 g2 k2.
    eapply VerticalEntry_functional__classification.
    unfold Pre in Hpre. tauto.
  - intros q Hq. apply Inconvenient_with_vertical_entry_iff__classification.
    + unfold Pre in Hpre. tauto.
    + apply (Pre_OnStreet_Znth__classification xs ys people q Hpre ltac:(lia)).
    + apply (Pre_OnStreet_Znth__classification xs ys people p Hpre Hp).
    + exact Hcur.
Qed.

Lemma horizontal_new_endpoint_card__classification :
  forall xs ys people p groups keys g k,
    Pre xs ys people -> 0 <= p < Zlength people ->
    HorizontalEntry xs ys (Znth p people (0, 0)) g k ->
    EnumeratesEntries (HorizontalEntry xs ys) people p groups keys ->
    #(fun q : Z => 0 <= q < p /\
      Inconvenient xs ys (Znth q people (0, 0))
        (Znth p people (0, 0))) =
    #(fun t : Z => 0 <= t < Zlength groups /\
      Znth t groups 0 = g /\ Znth t keys 0 <> k).
Proof.
  intros xs ys people p groups keys g k Hpre Hp Hcur Henum.
  eapply EnumeratesEntries_new_endpoint_card__classification
    with (Entry := HorizontalEntry xs ys)
         (Inc := fun q => Inconvenient xs ys
           (Znth q people (0, 0)) (Znth p people (0, 0))).
  - exact Henum.
  - intros person g1 k1 g2 k2.
    eapply HorizontalEntry_functional__classification.
    unfold Pre in Hpre. tauto.
  - intros q Hq. apply Inconvenient_with_horizontal_entry_iff__classification.
    + unfold Pre in Hpre. tauto.
    + apply (Pre_OnStreet_Znth__classification xs ys people q Hpre ltac:(lia)).
    + exact Hcur.
Qed.

Lemma EnumeratesEntries_lengths__classification :
  forall Entry people p groups keys,
    EnumeratesEntries Entry people p groups keys ->
    Zlength groups = Zlength keys.
Proof.
  intros Entry people p groups keys
    [indices [_ [Hlen _]]]. exact Hlen.
Qed.

Lemma PairCountPrefix_functional__classification :
  forall groups keys hi a b,
    PairCountPrefix groups keys hi a ->
    PairCountPrefix groups keys hi b -> a = b.
Proof.
  intros groups keys hi a b Ha Hb.
  unfold PairCountPrefix in Ha, Hb. lia.
Qed.

Definition InconvenientIndexRel__classification
    (xs ys : list Z) (people : list (Z * Z)) (i j : Z) : Prop :=
  Inconvenient xs ys
    (Znth i people (0, 0)) (Znth j people (0, 0)).

Lemma ClassifiedCountsCorrect_vertical_extend__classification :
  forall xs ys people p vg vk hg hk g k,
    Pre xs ys people -> 0 <= p < Zlength people ->
    ClassifiedPrefix xs ys people p vg vk hg hk ->
    ClassifiedCountsCorrect xs ys people p vg vk hg hk ->
    VerticalEntry xs ys (Znth p people (0, 0)) g k ->
    ClassifiedCountsCorrect xs ys people (p + 1)
      (vg ++ [g]) (vk ++ [k]) hg hk.
Proof.
  intros xs ys people p vg vk hg hk g k
    Hpre Hp [Hvenum Hhenum] Hcorrect Hentry.
  assert (Hvlen : Zlength vg = Zlength vk).
  { eapply EnumeratesEntries_lengths__classification; exact Hvenum. }
  set (oldv := #(fun ij : Z * Z =>
    0 <= fst ij < Zlength vg /\ 0 <= snd ij < Zlength vg /\
    fst ij < snd ij /\ Znth (fst ij) vg 0 = Znth (snd ij) vg 0 /\
    Znth (fst ij) vk 0 <> Znth (snd ij) vk 0)).
  set (oldh := #(fun ij : Z * Z =>
    0 <= fst ij < Zlength hg /\ 0 <= snd ij < Zlength hg /\
    fst ij < snd ij /\ Znth (fst ij) hg 0 = Znth (snd ij) hg 0 /\
    Znth (fst ij) hk 0 <> Znth (snd ij) hk 0)).
  assert (Hvold : PairCountPrefix vg vk (Zlength vg) oldv) by reflexivity.
  assert (Hhold : PairCountPrefix hg hk (Zlength hg) oldh) by reflexivity.
  set (delta := #(fun t : Z => 0 <= t < Zlength vg /\
    Znth t vg 0 = g /\ Znth t vk 0 <> k)).
  assert (Hvappend : PairCountPrefix (vg ++ [g]) (vk ++ [k])
    (Zlength (vg ++ [g])) (oldv + delta)).
  { apply PairCountPrefix_append__classification; assumption. }
  assert (Hnew : NewEndpointCard__classification p
      (InconvenientIndexRel__classification xs ys people) = delta).
  { unfold NewEndpointCard__classification, delta,
      InconvenientIndexRel__classification.
    apply vertical_new_endpoint_card__classification; assumption. }
  pose proof (Hcorrect oldv oldh Hvold Hhold) as Holdsum.
  change (oldv + oldh = PrefixPairCard__classification p
    (InconvenientIndexRel__classification xs ys people)) in Holdsum.
  pose proof (PrefixPairCard_extend__classification p
    (InconvenientIndexRel__classification xs ys people) ltac:(lia)) as Hextend.
  unfold ClassifiedCountsCorrect. intros vertical horizontal Hvnew Hhnew.
  assert (Hveq : vertical = oldv + delta).
  { eapply PairCountPrefix_functional__classification; eauto. }
  assert (Hheq : horizontal = oldh).
  { eapply PairCountPrefix_functional__classification; eauto. }
  change (vertical + horizontal = PrefixPairCard__classification (p + 1)
    (InconvenientIndexRel__classification xs ys people)).
  lia.
Qed.

Lemma ClassifiedCountsCorrect_horizontal_extend__classification :
  forall xs ys people p vg vk hg hk g k,
    Pre xs ys people -> 0 <= p < Zlength people ->
    ClassifiedPrefix xs ys people p vg vk hg hk ->
    ClassifiedCountsCorrect xs ys people p vg vk hg hk ->
    HorizontalEntry xs ys (Znth p people (0, 0)) g k ->
    ClassifiedCountsCorrect xs ys people (p + 1)
      vg vk (hg ++ [g]) (hk ++ [k]).
Proof.
  intros xs ys people p vg vk hg hk g k
    Hpre Hp [Hvenum Hhenum] Hcorrect Hentry.
  assert (Hhlen : Zlength hg = Zlength hk).
  { eapply EnumeratesEntries_lengths__classification; exact Hhenum. }
  set (oldv := #(fun ij : Z * Z =>
    0 <= fst ij < Zlength vg /\ 0 <= snd ij < Zlength vg /\
    fst ij < snd ij /\ Znth (fst ij) vg 0 = Znth (snd ij) vg 0 /\
    Znth (fst ij) vk 0 <> Znth (snd ij) vk 0)).
  set (oldh := #(fun ij : Z * Z =>
    0 <= fst ij < Zlength hg /\ 0 <= snd ij < Zlength hg /\
    fst ij < snd ij /\ Znth (fst ij) hg 0 = Znth (snd ij) hg 0 /\
    Znth (fst ij) hk 0 <> Znth (snd ij) hk 0)).
  assert (Hvold : PairCountPrefix vg vk (Zlength vg) oldv) by reflexivity.
  assert (Hhold : PairCountPrefix hg hk (Zlength hg) oldh) by reflexivity.
  set (delta := #(fun t : Z => 0 <= t < Zlength hg /\
    Znth t hg 0 = g /\ Znth t hk 0 <> k)).
  assert (Hhappend : PairCountPrefix (hg ++ [g]) (hk ++ [k])
    (Zlength (hg ++ [g])) (oldh + delta)).
  { apply PairCountPrefix_append__classification; assumption. }
  assert (Hnew : NewEndpointCard__classification p
      (InconvenientIndexRel__classification xs ys people) = delta).
  { unfold NewEndpointCard__classification, delta,
      InconvenientIndexRel__classification.
    apply horizontal_new_endpoint_card__classification; assumption. }
  pose proof (Hcorrect oldv oldh Hvold Hhold) as Holdsum.
  change (oldv + oldh = PrefixPairCard__classification p
    (InconvenientIndexRel__classification xs ys people)) in Holdsum.
  pose proof (PrefixPairCard_extend__classification p
    (InconvenientIndexRel__classification xs ys people) ltac:(lia)) as Hextend.
  unfold ClassifiedCountsCorrect. intros vertical horizontal Hvnew Hhnew.
  assert (Hveq : vertical = oldv).
  { eapply PairCountPrefix_functional__classification; eauto. }
  assert (Hheq : horizontal = oldh + delta).
  { eapply PairCountPrefix_functional__classification; eauto. }
  change (vertical + horizontal = PrefixPairCard__classification (p + 1)
    (InconvenientIndexRel__classification xs ys people)).
  lia.
Qed.

Lemma intersection_new_endpoint_card_zero__classification :
  forall xs ys people p,
    Pre xs ys people -> 0 <= p < Zlength people ->
    In (fst (Znth p people (0, 0))) xs ->
    In (snd (Znth p people (0, 0))) ys ->
    NewEndpointCard__classification p
      (InconvenientIndexRel__classification xs ys people) = 0.
Proof.
  intros xs ys people p Hpre Hp Hx Hy.
  unfold NewEndpointCard__classification.
  rewrite set_card_Z_range_filter_as_sum__classification.
  apply sum_Z_range_eq_zero. intros q Hq.
  destruct (prop_dec (InconvenientIndexRel__classification xs ys people q p))
    as [Hinc | Hnot]; [|reflexivity].
  exfalso. apply (intersection_second_not_Inconvenient__classification
    xs ys (Znth q people (0, 0)) (Znth p people (0, 0))).
  - apply (Pre_OnStreet_Znth__classification xs ys people q Hpre ltac:(lia)).
  - exact Hx.
  - exact Hy.
  - exact Hinc.
Qed.

Lemma ClassifiedCountsCorrect_intersection_extend__classification :
  forall xs ys people p vg vk hg hk,
    Pre xs ys people -> 0 <= p < Zlength people ->
    ClassifiedCountsCorrect xs ys people p vg vk hg hk ->
    In (fst (Znth p people (0, 0))) xs ->
    In (snd (Znth p people (0, 0))) ys ->
    ClassifiedCountsCorrect xs ys people (p + 1) vg vk hg hk.
Proof.
  intros xs ys people p vg vk hg hk Hpre Hp Hcorrect Hx Hy.
  set (oldv := #(fun ij : Z * Z =>
    0 <= fst ij < Zlength vg /\ 0 <= snd ij < Zlength vg /\
    fst ij < snd ij /\ Znth (fst ij) vg 0 = Znth (snd ij) vg 0 /\
    Znth (fst ij) vk 0 <> Znth (snd ij) vk 0)).
  set (oldh := #(fun ij : Z * Z =>
    0 <= fst ij < Zlength hg /\ 0 <= snd ij < Zlength hg /\
    fst ij < snd ij /\ Znth (fst ij) hg 0 = Znth (snd ij) hg 0 /\
    Znth (fst ij) hk 0 <> Znth (snd ij) hk 0)).
  assert (Hvold : PairCountPrefix vg vk (Zlength vg) oldv) by reflexivity.
  assert (Hhold : PairCountPrefix hg hk (Zlength hg) oldh) by reflexivity.
  pose proof (Hcorrect oldv oldh Hvold Hhold) as Holdsum.
  change (oldv + oldh = PrefixPairCard__classification p
    (InconvenientIndexRel__classification xs ys people)) in Holdsum.
  pose proof (PrefixPairCard_extend__classification p
    (InconvenientIndexRel__classification xs ys people) ltac:(lia)) as Hextend.
  pose proof (intersection_new_endpoint_card_zero__classification
    xs ys people p Hpre Hp Hx Hy) as Hzero.
  unfold ClassifiedCountsCorrect. intros vertical horizontal Hvnew Hhnew.
  assert (Hveq : vertical = oldv).
  { eapply PairCountPrefix_functional__classification; eauto. }
  assert (Hheq : horizontal = oldh).
  { eapply PairCountPrefix_functional__classification; eauto. }
  change (vertical + horizontal = PrefixPairCard__classification (p + 1)
    (InconvenientIndexRel__classification xs ys people)).
  lia.
Qed.

Lemma Znth_combine__sift_swap :
  forall {A B : Type} (xs : list A) (ys : list B) i da db,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (da, db) = (Znth i xs da, Znth i ys db).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys i da db Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma replace_Znth_length_one__sift_swap :
  forall {A : Type} (l : list A) i v,
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A l i v. unfold replace_Znth. rewrite !Zlength_correct.
  assert (Hlen : forall (xs : list A) n,
    length (replace_nth n xs v) = length xs).
  {
    intros xs. induction xs as [|x xs IH]; intros [|n]; simpl; auto.
  }
  rewrite Hlen. reflexivity.
Qed.
Lemma replace_Znth_two_swap_length__sift_swap :
  forall {A : Type} (l : list A) i j vi vj,
    Zlength (replace_Znth j vj (replace_Znth i vi l)) = Zlength l.
Proof.
  intros. repeat rewrite replace_Znth_length_one__sift_swap. reflexivity.
Qed.
Lemma sublist_two_swap_below_cut__sift_swap :
  forall {A : Type} (l : list A) (vi vj : A) i j lo hi,
    0 <= i < lo ->
    0 <= j < lo ->
    0 <= lo <= hi ->
    hi <= Zlength l ->
    sublist lo hi (replace_Znth j vj (replace_Znth i vi l)) =
    sublist lo hi l.
Proof.
  intros A l vi vj i j lo hi Hi Hj Hlohi Hhi.
  apply (proj2 (list_eq_ext _ _ vi)). split.
  - rewrite !Zlength_sublist by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite !Znth_sublist by lia.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.
Lemma permutation_move_head_to_index__sift_swap :
  forall {A : Type} (a d : A) (l : list A) j,
    0 <= j < Zlength l ->
    Permutation (a :: l) (Znth j l d :: replace_Znth j a l).
Proof.
  intros A a d l. revert a.
  induction l as [|b l IH]; intros a j Hj.
  - rewrite Zlength_nil in Hj. lia.
  - destruct (Z.eq_dec j 0) as [-> | Hj0].
    + apply perm_swap.
    + rewrite Znth_cons by lia.
      rewrite replace_Znth_cons by lia.
      eapply Permutation_trans.
      * apply perm_swap.
      * eapply Permutation_trans.
        -- apply perm_skip. apply (IH a (j - 1)).
           rewrite Zlength_cons in Hj. lia.
        -- apply perm_swap.
Qed.
Lemma permutation_two_swap_lt__sift_swap :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < j ->
    j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l. induction l as [|a l IH]; intros i j d Hij Hj.
  - rewrite Zlength_nil in Hj. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hi0].
    + assert (Hj0 : 0 < j) by lia.
      rewrite Znth0_cons.
      change
        (Permutation (a :: l)
          (replace_Znth j a (Znth j (a :: l) d :: l))).
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply permutation_move_head_to_index__sift_swap.
      rewrite Zlength_cons in Hj. lia.
    + assert (Hi : 0 < i) by lia.
      assert (Hj0 : 0 < j) by lia.
      rewrite !Znth_cons by lia.
      rewrite !replace_Znth_cons by lia.
      apply perm_skip. apply IH.
      * rewrite Zlength_cons in Hj. lia.
      * rewrite Zlength_cons in Hj. lia.
Qed.
Lemma combine_replace_Znth_both__sift_swap :
  forall {A B : Type} (xs : list A) (ys : list B) i x y,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    combine (replace_Znth i x xs) (replace_Znth i y ys) =
    replace_Znth i (x, y) (combine xs ys).
Proof.
  intros A B xs. induction xs as [|a xs IH]; intros ys i x y Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|b ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !replace_Znth_cons by lia. simpl. f_equal.
        apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_combine_eq__sift_swap :
  forall {A B : Type} (xs : list A) (ys : list B),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma combine_two_swap__sift_swap :
  forall (groups keys : list Z) root child,
    Zlength groups = Zlength keys ->
    0 <= root < Zlength groups ->
    0 <= child < Zlength groups ->
    combine
      (replace_Znth child (Znth root groups 0)
        (replace_Znth root (Znth child groups 0) groups))
      (replace_Znth child (Znth root keys 0)
        (replace_Znth root (Znth child keys 0) keys)) =
    replace_Znth child (Znth root (combine groups keys) (0, 0))
      (replace_Znth root (Znth child (combine groups keys) (0, 0))
        (combine groups keys)).
Proof.
  intros groups keys root child Hlen Hroot Hchild.
  rewrite combine_replace_Znth_both__sift_swap
    by (repeat rewrite replace_Znth_length_one__sift_swap; lia).
  rewrite combine_replace_Znth_both__sift_swap by lia.
  rewrite <- (Znth_combine__sift_swap groups keys root 0 0 Hlen Hroot).
  rewrite <- (Znth_combine__sift_swap groups keys child 0 0 Hlen Hchild).
  reflexivity.
Qed.
Lemma parallel_permutation_two_swap__sift_swap :
  forall groups keys groups_now keys_now root child,
    ParallelPermutation groups keys groups_now keys_now ->
    Zlength groups_now = Zlength keys_now ->
    0 <= root < child ->
    child < Zlength groups_now ->
    ParallelPermutation groups keys
      (replace_Znth child (Znth root groups_now 0)
        (replace_Znth root (Znth child groups_now 0) groups_now))
      (replace_Znth child (Znth root keys_now 0)
        (replace_Znth root (Znth child keys_now 0) keys_now)).
Proof.
  intros groups keys groups_now keys_now root child
    Hperm Hlen Hroots Hchild.
  unfold ParallelPermutation in *.
  eapply Permutation_trans; [exact Hperm |].
  rewrite combine_two_swap__sift_swap by lia.
  apply permutation_two_swap_lt__sift_swap.
  - exact Hroots.
  - rewrite Zlength_combine_eq__sift_swap by exact Hlen. lia.
Qed.
Lemma heap_parent_bounds_items__sift_swap :
  forall child,
    0 < child ->
    0 <= (child - 1) / 2 < child.
Proof.
  intros child Hchild. split.
  - apply Z_div_nonneg_nonneg; lia.
  - assert ((child - 1) / 2 <= child - 1) by
      (apply Z.div_le_upper_bound; lia).
    lia.
Qed.
Lemma heap_children_characterization_items__sift_swap :
  forall root child,
    0 <= root ->
    0 < child ->
    (child - 1) / 2 = root ->
    child = 2 * root + 1 \/ child = 2 * root + 2.
Proof.
  intros root child Hroot Hchild Hparent.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hrem.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hquot.
  rewrite Hparent in Hquot.
  assert (Z.modulo (child - 1) 2 = 0 \/ Z.modulo (child - 1) 2 = 1)
    as [Hr | Hr] by lia; lia.
Qed.
Lemma selected_child_parent_items__sift_swap :
  forall groups keys root hi child,
    0 <= root ->
    SelectedLargerChildItems groups keys root hi child ->
    (child - 1) / 2 = root.
Proof.
  intros groups keys root hi child Hroot
    [[Hleft | Hright] _]; subst child.
  - replace (2 * root + 1 - 1) with (root * 2) by ring.
    rewrite Z.div_mul by lia. reflexivity.
  - replace (2 * root + 2 - 1) with (root * 2 + 1) by ring.
    pose proof (Z.mod_pos_bound (root * 2 + 1) 2 ltac:(lia)) as Hrem.
    pose proof (Z.div_mod (root * 2 + 1) 2 ltac:(lia)) as Hquot.
    assert (Z.modulo (root * 2 + 1) 2 = 1) by lia. lia.
Qed.
Lemma swap_preserves_prefix_suffix_relation__sift_swap :
  forall {A : Type} (R : A -> A -> Prop) (l : list A) split root child d,
    0 <= root < child ->
    child < split ->
    split <= Zlength l ->
    (forall p q, 0 <= p < split -> split <= q < Zlength l ->
      R (Znth p l d) (Znth q l d)) ->
    forall p q,
      0 <= p < split ->
      split <= q < Zlength l ->
      R
        (Znth p
          (replace_Znth child (Znth root l d)
            (replace_Znth root (Znth child l d) l)) d)
        (Znth q
          (replace_Znth child (Znth root l d)
            (replace_Znth root (Znth child l d) l)) d).
Proof.
  intros A R l split root child d Hroots Hchild Hsplit Hrel p q Hp Hq.
  assert (Hroot_range : 0 <= root < Zlength l) by lia.
  assert (Hchild_range : 0 <= child < Zlength l) by lia.
  set (swapped :=
    replace_Znth child (Znth root l d)
      (replace_Znth root (Znth child l d) l)).
  assert (Hswap_root : Znth root swapped d = Znth child l d).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite Znth_replace_Znth_Same by exact Hroot_range.
    reflexivity.
  }
  assert (Hswap_child : Znth child swapped d = Znth root l d).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Same by
      (rewrite replace_Znth_length_one__sift_swap; exact Hchild_range).
    reflexivity.
  }
  assert (Hswap_other : forall x,
    0 <= x < Zlength l -> x <> root -> x <> child ->
    Znth x swapped d = Znth x l d).
  {
    intros x Hx Hxr Hxc. unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  change (R (Znth p swapped d) (Znth q swapped d)).
  rewrite (Hswap_other q) by lia.
  destruct (Z.eq_dec p child) as [-> | Hpchild].
  - rewrite Hswap_child.
    apply Hrel; lia.
  -
    destruct (Z.eq_dec p root) as [-> | Hproot].
    + rewrite Hswap_root.
      apply Hrel; lia.
    + rewrite Hswap_other by lia.
      apply Hrel; lia.
Qed.
Lemma extraction_frame_two_swap__sift_swap :
  forall groups keys split root child,
    Zlength groups = Zlength keys ->
    0 <= root < child ->
    child < split ->
    split <= Zlength groups ->
    ExtractionFrameItems groups keys split ->
    ExtractionFrameItems
      (replace_Znth child (Znth root groups 0)
        (replace_Znth root (Znth child groups 0) groups))
      (replace_Znth child (Znth root keys 0)
        (replace_Znth root (Znth child keys 0) keys)) split.
Proof.
  intros groups keys split root child Hlen Hroots Hchild Hsplit
    [Hinc Hcross].
  unfold ExtractionFrameItems. split.
  - repeat rewrite replace_Znth_length_one__sift_swap.
    rewrite sublist_two_swap_below_cut__sift_swap by lia.
    rewrite sublist_two_swap_below_cut__sift_swap by lia.
    exact Hinc.
  - repeat rewrite replace_Znth_length_one__sift_swap.
    intros p q Hp Hq.
    rewrite combine_two_swap__sift_swap by lia.
    eapply (swap_preserves_prefix_suffix_relation__sift_swap
      ItemLe (combine groups keys) split root child (0, 0)).
    + exact Hroots.
    + exact Hchild.
    + rewrite Zlength_combine_eq__sift_swap by exact Hlen. exact Hsplit.
    + intros p0 q0 Hp0 Hq0. apply Hcross; [exact Hp0 |].
      rewrite Zlength_combine_eq__sift_swap in Hq0 by exact Hlen. exact Hq0.
    + exact Hp.
    + rewrite Zlength_combine_eq__sift_swap by exact Hlen. exact Hq.
Qed.
Lemma heap_except_after_selected_swap_items__sift_swap :
  forall (items : list (Z * Z)) root_pre root hi child,
    0 <= root_pre <= root ->
    root <= hi ->
    hi < Zlength items ->
    (child = 2 * root + 1 \/ child = 2 * root + 2) ->
    child <= hi ->
    (2 * root + 1 <= hi ->
      ItemLe (Znth (2 * root + 1) items (0, 0))
             (Znth child items (0, 0))) ->
    (2 * root + 2 <= hi ->
      ItemLe (Znth (2 * root + 2) items (0, 0))
             (Znth child items (0, 0))) ->
    ItemLe (Znth root items (0, 0)) (Znth child items (0, 0)) ->
    (forall k,
      1 <= k <= hi -> root_pre <= (k - 1) / 2 ->
      (k - 1) / 2 <> root ->
      ItemLe (Znth k items (0, 0))
             (Znth ((k - 1) / 2) items (0, 0))) ->
    (1 <= root -> root_pre <= (root - 1) / 2 ->
      ItemLe (Znth child items (0, 0))
             (Znth ((root - 1) / 2) items (0, 0))) ->
    forall k,
      1 <= k <= hi -> root_pre <= (k - 1) / 2 ->
      (k - 1) / 2 <> child ->
      ItemLe
        (Znth k
          (replace_Znth child (Znth root items (0, 0))
            (replace_Znth root (Znth child items (0, 0)) items)) (0, 0))
        (Znth ((k - 1) / 2)
          (replace_Znth child (Znth root items (0, 0))
            (replace_Znth root (Znth child items (0, 0)) items)) (0, 0)).
Proof.
  intros items root_pre root hi child Hroots Hroot_hi Hhi Hchild_shape
    Hchild_hi Hleft Hright Hrise Hheap Henter k Hk Hparent
    Hparent_not_child.
  assert (Hchild_parent : (child - 1) / 2 = root).
  {
    destruct Hchild_shape as [Hshape | Hshape]; subst child.
    - replace (2 * root + 1 - 1) with (root * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity.
    - replace (2 * root + 2 - 1) with (root * 2 + 1) by ring.
      pose proof (Z.mod_pos_bound (root * 2 + 1) 2 ltac:(lia)) as Hrem.
      pose proof (Z.div_mod (root * 2 + 1) 2 ltac:(lia)) as Hquot.
      assert (Z.modulo (root * 2 + 1) 2 = 1) by lia. lia.
  }
  assert (Hroot_child : root < child) by
    (destruct Hchild_shape as [-> | ->]; lia).
  assert (Hroot_range : 0 <= root < Zlength items) by lia.
  assert (Hchild_range : 0 <= child < Zlength items) by lia.
  set (swapped :=
    replace_Znth child (Znth root items (0, 0))
      (replace_Znth root (Znth child items (0, 0)) items)).
  assert (Hswap_root :
    Znth root swapped (0, 0) = Znth child items (0, 0)).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite Znth_replace_Znth_Same by exact Hroot_range.
    reflexivity.
  }
  assert (Hswap_child :
    Znth child swapped (0, 0) = Znth root items (0, 0)).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Same by
      (rewrite replace_Znth_length_one__sift_swap; exact Hchild_range).
    reflexivity.
  }
  assert (Hswap_other : forall x,
    0 <= x < Zlength items -> x <> root -> x <> child ->
    Znth x swapped (0, 0) = Znth x items (0, 0)).
  {
    intros x Hx Hxr Hxc. unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  change (ItemLe (Znth k swapped (0, 0))
    (Znth ((k - 1) / 2) swapped (0, 0))).
  pose proof (heap_parent_bounds_items__sift_swap k ltac:(lia)) as Hp_bounds.
  assert (Hk_range : 0 <= k < Zlength items) by lia.
  assert (Hp_range : 0 <= (k - 1) / 2 < Zlength items) by lia.
  destruct (Z.eq_dec ((k - 1) / 2) root)
    as [Hparent_root | Hparent_not_root].
  - destruct (Z.eq_dec k child) as [Hk_child | Hk_not_child].
    + subst k. rewrite Hswap_child, Hchild_parent, Hswap_root. exact Hrise.
    + assert (Hk_not_root : k <> root) by lia.
      rewrite Hparent_root, Hswap_root.
      rewrite Hswap_other by assumption.
      destruct (heap_children_characterization_items__sift_swap
        root k ltac:(lia) ltac:(lia) Hparent_root) as [-> | ->].
      * apply Hleft. lia.
      * apply Hright. lia.
  - destruct (Z.eq_dec k root) as [Hk_root | Hk_not_root].
    + subst k.
      rewrite Hswap_root.
      rewrite Hswap_other by (try assumption; lia).
      apply Henter; [lia | exact Hparent].
    + assert (Hk_not_child : k <> child).
      { intro Heq. subst k. apply Hparent_not_root. exact Hchild_parent. }
      rewrite Hswap_other by assumption.
      rewrite Hswap_other by (try assumption; lia).
      apply Hheap; assumption.
Qed.
Lemma selected_swap_descendant_edge_items__sift_swap :
  forall (items : list (Z * Z)) root_pre root hi child descendant,
    0 <= root_pre <= root ->
    root <= hi ->
    hi < Zlength items ->
    (child = 2 * root + 1 \/ child = 2 * root + 2) ->
    child <= hi ->
    (forall k,
      1 <= k <= hi -> root_pre <= (k - 1) / 2 ->
      (k - 1) / 2 <> root ->
      ItemLe (Znth k items (0, 0))
             (Znth ((k - 1) / 2) items (0, 0))) ->
    (descendant = 2 * child + 1 \/ descendant = 2 * child + 2) ->
    descendant <= hi ->
    ItemLe
      (Znth descendant
        (replace_Znth child (Znth root items (0, 0))
          (replace_Znth root (Znth child items (0, 0)) items)) (0, 0))
      (Znth ((child - 1) / 2)
        (replace_Znth child (Znth root items (0, 0))
          (replace_Znth root (Znth child items (0, 0)) items)) (0, 0)).
Proof.
  intros items root_pre root hi child descendant Hroots Hroot_hi Hhi
    Hchild_shape Hchild_hi Hheap Hdesc_shape Hdesc_hi.
  assert (Hchild_parent : (child - 1) / 2 = root).
  {
    destruct Hchild_shape as [Hshape | Hshape]; subst child.
    - replace (2 * root + 1 - 1) with (root * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity.
    - replace (2 * root + 2 - 1) with (root * 2 + 1) by ring.
      pose proof (Z.mod_pos_bound (root * 2 + 1) 2 ltac:(lia)) as Hrem.
      pose proof (Z.div_mod (root * 2 + 1) 2 ltac:(lia)) as Hquot.
      assert (Z.modulo (root * 2 + 1) 2 = 1) by lia. lia.
  }
  assert (Hroot_child : root < child) by
    (destruct Hchild_shape as [-> | ->]; lia).
  assert (Hdesc_parent : (descendant - 1) / 2 = child).
  {
    destruct Hdesc_shape as [-> | ->].
    - replace (2 * child + 1 - 1) with (child * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity.
    - replace (2 * child + 2 - 1) with (child * 2 + 1) by ring.
      pose proof (Z.mod_pos_bound (child * 2 + 1) 2 ltac:(lia)) as Hrem.
      pose proof (Z.div_mod (child * 2 + 1) 2 ltac:(lia)) as Hquot.
      assert (Z.modulo (child * 2 + 1) 2 = 1) by lia. lia.
  }
  assert (Hroot_range : 0 <= root < Zlength items) by lia.
  assert (Hchild_range : 0 <= child < Zlength items) by lia.
  assert (Hdesc_range : 0 <= descendant < Zlength items) by
    (destruct Hdesc_shape as [-> | ->]; lia).
  pose proof (Hheap descendant ltac:(lia) ltac:(lia) ltac:(lia)) as Hedge.
  rewrite Hdesc_parent in Hedge.
  rewrite Hchild_parent.
  rewrite Znth_replace_Znth_Diff by
    (repeat rewrite replace_Znth_length_one__sift_swap; lia).
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite Znth_replace_Znth_Diff by
    (repeat rewrite replace_Znth_length_one__sift_swap; lia).
  rewrite Znth_replace_Znth_Same by exact Hroot_range.
  exact Hedge.
Qed.

(* The stable part of a heap-extraction state.  The prefix may be permuted by
   sifting, while the suffix remains sorted and above every prefix item. *)
Lemma heap_child_of_parent_items__sift_exit :
  forall child parent,
    1 <= child ->
    (child - 1) / 2 = parent ->
    child = 2 * parent + 1 \/ child = 2 * parent + 2.
Proof.
  intros child parent Hchild Hparent.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdecomp.
  rewrite Hparent in Hdecomp.
  assert ((child - 1) mod 2 = 0 \/ (child - 1) mod 2 = 1) by lia.
  destruct H as [H | H]; [left | right]; lia.
Qed.
Lemma item_le_trans__sift_exit :
  forall a b c,
    ItemLe a b -> ItemLe b c -> ItemLe a c.
Proof.
  intros [ag ak] [bg bk] [cg ck] Hab Hbc.
  unfold ItemLe in *; simpl in *; lia.
Qed.
Lemma heap_parents_after_selected_stop_items__sift_exit :
  forall groups keys lo hi root selected,
    Zlength groups = Zlength keys ->
    0 <= lo <= root ->
    root <= hi ->
    hi < Zlength groups ->
    SelectedLargerChildItems groups keys root hi selected ->
    ItemLe4 (Znth selected groups 0) (Znth selected keys 0)
            (Znth root groups 0) (Znth root keys 0) ->
    HeapOrderedExceptAtFromItems groups keys lo hi root ->
    HeapParentsFromItems groups keys lo hi.
Proof.
  intros groups keys lo hi root selected Hlen Hroots Hroot_hi Hhi
    Hselected Hstop Hordered.
  destruct Hselected as
    [Hselected_shape [Hselected_hi [Hleft_max Hright_max]]].
  assert (Hroot_range : 0 <= root < Zlength groups) by lia.
  assert (Hselected_range : 0 <= selected < Zlength groups).
  { destruct Hselected_shape as [-> | ->]; lia. }
  assert (Hstop_item :
    ItemLe (Znth selected (combine groups keys) (0, 0))
           (Znth root (combine groups keys) (0, 0))).
  {
    rewrite (Znth_combine__count_result groups keys selected 0 0)
      by assumption.
    rewrite (Znth_combine__count_result groups keys root 0 0)
      by assumption.
    exact Hstop.
  }
  unfold HeapParentsFromItems.
  intros current Hcurrent Hlo.
  destruct (Z.eq_dec ((current - 1) / 2) root) as [Hparent | Hparent].
  - rewrite Hparent.
    pose proof (heap_child_of_parent_items__sift_exit current root
      ltac:(lia) Hparent) as [Hleft | Hright].
    + subst current.
      eapply item_le_trans__sift_exit; [apply Hleft_max; lia | exact Hstop_item].
    + subst current.
      eapply item_le_trans__sift_exit; [apply Hright_max; lia | exact Hstop_item].
  - unfold HeapOrderedExceptAtFromItems in Hordered.
    eapply Hordered; eauto.
Qed.
Lemma heap_parents_after_leaf_stop_items__sift_exit :
  forall groups keys lo hi root,
    2 * root + 1 > hi ->
    HeapOrderedExceptAtFromItems groups keys lo hi root ->
    HeapParentsFromItems groups keys lo hi.
Proof.
  intros groups keys lo hi root Hleaf Hordered.
  unfold HeapParentsFromItems.
  intros current Hcurrent Hlo.
  destruct (Z.eq_dec ((current - 1) / 2) root) as [Hparent | Hparent].
  - pose proof (heap_child_of_parent_items__sift_exit current root
      ltac:(lia) Hparent) as [Hleft | Hright]; lia.
  - unfold HeapOrderedExceptAtFromItems in Hordered.
    eapply Hordered; eauto.
Qed.
Lemma ItemLe_refl__sort_extract_transition : forall p, ItemLe p p.
Proof.
  intros [g k]. unfold ItemLe. simpl. right. lia.
Qed.
Lemma ItemLe_trans__sort_extract_transition : forall a b c,
  ItemLe a b -> ItemLe b c -> ItemLe a c.
Proof.
  intros [ga ka] [gb kb] [gc kc].
  unfold ItemLe. simpl. intros [Hab | [Hab Hkab]] [Hbc | [Hbc Hkbc]].
  - left. lia.
  - left. lia.
  - left. lia.
  - right. split; lia.
Qed.
Lemma heap_parent_bounds_items__sort_extract_transition :
  forall child,
    0 < child ->
    0 <= (child - 1) / 2 < child.
Proof.
  intros child Hchild. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
Lemma heap_root_upper_bound_items__sort_extract_transition :
  forall groups keys hi i,
    HeapParentsFromItems groups keys 0 hi ->
    0 <= i <= hi ->
    ItemLe (Znth i (combine groups keys) (0, 0))
           (Znth 0 (combine groups keys) (0, 0)).
Proof.
  intros groups keys hi i Hheap Hi.
  remember (Z.to_nat i) as ni eqn:Hni.
  assert (Heq : i = Z.of_nat ni).
  { subst ni. symmetry. apply Z2Nat.id. lia. }
  subst i. clear Hni.
  revert Hi.
  induction ni as [ni IH] using lt_wf_ind.
  intros Hi.
  destruct ni as [|ni].
  - simpl. apply ItemLe_refl__sort_extract_transition.
  - set (child := Z.of_nat (S ni)).
    set (parent := (child - 1) / 2).
    assert (Hchild_pos : 1 <= child) by (subst child; lia).
    assert (Hparent_nonneg : 0 <= parent).
    { subst parent. apply Z.div_pos; lia. }
    assert (Hparent_lt : parent < child).
    { subst parent. apply Z.div_lt_upper_bound; lia. }
    assert (Hparent_nat_lt : (Z.to_nat parent < S ni)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. subst child. lia. }
    specialize (IH (Z.to_nat parent) Hparent_nat_lt).
    assert (Hparent_range : 0 <= Z.of_nat (Z.to_nat parent) <= hi).
    { rewrite Z2Nat.id by lia. subst child. lia. }
    specialize (IH Hparent_range).
    rewrite Z2Nat.id in IH by lia.
    assert (Hchild_hi : child <= hi).
    { unfold child. exact (proj2 Hi). }
    pose proof (Hheap child (conj Hchild_pos Hchild_hi)
      Hparent_nonneg) as Hedge.
    fold parent in Hedge.
    eapply ItemLe_trans__sort_extract_transition; eauto.
Qed.
Lemma Znth_swap_root_hi_items__sort_extract_transition :
  forall (A : Type) (d : A) (l : list A) hi k,
    0 < hi < Zlength l ->
    0 <= k < Zlength l ->
    Znth k
      (replace_Znth hi (Znth 0 l d)
        (replace_Znth 0 (Znth hi l d) l)) d =
    if Z.eq_dec k 0 then Znth hi l d
    else if Z.eq_dec k hi then Znth 0 l d
    else Znth k l d.
Proof.
  intros A d l hi k Hhi Hk.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - destruct (Z.eq_dec 0 0); [|contradiction].
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite replace_Znth_length_one__sift_swap; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - destruct (Z.eq_dec k 0); [contradiction |].
    destruct (Z.eq_dec k hi) as [-> | Hkhi].
    + destruct (Z.eq_dec hi hi); [|contradiction].
      rewrite Znth_replace_Znth_Same by
        (rewrite replace_Znth_length_one__sift_swap; lia).
      reflexivity.
    + destruct (Z.eq_dec k hi); [contradiction |].
      rewrite Znth_replace_Znth_Diff by
        (repeat rewrite replace_Znth_length_one__sift_swap; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
Qed.
Lemma heap_extract_except_items__sort_extract_transition :
  forall groups keys hi,
    Zlength groups = Zlength keys ->
    hi > 0 ->
    hi < Zlength groups ->
    HeapParentsFromItems groups keys 0 hi ->
    HeapOrderedExceptAtFromItems
      (replace_Znth hi (Znth 0 groups 0)
        (replace_Znth 0 (Znth hi groups 0) groups))
      (replace_Znth hi (Znth 0 keys 0)
        (replace_Znth 0 (Znth hi keys 0) keys))
      0 (hi - 1) 0.
Proof.
  intros groups keys hi Hlen Hhi Hhin Hheap.
  unfold HeapOrderedExceptAtFromItems.
  intros child Hchild Hparent Hparentneq.
  rewrite combine_two_swap__sift_swap by lia.
  assert (Hcombined_len : Zlength (combine groups keys) = Zlength groups).
  { apply Zlength_combine_eq__sift_swap. exact Hlen. }
  rewrite (@Znth_swap_root_hi_items__sort_extract_transition
    (Z * Z) (0, 0) (combine groups keys) hi child) by
    (rewrite Hcombined_len; lia).
  rewrite (@Znth_swap_root_hi_items__sort_extract_transition
    (Z * Z) (0, 0) (combine groups keys) hi ((child - 1) / 2)) by
    (rewrite Hcombined_len;
     pose proof (heap_parent_bounds_items__sort_extract_transition child
       ltac:(lia)); lia).
  pose proof (heap_parent_bounds_items__sort_extract_transition child
    ltac:(lia)) as Hparent_bounds.
  destruct (Z.eq_dec child 0); [lia |].
  destruct (Z.eq_dec child hi); [lia |].
  destruct (Z.eq_dec ((child - 1) / 2) 0); [contradiction |].
  destruct (Z.eq_dec ((child - 1) / 2) hi); [lia |].
  apply Hheap; lia.
Qed.
Lemma heap_extract_cross_items__sort_extract_transition :
  forall groups0 keys0 groups keys n hi,
    Zlength groups = n ->
    Zlength keys = n ->
    hi > 0 ->
    hi < n ->
    HeapSortItemsState groups0 keys0 groups keys hi ->
    forall p q,
      0 <= p < hi -> hi <= q < n ->
      ItemLe
        (Znth p
          (combine
            (replace_Znth hi (Znth 0 groups 0)
              (replace_Znth 0 (Znth hi groups 0) groups))
            (replace_Znth hi (Znth 0 keys 0)
              (replace_Znth 0 (Znth hi keys 0) keys))) (0, 0))
        (Znth q
          (combine
            (replace_Znth hi (Znth 0 groups 0)
              (replace_Znth 0 (Znth hi groups 0) groups))
            (replace_Znth hi (Znth 0 keys 0)
              (replace_Znth 0 (Znth hi keys 0) keys))) (0, 0)).
Proof.
  intros groups0 keys0 groups keys n hi Hg Hk Hhi Hhin Hstate p q Hp Hq.
  destruct Hstate as [_ [_ [_ [Hheap [_ Hcross]]]]].
  rewrite combine_two_swap__sift_swap by lia.
  assert (Hcombined_len : Zlength (combine groups keys) = n).
  { rewrite Zlength_combine_eq__sift_swap by lia. exact Hg. }
  rewrite (@Znth_swap_root_hi_items__sort_extract_transition
    (Z * Z) (0, 0) (combine groups keys) hi p) by
    (rewrite Hcombined_len; lia).
  rewrite (@Znth_swap_root_hi_items__sort_extract_transition
    (Z * Z) (0, 0) (combine groups keys) hi q) by
    (rewrite Hcombined_len; lia).
  destruct (Z.eq_dec p 0) as [-> | Hp0].
  - destruct (Z.eq_dec 0 0); [|contradiction].
    destruct (Z.eq_dec q 0); [lia |].
    destruct (Z.eq_dec q hi) as [-> | Hqhi].
    + eapply heap_root_upper_bound_items__sort_extract_transition; eauto; lia.
    + apply Hcross; lia.
  - destruct (Z.eq_dec p 0); [contradiction |].
    destruct (Z.eq_dec p hi); [lia |].
    destruct (Z.eq_dec q 0); [lia |].
    destruct (Z.eq_dec q hi) as [-> | Hqhi].
    + eapply heap_root_upper_bound_items__sort_extract_transition; eauto; lia.
    + apply Hcross; lia.
Qed.
Lemma heap_extract_suffix_items__sort_extract_transition :
  forall groups0 keys0 groups keys n hi,
    Zlength groups = n ->
    Zlength keys = n ->
    hi > 0 ->
    hi < n ->
    HeapSortItemsState groups0 keys0 groups keys hi ->
    ItemsIncreasing
      (sublist hi n
        (replace_Znth hi (Znth 0 groups 0)
          (replace_Znth 0 (Znth hi groups 0) groups)))
      (sublist hi n
        (replace_Znth hi (Znth 0 keys 0)
          (replace_Znth 0 (Znth hi keys 0) keys))).
Proof.
  intros groups0 keys0 groups keys n hi Hg Hk Hhi Hhin Hstate.
  destruct Hstate as [_ [_ [_ [_ [Hinc Hcross]]]]].
  destruct Hinc as [Hinc_len Hinc_order].
  rewrite Hg, Hk in Hinc_len, Hinc_order.
  set (groups' := replace_Znth hi (Znth 0 groups 0)
    (replace_Znth 0 (Znth hi groups 0) groups)).
  set (keys' := replace_Znth hi (Znth 0 keys 0)
    (replace_Znth 0 (Znth hi keys 0) keys)).
  assert (Hgroups' : Zlength groups' = n).
  { unfold groups'. repeat rewrite replace_Znth_length_one__sift_swap. exact Hg. }
  assert (Hkeys' : Zlength keys' = n).
  { unfold keys'. repeat rewrite replace_Znth_length_one__sift_swap. exact Hk. }
  assert (Hnew_point : forall t,
    0 <= t < n - hi ->
    Znth t (combine (sublist hi n groups') (sublist hi n keys')) (0, 0) =
    Znth (t + hi)
      (replace_Znth hi (Znth 0 (combine groups keys) (0, 0))
        (replace_Znth 0 (Znth hi (combine groups keys) (0, 0))
          (combine groups keys))) (0, 0)).
  {
    intros t Ht.
    rewrite Znth_combine__sift_swap by
      (repeat rewrite Zlength_sublist; lia).
    rewrite !Znth_sublist by lia.
    rewrite <- (Znth_combine__sift_swap groups' keys' (t + hi) 0 0)
      by lia.
    unfold groups', keys'.
    rewrite combine_two_swap__sift_swap by lia.
    reflexivity.
  }
  assert (Hold_point : forall t,
    0 <= t < n - (hi + 1) ->
    Znth t
      (combine (sublist (hi + 1) n groups)
               (sublist (hi + 1) n keys)) (0, 0) =
    Znth (t + hi + 1) (combine groups keys) (0, 0)).
  {
    intros t Ht.
    rewrite Znth_combine__sift_swap by
      (repeat rewrite Zlength_sublist; lia).
    rewrite !Znth_sublist by lia.
    replace (t + (hi + 1)) with (t + hi + 1) by lia.
    rewrite <- (Znth_combine__sift_swap groups keys (t + hi + 1) 0 0)
      by lia.
    reflexivity.
  }
  unfold ItemsIncreasing.
  split.
  - repeat rewrite Zlength_sublist; lia.
  - intros i j [Hi [Hij Hj]].
    rewrite Zlength_sublist in Hj by lia.
    rewrite Hnew_point by lia.
    rewrite Hnew_point by lia.
    assert (Hcombined_len : Zlength (combine groups keys) = n).
    { rewrite Zlength_combine_eq__sift_swap by lia. exact Hg. }
    rewrite (@Znth_swap_root_hi_items__sort_extract_transition
      (Z * Z) (0, 0) (combine groups keys) hi (i + hi)) by
      (rewrite Hcombined_len; lia).
    rewrite (@Znth_swap_root_hi_items__sort_extract_transition
      (Z * Z) (0, 0) (combine groups keys) hi (j + hi)) by
      (rewrite Hcombined_len; lia).
    destruct (Z.eq_dec (i + hi) 0); [lia |].
    destruct (Z.eq_dec (i + hi) hi) as [Hiz | Hinz].
    + assert (Hi0 : i = 0) by lia. subst i.
      destruct (Z.eq_dec (j + hi) 0); [lia |].
      destruct (Z.eq_dec (j + hi) hi) as [Hjz | Hjnz].
      * apply ItemLe_refl__sort_extract_transition.
      * apply Hcross; lia.
    + destruct (Z.eq_dec (j + hi) 0); [lia |].
      destruct (Z.eq_dec (j + hi) hi); [lia |].
      specialize (Hinc_order (i - 1) (j - 1)).
      assert (Hbounds :
        0 <= i - 1 /\ i - 1 <= j - 1 /\
        j - 1 < Zlength (sublist (hi + 1) n groups)).
      { rewrite Zlength_sublist by lia. lia. }
      specialize (Hinc_order Hbounds).
      rewrite Hold_point in Hinc_order by lia.
      rewrite Hold_point in Hinc_order by lia.
      replace (i - 1 + hi + 1) with (i + hi) in Hinc_order by lia.
      replace (j - 1 + hi + 1) with (j + hi) in Hinc_order by lia.
      exact Hinc_order.
Qed.
Lemma SameKeyCountRange_empty__count_group_close :
  forall keys i,
    SameKeyCountRange keys i i = 0.
Proof.
  intros keys i.
  unfold SameKeyCountRange.
  rewrite set_card_Z_rect_filter_as_nested_sum__count_result.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.
Lemma CountGroupPhase_initial__count_group_close :
  forall groups keys i j total,
    0 <= i <= j ->
    PairCountPrefix groups keys i total ->
    CountGroupPhase groups keys i j i
      (total + (j - i) * (j - i - 1) / 2).
Proof.
  intros groups keys i j total Hij Hprefix.
  unfold CountGroupPhase.
  exists total. split; [exact Hprefix |].
  rewrite SameKeyCountRange_empty__count_group_close.
  lia.
Qed.
Lemma PairCountPrefix_upper_bound__count_group_close :
  forall groups keys hi total,
    0 <= hi ->
    PairCountPrefix groups keys hi total ->
    total <= hi * (hi - 1) / 2.
Proof.
  intros groups keys hi total Hhi Hprefix.
  unfold PairCountPrefix in Hprefix. subst total.
  replace (hi * (hi - 1) / 2) with
    ((hi - 0) * (hi - 0 - 1) / 2) by (f_equal; ring).
  rewrite <- (unordered_pair_range_card__count_result 0 hi) by lia.
  rewrite !set_card_Z_rect_filter_as_nested_sum__count_result.
  apply SumLib.ZRange.sum_Z_range_le. intros x Hx.
  apply SumLib.ZRange.sum_Z_range_le. intros y Hy.
  repeat match goal with
  | |- context [prop_dec ?P] => destruct (prop_dec P)
  end; simpl; try lia; exfalso; tauto.
Qed.
Lemma PairCountPrefix_plus_run_cap__count_group_close :
  forall groups keys i j total,
    0 <= i <= j ->
    j <= 300000 ->
    PairCountPrefix groups keys i total ->
    total + (j - i) * (j - i - 1) / 2 <= 45000000000.
Proof.
  intros groups keys i j total Hij Hj Hprefix.
  pose proof (PairCountPrefix_upper_bound__count_group_close
    groups keys i total ltac:(lia) Hprefix) as Htotal.
  pose proof (Z.div_mod (i * (i - 1)) 2 ltac:(lia)) as Hdiv_i.
  pose proof (Z.mod_pos_bound (i * (i - 1)) 2 ltac:(lia)) as Hmod_i.
  pose proof (Z.div_mod ((j - i) * (j - i - 1)) 2 ltac:(lia)) as Hdiv_d.
  pose proof (Z.mod_pos_bound ((j - i) * (j - i - 1)) 2 ltac:(lia)) as Hmod_d.
  nia.
Qed.
Lemma SameValueRange_extend_right__count_group_close :
  forall l lo hi,
    SameValueRange l lo hi ->
    lo <= hi ->
    Znth hi l 0 = Znth lo l 0 ->
    SameValueRange l lo (hi + 1).
Proof.
  intros l lo hi Hrange Hle Heq.
  unfold SameValueRange in *.
  intros q Hq.
  destruct (Z.eq_dec q hi) as [-> | Hneq].
  - exact Heq.
  - apply Hrange. lia.
Qed.
Lemma choose_two_nonnegative__count_group_close :
  forall n,
    0 <= n ->
    0 <= n * (n - 1) / 2.
Proof.
  intros n Hn.
  destruct (Z_lt_ge_dec n 2) as [Hsmall | Hlarge].
  - destruct (Z.eq_dec n 0) as [-> | Hne].
    + reflexivity.
    + replace n with 1 by lia. reflexivity.
  - apply Z.div_pos; nia.
Qed.
Lemma ItemsIncreasing_key_monotone_same_group__count_same_key :
  forall groups keys x y,
    ItemsIncreasing groups keys ->
    0 <= x -> x <= y -> y < Zlength groups ->
    Znth x groups 0 = Znth y groups 0 ->
    Znth x keys 0 <= Znth y keys 0.
Proof.
  intros groups keys x y [Hlen Hinc] Hx Hxy Hy Hgroup.
  specialize (Hinc x y ltac:(lia)).
  rewrite !Znth_combine__count_result in Hinc by lia.
  unfold ItemLe in Hinc. simpl in Hinc. lia.
Qed.
Lemma ItemsIncreasing_keys_separated_at_boundary__count_same_key :
  forall groups keys lo hi p x y,
    0 <= lo -> hi <= Zlength groups ->
    ItemsIncreasing groups keys ->
    SameValueRange groups lo hi ->
    RangeRunBoundary keys lo hi p ->
    lo <= x < p -> p <= y < hi ->
    Znth x keys 0 <> Znth y keys 0.
Proof.
  intros groups keys lo hi p x y Hlo Hhi Hinc Hgroups Hboundary Hx Hy.
  unfold RangeRunBoundary in Hboundary.
  destruct Hboundary as [-> | [-> | [Hp Hneq]]]; try lia.
  assert (Hgroup_x_prev :
    Znth x groups 0 = Znth (p - 1) groups 0).
  { transitivity (Znth lo groups 0); [apply Hgroups | symmetry; apply Hgroups]; lia. }
  assert (Hgroup_p_y : Znth p groups 0 = Znth y groups 0).
  { transitivity (Znth lo groups 0); [apply Hgroups | symmetry; apply Hgroups]; lia. }
  pose proof (ItemsIncreasing_key_monotone_same_group__count_same_key
    groups keys x (p - 1) Hinc ltac:(lia) ltac:(lia) ltac:(lia)
    Hgroup_x_prev) as Hleft.
  pose proof (ItemsIncreasing_key_monotone_same_group__count_same_key
    groups keys p y Hinc ltac:(lia) ltac:(lia) ltac:(lia)
    Hgroup_p_y) as Hright.
  assert (Hgroup_prev_p :
    Znth (p - 1) groups 0 = Znth p groups 0).
  { transitivity (Znth lo groups 0); [apply Hgroups | symmetry; apply Hgroups]; lia. }
  pose proof (ItemsIncreasing_key_monotone_same_group__count_same_key
    groups keys (p - 1) p Hinc ltac:(lia) ltac:(lia) ltac:(lia)
    Hgroup_prev_p) as Hmiddle.
  lia.
Qed.
Lemma SameKeyCountRange_advance_complete_run__count_same_key :
  forall keys lo p q,
    lo <= p <= q ->
    (forall x y, lo <= x < p -> p <= y < q ->
       Znth x keys 0 <> Znth y keys 0) ->
    SameValueRange keys p q ->
    SameKeyCountRange keys lo q =
      SameKeyCountRange keys lo p + (q - p) * (q - p - 1) / 2.
Proof.
  intros keys lo p q Hbounds Hseparate Hsame.
  unfold SameKeyCountRange.
  rewrite !set_card_Z_rect_filter_as_nested_sum__count_result.
  set (F := fun x y : Z =>
    if prop_dec (x < y /\ Znth x keys 0 = Znth y keys 0)
    then 1 else 0).
  change
    (SumLib.Sum.sum (fun x : Z => lo <= x < q)
       (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < q) (F x)) =
     SumLib.Sum.sum (fun x : Z => lo <= x < p)
       (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < p) (F x)) +
     (q - p) * (q - p - 1) / 2).
  assert (Hold :
    SumLib.Sum.sum (fun x : Z => lo <= x < p)
      (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < q) (F x)) =
    SumLib.Sum.sum (fun x : Z => lo <= x < p)
      (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < p) (F x))).
  {
    apply SumLib.Sum.sum_ext. intros x Hx.
    rewrite (sum_Z_range_split lo p q) by lia.
    assert (Hzero :
      SumLib.Sum.sum (fun y : Z => p <= y < q) (F x) = 0).
    {
      apply sum_Z_range_eq_zero. intros y Hy.
      unfold F.
      destruct (prop_dec (x < y /\ Znth x keys 0 = Znth y keys 0))
        as [Heq | Hneq]; [| reflexivity].
      exfalso. apply (Hseparate x y); tauto.
    }
    rewrite Hzero. lia.
  }
  assert (Hnew :
    SumLib.Sum.sum (fun x : Z => p <= x < q)
      (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < q) (F x)) =
    (q - p) * (q - p - 1) / 2).
  {
    transitivity
      (SumLib.Sum.sum (fun x : Z => p <= x < q)
        (fun x => SumLib.Sum.sum (fun y : Z => p <= y < q) (F x))).
    - apply SumLib.Sum.sum_ext. intros x Hx.
      rewrite (sum_Z_range_split lo p q) by lia.
      assert (Hzero :
        SumLib.Sum.sum (fun y : Z => lo <= y < p) (F x) = 0).
      {
        apply sum_Z_range_eq_zero. intros y Hy.
        unfold F.
        destruct (prop_dec (x < y /\ Znth x keys 0 = Znth y keys 0));
          [lia | reflexivity].
      }
      rewrite Hzero. lia.
    - rewrite <- unordered_pair_range_card__count_result by lia.
      rewrite set_card_Z_rect_filter_as_nested_sum__count_result.
      apply SumLib.Sum.sum_ext. intros x Hx.
      apply SumLib.Sum.sum_ext. intros y Hy.
      unfold F. cbn.
      assert (Hkeys : Znth x keys 0 = Znth y keys 0).
      { transitivity (Znth p keys 0); [apply Hsame | symmetry; apply Hsame]; lia. }
      destruct (prop_dec (x < y /\ Znth x keys 0 = Znth y keys 0))
        as [Hboth | Hnot].
      { destruct (prop_dec (x < y)) as [Hlt | Hnlt].
        { reflexivity. }
        { exfalso. apply Hnlt. exact (proj1 Hboth). } }
      { destruct (prop_dec (x < y)) as [Hlt | Hnlt].
        { exfalso. apply Hnot. split; [exact Hlt | exact Hkeys]. }
        { reflexivity. } }
  }
  rewrite (sum_Z_range_split lo p q) by lia.
  rewrite Hold, Hnew. lia.
Qed.
Lemma CountGroupPhase_advance_complete_key_run__count_same_key :
  forall groups keys i j p q total,
    0 <= i < j -> j <= Zlength groups ->
    i <= p /\ p <= q /\ q <= j ->
    ItemsIncreasing groups keys ->
    SameValueRange groups i j ->
    RangeRunBoundary keys i j p ->
    SameValueRange keys p q ->
    CountGroupPhase groups keys i j p total ->
    CountGroupPhase groups keys i j q
      (total - (q - p) * (q - p - 1) / 2).
Proof.
  intros groups keys i j p q total Hij Hj Hbounds Hinc Hgroups
    Hboundary Hkeys Hphase.
  unfold CountGroupPhase in Hphase |- *.
  destruct Hphase as [before [Hbefore Htotal]].
  exists before. split; [exact Hbefore |].
  pose proof (SameKeyCountRange_advance_complete_run__count_same_key
    keys i p q ltac:(lia)) as Hadvance.
  specialize (Hadvance
    ltac:(intros x y Hx Hy;
      eapply ItemsIncreasing_keys_separated_at_boundary__count_same_key;
      eauto; lia)
    Hkeys).
  rewrite Hadvance. lia.
Qed.
Lemma set_card_nonnegative__count_same_key :
  forall (A : Type) (P : A -> Prop) (FP : @Finite A P),
    0 <= @set_card A P FP.
Proof.
  intros A P FP. unfold set_card.
  apply SumLib.Sum.sum_nonneg. intros x Hx.
  destruct (prop_dec (P x)); lia.
Qed.
Lemma SameKeyCountRange_monotone_hi__count_same_key :
  forall keys lo p hi,
    lo <= p <= hi ->
    SameKeyCountRange keys lo p <= SameKeyCountRange keys lo hi.
Proof.
  intros keys lo p hi Hbounds.
  unfold SameKeyCountRange.
  rewrite !set_card_Z_rect_filter_as_nested_sum__count_result.
  set (F := fun x y : Z =>
    if prop_dec (x < y /\ Znth x keys 0 = Znth y keys 0)
    then 1 else 0).
  change
    (SumLib.Sum.sum (fun x : Z => lo <= x < p)
       (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < p) (F x)) <=
     SumLib.Sum.sum (fun x : Z => lo <= x < hi)
       (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < hi) (F x))).
  assert (Hinner : forall x, lo <= x < p ->
    SumLib.Sum.sum (fun y : Z => lo <= y < p) (F x) <=
    SumLib.Sum.sum (fun y : Z => lo <= y < hi) (F x)).
  {
    intros x Hx. rewrite (sum_Z_range_split lo p hi) by lia.
    assert (Hnonneg :
      0 <= SumLib.Sum.sum (fun y : Z => p <= y < hi) (F x)).
    {
      apply SumLib.Sum.sum_nonneg. intros y Hy.
      unfold F. destruct (prop_dec
        (x < y /\ Znth x keys 0 = Znth y keys 0)); lia.
    }
    lia.
  }
  pose proof (SumLib.Sum.sum_le (fun x : Z => lo <= x < p)
    (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < p) (F x))
    (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < hi) (F x))
    Hinner) as Hold.
  rewrite (sum_Z_range_split lo p hi) by lia.
  assert (Hnew :
    0 <= SumLib.Sum.sum (fun x : Z => p <= x < hi)
      (fun x => SumLib.Sum.sum (fun y : Z => lo <= y < hi) (F x))).
  {
    apply SumLib.Sum.sum_nonneg. intros x Hx.
    apply SumLib.Sum.sum_nonneg. intros y Hy.
    unfold F. destruct (prop_dec
      (x < y /\ Znth x keys 0 = Znth y keys 0)); lia.
  }
  lia.
Qed.
Lemma CountGroupPhase_nonnegative__count_same_key :
  forall groups keys i j p total,
    i <= p <= j ->
    CountGroupPhase groups keys i j p total ->
    0 <= total.
Proof.
  intros groups keys i j p total Hbounds Hphase.
  unfold CountGroupPhase in Hphase.
  destruct Hphase as [before [Hbefore Htotal]].
  unfold PairCountPrefix in Hbefore. subst before.
  pose proof (SameKeyCountRange_monotone_hi__count_same_key
    keys i p j Hbounds) as Hsame_le.
  pose proof (unequal_pair_range_card__count_result keys i j ltac:(lia))
    as Hunequal.
  pose proof (@set_card_nonnegative__count_same_key
    (Z * Z)
    (fun ij : Z * Z =>
      0 <= fst ij < i /\ 0 <= snd ij < i /\ fst ij < snd ij /\
      Znth (fst ij) groups 0 = Znth (snd ij) groups 0 /\
      Znth (fst ij) keys 0 <> Znth (snd ij) keys 0) _) as Hold.
  pose proof (@set_card_nonnegative__count_same_key
    (Z * Z)
    (fun ij : Z * Z =>
      i <= fst ij < j /\ i <= snd ij < j /\ fst ij < snd ij /\
      Znth (fst ij) keys 0 <> Znth (snd ij) keys 0) _) as Hnew.
  set (comb := (j - i) * (j - i - 1) / 2) in *.
  lia.
Qed.
Lemma EntryPairRel_sym__count_final :
  forall a b : Z * Z,
    (fst a = fst b /\ snd a <> snd b) <->
    (fst b = fst a /\ snd b <> snd a).
Proof.
  intros [ag ak] [bg bk]. simpl. lia.
Qed.
Lemma EntryRelCount_cons__count_final :
  forall x y l,
    #(fun i : Z =>
        0 <= i < Zlength (y :: l) /\
        fst x = fst (Znth i (y :: l) (0, 0)) /\
        snd x <> snd (Znth i (y :: l) (0, 0))) =
      (if prop_dec (fst x = fst y /\ snd x <> snd y) then 1 else 0) +
      #(fun i : Z =>
          0 <= i < Zlength l /\
          fst x = fst (Znth i l (0, 0)) /\
          snd x <> snd (Znth i l (0, 0))).
Proof.
  intros x y l.
  rewrite !set_card_Z_range_filter_as_sum__classification.
  rewrite Zlength_cons.
  rewrite (sum_Z_range_cons 0 (Zlength l + 1)) by
    (pose proof (Zlength_nonneg l); lia).
  rewrite sum_Z_range_shift_1.
  rewrite Znth0_cons.
  f_equal.
  apply SumLib.Sum.sum_ext. intros i Hi.
  rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  reflexivity.
Qed.
Lemma EntryRelCount_permutation__count_final :
  forall x l l',
    Permutation l l' ->
    #(fun i : Z =>
        0 <= i < Zlength l /\
        fst x = fst (Znth i l (0, 0)) /\
        snd x <> snd (Znth i l (0, 0))) =
    #(fun i : Z =>
        0 <= i < Zlength l' /\
        fst x = fst (Znth i l' (0, 0)) /\
        snd x <> snd (Znth i l' (0, 0))).
Proof.
  intros x l l' Hperm. induction Hperm.
  - reflexivity.
  - rewrite !EntryRelCount_cons__count_final. now rewrite IHHperm.
  - rewrite !EntryRelCount_cons__count_final.
    destruct (prop_dec (fst x = fst x0 /\ snd x <> snd x0));
      destruct (prop_dec (fst x = fst y /\ snd x <> snd y)); lia.
  - now rewrite IHHperm1, IHHperm2.
Qed.
Lemma EntryPairCard_cons__count_final :
  forall x l,
    PrefixPairCard__classification (Zlength (x :: l))
      (fun i j =>
         fst (Znth i (x :: l) (0, 0)) = fst (Znth j (x :: l) (0, 0)) /\
         snd (Znth i (x :: l) (0, 0)) <> snd (Znth j (x :: l) (0, 0))) =
      #(fun i : Z =>
          0 <= i < Zlength l /\
          fst x = fst (Znth i l (0, 0)) /\
          snd x <> snd (Znth i l (0, 0))) +
      PrefixPairCard__classification (Zlength l)
        (fun i j =>
           fst (Znth i l (0, 0)) = fst (Znth j l (0, 0)) /\
           snd (Znth i l (0, 0)) <> snd (Znth j l (0, 0))).
Proof.
  intros x l.
  unfold PrefixPairCard__classification.
  rewrite Zlength_cons.
  change
    (#(fun ij : Z * Z =>
        0 <= fst ij < Zlength l + 1 /\
        0 <= snd ij < Zlength l + 1 /\
        (fst ij < snd ij /\
         (fst (Znth (fst ij) (x :: l) (0, 0)) =
            fst (Znth (snd ij) (x :: l) (0, 0)) /\
          snd (Znth (fst ij) (x :: l) (0, 0)) <>
            snd (Znth (snd ij) (x :: l) (0, 0))))) =
     #(fun i : Z =>
         0 <= i < Zlength l /\
         fst x = fst (Znth i l (0, 0)) /\
         snd x <> snd (Znth i l (0, 0))) +
     #(fun ij : Z * Z =>
         0 <= fst ij < Zlength l /\
         0 <= snd ij < Zlength l /\
         fst ij < snd ij /\
         fst (Znth (fst ij) l (0, 0)) = fst (Znth (snd ij) l (0, 0)) /\
         snd (Znth (fst ij) l (0, 0)) <> snd (Znth (snd ij) l (0, 0)))).
  rewrite (set_card_Z_rect_partition__count_result
    0 (Zlength l + 1) 0 (Zlength l + 1)
    (fun ij : Z * Z =>
       fst ij < snd ij /\
       fst (Znth (fst ij) (x :: l) (0, 0)) =
         fst (Znth (snd ij) (x :: l) (0, 0)) /\
       snd (Znth (fst ij) (x :: l) (0, 0)) <>
         snd (Znth (snd ij) (x :: l) (0, 0)))
    (fun ij : Z * Z => fst ij = 0)).
  f_equal.
  - eapply set_card_bijection__classification
      with (f := fun ij : Z * Z => snd ij - 1)
           (g := fun i : Z => (0, i + 1)).
    + intros [i j] [Hi [Hj [[Hij Hrel] Hi0]]]. simpl in *.
      subst i. split; [lia |].
      rewrite Znth0_cons in Hrel.
      rewrite Znth_cons in Hrel by lia.
      exact Hrel.
    + intros i [Hi [Hg Hk]]. simpl in *.
      repeat split; try lia.
      * rewrite Znth0_cons.
        rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        exact Hg.
      * rewrite Znth0_cons.
        rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        exact Hk.
    + intros [i j] [Hi [Hj [[Hij Hrel] Hi0]]]. simpl in *.
      subst i. f_equal; lia.
    + intros i [Hi Hrel]. simpl. lia.
  - eapply set_card_bijection__classification
      with (f := fun ij : Z * Z => (fst ij - 1, snd ij - 1))
           (g := fun ij : Z * Z => (fst ij + 1, snd ij + 1)).
    + intros [i j] [Hi [Hj [[Hij [Hg Hk]] Hi0]]]. simpl in *.
      repeat split; try lia.
      * rewrite !Znth_cons in Hg by lia. exact Hg.
      * rewrite !Znth_cons in Hk by lia. exact Hk.
    + intros [i j] [Hi [Hj [Hij [Hg Hk]]]]. simpl in *.
      repeat split; try lia.
      * rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        replace (j + 1 - 1) with j by lia.
        exact Hg.
      * rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        replace (j + 1 - 1) with j by lia.
        exact Hk.
    + intros [i j] [Hi [Hj [[Hij Hrel] Hi0]]]. simpl in *. f_equal; lia.
    + intros [i j] [Hi [Hj [Hij Hrel]]]. simpl in *. f_equal; lia.
Qed.
Lemma EntryPairCard_permutation__count_final :
  forall l l',
    Permutation l l' ->
    PrefixPairCard__classification (Zlength l)
      (fun i j =>
         fst (Znth i l (0, 0)) = fst (Znth j l (0, 0)) /\
         snd (Znth i l (0, 0)) <> snd (Znth j l (0, 0))) =
    PrefixPairCard__classification (Zlength l')
      (fun i j =>
         fst (Znth i l' (0, 0)) = fst (Znth j l' (0, 0)) /\
         snd (Znth i l' (0, 0)) <> snd (Znth j l' (0, 0))).
Proof.
  intros l l' Hperm. induction Hperm.
  - reflexivity.
  - rewrite !EntryPairCard_cons__count_final.
    rewrite IHHperm.
    rewrite (EntryRelCount_permutation__count_final x l l' Hperm).
    reflexivity.
  - rewrite !EntryPairCard_cons__count_final.
    rewrite !EntryRelCount_cons__count_final.
    assert (Hsym :
      (if prop_dec (fst y = fst x /\ snd y <> snd x) then 1 else 0) =
      (if prop_dec (fst x = fst y /\ snd x <> snd y) then 1 else 0)).
    { destruct (prop_dec (fst y = fst x /\ snd y <> snd x)) as [Hyx | Hyx];
        destruct (prop_dec (fst x = fst y /\ snd x <> snd y)) as [Hxy | Hxy];
        try reflexivity.
      - exfalso. apply Hxy. apply EntryPairRel_sym__count_final. exact Hyx.
      - exfalso. apply Hyx. apply EntryPairRel_sym__count_final. exact Hxy. }
    lia.
  - now rewrite IHHperm1, IHHperm2.
Qed.
Lemma Zlength_combine_eq__count_final :
  forall {A B : Type} (xs : list A) (ys : list B),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_combine_in_bounds__count_final :
  forall {A B : Type} (xs : list A) (ys : list B) i da db,
    0 <= i < Zlength (combine xs ys) ->
    Znth i (combine xs ys) (da, db) = (Znth i xs da, Znth i ys db).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys i da db Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite Zlength_nil in Hi. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        change (0 <= i < Zlength ((x, y) :: combine xs ys)) in Hi.
        rewrite Zlength_cons in Hi. lia.
Qed.
Lemma PairCountPrefix_as_EntryPairCard__count_final :
  forall groups keys n,
    Zlength (combine groups keys) = n ->
    PairCountPrefix groups keys n
      (PrefixPairCard__classification (Zlength (combine groups keys))
        (fun i j =>
           fst (Znth i (combine groups keys) (0, 0)) =
             fst (Znth j (combine groups keys) (0, 0)) /\
           snd (Znth i (combine groups keys) (0, 0)) <>
             snd (Znth j (combine groups keys) (0, 0)))).
Proof.
  intros groups keys n Hlen.
  unfold PairCountPrefix, PrefixPairCard__classification.
  rewrite Hlen.
  apply set_card_ext__classification. intros [i j]. simpl.
  split.
  - intros [Hi [Hj [Hij [Hg Hk]]]].
    rewrite !Znth_combine_in_bounds__count_final in Hg by lia. simpl in Hg.
    rewrite !Znth_combine_in_bounds__count_final in Hk by lia. simpl in Hk.
    tauto.
  - intros [Hi [Hj [Hij [Hg Hk]]]].
    split; [exact Hi |]. split; [exact Hj |]. split; [exact Hij |].
    split.
    + rewrite (Znth_combine_in_bounds__count_final groups keys i 0 0) by lia.
      rewrite (Znth_combine_in_bounds__count_final groups keys j 0 0) by lia.
      simpl. exact Hg.
    + rewrite (Znth_combine_in_bounds__count_final groups keys i 0 0) by lia.
      rewrite (Znth_combine_in_bounds__count_final groups keys j 0 0) by lia.
      simpl. exact Hk.
Qed.
Lemma PairCountPrefix_parallel_permutation__count_final :
  forall groups keys groups' keys' n out,
    Zlength groups' = n ->
    Zlength keys' = n ->
    ParallelPermutation groups keys groups' keys' ->
    PairCountPrefix groups' keys' n out ->
    PairCountPrefix groups keys n out.
Proof.
  intros groups keys groups' keys' n out Hgroups' Hkeys' Hperm Hcount.
  assert (Hsorted_len : Zlength (combine groups' keys') = n).
  { rewrite Zlength_combine_eq__count_final by lia. exact Hgroups'. }
  unfold ParallelPermutation in Hperm.
  assert (Horig_len : Zlength (combine groups keys) = n).
  { rewrite !Zlength_correct.
    rewrite (Permutation_length Hperm).
    rewrite <- Zlength_correct. exact Hsorted_len. }
  pose proof (PairCountPrefix_as_EntryPairCard__count_final
    groups keys n Horig_len) as Horig.
  pose proof (PairCountPrefix_as_EntryPairCard__count_final
    groups' keys' n Hsorted_len) as Hsorted.
  pose proof (EntryPairCard_permutation__count_final
    (combine groups keys) (combine groups' keys') Hperm) as Hcard.
  unfold PairCountPrefix in Hcount, Horig, Hsorted |- *.
  lia.
Qed.
Lemma set_card_empty__solver_init :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso. apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma EnumeratesEntries_nil__solver_init :
  forall Entry people,
    EnumeratesEntries Entry people 0 nil nil.
Proof.
  intros Entry people.
  unfold EnumeratesEntries.
  exists (@nil Z).
  split; [reflexivity |].
  split; [reflexivity |].
  split; [apply mono_inc_nil |].
  split.
  - intros t Ht. rewrite Zlength_nil in Ht. lia.
  - intros q Hq Hex. lia.
Qed.
Lemma ClassifiedPrefix_nil__solver_init :
  forall xs ys people,
    ClassifiedPrefix xs ys people 0 nil nil nil nil.
Proof.
  intros xs ys people. split; apply EnumeratesEntries_nil__solver_init.
Qed.
Lemma ClassifiedCountsCorrect_nil__solver_init :
  forall xs ys people,
    ClassifiedCountsCorrect xs ys people 0 nil nil nil nil.
Proof.
  intros xs ys people vertical horizontal Hv Hh.
  unfold PairCountPrefix in Hv, Hh.
  rewrite set_card_empty__solver_init in Hv, Hh by
    (intros [i j] Hbad; simpl in Hbad; lia).
  subst vertical horizontal.
  rewrite set_card_empty__solver_init by
    (intros [i j] Hbad; simpl in Hbad; lia).
  lia.
Qed.
Lemma EnumeratesEntries_append__solver_classify_append :
  forall Entry people p groups keys g k,
    EnumeratesEntries Entry people p groups keys ->
    0 <= p ->
    Entry (Znth p people (0, 0)) g k ->
    EnumeratesEntries Entry people (p + 1)
      (groups ++ [g]) (keys ++ [k]).
Proof.
  intros Entry people p groups keys g k
    [indices [Hilen [Hgklen [Hmono [Hindexed Hcomplete]]]]] Hp Hentry.
  exists (indices ++ [p]).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil, Hilen. lia.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil, Hgklen. lia.
  - unfold mono_inc in Hmono |- *.
    intros i j Hi Hij Hj.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
    destruct (Z_lt_ge_dec j (Zlength indices)) as [Hjold | Hjnew].
    + rewrite !Znth_app_left__classification by lia.
      apply Hmono; lia.
    + assert (Hjeq : j = Zlength indices) by lia. subst j.
      rewrite Znth_app_last__classification.
      rewrite Znth_app_left__classification by lia.
      specialize (Hindexed i ltac:(lia)). tauto.
  - intros t Ht.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Ht.
    destruct (Z_lt_ge_dec t (Zlength indices)) as [Htold | Htnew].
    + specialize (Hindexed t ltac:(lia)). destruct Hindexed as [Hrange Hentry_old].
      rewrite Znth_app_left__classification by lia.
      split; [lia |].
      rewrite !Znth_app_left__classification by
        (rewrite <- ?Hilen, <- ?Hgklen; lia).
      exact Hentry_old.
    + assert (Hteq : t = Zlength indices) by lia. subst t.
      rewrite Znth_app_last__classification.
      rewrite Hilen, Znth_app_last__classification.
      rewrite Hgklen, Znth_app_last__classification.
      split; [lia | exact Hentry].
  - intros q Hq Hex.
    destruct (Z_lt_ge_dec q p) as [Hqold | Hqnew].
    + apply in_or_app. left. apply Hcomplete; [lia | exact Hex].
    + assert (Hqeq : q = p) by lia. subst q.
      apply in_or_app. right. simpl. auto.
Qed.
Lemma EnumeratesEntries_skip__solver_classify_append :
  forall Entry people p groups keys,
    EnumeratesEntries Entry people p groups keys ->
    0 <= p ->
    (forall g k, ~ Entry (Znth p people (0, 0)) g k) ->
    EnumeratesEntries Entry people (p + 1) groups keys.
Proof.
  intros Entry people p groups keys
    [indices [Hilen [Hgklen [Hmono [Hindexed Hcomplete]]]]] Hp Hnone.
  exists indices.
  refine (conj Hilen (conj Hgklen (conj Hmono (conj _ _)))).
  - intros t Ht. specialize (Hindexed t Ht). destruct Hindexed as [Hrange Hentry].
    split; [lia | exact Hentry].
  - intros q Hq [g [k Hentry]].
    destruct (Z_lt_ge_dec q p) as [Hqold | Hqnew].
    + apply Hcomplete; [lia |]. exists g, k. exact Hentry.
    + assert (Hqeq : q = p) by lia. subst q.
      exfalso. exact (Hnone g k Hentry).
Qed.
Lemma StripIndex_nonnegative_not_minus_one__solver_classify_append :
  forall streets v r,
    mono_inc streets -> 0 <= r ->
    StripIndex streets v r -> ~ StripIndex streets v (-1).
Proof.
  intros streets v r Hmono Hr Hstrip Hminus.
  unfold StripIndex in Hstrip, Hminus.
  destruct Hstrip as [[Hbad _] | [Hbounds Hinside]]; [lia |].
  destruct Hminus as [[_ Hin] | [Hbad _]]; [|lia].
  pose proof (mono_inc_member_outside_gap__classification
    streets r v Hmono Hbounds Hin). lia.
Qed.
Lemma PairCountPrefix_bounds__solver_bounds_safety :
  forall groups keys hi out,
    0 <= hi ->
    PairCountPrefix groups keys hi out ->
    0 <= out <= hi * hi.
Proof.
  intros groups keys hi out Hhi Hcount.
  unfold PairCountPrefix in Hcount. subst out.
  rewrite set_card_Z_rect_filter_as_nested_sum__count_result.
  pose proof
    (sum_Z_range_bounds 0 hi
      (fun x =>
        SumLib.Sum.sum (fun y : Z => 0 <= y < hi)
          (fun y =>
            if prop_dec
              (fst (x, y) < snd (x, y) /\
               Znth (fst (x, y)) groups 0 = Znth (snd (x, y)) groups 0 /\
               Znth (fst (x, y)) keys 0 <> Znth (snd (x, y)) keys 0)
            then 1 else 0))
      0 hi ltac:(lia)) as Houter.
  assert (Hinner : forall x, 0 <= x < hi ->
    0 <= SumLib.Sum.sum (fun y : Z => 0 <= y < hi)
      (fun y =>
        if prop_dec
          (x < y /\ Znth x groups 0 = Znth y groups 0 /\
           Znth x keys 0 <> Znth y keys 0)
        then 1 else 0) <= hi).
  {
    intros x Hx.
    pose proof
      (sum_Z_range_bounds 0 hi
        (fun y =>
          if prop_dec
            (x < y /\ Znth x groups 0 = Znth y groups 0 /\
             Znth x keys 0 <> Znth y keys 0)
          then 1 else 0)
        0 1 ltac:(lia)) as Hbounds.
    assert (Hpoint : forall y, 0 <= y < hi ->
      0 <= (if prop_dec
        (x < y /\ Znth x groups 0 = Znth y groups 0 /\
         Znth x keys 0 <> Znth y keys 0)
      then 1 else 0) <= 1).
    {
      intros y Hy.
      destruct (prop_dec
        (x < y /\ Znth x groups 0 = Znth y groups 0 /\
         Znth x keys 0 <> Znth y keys 0)); lia.
    }
    specialize (Hbounds Hpoint).
    lia.
  }
  specialize (Houter Hinner).
  lia.
Qed.
