Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Local Open Scope Z_scope.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition AtMostOneSwap (before after : list Z) : Prop :=
  after = before \/ exists i j,
    0 <= i < Zlength before /\ 0 <= j < Zlength before /\
    after = replace_Znth j (Znth i before 0)
              (replace_Znth i (Znth j before 0) before).

Definition PairDistanceSum (a b : list Z) : Z :=
  fold_right Z.add 0 (Zmap_range (fun i => Z.abs (Znth i a 0 - Znth i b 0))
                               (Zlength a)).

Definition Pre (a b : list Z) : Prop :=
  1 <= Zlength a <= 200000 /\ Zlength b = Zlength a /\
  Forall (fun x => 1 <= x <= 1000000000) a /\
  Forall (fun x => 1 <= x <= 1000000000) b.

Definition Spec (a b : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (AtMostOneSwap b) (PairDistanceSum a) out.

(** A [Seg] value is represented by its left and right endpoints. *)
Definition store_segment
    (base : addr) (i : Z) (segment : Z * Z) : Assertion :=
  let p := base + i * sizeof_front_end_type (FET_alias "<anonymous struct>") in
  (&((p) # "anonymous struct 1" ->ₛ "l") # Int |-> fst segment) **
  (&((p) # "anonymous struct 1" ->ₛ "r") # Int |-> snd segment).

Definition undef_segment (base : addr) (i : Z) : Assertion :=
  let p := base + i * sizeof_front_end_type (FET_alias "<anonymous struct>") in
  (&((p) # "anonymous struct 1" ->ₛ "l") # Int |->_) **
  (&((p) # "anonymous struct 1" ->ₛ "r") # Int |->_).

Module SegArray.
Definition full
    (base : addr) (n : Z) (segments : list (Z * Z)) : Assertion :=
  store_array store_segment base n segments.
Definition undef_full (base : addr) (n : Z) : Assertion :=
  store_undef_array undef_segment base n.
End SegArray.

Definition SegmentAllocationSize (size capacity : Z) : Prop :=
  size = capacity * sizeof_front_end_type (FET_alias "<anonymous struct>").

Definition SegmentProper (s : Z * Z) : Prop := fst s < snd s.

Definition SegmentsProper (segments : list (Z * Z)) : Prop :=
  Forall SegmentProper segments.

Definition SegmentsBounded (segments : list (Z * Z)) : Prop :=
  Forall (fun s => 1 <= fst s /\ fst s < snd s /\ snd s <= 1000000000)
         segments.

Definition SegmentsSortedByLeft (segments : list (Z * Z)) : Prop :=
  forall i j,
    0 <= i /\ i <= j /\ j < Zlength segments ->
    fst (Znth i segments (0, 0)) <= fst (Znth j segments (0, 0)).

Definition IncreasingIntervals
    (a b : list Z) (limit : Z) : list (Z * Z) :=
  map (fun i => (Znth i a 0, Znth i b 0))
      (filter (fun i => (Znth i a 0 <? Znth i b 0)%Z)
              (Zrange 0 limit)).

Definition DecreasingIntervals
    (a b : list Z) (limit : Z) : list (Z * Z) :=
  map (fun i => (Znth i b 0, Znth i a 0))
      (filter (fun i => (Znth i b 0 <? Znth i a 0)%Z)
              (Zrange 0 limit)).

Definition PairDistancePrefix (a b : list Z) (limit : Z) : Z :=
  fold_right Z.add 0
    (Zmap_range
       (fun i => Z.abs (Znth i a 0 - Znth i b 0)) limit).

(** Stable mathematical state of the classification pass in [solver]. *)
Definition SolverScanState
    (a b : list Z) (limit base : Z)
    (increasing decreasing : list (Z * Z)) : Prop :=
  increasing = IncreasingIntervals a b limit /\
  decreasing = DecreasingIntervals a b limit /\
  base = PairDistancePrefix a b limit.

Definition IntervalOverlap (s t : Z * Z) : Z :=
  Z.max 0 (Z.min (snd s) (snd t) - Z.max (fst s) (fst t)).

(** Candidates considered by one directed call of [overlap]. *)
Definition DirectedOverlapCandidatePrefix
    (left right : list (Z * Z)) (limit value : Z) : Prop :=
  value = 0 \/
  exists i j,
    0 <= i < limit /\ 0 <= j < Zlength right /\
    fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) /\
    value = IntervalOverlap (Znth i left (0, 0))
                            (Znth j right (0, 0)).

Definition DirectedOverlapMaximumPrefix
    (left right : list (Z * Z)) (limit best : Z) : Prop :=
  max_value_of_subset Z.le
    (DirectedOverlapCandidatePrefix left right limit)
    (fun value => value) best.

Definition DirectedOverlapMaximum
    (left right : list (Z * Z)) (best : Z) : Prop :=
  DirectedOverlapMaximumPrefix left right (Zlength left) best.

(** Prefix maxima of right endpoints in a list sorted by left endpoint. *)
Definition PrefixRightMaxima
    (segments : list (Z * Z)) (prefix : list Z) (limit : Z) : Prop :=
  Zlength prefix = limit /\
  forall i,
    0 <= i < limit ->
    max_value_of_subset Z.le
      (fun j : Z => 0 <= j <= i)
      (fun j => snd (Znth j segments (0, 0)))
      (Znth i prefix 0).

(** Binary-search bracket for the first segment whose left endpoint exceeds
    [key].  Bounds remain in the C invariant; this predicate owns only the
    mathematical partition of the sorted search space. *)
Definition UpperBoundBracket
    (segments : list (Z * Z)) (key lo hi : Z) : Prop :=
  (forall j, 0 <= j < lo ->
     fst (Znth j segments (0, 0)) <= key) /\
  (forall j, hi <= j < Zlength segments ->
     key < fst (Znth j segments (0, 0))).

(** The final, symmetric overlap optimized by the two directed calls. *)
Definition SwappingOverlapCandidate
    (a b : list Z) (value : Z) : Prop :=
  value = 0 \/
  exists s t,
    In s (IncreasingIntervals a b (Zlength a)) /\
    In t (DecreasingIntervals a b (Zlength a)) /\
    value = IntervalOverlap s t.

Definition SwappingOverlapMaximum
    (a b : list Z) (best : Z) : Prop :=
  max_value_of_subset Z.le
    (SwappingOverlapCandidate a b) (fun value => value) best.

Lemma abs_sub_strict_lt :
  forall x y, x < y -> Z.abs (x - y) = y - x.
Proof.
  intros x y Hxy.
  rewrite Z.abs_neq by lia.
  lia.
Qed.

Lemma abs_sub_ge :
  forall x y, y <= x -> Z.abs (x - y) = x - y.
Proof.
  intros x y Hxy.
  rewrite Z.abs_eq by lia.
  reflexivity.
Qed.

Lemma interval_overlap_nonnegative :
  forall s t, 0 <= IntervalOverlap s t.
Proof.
  intros s t. unfold IntervalOverlap. apply Z.le_max_l.
Qed.

Require Import Coq.Sorting.Permutation.
Lemma segments_bounded_znth_bounds__priority_overlap_safety_bounds :
  forall segments i default,
    SegmentsBounded segments ->
    0 <= i < Zlength segments ->
    1 <= fst (Znth i segments default) /\
    fst (Znth i segments default) < snd (Znth i segments default) /\
    snd (Znth i segments default) <= 1000000000.
Proof.
  intros segments i default Hbounded Hi.
  unfold SegmentsBounded in Hbounded.
  eapply Forall_Znth_Zlength; eauto.
Qed.
Lemma prefix_right_maxima_value_bounds__priority_overlap_safety_bounds :
  forall segments prefix limit i,
    Zlength segments = limit ->
    SegmentsBounded segments ->
    PrefixRightMaxima segments prefix limit ->
    0 <= i < limit ->
    1 <= Znth i prefix 0 <= 1000000000.
Proof.
  intros segments prefix limit i Hlength Hbounded Hprefix Hi.
  unfold PrefixRightMaxima in Hprefix.
  destruct Hprefix as [_ Hmaximum].
  specialize (Hmaximum i Hi).
  unfold max_value_of_subset, max_object_of_subset in Hmaximum.
  destruct Hmaximum as [j [[[Hj0 Hji] Hjmax] Hvalue]].
  pose proof
    (segments_bounded_znth_bounds__priority_overlap_safety_bounds
       segments j (0, 0) Hbounded ltac:(lia)) as Hjbound.
  pose proof
    (segments_bounded_znth_bounds__priority_overlap_safety_bounds
       segments i (0, 0) Hbounded ltac:(lia)) as Hibound.
  assert (Hi_member : (fun k : Z => 0 <= k <= i) i) by lia.
  specialize (Hjmax i Hi_member).
  lia.
Qed.
Lemma Znth_app_left__overlap_prefix_construction :
  forall {A : Type} (d : A) (l1 l2 : list A) i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_last__overlap_prefix_construction :
  forall {A : Type} (d x : A) (l : list A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A d x l.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat (Zlength l) - length l)%nat with 0%nat.
    + reflexivity.
    + rewrite Zlength_correct, Nat2Z.id. lia.
  - rewrite Zlength_correct, Nat2Z.id. lia.
Qed.
Lemma store_array_rec_split_to_rec__overlap_prefix_construction :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid hi (values : list A),
    lo <= mid <= hi ->
    store_array_rec storeA x lo hi values |--
      store_array_rec storeA x lo mid
        (sublist 0 (mid - lo) values) **
      store_array_rec storeA x mid hi
        (sublist (mid - lo) (hi - lo) values).
Proof.
  intros A storeA x lo mid hi values Hbounds.
  generalize dependent lo. revert mid hi.
  induction values as [|a values IH]; intros; simpl store_array_rec.
  - do 2 rewrite Zsublist_of_nil.
    simpl store_array_rec. LLM_pre_process ltac:(lia).
  - prop_apply (store_array_rec_length A storeA x lo hi (a :: values)).
    Intros_p Hlen.
    destruct (Z_lt_ge_dec mid (lo + 1)).
    + assert (mid = lo) by lia; subst mid.
      rewrite Zsublist_nil by lia.
      replace (lo - lo) with 0 by lia.
      rewrite sublist_cons1; try lia.
      simpl store_array_rec.
      rewrite sublist_self by
        (rewrite Zlength_correct; simpl in Hlen; lia).
      LLM_pre_process ltac:(lia).
      simpl in Hlen; lia.
    + rewrite sublist_cons1 by lia.
      rewrite sublist_cons2; try lia.
      2:{ rewrite Zlength_correct, Hlen. lia. }
      replace (mid - lo - 1) with (mid - (lo + 1)) by lia.
      replace (hi - lo - 1) with (hi - (lo + 1)) by lia.
      cbn [store_array_rec].
      sep_apply_l_atomic (IH mid hi (lo + 1) ltac:(lia)).
      simpl store_array_rec.
      LLM_pre_process ltac:(lia).
Qed.
Lemma store_array_rec_merge_to_rec__overlap_prefix_construction :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid hi (left right : list A),
    store_array_rec storeA x lo mid left **
    store_array_rec storeA x mid hi right |--
    store_array_rec storeA x lo hi (left ++ right).
Proof.
  intros A storeA x lo mid hi left.
  generalize dependent lo.
  induction left as [|a left IH]; intros; simpl store_array_rec.
  - Intros_p Hmid.
    Intros_p Hnil.
    subst mid.
    asrt_simpl.
    reflexivity.
  - simpl. cancel (storeA x lo a).
    sep_apply_l_atomic (IH (lo + 1) right).
    LLM_pre_process ltac:(lia).
Qed.
Lemma store_array_rec_sublist_merge_to_rec__overlap_prefix_construction :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid hi (values : list A),
    lo <= mid <= hi ->
    Zlength values = hi - lo ->
    store_array_rec storeA x lo mid
      (sublist 0 (mid - lo) values) **
    store_array_rec storeA x mid hi
      (sublist (mid - lo) (hi - lo) values) |--
    store_array_rec storeA x lo hi values.
Proof.
  intros A storeA x lo mid hi values Hbounds Hlen.
  rewrite <- (sublist_self values) at 3 by reflexivity.
  rewrite (sublist_split 0 (Zlength values) (mid - lo) values) by lia.
  rewrite Hlen.
  sep_apply_l_atomic
    (store_array_rec_merge_to_rec__overlap_prefix_construction
       A storeA x lo mid hi
       (sublist 0 (mid - lo) values)
       (sublist (mid - lo) (hi - lo) values)).
  reflexivity.
Qed.
Lemma int_cell_to_full_one__overlap_prefix_construction :
  forall x value,
    x # Int |-> value |-- IntArray.full x 1 (value :: nil).
Proof.
  intros x value.
  rewrite (IntArray.full_unfold x 1 nil value).
  rewrite (IntArray.seg_empty x 1).
  replace (x + 0 * sizeof(INT)) with x by
    (rewrite Z.mul_0_l, Z.add_0_r; reflexivity).
  cancel (x # Int |-> value).
  LLM_pre_process ltac:(lia).
Qed.
Lemma store_array_rec_snoc__overlap_prefix_construction :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo hi (values : list A) value,
    Zlength values = hi - lo ->
    store_array_rec storeA x lo hi values ** storeA x hi value |--
    store_array_rec storeA x lo (hi + 1) (values ++ value :: nil).
Proof.
  intros A storeA x lo hi values.
  generalize dependent lo. generalize dependent hi.
  induction values as [|a values IH]; intros hi lo value Hlen;
    simpl store_array_rec.
  - Intros_p Hbounds.
    Intros_p Hnil.
    rewrite Zlength_nil in Hlen.
    subst hi.
    simpl store_array_rec.
    split_pure_spatial.
    + asrt_simpl. reflexivity.
    + split_pures; dump_pre_spatial; reflexivity.
  - cancel (storeA x lo a).
    rewrite Zlength_cons in Hlen.
    sep_apply_l_atomic (IH hi (lo + 1) value ltac:(lia)).
    reflexivity.
Qed.
Lemma int_full_snoc_cell_merge__overlap_prefix_construction :
  forall x n (values : list Z) value,
    Zlength values = n ->
    IntArray.full x n values **
    (x + n * sizeof(INT)) # Int |-> value |--
    IntArray.full x (n + 1) (values ++ value :: nil).
Proof.
  intros x n values value Hlen.
  unfold IntArray.full, store_array,
    StoreIntAsElement.storeA.
  apply (store_array_rec_snoc__overlap_prefix_construction
    Z (fun (base : addr) (idx value0 : Z) =>
      (base + idx * sizeof(INT)) # Int |-> value0)
    x 0 n values value).
  lia.
Qed.
Lemma segarray_rec_shift__overlap_prefix_construction :
  forall x shift lo hi segments,
    store_array_rec store_segment x lo hi segments |--
    store_array_rec store_segment
      (x + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      (lo - shift) (hi - shift) segments.
Proof.
  intros x shift lo hi segments.
  generalize dependent lo. revert hi.
  induction segments as [|segment segments IH]; intros;
    simpl store_array_rec.
  - LLM_pre_process ltac:(lia).
  - unfold store_segment.
    assert (Hsize :
      sizeof_front_end_type (FET_alias "<anonymous struct>") =
      sizeof_alias_type "<anonymous struct>") by reflexivity.
    rewrite Hsize.
    replace
      (x + shift * sizeof_alias_type "<anonymous struct>" +
       (lo - shift) * sizeof_alias_type "<anonymous struct>")
      with (x + lo * sizeof_alias_type "<anonymous struct>") by ring.
    cancel.
    sep_apply_l_atomic (IH hi (lo + 1)).
    replace (lo + 1 - shift) with (lo - shift + 1) by lia.
    LLM_pre_process ltac:(lia).
Qed.
Lemma prefix_right_maxima_nil__overlap_prefix_construction :
  forall segments,
    PrefixRightMaxima segments nil 0.
Proof.
  intros segments.
  unfold PrefixRightMaxima.
  split.
  - reflexivity.
  - intros i Hi. lia.
Qed.
Lemma prefix_right_maxima_singleton__overlap_prefix_construction :
  forall segments,
    0 < Zlength segments ->
    PrefixRightMaxima segments
      (snd (Znth 0 segments (0, 0)) :: nil) 1.
Proof.
  intros segments Hlen.
  unfold PrefixRightMaxima.
  split.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - intros k Hk.
    assert (k = 0) by lia. subst k.
    unfold MaxMin.max_value_of_subset,
      MaxMin.max_object_of_subset.
    exists 0. split.
    + split.
      * change (0 <= 0 <= 0). lia.
      * intros b Hb.
        change (0 <= b <= 0) in Hb.
        assert (b = 0) by lia. subst b. lia.
    + reflexivity.
Qed.
Lemma prefix_right_maxima_snoc__overlap_prefix_construction :
  forall segments prefix i,
    0 < i ->
    PrefixRightMaxima segments prefix i ->
    PrefixRightMaxima segments
      (prefix ++
       [Z.max (Znth (i - 1) prefix 0)
              (snd (Znth i segments (0, 0)))])
      (i + 1).
Proof.
  intros segments prefix i Hi_pos Hprefix.
  destruct Hprefix as [Hlen Hmax].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + rewrite Znth_app_left__overlap_prefix_construction by lia.
      apply Hmax. lia.
    + assert (k = i) by lia. subst k.
      specialize (Hmax (i - 1) ltac:(lia)).
      unfold MaxMin.max_value_of_subset,
        MaxMin.max_object_of_subset in *.
      destruct Hmax as [j [[Hj Hupper] Heq]].
      change (0 <= j <= i - 1) in Hj.
      assert (Hlast :
        Znth i
          (prefix ++
           [Z.max (Znth (i - 1) prefix 0)
                  (snd (Znth i segments (0, 0)))]) 0 =
        Z.max (Znth (i - 1) prefix 0)
              (snd (Znth i segments (0, 0)))).
      { rewrite <- Hlen.
        apply Znth_app_last__overlap_prefix_construction. }
      destruct (Z_le_gt_dec
        (snd (Znth i segments (0, 0)))
        (Znth (i - 1) prefix 0)) as [Hnew | Hnew].
      * exists j. split.
        -- split.
           ++ change (0 <= j <= i). lia.
           ++ intros b Hb.
              change (0 <= b <= i) in Hb.
              destruct (Z_lt_ge_dec b i) as [Hbi | Hbi].
              ** specialize (Hupper b ltac:(change (0 <= b <= i - 1); lia)).
                 exact Hupper.
              ** assert (b = i) by lia. subst b.
                 lia.
        -- rewrite Hlast.
           rewrite Z.max_l by lia. exact Heq.
      * exists i. split.
        -- split.
           ++ change (0 <= i <= i). lia.
           ++ intros b Hb.
              change (0 <= b <= i) in Hb.
              destruct (Z_lt_ge_dec b i) as [Hbi | Hbi].
              ** specialize (Hupper b ltac:(change (0 <= b <= i - 1); lia)).
                 lia.
              ** assert (b = i) by lia. subst b.
                 lia.
        -- rewrite Hlast.
           rewrite Z.max_r by lia. reflexivity.
Qed.
Lemma directed_overlap_maximum_prefix_zero__overlap_prefix_construction :
  forall left right,
    DirectedOverlapMaximumPrefix left right 0 0.
Proof.
  intros left right.
  unfold DirectedOverlapMaximumPrefix,
    DirectedOverlapCandidatePrefix,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists 0. split.
  - split.
    + left. reflexivity.
    + intros b Hb.
      destruct Hb as [-> | [i [j [Hi _]]]]; lia.
  - reflexivity.
Qed.
Lemma upper_bound_bracket_initial__overlap_binary_search :
  forall segments key,
    UpperBoundBracket segments key 0 (Zlength segments).
Proof.
  intros segments key.
  unfold UpperBoundBracket.
  split; intros j Hj; lia.
Qed.
Lemma upper_bound_bracket_advance_lo__overlap_binary_search :
  forall segments key lo hi md,
    SegmentsSortedByLeft segments ->
    UpperBoundBracket segments key lo hi ->
    0 <= lo -> lo <= md -> md < hi -> hi <= Zlength segments ->
    fst (Znth md segments (0, 0)) <= key ->
    UpperBoundBracket segments key (md + 1) hi.
Proof.
  intros segments key lo hi md Hsorted [Hlower Hupper]
    Hlo Hlomd Hmdhi Hhilen Hmdkey.
  unfold UpperBoundBracket.
  split.
  - intros j Hj.
    destruct (Z_lt_ge_dec j lo) as [Hjlo | Hloj].
    + apply Hlower. lia.
    + assert (Hjm : j <= md) by lia.
      assert (Hmono : fst (Znth j segments (0, 0)) <=
                      fst (Znth md segments (0, 0))).
      { apply Hsorted. lia. }
      lia.
  - exact Hupper.
Qed.
Lemma upper_bound_bracket_lower_hi__overlap_binary_search :
  forall segments key lo hi md,
    SegmentsSortedByLeft segments ->
    UpperBoundBracket segments key lo hi ->
    0 <= lo -> lo <= md -> md < hi -> hi <= Zlength segments ->
    key < fst (Znth md segments (0, 0)) ->
    UpperBoundBracket segments key lo md.
Proof.
  intros segments key lo hi md Hsorted [Hlower Hupper]
    Hlo Hlomd Hmdhi Hhilen Hkeymd.
  unfold UpperBoundBracket.
  split.
  - exact Hlower.
  - intros j Hj.
    assert (Hmono : fst (Znth md segments (0, 0)) <=
                    fst (Znth j segments (0, 0))).
    { apply Hsorted. lia. }
    lia.
Qed.
Lemma list_split_at_Znth__overlap_binary_search :
  forall {A : Type} (values : list A) (d : A) i,
    0 <= i < Zlength values ->
    values = List.app (sublist 0 i values)
             (Znth i values d :: sublist (i + 1) (Zlength values) values).
Proof.
  intros A values d i Hi.
  rewrite <- (sublist_self values (Zlength values) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength values) i values) by lia.
  rewrite (sublist_split i (Zlength values) (i + 1) values) by lia.
  rewrite (sublist_single d i values) by lia.
  reflexivity.
Qed.
Lemma store_array_rec_rebase_segment__overlap_binary_search :
  forall values p q lo lo' hi hi',
    p + lo * sizeof_front_end_type (FET_alias "<anonymous struct>") =
      q + lo' * sizeof_front_end_type (FET_alias "<anonymous struct>") ->
    hi - lo = hi' - lo' ->
    store_array_rec store_segment p lo hi values |--
      store_array_rec store_segment q lo' hi' values.
Proof.
  induction values as [|a values IH]; intros; simpl.
  - LLM_pre_process ltac:(lia || nia).
  - unfold store_segment.
    rewrite <- H.
    cancel.
    apply IH; lia.
Qed.
Lemma store_array_rec_decompose_segment__overlap_binary_search :
  forall prefix row suffix p lo hi,
    store_array_rec store_segment p lo hi (List.app prefix (row :: suffix)) |--
      store_array_rec store_segment p lo (lo + Zlength prefix) prefix **
      store_segment p (lo + Zlength prefix) row **
      store_array_rec store_segment p (lo + Zlength prefix + 1) hi suffix.
Proof.
  induction prefix as [|a prefix IH]; intros; simpl.
  - rewrite Zlength_nil.
    replace (lo + 0) with lo by lia.
    LLM_pre_process ltac:(lia || nia).
  - rewrite Zlength_cons.
    replace (Z.succ (Zlength prefix)) with (Zlength prefix + 1) by lia.
    replace (lo + (Zlength prefix + 1)) with
      ((lo + 1) + Zlength prefix) by lia.
    cancel (store_segment p lo a).
    sep_apply_l_atomic (IH row suffix p (lo + 1) hi).
    cancel.
Qed.
Lemma store_array_rec_compose_segment__overlap_binary_search :
  forall prefix row suffix p lo hi,
    store_array_rec store_segment p lo (lo + Zlength prefix) prefix **
    store_segment p (lo + Zlength prefix) row **
    store_array_rec store_segment p (lo + Zlength prefix + 1) hi suffix |--
      store_array_rec store_segment p lo hi (List.app prefix (row :: suffix)).
Proof.
  induction prefix as [|a prefix IH]; intros; simpl.
  - rewrite Zlength_nil.
    replace (lo + 0) with lo by lia.
    LLM_pre_process ltac:(lia || nia).
  - rewrite Zlength_cons.
    replace (Z.succ (Zlength prefix)) with (Zlength prefix + 1) by lia.
    replace (lo + (Zlength prefix + 1)) with
      ((lo + 1) + Zlength prefix) by lia.
    cancel (store_segment p lo a).
    sep_apply_l_atomic (IH row suffix p (lo + 1) hi).
    cancel.
Qed.
Lemma store_array_rec_compose_segment_at__overlap_binary_search :
  forall prefix row suffix p lo mid hi,
    mid = lo + Zlength prefix ->
    store_array_rec store_segment p lo mid prefix **
    store_segment p mid row **
    store_array_rec store_segment p (mid + 1) hi suffix |--
      store_array_rec store_segment p lo hi (List.app prefix (row :: suffix)).
Proof.
  intros prefix row suffix p lo mid hi Hmid.
  subst mid.
  apply store_array_rec_compose_segment__overlap_binary_search.
Qed.
Lemma seg_array_full_split_at__overlap_binary_search :
  forall base n values i d,
    Zlength values = n -> 0 <= i < n ->
    SegArray.full base n values |--
      SegArray.full base i (sublist 0 i values) **
      store_segment base i (Znth i values d) **
      SegArray.full
        (base + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        (n - i - 1) (sublist (i + 1) n values).
Proof.
  intros base n values i d Hlen Hi.
  unfold SegArray.full, store_array.
  rewrite (list_split_at_Znth__overlap_binary_search values d i) at 1 by lia.
  sep_apply_l_atomic
    (store_array_rec_decompose_segment__overlap_binary_search
       (sublist 0 i values) (Znth i values d)
       (sublist (i + 1) (Zlength values) values) base 0 n).
  rewrite Zlength_sublist by lia.
  replace (i - 0) with i by lia.
  replace (0 + i) with i by lia.
  rewrite Hlen.
  sep_apply_l_atomic
    (store_array_rec_rebase_segment__overlap_binary_search
       (sublist (i + 1) n values) base
       (base + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
       (i + 1) 0 n (n - i - 1) ltac:(ring) ltac:(lia)).
  cancel.
Qed.
Lemma seg_array_full_merge_at__overlap_binary_search :
  forall base n values i d,
    Zlength values = n -> 0 <= i < n ->
    SegArray.full base i (sublist 0 i values) **
    store_segment base i (Znth i values d) **
    SegArray.full
      (base + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      (n - i - 1) (sublist (i + 1) n values) |--
    SegArray.full base n values.
Proof.
  intros base n values i d Hlen Hi.
  unfold SegArray.full, store_array.
  sep_apply_l_atomic
    (store_array_rec_rebase_segment__overlap_binary_search
       (sublist (i + 1) n values)
       (base + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
       base 0 (i + 1) (n - i - 1) n
       ltac:(ring) ltac:(lia)).
  sep_apply_l_atomic
    (store_array_rec_compose_segment_at__overlap_binary_search
       (sublist 0 i values) (Znth i values d)
       (sublist (i + 1) n values) base 0 i n
       ltac:(rewrite Zlength_sublist; lia)).
  rewrite <- Hlen.
  rewrite <- (list_split_at_Znth__overlap_binary_search values d i) by lia.
  cancel.
Qed.
Lemma seg_array_full_merge_at_flat__overlap_binary_search :
  forall base n values i d,
    Zlength values = n -> 0 <= i < n ->
    SegArray.full base i (sublist 0 i values) **
    ((&(((base + (i * sizeof ("<anonymous struct>"))))
         # "anonymous struct 1" ->ₛ "l")) # Int |-> fst (Znth i values d)) **
    ((&(((base + (i * sizeof ("<anonymous struct>"))))
         # "anonymous struct 1" ->ₛ "r")) # Int |-> snd (Znth i values d)) **
    SegArray.full
      (base + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      (n - i - 1) (sublist (i + 1) n values) |--
    SegArray.full base n values.
Proof.
  intros base n values i d Hlen Hi.
  sep_apply_r_atomic
    (seg_array_full_merge_at__overlap_binary_search
       base n values i d Hlen Hi).
  unfold store_segment.
  cancel (SegArray.full base i (sublist 0 i values)).
  cancel ((&(((base + (i * sizeof ("<anonymous struct>"))))
                # "anonymous struct 1" ->ₛ "l")) # Int
            |-> fst (Znth i values d)).
  cancel ((&(((base + (i * sizeof ("<anonymous struct>"))))
                # "anonymous struct 1" ->ₛ "r")) # Int
            |-> snd (Znth i values d)).
  cancel (SegArray.full
    (base + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
    (n - i - 1) (sublist (i + 1) n values)).
Qed.
Lemma Znth_in_bounds__overlap_directed_scan_step :
  forall {A : Type} (l : list A) i d,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma In_as_Znth__overlap_directed_scan_step :
  forall {A : Type} (l : list A) (x d : A),
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (In_nth l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma Zlength_permutation__overlap_directed_scan_step :
  forall {A : Type} (l1 l2 : list A),
    Permutation l1 l2 -> Zlength l1 = Zlength l2.
Proof.
  intros A l1 l2 Hp.
  repeat rewrite Zlength_correct.
  now rewrite (Permutation_length Hp).
Qed.
Lemma bounded_Znth__overlap_directed_scan_step :
  forall segments i d,
    SegmentsBounded segments ->
    0 <= i < Zlength segments ->
    1 <= fst (Znth i segments d) /\
    fst (Znth i segments d) < snd (Znth i segments d) /\
    snd (Znth i segments d) <= 1000000000.
Proof.
  intros segments i d Hb Hi.
  unfold SegmentsBounded in Hb.
  rewrite Forall_forall in Hb.
  apply Hb.
  apply Znth_in_bounds__overlap_directed_scan_step.
  exact Hi.
Qed.
Lemma interval_overlap_bound_left__overlap_directed_scan_step :
  forall sl sr tl tr cap,
    tl <= sl -> 0 <= cap -> Z.min sr tr - sl <= cap ->
    IntervalOverlap (sl, sr) (tl, tr) <= cap.
Proof.
  intros sl sr tl tr cap Hls Hcap Hdiff.
  unfold IntervalOverlap; simpl.
  rewrite (Z.max_l sl tl Hls).
  destruct (Z_le_gt_dec (Z.min sr tr - sl) 0).
  - rewrite Z.max_l by lia. lia.
  - rewrite Z.max_r by lia. lia.
Qed.
Lemma interval_overlap_eq_prefix__overlap_directed_scan_step :
  forall sl sr tl tr,
    tl <= sl -> sl < tr -> tr < sr ->
    IntervalOverlap (sl, sr) (tl, tr) = tr - sl.
Proof.
  intros sl sr tl tr Htl Hpos Htr.
  unfold IntervalOverlap; simpl.
  rewrite (Z.max_l sl tl Htl).
  rewrite Z.min_r by lia.
  rewrite Z.max_r by lia.
  reflexivity.
Qed.
Lemma interval_overlap_eq_left__overlap_directed_scan_step :
  forall sl sr tl tr,
    tl <= sl -> sl < sr -> sr <= tr ->
    IntervalOverlap (sl, sr) (tl, tr) = sr - sl.
Proof.
  intros sl sr tl tr Htl Hproper Hsr.
  unfold IntervalOverlap; simpl.
  rewrite (Z.max_l sl tl Htl).
  rewrite Z.min_l by lia.
  rewrite Z.max_r by lia.
  reflexivity.
Qed.
Lemma directed_overlap_extend_old__overlap_directed_scan_step :
  forall left right i value,
    DirectedOverlapCandidatePrefix left right i value ->
    DirectedOverlapCandidatePrefix left right (i + 1) value.
Proof.
  intros left right i value Hcand.
  unfold DirectedOverlapCandidatePrefix in *.
  destruct Hcand as [Hz | (ii & j & Hii & Hj & Hg & Hv)].
  - now left.
  - right. exists ii, j. repeat split; try lia; assumption.
Qed.
Lemma directed_overlap_prefix_step__overlap_directed_scan_step :
  forall left right i best target,
    DirectedOverlapMaximumPrefix left right i best ->
    best <= target ->
    DirectedOverlapCandidatePrefix left right (i + 1) target ->
    (forall j,
       0 <= j < Zlength right ->
       fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) ->
       IntervalOverlap (Znth i left (0, 0))
                       (Znth j right (0, 0)) <= target) ->
    DirectedOverlapMaximumPrefix left right (i + 1) target.
Proof.
  intros left right i best target Hprev Hbest Htarget Hnew.
  unfold DirectedOverlapMaximumPrefix in *.
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
  destruct Hprev as [old [[Hold_in Hold_max] Hold_eq]].
  exists target. split; [split | reflexivity].
  - exact Htarget.
  - intros value Hvalue.
    unfold DirectedOverlapCandidatePrefix in Hvalue.
    destruct Hvalue as [Hz | (ii & j & Hii & Hj & Hg & Hv)].
    + subst value.
      specialize (Hold_max 0).
      assert (DirectedOverlapCandidatePrefix left right i 0) by (left; reflexivity).
      specialize (Hold_max H).
      lia.
    + subst value.
      destruct Hii as [Hii0 Hii1].
      assert (ii < i \/ ii = i) by lia.
      destruct H as [Hlt | Heq].
      * specialize (Hold_max
          (IntervalOverlap (Znth ii left (0, 0)) (Znth j right (0, 0)))).
        assert (DirectedOverlapCandidatePrefix left right i
          (IntervalOverlap (Znth ii left (0, 0)) (Znth j right (0, 0)))).
        { right. exists ii, j. repeat split; try lia; reflexivity || assumption. }
        specialize (Hold_max H).
        lia.
      * subst ii. apply Hnew; assumption.
Qed.
Lemma right_prefix_attains_and_bounds__overlap_directed_scan_step :
  forall right sorted prefix limit lo hi key,
    Permutation right sorted ->
    PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted key lo hi ->
    Zlength sorted = limit ->
    lo = hi -> 0 < lo -> lo <= limit ->
    (exists j,
       0 <= j < Zlength right /\
       fst (Znth j right (0, 0)) <= key /\
       snd (Znth j right (0, 0)) = Znth (lo - 1) prefix 0) /\
    (forall j,
       0 <= j < Zlength right ->
       fst (Znth j right (0, 0)) <= key ->
       snd (Znth j right (0, 0)) <= Znth (lo - 1) prefix 0).
Proof.
  intros right sorted prefix limit lo hi key Hperm Hpref Hbracket
    Hsorted Hlohi Hlo Hlolimit.
  destruct Hpref as [Hprefix Hmax].
  specialize (Hmax (lo - 1)).
  assert (0 <= lo - 1 < limit) by lia.
  specialize (Hmax H).
  unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [k [[Hk Hall] Hkeq]].
  change (0 <= k <= lo - 1) in Hk.
  destruct Hbracket as [Hbefore Hafter].
  assert (Hkin : In (Znth k sorted (0, 0)) sorted).
  { apply Znth_in_bounds__overlap_directed_scan_step. rewrite Hsorted. lia. }
  assert (Hkin_right : In (Znth k sorted (0, 0)) right).
  { eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hkin. }
  destruct (In_as_Znth__overlap_directed_scan_step
    right (Znth k sorted (0, 0)) (0, 0) Hkin_right)
    as [j [Hj Hjval]].
  split.
  - exists j. split; [exact Hj |].
    rewrite Hjval. split.
    + apply Hbefore. lia.
    + exact Hkeq.
  - intros j' Hj' Hguard.
    assert (Hjin : In (Znth j' right (0, 0)) right).
    { apply Znth_in_bounds__overlap_directed_scan_step. exact Hj'. }
    assert (Hjin_sorted : In (Znth j' right (0, 0)) sorted).
    { eapply Permutation_in; eauto. }
    destruct (In_as_Znth__overlap_directed_scan_step
      sorted (Znth j' right (0, 0)) (0, 0) Hjin_sorted)
      as [k' [Hk' Hk'val]].
    assert (Hklo : k' < lo).
    { destruct (Z_lt_ge_dec k' lo); [assumption |].
      specialize (Hafter k').
      rewrite <- Hlohi in Hafter.
      specialize (Hafter ltac:(lia)).
      rewrite Hk'val in Hafter.
      lia. }
    specialize (Hall k').
    assert (Hkrange : 0 <= k' <= lo - 1) by lia.
    specialize (Hall Hkrange).
    rewrite Hk'val in Hall.
    lia.
Qed.
Lemma current_overlap_prefix_case__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi (best : Z),
    0 <= i < Zlength left ->
    SegmentsBounded left ->
    Permutation right sorted ->
    PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit ->
    lo = hi -> 0 < lo -> lo <= limit ->
    fst (Znth i left (0, 0)) < Znth (lo - 1) prefix 0 ->
    Znth (lo - 1) prefix 0 < snd (Znth i left (0, 0)) ->
    (exists j,
       0 <= j < Zlength right /\
       fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) /\
       IntervalOverlap (Znth i left (0, 0)) (Znth j right (0, 0)) =
         Znth (lo - 1) prefix 0 - fst (Znth i left (0, 0))) /\
    (forall j,
       0 <= j < Zlength right ->
       fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) ->
       IntervalOverlap (Znth i left (0, 0)) (Znth j right (0, 0)) <=
         Z.max 0 (Znth (lo - 1) prefix 0 - fst (Znth i left (0, 0)))).
Proof.
  intros left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref
    Hbracket Hsorted Hlohi Hlo Hlolimit Hpositive Hprefix_lt.
  pose proof (right_prefix_attains_and_bounds__overlap_directed_scan_step
    right sorted prefix limit lo hi (fst (Znth i left (0, 0)))
    Hperm Hpref Hbracket Hsorted Hlohi Hlo Hlolimit) as [Hattain Hbound].
  destruct Hattain as [j [Hj [Hguard Hsnd]]].
  destruct (Znth i left (0, 0)) as [sl sr] eqn:Hlefti.
  simpl in *.
  split.
  - exists j. split; [exact Hj |]. split; [exact Hguard |].
    rewrite <- Hsnd.
    apply interval_overlap_eq_prefix__overlap_directed_scan_step.
    + exact Hguard.
    + rewrite Hsnd. exact Hpositive.
    + rewrite Hsnd. exact Hprefix_lt.
  - intros j' Hj' Hguard'.
    specialize (Hbound j' Hj' Hguard').
    apply interval_overlap_bound_left__overlap_directed_scan_step.
    + exact Hguard'.
    + apply Z.le_max_l.
    + apply Z.le_trans with (snd (Znth j' right (0, 0)) - sl).
      * apply Z.sub_le_mono_r, Z.le_min_r.
      * apply Z.le_trans with (Znth (lo - 1) prefix 0 - sl); [lia |].
        apply Z.le_max_r.
Qed.
Lemma current_overlap_left_case__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi (best : Z),
    0 <= i < Zlength left ->
    SegmentsBounded left ->
    Permutation right sorted ->
    PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit ->
    lo = hi -> 0 < lo -> lo <= limit ->
    snd (Znth i left (0, 0)) <= Znth (lo - 1) prefix 0 ->
    (exists j,
       0 <= j < Zlength right /\
       fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) /\
       IntervalOverlap (Znth i left (0, 0)) (Znth j right (0, 0)) =
         snd (Znth i left (0, 0)) - fst (Znth i left (0, 0))) /\
    (forall j,
       0 <= j < Zlength right ->
       fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) ->
       IntervalOverlap (Znth i left (0, 0)) (Znth j right (0, 0)) <=
         snd (Znth i left (0, 0)) - fst (Znth i left (0, 0))).
Proof.
  intros left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref
    Hbracket Hsorted Hlohi Hlo Hlolimit Hprefix_ge.
  pose proof (right_prefix_attains_and_bounds__overlap_directed_scan_step
    right sorted prefix limit lo hi (fst (Znth i left (0, 0)))
    Hperm Hpref Hbracket Hsorted Hlohi Hlo Hlolimit) as [Hattain Hbound].
  destruct Hattain as [j [Hj [Hguard Hsnd]]].
  pose proof (bounded_Znth__overlap_directed_scan_step left i (0, 0) Hleft Hi)
    as Hleft_bounds.
  destruct (Znth i left (0, 0)) as [sl sr] eqn:Hlefti.
  simpl in *.
  split.
  - exists j. split; [exact Hj |]. split; [exact Hguard |].
    apply interval_overlap_eq_left__overlap_directed_scan_step.
    + exact Hguard.
    + lia.
    + change (sr <= snd (Znth j right (0, 0))).
      rewrite Hsnd. exact Hprefix_ge.
  - intros j' Hj' Hguard'.
    apply interval_overlap_bound_left__overlap_directed_scan_step.
    + exact Hguard'.
    + lia.
    + apply Z.sub_le_mono_r, Z.le_min_l.
Qed.
Lemma no_current_overlap_when_lo_zero__overlap_directed_scan_step :
  forall right sorted key lo hi,
    Permutation right sorted ->
    UpperBoundBracket sorted key lo hi ->
    lo = hi -> lo = 0 ->
    forall j, 0 <= j < Zlength right ->
      ~ fst (Znth j right (0, 0)) <= key.
Proof.
  intros right sorted key lo hi Hperm Hbracket Hlohi Hlo j Hj Hguard.
  assert (Hjin : In (Znth j right (0, 0)) right).
  { apply Znth_in_bounds__overlap_directed_scan_step. exact Hj. }
  assert (Hjin_sorted : In (Znth j right (0, 0)) sorted).
  { eapply Permutation_in; eauto. }
  destruct (In_as_Znth__overlap_directed_scan_step
    sorted (Znth j right (0, 0)) (0, 0) Hjin_sorted)
    as [k [Hk Hkval]].
  destruct Hbracket as [_ Hafter].
  specialize (Hafter k).
  rewrite <- Hlohi, Hlo in Hafter.
  specialize (Hafter ltac:(lia)).
  rewrite Hkval in Hafter.
  lia.
Qed.
Lemma current_overlap_prefix_upper__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi,
    Permutation right sorted ->
    PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit ->
    lo = hi -> 0 < lo -> lo <= limit ->
    forall j,
      0 <= j < Zlength right ->
      fst (Znth j right (0, 0)) <= fst (Znth i left (0, 0)) ->
      IntervalOverlap (Znth i left (0, 0)) (Znth j right (0, 0)) <=
        Z.max 0 (Znth (lo - 1) prefix 0 - fst (Znth i left (0, 0))).
Proof.
  intros left right sorted prefix limit i lo hi Hperm Hpref Hbracket
    Hsorted Hlohi Hlo Hlolimit j Hj Hguard.
  pose proof (right_prefix_attains_and_bounds__overlap_directed_scan_step
    right sorted prefix limit lo hi (fst (Znth i left (0, 0)))
    Hperm Hpref Hbracket Hsorted Hlohi Hlo Hlolimit) as [_ Hbound].
  specialize (Hbound j Hj Hguard).
  destruct (Znth i left (0, 0)) as [sl sr] eqn:Hlefti.
  simpl in *.
  apply interval_overlap_bound_left__overlap_directed_scan_step.
  - exact Hguard.
  - apply Z.le_max_l.
  - apply Z.le_trans with (snd (Znth j right (0, 0)) - sl).
    + apply Z.sub_le_mono_r, Z.le_min_r.
    + apply Z.le_trans with (Znth (lo - 1) prefix 0 - sl); [lia |].
      apply Z.le_max_r.
Qed.
Lemma directed_overlap_maximum_is_candidate__overlap_directed_scan_step :
  forall left right i best,
    DirectedOverlapMaximumPrefix left right i best ->
    DirectedOverlapCandidatePrefix left right i best.
Proof.
  intros left right i best Hmax.
  unfold DirectedOverlapMaximumPrefix,
    MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmax.
  destruct Hmax as [value [[Hvalue _] Heq]].
  now subst value.
Qed.
Lemma directed_overlap_step_prefix_grow__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi best,
    0 <= i < Zlength left -> SegmentsBounded left ->
    Permutation right sorted -> PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit -> lo = hi -> 0 < lo -> lo <= limit ->
    Znth (lo - 1) prefix 0 - fst (Znth i left (0, 0)) > best ->
    Znth (lo - 1) prefix 0 < snd (Znth i left (0, 0)) ->
    0 <= best ->
    DirectedOverlapMaximumPrefix left right i best ->
    DirectedOverlapMaximumPrefix left right (i + 1)
      (Znth (lo - 1) prefix 0 - fst (Znth i left (0, 0))).
Proof.
  intros left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref
    Hbracket Hsorted Hlohi Hlo Hlolimit Hgrow Hprefix_lt Hbest Hprev.
  pose proof (current_overlap_prefix_case__overlap_directed_scan_step
    left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref Hbracket
    Hsorted Hlohi Hlo Hlolimit ltac:(lia) Hprefix_lt) as [Hattain Hbound].
  rewrite Z.max_r in Hbound by lia.
  destruct Hattain as [j [Hj [Hguard Heq]]].
  eapply directed_overlap_prefix_step__overlap_directed_scan_step
    with (best := best).
  - exact Hprev.
  - lia.
  - unfold DirectedOverlapCandidatePrefix. right.
    exists i, j. repeat split; try lia; try assumption.
  - exact Hbound.
Qed.
Lemma directed_overlap_step_left_grow__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi best,
    0 <= i < Zlength left -> SegmentsBounded left ->
    Permutation right sorted -> PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit -> lo = hi -> 0 < lo -> lo <= limit ->
    snd (Znth i left (0, 0)) - fst (Znth i left (0, 0)) > best ->
    snd (Znth i left (0, 0)) <= Znth (lo - 1) prefix 0 ->
    DirectedOverlapMaximumPrefix left right i best ->
    DirectedOverlapMaximumPrefix left right (i + 1)
      (snd (Znth i left (0, 0)) - fst (Znth i left (0, 0))).
Proof.
  intros left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref
    Hbracket Hsorted Hlohi Hlo Hlolimit Hgrow Hprefix_ge Hprev.
  pose proof (current_overlap_left_case__overlap_directed_scan_step
    left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref Hbracket
    Hsorted Hlohi Hlo Hlolimit Hprefix_ge) as [Hattain Hbound].
  destruct Hattain as [j [Hj [Hguard Heq]]].
  eapply directed_overlap_prefix_step__overlap_directed_scan_step
    with (best := best).
  - exact Hprev.
  - lia.
  - unfold DirectedOverlapCandidatePrefix. right.
    exists i, j. repeat split; try lia; try assumption.
  - exact Hbound.
Qed.
Lemma directed_overlap_step_prefix_keep__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi best,
    Permutation right sorted -> PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit -> lo = hi -> 0 < lo -> lo <= limit ->
    Znth (lo - 1) prefix 0 - fst (Znth i left (0, 0)) <= best ->
    0 <= best ->
    DirectedOverlapMaximumPrefix left right i best ->
    DirectedOverlapMaximumPrefix left right (i + 1) best.
Proof.
  intros left right sorted prefix limit i lo hi best Hperm Hpref Hbracket
    Hsorted Hlohi Hlo Hlolimit Hcap Hbest Hprev.
  eapply directed_overlap_prefix_step__overlap_directed_scan_step
    with (best := best).
  - exact Hprev.
  - lia.
  - apply directed_overlap_extend_old__overlap_directed_scan_step.
    apply directed_overlap_maximum_is_candidate__overlap_directed_scan_step.
    exact Hprev.
  - intros j Hj Hguard.
    pose proof (current_overlap_prefix_upper__overlap_directed_scan_step
      left right sorted prefix limit i lo hi Hperm Hpref Hbracket Hsorted
      Hlohi Hlo Hlolimit j Hj Hguard).
    destruct (Z_le_gt_dec (Znth (lo - 1) prefix 0 -
      fst (Znth i left (0, 0))) 0).
    + rewrite Z.max_l in H by lia. lia.
    + rewrite Z.max_r in H by lia. lia.
Qed.
Lemma directed_overlap_step_left_keep__overlap_directed_scan_step :
  forall left right sorted prefix limit i lo hi best,
    0 <= i < Zlength left -> SegmentsBounded left ->
    Permutation right sorted -> PrefixRightMaxima sorted prefix limit ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    Zlength sorted = limit -> lo = hi -> 0 < lo -> lo <= limit ->
    snd (Znth i left (0, 0)) - fst (Znth i left (0, 0)) <= best ->
    snd (Znth i left (0, 0)) <= Znth (lo - 1) prefix 0 ->
    DirectedOverlapMaximumPrefix left right i best ->
    DirectedOverlapMaximumPrefix left right (i + 1) best.
Proof.
  intros left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref
    Hbracket Hsorted Hlohi Hlo Hlolimit Hcap Hprefix_ge Hprev.
  pose proof (current_overlap_left_case__overlap_directed_scan_step
    left right sorted prefix limit i lo hi best Hi Hleft Hperm Hpref Hbracket
    Hsorted Hlohi Hlo Hlolimit Hprefix_ge) as [_ Hbound].
  eapply directed_overlap_prefix_step__overlap_directed_scan_step
    with (best := best).
  - exact Hprev.
  - lia.
  - apply directed_overlap_extend_old__overlap_directed_scan_step.
    apply directed_overlap_maximum_is_candidate__overlap_directed_scan_step.
    exact Hprev.
  - intros j Hj Hguard.
    specialize (Hbound j Hj Hguard). lia.
Qed.
Lemma directed_overlap_step_empty_keep__overlap_directed_scan_step :
  forall left right sorted i lo hi best,
    Permutation right sorted ->
    UpperBoundBracket sorted (fst (Znth i left (0, 0))) lo hi ->
    lo = hi -> lo = 0 ->
    DirectedOverlapMaximumPrefix left right i best ->
    DirectedOverlapMaximumPrefix left right (i + 1) best.
Proof.
  intros left right sorted i lo hi best Hperm Hbracket Hlohi Hlo Hprev.
  eapply directed_overlap_prefix_step__overlap_directed_scan_step
    with (best := best).
  - exact Hprev.
  - lia.
  - apply directed_overlap_extend_old__overlap_directed_scan_step.
    apply directed_overlap_maximum_is_candidate__overlap_directed_scan_step.
    exact Hprev.
  - intros j Hj Hguard.
    exfalso.
    eapply (no_current_overlap_when_lo_zero__overlap_directed_scan_step
      right sorted (fst (Znth i left (0, 0))) lo hi); eauto.
Qed.
Lemma store_segment_shift__overlap_directed_scan_step :
  forall x off idx segment,
    store_segment (x + off * sizeof_front_end_type
      (FET_alias "<anonymous struct>")) idx segment =
    store_segment x (idx + off) segment.
Proof.
  intros x off idx [sl sr].
  unfold store_segment; simpl.
  replace (x + off * sizeof_alias_type "<anonymous struct>" +
    idx * sizeof_alias_type "<anonymous struct>")
    with (x + (idx + off) * sizeof_alias_type "<anonymous struct>") by ring.
  reflexivity.
Qed.
Lemma store_segment_fold__overlap_directed_scan_step :
  forall (base : addr) (i : Z) (segment : Z * Z),
    (&(((base + i * sizeof_front_end_type
          (FET_alias "<anonymous struct>"))) #
        "anonymous struct 1" ->ₛ "l") # Int |-> fst segment) **
    (&(((base + i * sizeof_front_end_type
          (FET_alias "<anonymous struct>"))) #
        "anonymous struct 1" ->ₛ "r") # Int |-> snd segment) |--
    store_segment base i segment.
Proof.
  intros base i segment.
  unfold store_segment.
  reflexivity.
Qed.
Lemma store_segment_array_shift__overlap_directed_scan_step :
  forall values x off lo hi,
    store_array_rec store_segment
      (x + off * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      lo hi values |--
    store_array_rec store_segment x (lo + off) (hi + off) values.
Proof.
  induction values as [|segment values IH]; intros x off lo hi;
    cbn [store_array_rec].
  - LLM_pre_process ltac:(lia || nia).
  - rewrite (store_segment_shift__overlap_directed_scan_step
      x off lo segment).
    cancel (store_segment x (lo + off) segment).
    replace (lo + off + 1) with (lo + 1 + off) by lia.
    apply (IH x off (lo + 1) hi).
Qed.
Lemma store_array_rec_merge__overlap_directed_scan_step :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid hi (first second : list A),
    store_array_rec storeA x lo mid first **
    store_array_rec storeA x mid hi second |--
    store_array_rec storeA x lo hi (first ++ second).
Proof.
  intros A storeA x lo mid hi first.
  generalize dependent lo.
  induction first as [|a first IH]; intros lo second; simpl store_array_rec.
  - LLM_pre_process ltac:(lia || nia).
    replace lo with mid by lia. reflexivity.
  - cancel (storeA x lo a).
    sep_apply_l_atomic (IH (lo + 1) second).
    LLM_pre_process ltac:(lia || nia).
Qed.
Lemma store_array_rec_single__overlap_directed_scan_step :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion) x lo value,
    storeA x lo value |--
    store_array_rec storeA x lo (lo + 1) [value].
Proof.
  intros A storeA x lo value.
  cbn [store_array_rec].
  LLM_pre_process ltac:(lia || nia).
Qed.
Lemma store_array_rec_snoc__overlap_directed_scan_step :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid (first : list A) value,
    store_array_rec storeA x lo mid first ** storeA x mid value |--
    store_array_rec storeA x lo (mid + 1) (first ++ [value]).
Proof.
  intros A storeA x lo mid first value.
  sep_apply_l_atomic
    (store_array_rec_single__overlap_directed_scan_step
      A storeA x mid value).
  sep_apply_l_atomic
    (store_array_rec_merge__overlap_directed_scan_step
      A storeA x lo mid (mid + 1) first [value]).
  cbn [store_array_rec].
  LLM_pre_process ltac:(lia || nia).
Qed.
Lemma seg_array_merge_current__overlap_directed_scan_step :
  forall x n i values d,
    n = Zlength values -> 0 <= i < n ->
    SegArray.full x i (sublist 0 i values) **
    store_segment x i (Znth i values d) **
    SegArray.full
      (x + (i + 1) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      (n - i - 1) (sublist (i + 1) n values) |--
    SegArray.full x n values.
Proof.
  intros x n i values d Hn Hi.
  unfold SegArray.full, store_array.
  sep_apply_l_atomic
    (store_array_rec_snoc__overlap_directed_scan_step
      (Z * Z) store_segment x 0 i (sublist 0 i values)
      (Znth i values d)).
  sep_apply_l_atomic
    (store_segment_array_shift__overlap_directed_scan_step
      (sublist (i + 1) n values) x (i + 1) 0 (n - i - 1)).
  replace (0 + (i + 1)) with (i + 1) by lia.
  replace (n - i - 1 + (i + 1)) with n by lia.
  sep_apply_l_atomic
    (store_array_rec_merge__overlap_directed_scan_step
      (Z * Z) store_segment x 0 (i + 1) n
      (sublist 0 i values ++ [Znth i values d])
      (sublist (i + 1) n values)).
  rewrite <- (sublist_single d i values) by lia.
  rewrite <- sublist_split by lia.
  rewrite <- sublist_split by lia.
  rewrite (sublist_self values n Hn).
  reflexivity.
Qed.
Lemma directed_overlap_maximum_empty_left__overlap_returns_and_contract :
  forall left right,
    Zlength left = 0 ->
    DirectedOverlapMaximum left right 0.
Proof.
  intros left right Hleft.
  unfold DirectedOverlapMaximum, DirectedOverlapMaximumPrefix.
  apply (max_1 Z.le 0).
  intros value.
  unfold DirectedOverlapCandidatePrefix.
  split.
  - intros [Hvalue | [i [j [Hi _]]]].
    + lia.
    + lia.
  - intros Hvalue.
    left.
    lia.
Qed.
Lemma directed_overlap_maximum_empty_right__overlap_returns_and_contract :
  forall left right,
    Zlength right = 0 ->
    DirectedOverlapMaximum left right 0.
Proof.
  intros left right Hright.
  unfold DirectedOverlapMaximum, DirectedOverlapMaximumPrefix.
  apply (max_1 Z.le 0).
  intros value.
  unfold DirectedOverlapCandidatePrefix.
  split.
  - intros [Hvalue | [i [j [_ [Hj _]]]]].
    + lia.
    + lia.
  - intros Hvalue.
    left.
    lia.
Qed.
Lemma solver_scan_state_zero__solver_initialization_and_frame :
  forall values b_data,
    SolverScanState values b_data 0 0 nil nil /\
    SegmentsBounded nil /\ SegmentsBounded nil.
Proof.
  intros values b_data.
  unfold SolverScanState, IncreasingIntervals, DecreasingIntervals,
    PairDistancePrefix, Zmap_range, SegmentsBounded.
  simpl.
  repeat split; constructor.
Qed.
Lemma undef_segment_shift__solver_initialization_and_frame :
  forall base shift i,
    undef_segment base i |--
    undef_segment
      (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      (i - shift).
Proof.
  intros base shift i.
  unfold undef_segment.
  replace
    (base + i * sizeof_front_end_type (FET_alias "<anonymous struct>"))
    with
    (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>") +
     (i - shift) * sizeof_front_end_type (FET_alias "<anonymous struct>"))
    by lia.
  cancel.
Qed.
Lemma undef_segment_rec_shift__solver_initialization_and_frame :
  forall len base shift lo hi,
    store_undef_array_rec undef_segment base lo hi len |--
    store_undef_array_rec undef_segment
      (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
      (lo - shift) (hi - shift) len.
Proof.
  induction len; intros base shift lo hi; simpl.
  - Intros_p Hlohi.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - sep_apply
      (IHlen base shift (lo + 1) hi).
    sep_apply
      (undef_segment_shift__solver_initialization_and_frame base shift lo).
    replace (lo + 1 - shift) with (lo - shift + 1) by lia.
    cancel
      (undef_segment
        (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        (lo - shift)).
    change
      (store_undef_array_rec undef_segment
        (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        (lo - shift + 1) (hi - shift) len |--
       store_undef_array_rec undef_segment
        (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        (lo - shift + 1) (hi - shift) len).
    cancel
      (store_undef_array_rec undef_segment
        (base + shift * sizeof_front_end_type (FET_alias "<anonymous struct>"))
        (lo - shift + 1) (hi - shift) len).
Qed.
Lemma Zrange_zero_succ__solver_scan_transitions_and_exit :
  forall i, 0 <= i -> Zrange 0 (i + 1) = (Zrange 0 i ++ [i])%list.
Proof.
  intros i Hi.
  unfold Zrange.
  replace (Z.to_nat (i + 1 - 0)) with (Z.to_nat (i - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  simpl.
  rewrite Z2Nat.id by lia.
  replace (0 + i) with i by lia.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.
Lemma fold_right_Zadd_app__solver_scan_transitions_and_exit :
  forall left right,
    fold_right Z.add 0 (left ++ right)%list =
    fold_right Z.add 0 left + fold_right Z.add 0 right.
Proof.
  intros left right.
  induction left; simpl; lia.
Qed.
Lemma increasing_intervals_step_lt__solver_scan_transitions_and_exit :
  forall a b i,
    0 <= i -> Znth i a 0 < Znth i b 0 ->
    IncreasingIntervals a b (i + 1) =
    (IncreasingIntervals a b i ++ [(Znth i a 0, Znth i b 0)])%list.
Proof.
  intros a b i Hi Hlt.
  unfold IncreasingIntervals.
  rewrite Zrange_zero_succ__solver_scan_transitions_and_exit by exact Hi.
  rewrite filter_app, map_app.
  simpl.
  replace (Znth i a 0 <? Znth i b 0)%Z with true
    by (symmetry; apply Z.ltb_lt; exact Hlt).
  simpl.
  reflexivity.
Qed.
Lemma increasing_intervals_step_not_lt__solver_scan_transitions_and_exit :
  forall a b i,
    0 <= i -> Znth i b 0 <= Znth i a 0 ->
    IncreasingIntervals a b (i + 1) = IncreasingIntervals a b i.
Proof.
  intros a b i Hi Hge.
  unfold IncreasingIntervals.
  rewrite Zrange_zero_succ__solver_scan_transitions_and_exit by exact Hi.
  rewrite filter_app, map_app.
  simpl.
  replace (Znth i a 0 <? Znth i b 0)%Z with false
    by (symmetry; apply Z.ltb_ge; exact Hge).
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma decreasing_intervals_step_gt__solver_scan_transitions_and_exit :
  forall a b i,
    0 <= i -> Znth i b 0 < Znth i a 0 ->
    DecreasingIntervals a b (i + 1) =
    (DecreasingIntervals a b i ++ [(Znth i b 0, Znth i a 0)])%list.
Proof.
  intros a b i Hi Hgt.
  unfold DecreasingIntervals.
  rewrite Zrange_zero_succ__solver_scan_transitions_and_exit by exact Hi.
  rewrite filter_app, map_app.
  simpl.
  replace (Znth i b 0 <? Znth i a 0)%Z with true
    by (symmetry; apply Z.ltb_lt; exact Hgt).
  simpl.
  reflexivity.
Qed.
Lemma decreasing_intervals_step_not_gt__solver_scan_transitions_and_exit :
  forall a b i,
    0 <= i -> Znth i a 0 <= Znth i b 0 ->
    DecreasingIntervals a b (i + 1) = DecreasingIntervals a b i.
Proof.
  intros a b i Hi Hle.
  unfold DecreasingIntervals.
  rewrite Zrange_zero_succ__solver_scan_transitions_and_exit by exact Hi.
  rewrite filter_app, map_app.
  simpl.
  replace (Znth i b 0 <? Znth i a 0)%Z with false
    by (symmetry; apply Z.ltb_ge; exact Hle).
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma pair_distance_prefix_step__solver_scan_transitions_and_exit :
  forall a b i,
    0 <= i ->
    PairDistancePrefix a b (i + 1) =
    PairDistancePrefix a b i + Z.abs (Znth i a 0 - Znth i b 0).
Proof.
  intros a b i Hi.
  unfold PairDistancePrefix, Zmap_range.
  rewrite Zrange_zero_succ__solver_scan_transitions_and_exit by exact Hi.
  rewrite map_app.
  rewrite fold_right_Zadd_app__solver_scan_transitions_and_exit.
  simpl.
  lia.
Qed.
Lemma solver_scan_state_step_lt__solver_scan_transitions_and_exit :
  forall a b i base increasing decreasing,
    0 <= i ->
    Znth i a 0 < Znth i b 0 ->
    SolverScanState a b i base increasing decreasing ->
    SolverScanState a b (i + 1)
      (base + (Znth i b 0 - Znth i a 0))
      (increasing ++ [(Znth i a 0, Znth i b 0)])%list decreasing.
Proof.
  intros a b i base increasing decreasing Hi Hlt Hstate.
  unfold SolverScanState in *.
  destruct Hstate as [Hinc [Hdec Hbase]].
  repeat split.
  - rewrite increasing_intervals_step_lt__solver_scan_transitions_and_exit
      by assumption.
    now rewrite Hinc.
  - rewrite decreasing_intervals_step_not_gt__solver_scan_transitions_and_exit
      by lia.
    exact Hdec.
  - rewrite pair_distance_prefix_step__solver_scan_transitions_and_exit
      by exact Hi.
    rewrite Hbase, abs_sub_strict_lt by exact Hlt.
    lia.
Qed.
Lemma solver_scan_state_step_gt__solver_scan_transitions_and_exit :
  forall a b i base increasing decreasing,
    0 <= i ->
    Znth i b 0 < Znth i a 0 ->
    SolverScanState a b i base increasing decreasing ->
    SolverScanState a b (i + 1)
      (base + (Znth i a 0 - Znth i b 0))
      increasing (decreasing ++ [(Znth i b 0, Znth i a 0)])%list.
Proof.
  intros a b i base increasing decreasing Hi Hgt Hstate.
  unfold SolverScanState in *.
  destruct Hstate as [Hinc [Hdec Hbase]].
  repeat split.
  - rewrite increasing_intervals_step_not_lt__solver_scan_transitions_and_exit
      by lia.
    exact Hinc.
  - rewrite decreasing_intervals_step_gt__solver_scan_transitions_and_exit
      by assumption.
    now rewrite Hdec.
  - rewrite pair_distance_prefix_step__solver_scan_transitions_and_exit
      by exact Hi.
    rewrite Hbase, abs_sub_ge by lia.
    lia.
Qed.
Lemma solver_scan_state_step_eq__solver_scan_transitions_and_exit :
  forall a b i base increasing decreasing,
    0 <= i ->
    Znth i a 0 = Znth i b 0 ->
    SolverScanState a b i base increasing decreasing ->
    SolverScanState a b (i + 1) base increasing decreasing.
Proof.
  intros a b i base increasing decreasing Hi Heq Hstate.
  unfold SolverScanState in *.
  destruct Hstate as [Hinc [Hdec Hbase]].
  repeat split.
  - rewrite increasing_intervals_step_not_lt__solver_scan_transitions_and_exit
      by lia.
    exact Hinc.
  - rewrite decreasing_intervals_step_not_gt__solver_scan_transitions_and_exit
      by lia.
    exact Hdec.
  - rewrite pair_distance_prefix_step__solver_scan_transitions_and_exit
      by exact Hi.
    rewrite Hbase, Heq, Z.sub_diag, Z.abs_0.
    lia.
Qed.
Lemma segments_bounded_snoc__solver_scan_transitions_and_exit :
  forall segments l r,
    SegmentsBounded segments ->
    1 <= l -> l < r -> r <= 1000000000 ->
    SegmentsBounded (segments ++ [(l, r)])%list.
Proof.
  intros segments l r Hsegments Hl Hlr Hr.
  unfold SegmentsBounded in *.
  apply Forall_app.
  split; [exact Hsegments |].
  constructor; [simpl; lia | constructor].
Qed.
Lemma solver_scan_state_at_length__solver_scan_transitions_and_exit :
  forall a b i base increasing decreasing,
    i = Zlength a ->
    SolverScanState a b i base increasing decreasing ->
    increasing = IncreasingIntervals a b (Zlength a) /\
    decreasing = DecreasingIntervals a b (Zlength a) /\
    base = PairDistanceSum a b.
Proof.
  intros a b i base increasing decreasing Hi Hstate.
  subst i.
  unfold SolverScanState in Hstate.
  destruct Hstate as [Hinc [Hdec Hbase]].
  repeat split; try assumption.
Qed.
Lemma store_segment_array_rec_snoc__solver_scan_transitions_and_exit :
  forall segments segment base lo hi,
    0 <= lo ->
    hi = lo + Zlength segments ->
    store_array_rec store_segment base lo hi segments **
      store_segment base hi segment |--
    store_array_rec store_segment base lo (hi + 1)
      (segments ++ [segment])%list.
Proof.
  intros segments.
  induction segments as [|head tail IH]; intros segment base lo hi Hlo Hhi.
  - simpl.
    rewrite Zlength_nil in Hhi.
    subst hi.
    simpl.
    replace (lo + 0) with lo by lia.
    split_pure_spatial.
    + Intros_p Hlo_eq.
      Intros_p Hnil_eq.
      cancel.
    + split_pures; dump_pre_spatial; auto.
  - simpl.
    rewrite Zlength_cons in Hhi.
    unfold Z.succ in Hhi.
    sep_apply (IH segment base (lo + 1) hi); try lia.
    cancel.
Qed.
Lemma segarray_full_snoc__solver_scan_transitions_and_exit :
  forall base n segments segment,
    n = Zlength segments ->
    SegArray.full base n segments ** store_segment base n segment |--
    SegArray.full base (n + 1) (segments ++ [segment])%list.
Proof.
  intros base n segments segment Hlen.
  unfold SegArray.full, store_array.
  sep_apply
    (store_segment_array_rec_snoc__solver_scan_transitions_and_exit
       segments segment base 0 n); try lia.
  cancel.
Qed.
Lemma store_segment_lr_to_store_segment__solver_scan_transitions_and_exit :
  forall base i l r,
    ((&(((base + (i * sizeof ("<anonymous struct>"))))
           # "anonymous struct 1" ->ₛ "l")) # Int |-> l) **
    ((&(((base + (i * sizeof ("<anonymous struct>"))))
           # "anonymous struct 1" ->ₛ "r")) # Int |-> r) |--
    store_segment base i (l, r).
Proof.
  intros base i l r.
  unfold store_segment.
  simpl.
  cancel.
Qed.
Lemma segarray_full_snoc_lr__solver_scan_transitions_and_exit :
  forall base n segments l r,
    n = Zlength segments ->
    SegArray.full base n segments **
      ((&(((base + (n * sizeof ("<anonymous struct>"))))
             # "anonymous struct 1" ->ₛ "l")) # Int |-> l) **
      ((&(((base + (n * sizeof ("<anonymous struct>"))))
             # "anonymous struct 1" ->ₛ "r")) # Int |-> r) |--
    SegArray.full base (n + 1) (segments ++ [(l, r)])%list.
Proof.
  intros base n segments l r Hlen.
  sep_apply_l_atomic
    (store_segment_lr_to_store_segment__solver_scan_transitions_and_exit
       base n l r).
  sep_apply
    (segarray_full_snoc__solver_scan_transitions_and_exit
       base n segments (l, r) Hlen).
  cancel.
Qed.
Lemma Znth_In_index__solver_final_maximum_and_spec :
  forall (A : Type) (l : list A) i d,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma In_Znth_index__solver_final_maximum_and_spec :
  forall (A : Type) (l : list A) x d,
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (In_nth l x d Hin) as [i [Hi Hnth]].
  exists (Z.of_nat i).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma directed_overlap_candidate_full_iff__solver_final_maximum_and_spec :
  forall left right value,
    DirectedOverlapCandidatePrefix left right (Zlength left) value <->
    value = 0 \/
    exists s t,
      In s left /\ In t right /\ fst t <= fst s /\
      value = IntervalOverlap s t.
Proof.
  intros left right value.
  unfold DirectedOverlapCandidatePrefix.
  split.
  - intros [Hz | [i [j [Hi [Hj [Hord Heq]]]]]].
    + now left.
    + right.
      exists (Znth i left (0, 0)), (Znth j right (0, 0)).
      repeat split; auto using Znth_In_index__solver_final_maximum_and_spec.
  - intros [Hz | [s [t [Hs [Ht [Hord Heq]]]]]].
    + now left.
    + right.
      destruct (In_Znth_index__solver_final_maximum_and_spec
                  _ left s (0, 0) Hs) as [i [Hi Hsi]].
      destruct (In_Znth_index__solver_final_maximum_and_spec
                  _ right t (0, 0) Ht) as [j [Hj Htj]].
      subst s. subst t.
      exists i, j.
      repeat split; auto; lia.
Qed.
Lemma directed_overlap_candidate_permutation_left__solver_final_maximum_and_spec :
  forall left left' right value,
    Permutation left left' ->
    (DirectedOverlapCandidatePrefix left right (Zlength left) value <->
     DirectedOverlapCandidatePrefix left' right (Zlength left') value).
Proof.
  intros left left' right value Hperm.
  rewrite !directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
  split; intros [Hz | [s [t [Hs [Ht [Hord Heq]]]]]].
  - now left.
  - right. exists s, t. repeat split; auto.
    eapply Permutation_in; eauto.
  - now left.
  - right. exists s, t. repeat split; auto.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hs].
Qed.
Lemma directed_overlap_maximum_permutation_left__solver_final_maximum_and_spec :
  forall left left' right best,
    Permutation left left' ->
    DirectedOverlapMaximum left right best ->
    DirectedOverlapMaximum left' right best.
Proof.
  intros left left' right best Hperm Hmax.
  unfold DirectedOverlapMaximum in *.
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hmax as [value [[Hvalue Hgreatest] Heq]].
  exists value. split; [split |]; auto.
  - apply (proj1
      (directed_overlap_candidate_permutation_left__solver_final_maximum_and_spec
         left left' right value Hperm)).
    exact Hvalue.
  - intros other Hother.
    apply Hgreatest.
    apply (proj2
      (directed_overlap_candidate_permutation_left__solver_final_maximum_and_spec
         left left' right other Hperm)).
    exact Hother.
Qed.
Lemma interval_overlap_sym__solver_final_maximum_and_spec :
  forall s t, IntervalOverlap s t = IntervalOverlap t s.
Proof.
  intros [sl sr] [tl tr].
  unfold IntervalOverlap. simpl.
  rewrite (Z.min_comm sr tr), (Z.max_comm sl tl).
  reflexivity.
Qed.
Lemma swapping_overlap_maximum_from_directed__solver_final_maximum_and_spec :
  forall a b forward reverse,
    DirectedOverlapMaximum
      (IncreasingIntervals a b (Zlength a))
      (DecreasingIntervals a b (Zlength a)) forward ->
    DirectedOverlapMaximum
      (DecreasingIntervals a b (Zlength a))
      (IncreasingIntervals a b (Zlength a)) reverse ->
    reverse <= forward ->
    SwappingOverlapMaximum a b forward.
Proof.
  intros a b forward reverse Hforward Hreverse Hle.
  unfold DirectedOverlapMaximum in Hforward, Hreverse.
  unfold SwappingOverlapMaximum.
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hforward as [vf [[Hvf Hforward] Evf]].
  destruct Hreverse as [vr [[Hvr Hreverse] Evr]].
  simpl in *.
  subst forward. subst reverse.
  exists vf. split; [split |]; auto.
  - apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec in Hvf.
    unfold SwappingOverlapCandidate.
    destruct Hvf as [Hz | [s [t [Hs [Ht [Hord Heq]]]]]].
    + now left.
    + right. exists s, t. repeat split; auto.
  - intros value Hvalue.
    unfold SwappingOverlapCandidate in Hvalue.
    destruct Hvalue as [Hz | [s [t [Hs [Ht Heq]]]]].
    + subst value.
      apply Hforward.
      apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
      now left.
    + destruct (Z_le_gt_dec (fst t) (fst s)) as [Hord | Hord].
      * apply Hforward.
        apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
        right. exists s, t. repeat split; auto.
      * eapply Z.le_trans; [apply Hreverse | exact Hle].
        apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
        right. exists t, s. repeat split; auto; try lia.
        rewrite interval_overlap_sym__solver_final_maximum_and_spec.
        exact Heq.
Qed.
Lemma swapping_overlap_maximum_from_directed_reverse__solver_final_maximum_and_spec :
  forall a b forward reverse,
    DirectedOverlapMaximum
      (IncreasingIntervals a b (Zlength a))
      (DecreasingIntervals a b (Zlength a)) forward ->
    DirectedOverlapMaximum
      (DecreasingIntervals a b (Zlength a))
      (IncreasingIntervals a b (Zlength a)) reverse ->
    forward <= reverse ->
    SwappingOverlapMaximum a b reverse.
Proof.
  intros a b forward reverse Hforward Hreverse Hle.
  unfold DirectedOverlapMaximum in Hforward, Hreverse.
  unfold SwappingOverlapMaximum.
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hforward as [vf [[Hvf Hforward] Evf]].
  destruct Hreverse as [vr [[Hvr Hreverse] Evr]].
  simpl in *.
  subst forward. subst reverse.
  exists vr. split; [split |]; auto.
  - apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec in Hvr.
    unfold SwappingOverlapCandidate.
    destruct Hvr as [Hz | [t [s [Ht [Hs [Hord Heq]]]]]].
    + now left.
    + right. exists s, t. repeat split; auto.
      rewrite interval_overlap_sym__solver_final_maximum_and_spec.
      exact Heq.
  - intros value Hvalue.
    unfold SwappingOverlapCandidate in Hvalue.
    destruct Hvalue as [Hz | [s [t [Hs [Ht Heq]]]]].
    + subst value.
      apply Hreverse.
      apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
      now left.
    + destruct (Z_le_gt_dec (fst t) (fst s)) as [Hord | Hord].
      * eapply Z.le_trans; [apply Hforward | exact Hle].
        apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
        right. exists s, t. repeat split; auto.
      * apply Hreverse.
        apply directed_overlap_candidate_full_iff__solver_final_maximum_and_spec.
        right. exists t, s. repeat split; auto; try lia.
        rewrite interval_overlap_sym__solver_final_maximum_and_spec.
        exact Heq.
Qed.
Lemma fold_map_single_change__solver_final_maximum_and_spec :
  forall (xs : list Z) (f g : Z -> Z) i,
    NoDup xs -> In i xs ->
    (forall k, In k xs -> k <> i -> f k = g k) ->
    fold_right Z.add 0 (map f xs) - fold_right Z.add 0 (map g xs) =
    f i - g i.
Proof.
  induction xs as [|x xs IH]; intros f g i Hnodup Hin Heq; simpl in *.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    destruct Hin as [Hxi | Hin].
    + subst x.
      assert (Htail : forall k, In k xs -> f k = g k).
      { intros k Hk. apply Heq; auto. congruence. }
      assert (Hsum : fold_right Z.add 0 (map f xs) =
                     fold_right Z.add 0 (map g xs)).
      { f_equal. apply map_ext_in. intros a Ha. apply Htail. exact Ha. }
      simpl. lia.
    + destruct (Z.eq_dec x i) as [Hxi | Hxi].
      * subst x. contradiction.
      * rewrite (Heq x) by auto.
        assert (Hrest := IH f g i Hnodup' Hin).
        specialize (Hrest ltac:(intros k Hk Hki; apply Heq; auto)).
        lia.
Qed.
Lemma fold_map_two_changes__solver_final_maximum_and_spec :
  forall (xs : list Z) (f g : Z -> Z) i j,
    NoDup xs -> i <> j -> In i xs -> In j xs ->
    (forall k, In k xs -> k <> i -> k <> j -> f k = g k) ->
    fold_right Z.add 0 (map f xs) - fold_right Z.add 0 (map g xs) =
    (f i - g i) + (f j - g j).
Proof.
  induction xs as [|x xs IH]; intros f g i j Hnodup Hij Hini Hinj Heq;
    simpl in *; [contradiction |].
  inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
  destruct Hini as [Hxi | Hini].
  - subst x.
    assert (Hsingle :
      fold_right Z.add 0 (map f xs) - fold_right Z.add 0 (map g xs) =
      f j - g j).
    { apply fold_map_single_change__solver_final_maximum_and_spec; auto.
      * destruct Hinj; [congruence | assumption].
      * intros k Hk Hkj. apply Heq; auto. congruence. }
    simpl. lia.
  - destruct Hinj as [Hxj | Hinj].
    + subst x.
      assert (Hsingle :
        fold_right Z.add 0 (map f xs) - fold_right Z.add 0 (map g xs) =
        f i - g i).
      { apply fold_map_single_change__solver_final_maximum_and_spec; auto.
        intros k Hk Hki. apply Heq; auto. congruence. }
      simpl. lia.
    + assert (Hxi : x <> i) by (intro; subst; contradiction).
      assert (Hxj : x <> j) by (intro; subst; contradiction).
      rewrite (Heq x) by auto.
      assert (Hrest := IH f g i j Hnodup' Hij Hini Hinj).
      specialize (Hrest ltac:(intros k Hk Hki Hkj; apply Heq; auto)).
      lia.
Qed.
Lemma increasing_interval_member__solver_final_maximum_and_spec :
  forall a b n s,
    In s (IncreasingIntervals a b n) ->
    exists i,
      0 <= i < n /\ Znth i a 0 < Znth i b 0 /\
      s = (Znth i a 0, Znth i b 0).
Proof.
  intros a b n s Hin.
  unfold IncreasingIntervals in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hs Hi]].
  apply filter_In in Hi.
  destruct Hi as [Hirange Hlt].
  apply Z.ltb_lt in Hlt.
  apply <- In_Zrange in Hirange.
  exists i. split; [exact Hirange |].
  split; [exact Hlt |]. symmetry. exact Hs.
Qed.
Lemma decreasing_interval_member__solver_final_maximum_and_spec :
  forall a b n s,
    In s (DecreasingIntervals a b n) ->
    exists i,
      0 <= i < n /\ Znth i b 0 < Znth i a 0 /\
      s = (Znth i b 0, Znth i a 0).
Proof.
  intros a b n s Hin.
  unfold DecreasingIntervals in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hs Hi]].
  apply filter_In in Hi.
  destruct Hi as [Hirange Hlt].
  apply Z.ltb_lt in Hlt.
  apply <- In_Zrange in Hirange.
  exists i. split; [exact Hirange |].
  split; [exact Hlt |]. symmetry. exact Hs.
Qed.
Lemma opposite_distance_overlap_identity__solver_final_maximum_and_spec :
  forall ai bi aj bj,
    ai < bi -> bj < aj ->
    Z.abs (ai - bi) + Z.abs (aj - bj) -
      (Z.abs (ai - bj) + Z.abs (aj - bi)) <=
    2 * IntervalOverlap (ai, bi) (bj, aj).
Proof.
  intros ai bi aj bj Hai Haj.
  replace (2 * IntervalOverlap (ai, bi) (bj, aj)) with
      (IntervalOverlap (ai, bi) (bj, aj) +
       IntervalOverlap (ai, bi) (bj, aj)) by ring.
  rewrite (abs_sub_strict_lt ai bi Hai).
  rewrite (abs_sub_ge aj bj) by lia.
  unfold IntervalOverlap. simpl.
  destruct (Z_le_gt_dec bi aj) as [Hmin | Hmin].
  - rewrite (Z.min_l bi aj) by lia.
    destruct (Z_le_gt_dec ai bj) as [Hmax | Hmax].
    + rewrite (Z.max_r ai bj) by lia.
      destruct (Z.eq_dec ai bj) as [Heq | Hneq].
      * subst bj. replace (ai - ai) with 0 by lia. rewrite Z.abs_0.
        rewrite (abs_sub_ge aj bi) by lia.
        rewrite (Z.max_r 0 (bi - ai)) by lia. lia.
      * rewrite (Z.abs_neq (ai - bj)) by lia.
        rewrite (abs_sub_ge aj bi) by lia.
        destruct (Z_le_gt_dec bj bi) as [Hover | Hover].
        -- rewrite (Z.max_r 0 (bi - bj)) by lia. lia.
        -- rewrite (Z.max_l 0 (bi - bj)) by lia. lia.
    + rewrite (Z.max_l ai bj) by lia.
      rewrite (abs_sub_ge ai bj) by lia.
      rewrite (abs_sub_ge aj bi) by lia.
      rewrite (Z.max_r 0 (bi - ai)) by lia. lia.
  - rewrite (Z.min_r bi aj) by lia.
    destruct (Z_le_gt_dec ai bj) as [Hmax | Hmax].
    + rewrite (Z.max_r ai bj) by lia.
      destruct (Z.eq_dec ai bj) as [Heq | Hneq].
      * subst bj. replace (ai - ai) with 0 by lia. rewrite Z.abs_0.
        rewrite (abs_sub_strict_lt aj bi) by lia.
        rewrite (Z.max_r 0 (aj - ai)) by lia. lia.
      * rewrite (Z.abs_neq (ai - bj)) by lia.
        rewrite (abs_sub_strict_lt aj bi) by lia.
        rewrite (Z.max_r 0 (aj - bj)) by lia. lia.
    + rewrite (Z.max_l ai bj) by lia.
      rewrite (abs_sub_ge ai bj) by lia.
      rewrite (abs_sub_strict_lt aj bi) by lia.
      destruct (Z_le_gt_dec ai aj) as [Hover | Hover].
      * rewrite (Z.max_r 0 (aj - ai)) by lia. lia.
      * rewrite (Z.max_l 0 (aj - ai)) by lia. lia.
Qed.
Lemma pair_distance_sum_swap_difference__solver_final_maximum_and_spec :
  forall a b i j,
    Zlength b = Zlength a ->
    0 <= i < Zlength a -> 0 <= j < Zlength a ->
    PairDistanceSum a b -
      PairDistanceSum a
        (replace_Znth j (Znth i b 0)
          (replace_Znth i (Znth j b 0) b)) =
    (Z.abs (Znth i a 0 - Znth i b 0) -
       Z.abs (Znth i a 0 - Znth j b 0)) +
    (Z.abs (Znth j a 0 - Znth j b 0) -
       Z.abs (Znth j a 0 - Znth i b 0)).
Proof.
  intros a b i j Hlen Hi Hj.
  destruct (Z.eq_dec i j) as [Hij | Hij].
  - subst j.
    rewrite (replace_Znth_Znth i b 0).
    rewrite (replace_Znth_Znth i b 0).
    lia.
  - unfold PairDistanceSum, Zmap_range.
    assert (Hsum :
      fold_right Z.add 0
        (map (fun k => Z.abs (Znth k a 0 - Znth k b 0))
             (Zrange 0 (Zlength a))) -
      fold_right Z.add 0
        (map (fun k => Z.abs (Znth k a 0 -
          Znth k (replace_Znth j (Znth i b 0)
            (replace_Znth i (Znth j b 0) b)) 0))
             (Zrange 0 (Zlength a))) =
      (Z.abs (Znth i a 0 - Znth i b 0) -
       Z.abs (Znth i a 0 -
         Znth i (replace_Znth j (Znth i b 0)
           (replace_Znth i (Znth j b 0) b)) 0)) +
      (Z.abs (Znth j a 0 - Znth j b 0) -
       Z.abs (Znth j a 0 -
         Znth j (replace_Znth j (Znth i b 0)
           (replace_Znth i (Znth j b 0) b)) 0))).
    { apply (fold_map_two_changes__solver_final_maximum_and_spec
        (Zrange 0 (Zlength a))
        (fun k => Z.abs (Znth k a 0 - Znth k b 0))
        (fun k => Z.abs (Znth k a 0 -
          Znth k (replace_Znth j (Znth i b 0)
            (replace_Znth i (Znth j b 0) b)) 0)) i j).
      - apply NoDup_Zrange.
      - exact Hij.
      - apply In_Zrange. exact Hi.
      - apply In_Zrange. exact Hj.
      - intros k Hk Hki Hkj.
        apply <- In_Zrange in Hk.
        rewrite (Znth_replace_Znth_Diff 0
          (replace_Znth i (Znth j b 0) b) j k (Znth i b 0)).
        2: rewrite Zlength_replace_Znth, Hlen; lia.
        2: rewrite Zlength_replace_Znth, Hlen; lia.
        2: congruence.
        rewrite (Znth_replace_Znth_Diff 0 b i k (Znth j b 0)); auto; lia. }
    assert (HiSwap :
      Znth i (replace_Znth j (Znth i b 0)
        (replace_Znth i (Znth j b 0) b)) 0 = Znth j b 0).
    { rewrite (Znth_replace_Znth_Diff 0
        (replace_Znth i (Znth j b 0) b) j i (Znth i b 0)).
      2: rewrite Zlength_replace_Znth, Hlen; lia.
      2: rewrite Zlength_replace_Znth, Hlen; lia.
      2: congruence.
      apply Znth_replace_Znth_Same. rewrite Hlen. exact Hi. }
    assert (HjSwap :
      Znth j (replace_Znth j (Znth i b 0)
        (replace_Znth i (Znth j b 0) b)) 0 = Znth i b 0).
    { apply Znth_replace_Znth_Same.
      rewrite Zlength_replace_Znth, Hlen. exact Hj. }
    rewrite HiSwap, HjSwap in Hsum.
    exact Hsum.
Qed.
Lemma nonopposite_distance_swap_nonpositive__solver_final_maximum_and_spec :
  forall ai bi aj bj,
    ~ (ai < bi /\ bj < aj) ->
    ~ (aj < bj /\ bi < ai) ->
    Z.abs (ai - bi) + Z.abs (aj - bj) -
      (Z.abs (ai - bj) + Z.abs (aj - bi)) <= 0.
Proof.
  intros ai bi aj bj Hfirst Hsecond.
  repeat match goal with
  | |- context [Z.abs (?x - ?y)] =>
      destruct (Z_le_gt_dec y x) as [?H | ?H];
      [rewrite (abs_sub_ge x y) by lia |
       rewrite (abs_sub_strict_lt x y) by lia]
  end;
  try (exfalso; apply Hfirst; split; lia);
  try (exfalso; apply Hsecond; split; lia);
  lia.
Qed.
Lemma opposite_distance_overlap_positive_identity__solver_final_maximum_and_spec :
  forall ai bi aj bj,
    ai < bi -> bj < aj -> 0 < IntervalOverlap (ai, bi) (bj, aj) ->
    Z.abs (ai - bi) + Z.abs (aj - bj) -
      (Z.abs (ai - bj) + Z.abs (aj - bi)) =
    2 * IntervalOverlap (ai, bi) (bj, aj).
Proof.
  intros ai bi aj bj Hai Haj Hpositive.
  replace (2 * IntervalOverlap (ai, bi) (bj, aj)) with
      (IntervalOverlap (ai, bi) (bj, aj) +
       IntervalOverlap (ai, bi) (bj, aj)) by ring.
  rewrite (abs_sub_strict_lt ai bi Hai).
  rewrite (abs_sub_ge aj bj) by lia.
  unfold IntervalOverlap in *. simpl in *.
  destruct (Z_le_gt_dec bi aj) as [Hmin | Hmin].
  - rewrite (Z.min_l bi aj) in * by lia.
    destruct (Z_le_gt_dec ai bj) as [Hmax | Hmax].
    + rewrite (Z.max_r ai bj) in * by lia.
      destruct (Z.eq_dec ai bj) as [Heq | Hneq].
      * subst bj. replace (ai - ai) with 0 by lia. rewrite Z.abs_0.
        rewrite (abs_sub_ge aj bi) by lia.
        rewrite (Z.max_r 0 (bi - ai)) in * by lia. lia.
      * rewrite (Z.abs_neq (ai - bj)) by lia.
        rewrite (abs_sub_ge aj bi) by lia.
        destruct (Z_le_gt_dec bj bi) as [Hover | Hover].
        -- rewrite (Z.max_r 0 (bi - bj)) in * by lia. lia.
        -- rewrite (Z.max_l 0 (bi - bj)) in * by lia. lia.
    + rewrite (Z.max_l ai bj) in * by lia.
      rewrite (abs_sub_ge ai bj) by lia.
      rewrite (abs_sub_ge aj bi) by lia.
      rewrite (Z.max_r 0 (bi - ai)) in * by lia. lia.
  - rewrite (Z.min_r bi aj) in * by lia.
    destruct (Z_le_gt_dec ai bj) as [Hmax | Hmax].
    + rewrite (Z.max_r ai bj) in * by lia.
      destruct (Z.eq_dec ai bj) as [Heq | Hneq].
      * subst bj. replace (ai - ai) with 0 by lia. rewrite Z.abs_0.
        rewrite (abs_sub_strict_lt aj bi) by lia.
        rewrite (Z.max_r 0 (aj - ai)) in * by lia. lia.
      * rewrite (Z.abs_neq (ai - bj)) by lia.
        rewrite (abs_sub_strict_lt aj bi) by lia.
        rewrite (Z.max_r 0 (aj - bj)) in * by lia. lia.
    + rewrite (Z.max_l ai bj) in * by lia.
      rewrite (abs_sub_ge ai bj) by lia.
      rewrite (abs_sub_strict_lt aj bi) by lia.
      destruct (Z_le_gt_dec ai aj) as [Hover | Hover].
      * rewrite (Z.max_r 0 (aj - ai)) in * by lia. lia.
      * rewrite (Z.max_l 0 (aj - ai)) in * by lia. lia.
Qed.
Lemma pair_distance_sum_after_swap__solver_final_maximum_and_spec :
  forall a b i j,
    Zlength b = Zlength a ->
    0 <= i < Zlength a -> 0 <= j < Zlength a ->
    Znth i a 0 < Znth i b 0 -> Znth j b 0 < Znth j a 0 ->
    0 < IntervalOverlap
      (Znth i a 0, Znth i b 0) (Znth j b 0, Znth j a 0) ->
    PairDistanceSum a
      (replace_Znth j (Znth i b 0)
        (replace_Znth i (Znth j b 0) b)) =
    PairDistanceSum a b -
      2 * IntervalOverlap
        (Znth i a 0, Znth i b 0) (Znth j b 0, Znth j a 0).
Proof.
  intros a b i j Hlen Hi Hj Hai Haj Hpositive.
  pose proof (pair_distance_sum_swap_difference__solver_final_maximum_and_spec
    a b i j Hlen Hi Hj) as Hdiff.
  pose proof (opposite_distance_overlap_positive_identity__solver_final_maximum_and_spec
    (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
    Hai Haj Hpositive) as Hlocal.
  lia.
Qed.
Lemma increasing_interval_index__solver_final_maximum_and_spec :
  forall a b n i,
    0 <= i < n -> Znth i a 0 < Znth i b 0 ->
    In (Znth i a 0, Znth i b 0) (IncreasingIntervals a b n).
Proof.
  intros a b n i Hi Hlt.
  unfold IncreasingIntervals.
  apply in_map_iff. exists i. split; [reflexivity |].
  apply filter_In. split.
  - apply In_Zrange. exact Hi.
  - apply Z.ltb_lt. exact Hlt.
Qed.
Lemma decreasing_interval_index__solver_final_maximum_and_spec :
  forall a b n i,
    0 <= i < n -> Znth i b 0 < Znth i a 0 ->
    In (Znth i b 0, Znth i a 0) (DecreasingIntervals a b n).
Proof.
  intros a b n i Hi Hlt.
  unfold DecreasingIntervals.
  apply in_map_iff. exists i. split; [reflexivity |].
  apply filter_In. split.
  - apply In_Zrange. exact Hi.
  - apply Z.ltb_lt. exact Hlt.
Qed.
Lemma swapping_overlap_bound__solver_final_maximum_and_spec :
  forall a b best value,
    SwappingOverlapMaximum a b best ->
    SwappingOverlapCandidate a b value -> value <= best.
Proof.
  intros a b best value Hmax Hvalue.
  unfold SwappingOverlapMaximum, max_value_of_subset,
    max_object_of_subset in Hmax.
  destruct Hmax as [w [[Hw Hgreatest] Heq]].
  simpl in *. subst best. apply Hgreatest. exact Hvalue.
Qed.
Lemma swapping_overlap_nonnegative__solver_final_maximum_and_spec :
  forall a b best,
    SwappingOverlapMaximum a b best -> 0 <= best.
Proof.
  intros a b best Hmax.
  eapply swapping_overlap_bound__solver_final_maximum_and_spec; eauto.
  unfold SwappingOverlapCandidate. now left.
Qed.
Lemma swap_improvement_bounded_by_best__solver_final_maximum_and_spec :
  forall a b best i j,
    Zlength b = Zlength a ->
    SwappingOverlapMaximum a b best ->
    0 <= i < Zlength a -> 0 <= j < Zlength a ->
    PairDistanceSum a b -
      PairDistanceSum a
        (replace_Znth j (Znth i b 0)
          (replace_Znth i (Znth j b 0) b)) <= 2 * best.
Proof.
  intros a b best i j Hlen Hmax Hi Hj.
  pose proof (pair_distance_sum_swap_difference__solver_final_maximum_and_spec
    a b i j Hlen Hi Hj) as Hdiff.
  pose proof (swapping_overlap_nonnegative__solver_final_maximum_and_spec
    a b best Hmax) as Hbest0.
  destruct (Z_lt_dec (Znth i a 0) (Znth i b 0)) as [Hai | Hai];
  destruct (Z_lt_dec (Znth j b 0) (Znth j a 0)) as [Hbj | Hbj].
  - pose proof (opposite_distance_overlap_identity__solver_final_maximum_and_spec
      (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
      Hai Hbj) as Hlocal.
    assert (Hcand : SwappingOverlapCandidate a b
      (IntervalOverlap
        (Znth i a 0, Znth i b 0) (Znth j b 0, Znth j a 0))).
    { unfold SwappingOverlapCandidate. right.
      exists (Znth i a 0, Znth i b 0),
             (Znth j b 0, Znth j a 0).
      repeat split; auto using increasing_interval_index__solver_final_maximum_and_spec,
        decreasing_interval_index__solver_final_maximum_and_spec. }
    pose proof (swapping_overlap_bound__solver_final_maximum_and_spec
      a b best _ Hmax Hcand) as Hbound.
    lia.
  - assert (Hnot1 : ~ (Znth i a 0 < Znth i b 0 /\
                        Znth j b 0 < Znth j a 0)) by tauto.
    assert (Hnot2 : ~ (Znth j a 0 < Znth j b 0 /\
                        Znth i b 0 < Znth i a 0)).
    { intros [? ?]. lia. }
    pose proof (nonopposite_distance_swap_nonpositive__solver_final_maximum_and_spec
      (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
      Hnot1 Hnot2) as Hlocal.
    lia.
  - assert (Hnot1 : ~ (Znth i a 0 < Znth i b 0 /\
                        Znth j b 0 < Znth j a 0)) by tauto.
    assert (Hnot2 : ~ (Znth j a 0 < Znth j b 0 /\
                        Znth i b 0 < Znth i a 0)).
    { intros [? ?]. lia. }
    pose proof (nonopposite_distance_swap_nonpositive__solver_final_maximum_and_spec
      (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
      Hnot1 Hnot2) as Hlocal.
    lia.
  - destruct (Z_lt_dec (Znth j a 0) (Znth j b 0)) as [Haj | Haj];
    destruct (Z_lt_dec (Znth i b 0) (Znth i a 0)) as [Hbi | Hbi].
    + pose proof (opposite_distance_overlap_identity__solver_final_maximum_and_spec
        (Znth j a 0) (Znth j b 0) (Znth i a 0) (Znth i b 0)
        Haj Hbi) as Hlocal.
      assert (Hcand : SwappingOverlapCandidate a b
        (IntervalOverlap
          (Znth j a 0, Znth j b 0) (Znth i b 0, Znth i a 0))).
      { unfold SwappingOverlapCandidate. right.
        exists (Znth j a 0, Znth j b 0),
               (Znth i b 0, Znth i a 0).
        repeat split; auto using increasing_interval_index__solver_final_maximum_and_spec,
          decreasing_interval_index__solver_final_maximum_and_spec. }
      pose proof (swapping_overlap_bound__solver_final_maximum_and_spec
        a b best _ Hmax Hcand) as Hbound.
      lia.
    + assert (Hnot1 : ~ (Znth i a 0 < Znth i b 0 /\
                          Znth j b 0 < Znth j a 0)) by tauto.
      assert (Hnot2 : ~ (Znth j a 0 < Znth j b 0 /\
                          Znth i b 0 < Znth i a 0)) by tauto.
      pose proof (nonopposite_distance_swap_nonpositive__solver_final_maximum_and_spec
        (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
        Hnot1 Hnot2) as Hlocal. lia.
    + assert (Hnot1 : ~ (Znth i a 0 < Znth i b 0 /\
                          Znth j b 0 < Znth j a 0)) by tauto.
      assert (Hnot2 : ~ (Znth j a 0 < Znth j b 0 /\
                          Znth i b 0 < Znth i a 0)) by tauto.
      pose proof (nonopposite_distance_swap_nonpositive__solver_final_maximum_and_spec
        (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
        Hnot1 Hnot2) as Hlocal. lia.
    + assert (Hnot1 : ~ (Znth i a 0 < Znth i b 0 /\
                          Znth j b 0 < Znth j a 0)) by tauto.
      assert (Hnot2 : ~ (Znth j a 0 < Znth j b 0 /\
                          Znth i b 0 < Znth i a 0)) by tauto.
      pose proof (nonopposite_distance_swap_nonpositive__solver_final_maximum_and_spec
        (Znth i a 0) (Znth i b 0) (Znth j a 0) (Znth j b 0)
        Hnot1 Hnot2) as Hlocal. lia.
Qed.
Lemma spec_from_swapping_overlap_maximum__solver_final_maximum_and_spec :
  forall a b base best,
    Zlength b = Zlength a ->
    base = PairDistanceSum a b ->
    SwappingOverlapMaximum a b best ->
    Spec a b (base - 2 * best).
Proof.
  intros a b base best Hlen Hbase Hmaximum.
  pose proof Hmaximum as Hmaximum_copy.
  unfold SwappingOverlapMaximum, max_value_of_subset,
    max_object_of_subset in Hmaximum.
  destruct Hmaximum as [value [[Hcandidate Hgreatest] Hvalue]].
  simpl in Hvalue. subst best.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  destruct (Z.eq_dec value 0) as [Hzero | Hnonzero].
  - subst value.
    exists b. split.
    + split.
      * unfold AtMostOneSwap. now left.
      * intros after Hswap.
        unfold AtMostOneSwap in Hswap.
        destruct Hswap as [Hsame | [i [j [Hi [Hj Hafter]]]]].
        -- subst after. lia.
        -- subst after. rewrite Hlen in Hi, Hj.
           pose proof (swap_improvement_bounded_by_best__solver_final_maximum_and_spec
             a b 0 i j Hlen Hmaximum_copy Hi Hj) as Hbound.
           lia.
    + simpl. lia.
  - unfold SwappingOverlapCandidate in Hcandidate.
    destruct Hcandidate as [Hzero | [s [t [Hs [Ht Hcandidate]]]]].
    + contradiction.
    + destruct (increasing_interval_member__solver_final_maximum_and_spec
        a b (Zlength a) s Hs) as [i [Hi [Hinc Hseq]]].
      destruct (decreasing_interval_member__solver_final_maximum_and_spec
        a b (Zlength a) t Ht) as [j [Hj [Hdec Hteq]]].
      subst s. subst t.
      assert (Hpositive : 0 < IntervalOverlap
        (Znth i a 0, Znth i b 0) (Znth j b 0, Znth j a 0)).
      { pose proof (interval_overlap_nonnegative
          (Znth i a 0, Znth i b 0) (Znth j b 0, Znth j a 0)).
        lia. }
      set (swapped := replace_Znth j (Znth i b 0)
        (replace_Znth i (Znth j b 0) b)).
      assert (Hchosen : PairDistanceSum a swapped =
        PairDistanceSum a b - 2 * value).
      { unfold swapped.
        pose proof (pair_distance_sum_after_swap__solver_final_maximum_and_spec
          a b i j Hlen Hi Hj Hinc Hdec Hpositive) as Hcost.
        lia. }
      exists swapped. split.
      * split.
        -- unfold AtMostOneSwap. right.
           exists i, j. split.
           ++ rewrite Hlen. exact Hi.
           ++ split.
              ** rewrite Hlen. exact Hj.
              ** unfold swapped. reflexivity.
        -- intros after Hswap.
           unfold AtMostOneSwap in Hswap.
           destruct Hswap as [Hsame | [p [q [Hp [Hq Hafter]]]]].
           ++ subst after.
              pose proof (swapping_overlap_nonnegative__solver_final_maximum_and_spec
                a b value Hmaximum_copy) as Hbest0.
              simpl. lia.
           ++ subst after. rewrite Hlen in Hp, Hq.
              pose proof (swap_improvement_bounded_by_best__solver_final_maximum_and_spec
                a b value p q Hlen Hmaximum_copy Hp Hq) as Hbound.
              simpl. lia.
      * change (PairDistanceSum a swapped = base - 2 * value).
        lia.
Qed.
