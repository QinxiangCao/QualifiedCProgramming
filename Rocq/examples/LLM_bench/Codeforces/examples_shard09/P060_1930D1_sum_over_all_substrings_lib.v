Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Count (x : Z) (xs : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x).

(* character codes: '0' = 48, '1' = 49 *)
Definition Mode (c : Z) (q : list Z) (l r : Z) : Prop :=
  0 <= l < r /\ r <= Zlength q /\
  Count c (sublist l r q) >= (r - l + 1) / 2.
Definition PGood (p q : list Z) : Prop :=
  Zlength q = Zlength p /\ Forall (fun c => c = 48 \/ c = 49) q /\
  forall i, 0 <= i < Zlength p -> exists l r, l <= i < r /\ Mode (Znth i p 0) q l r.
Definition FValue (p : list Z) (v : Z) : Prop :=
  min_value_of_subset Z.le (fun w => exists q, PGood p q /\ w = Count 49 q) (fun x => x) v.
Definition Pre (s : list Z) : Prop :=
  (* Stated explicitly in the P060 solver Require, so dropped here:
       1 <= Zlength s <= 100 /\
       Forall (fun c => c = 48 \/ c = 49) s  *)
  True.

Definition Spec (s : list Z) (out : Z) : Prop :=
  exists f : Z -> Z -> Z,
   (forall i j, 0 <= i < j /\ j <= Zlength s -> FValue (sublist i j s) (f i j)) /\
   out = sum_range 0 (Zlength s - 1) (fun i => sum_range (i + 1) (Zlength s) (fun j => f i j)).

(* A mathematical summary of the substring rows whose left endpoints have
   already been processed.  The witness is intentionally hidden behind this
   predicate so that the C invariant talks about completed rows, rather than
   about updates to a higher-order function. *)
Definition CompletedRows (s : list Z) (upto total : Z) : Prop :=
  exists f : Z -> Z -> Z,
    (forall i j,
       0 <= i < upto -> i < j <= Zlength s ->
       FValue (sublist i j s) (f i j)) /\
    total =
      sum_range 0 (upto - 1)
        (fun i => sum_range (i + 1) (Zlength s) (fun j => f i j)).

(* The already visited right endpoints in one fixed-left-endpoint row. *)
Definition CurrentRow
    (s : list Z) (left upto row_total : Z) : Prop :=
  exists f : Z -> Z,
    (forall right,
       left < right <= upto ->
       FValue (sublist left right s) (f right)) /\
    row_total = sum_range (left + 1) upto f.

Fixpoint ThreeSeparated (positions : list Z) : Prop :=
  match positions with
  | nil => True
  | x :: rest =>
      Forall (fun y => x + 3 <= y) rest /\ ThreeSeparated rest
  end.

Definition CoveredBy (positions : list Z) (q : Z) : Prop :=
  exists p, In p positions /\ p <= q <= p + 2.

(* [positions] is a minimum-cardinality set of binary-one positions whose
   length-three rightward intervals cover every one in the visited prefix.
   This is an implementation-independent packing/covering property; [cover]
   merely exposes the right frontier needed by the next C step. *)
Definition PrefixCoverSummary
    (s : list Z) (left upto cover count : Z) : Prop :=
  left <= upto <= Zlength s /\
  exists positions : list Z,
    Zlength positions = count /\
    Forall
      (fun p => left <= p < upto /\ Znth p s 0 = 49)
      positions /\
    ThreeSeparated positions /\
    (forall q,
       left <= q < upto -> Znth q s 0 = 49 -> CoveredBy positions q) /\
    ((positions = nil /\ cover = left - 1) \/
     exists prefix last,
       positions = prefix ++ last :: nil /\ cover = last + 2) /\
    (left < upto -> FValue (sublist left upto s) count).

Require Import Coq.micromega.Lia.

Lemma ThreeSeparated_app_last :
  forall positions last,
    ThreeSeparated positions ->
    Forall (fun p => p + 3 <= last) positions ->
    ThreeSeparated (positions ++ last :: nil).
Proof.
  induction positions as [|p positions IH]; intros last Hsep Hbefore.
  - simpl. auto.
  - simpl in Hsep, Hbefore |- *.
    destruct Hsep as [Hpairwise Htail].
    inversion Hbefore as [|? ? Hp Hbefore_tail]; subst.
    split.
    + apply Forall_app. split; [exact Hpairwise |].
      constructor; [exact Hp | constructor].
    + apply IH; assumption.
Qed.

Lemma ThreeSeparated_last_dominates :
  forall positions prefix last,
    ThreeSeparated positions ->
    positions = prefix ++ last :: nil ->
    forall p, In p positions -> p = last \/ p + 3 <= last.
Proof.
  induction positions as [|x positions IH]; intros prefix last Hsep Heq p Hin.
  - destruct prefix; discriminate.
  - simpl in Hsep. destruct Hsep as [Hall Htail].
    destruct Hin as [-> | Hin].
    + destruct prefix as [|y prefix].
      * simpl in Heq. inversion Heq. auto.
      * simpl in Heq. inversion Heq; subst.
        right. apply Forall_forall with (x := last) in Hall.
        -- exact Hall.
        -- apply in_or_app. right. simpl. auto.
    + destruct prefix as [|y prefix].
      * simpl in Heq. inversion Heq; subst. contradiction.
      * simpl in Heq. inversion Heq; subst.
        eapply IH; eauto.
Qed.

Lemma CurrentRow_extend :
  forall s left upto row_total value,
    left <= upto ->
    CurrentRow s left upto row_total ->
    FValue (sublist left (upto + 1) s) value ->
    CurrentRow s left (upto + 1) (row_total + value).
Proof.
  intros s left upto row_total value Hbounds Hrow Hvalue.
  unfold CurrentRow in *.
  destruct Hrow as [f [Hf Hsum]].
  exists (fun right => if Z.eq_dec right (upto + 1) then value else f right).
  split.
  - intros right Hright.
    destruct (Z.eq_dec right (upto + 1)) as [-> | Hneq].
    + exact Hvalue.
    + simpl. destruct (Z.eq_dec right (upto + 1)); [contradiction |].
      apply Hf. lia.
  - unfold sum_range in *.
    rewrite (sum_Z_range_extend_right (left + 1) (upto + 1)) by lia.
    assert (Hold :
      sum (fun x : Z => left + 1 <= x < upto + 1)
        (fun right => if Z.eq_dec right (upto + 1) then value else f right) =
      sum (fun x : Z => left + 1 <= x < upto + 1) f).
    { apply sum_Z_range_ext. intros x Hx.
      destruct (Z.eq_dec x (upto + 1)); [lia | reflexivity]. }
    rewrite Hold.
    rewrite <- Hsum.
    destruct (Z.eq_dec (upto + 1) (upto + 1)); [ring | contradiction].
Qed.

Lemma PrefixCoverSummary_extend_uncovered_one :
  forall s left upto cover count,
    PrefixCoverSummary s left upto cover count ->
    upto < Zlength s ->
    Znth upto s 0 = 49 ->
    cover < upto ->
    FValue (sublist left (upto + 1) s) (count + 1) ->
    PrefixCoverSummary s left (upto + 1) (upto + 2) (count + 1).
Proof.
  intros s left upto cover count Hsummary Hlen Hbit Huncovered Hvalue.
  unfold PrefixCoverSummary in *.
  destruct Hsummary as [Hrange [positions
    [Hcount [Hvalid [Hsep [Hcovered [Hfrontier HFvalue]]]]]]].
  split; [lia |].
  exists (positions ++ upto :: nil).
  repeat split.
  - rewrite Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - apply Forall_app. split.
    + eapply Forall_impl; [| exact Hvalid].
      intros p Hp. destruct Hp as [Hp Hpone]. split; [lia | exact Hpone].
    + constructor; [split; lia | constructor].
  - apply ThreeSeparated_app_last; [exact Hsep |].
    apply Forall_forall. intros p Hp.
    destruct Hfrontier as [[Hnil Hcover] | [prefix [last [Hpositions Hcover]]]].
    + subst positions. contradiction.
    + pose proof
        (ThreeSeparated_last_dominates positions prefix last Hsep Hpositions p Hp)
        as [-> | Hp_last].
      * lia.
      * lia.
  - intros q Hq Hqbit.
    destruct (Z_lt_ge_dec q upto) as [Hqold | Hqnew].
    + unfold CoveredBy. destruct (Hcovered q ltac:(lia) Hqbit) as [p [Hp Hpq]].
      exists p. split; [apply in_or_app; left; exact Hp | exact Hpq].
    + assert (q = upto) by lia. subst q.
      unfold CoveredBy. exists upto. split.
      * apply in_or_app. right. simpl. auto.
      * lia.
  - right. exists positions, upto. split; [reflexivity | lia].
  - intros _. exact Hvalue.
Qed.

Lemma PrefixCoverSummary_extend_no_new_cover :
  forall s left upto cover count,
    PrefixCoverSummary s left upto cover count ->
    upto < Zlength s ->
    (Znth upto s 0 <> 49 \/ upto <= cover) ->
    FValue (sublist left (upto + 1) s) count ->
    PrefixCoverSummary s left (upto + 1) cover count.
Proof.
  intros s left upto cover count Hsummary Hlen Hno_new Hvalue.
  unfold PrefixCoverSummary in *.
  destruct Hsummary as [Hrange [positions
    [Hcount [Hvalid [Hsep [Hcovered [Hfrontier HFvalue]]]]]]].
  split; [lia |].
  exists positions.
  repeat split; try assumption.
  - eapply Forall_impl; [| exact Hvalid].
    intros p Hp. destruct Hp as [Hp Hbit]. split; [lia | exact Hbit].
  - intros q Hq Hqbit.
    destruct (Z_lt_ge_dec q upto) as [Hqold | Hqnew].
    + apply Hcovered; [lia | exact Hqbit].
    + assert (q = upto) by lia. subst q.
      destruct Hno_new as [Hnot_one | Hwithin].
      * contradiction.
      * destruct Hfrontier as [[Hnil Hcover] |
          [prefix [last [Hpositions Hcover]]]].
        -- subst positions. lia.
        -- unfold CoveredBy. exists last. split.
           ++ rewrite Hpositions. apply in_or_app. right. simpl. auto.
           ++ assert (Hlast_valid : left <= last < upto /\ Znth last s 0 = 49).
              { apply Forall_forall with (x := last) in Hvalid.
                - exact Hvalid.
                - rewrite Hpositions. apply in_or_app. right. simpl. auto. }
              destruct Hlast_valid. lia.
  - intros _. exact Hvalue.
Qed.

(* A proof-oriented interface for the two mathematical directions hidden by
   [min_value_of_subset]: one feasible output with the advertised number of
   ones, and a matching lower bound for every feasible output. *)
Definition ExactPGoodCount (p : list Z) (v : Z) : Prop :=
  exists q,
    PGood p q /\
    Count 49 q = v /\
    forall q', PGood p q' -> v <= Count 49 q'.

Lemma ExactPGoodCount_FValue :
  forall p v, ExactPGoodCount p v -> FValue p v.
Proof.
  intros p v [q [Hgood [Hcount Hlower]]].
  unfold FValue, min_value_of_subset, min_object_of_subset.
  exists v. split.
  - split.
    + exists q. split; [exact Hgood | lia].
    + intros w [q' [Hgood' Hw]]. subst w.
      apply Hlower. exact Hgood'.
  - reflexivity.
Qed.

Definition MajorityOneAt (q : list Z) (i : Z) : Prop :=
  exists l r, l <= i < r /\ Mode 49 q l r.

Lemma PGood_selected_ones_have_majority_intervals :
  forall p q positions,
    PGood p q ->
    Forall
      (fun i => 0 <= i < Zlength p /\ Znth i p 0 = 49)
      positions ->
    Forall (MajorityOneAt q) positions.
Proof.
  intros p q positions Hgood Hpositions.
  destruct Hgood as [_ [_ Hall]].
  apply Forall_forall. intros i Hi.
  apply Forall_forall with (x := i) in Hpositions; [| exact Hi].
  destruct Hpositions as [Hirange Hibit].
  destruct (Hall i Hirange) as [l [r [Hcontains Hmode]]].
  unfold MajorityOneAt. exists l, r.
  rewrite Hibit in Hmode. auto.
Qed.

Lemma Count_nonnegative :
  forall x xs, 0 <= Count x xs.
Proof.
  intros x xs. unfold Count, set_card.
  apply sum_nonneg. intros i _. lia.
Qed.

Lemma set_card_singleton_value {A : Type} :
  forall (P : A -> Prop) (finiteP : Finite P) (a : A),
    (forall x, P x <-> x = a) ->
    @set_card A P finiteP = 1.
Proof.
  intros P [items Hitems Hnodup] a Hone.
  unfold set_card, sum. simpl.
  assert (Ha : In a items).
  { apply (proj1 (Hitems a)). apply (proj2 (Hone a)). reflexivity. }
  destruct items as [|x items]; [contradiction |].
  assert (Hx : x = a).
  { apply (proj1 (Hone x)). apply (proj2 (Hitems x)). simpl; auto. }
  subst x.
  assert (Htail : items = nil).
  { destruct items as [|y items]; [reflexivity |].
    exfalso. inversion Hnodup as [|? ? Hnotin _]; subst.
    apply Hnotin. left.
    apply (proj1 (Hone y)). apply (proj2 (Hitems y)). simpl; auto. }
  subst items. reflexivity.
Qed.

Lemma set_card_empty_value {A : Type} :
  forall (P : A -> Prop) (finiteP : Finite P),
    (forall x, ~ P x) ->
    @set_card A P finiteP = 0.
Proof.
  intros P [items Hitems Hnodup] Hnone.
  unfold set_card, sum. simpl.
  destruct items as [|x items]; [reflexivity |].
  exfalso. apply (Hnone x).
  apply (proj2 (Hitems x)). simpl; auto.
Qed.

Lemma Count_single_same :
  forall x, Count x (x :: nil) = 1.
Proof.
  intros x. unfold Count.
  apply set_card_singleton_value with (a := 0).
  intros i. split.
  - intros [Hi _]. change (0 <= i < 1) in Hi. lia.
  - intros ->. split.
    + change (0 <= 0 < 1). lia.
    + simpl. reflexivity.
Qed.

Lemma Count_single_different :
  forall x y, x <> y -> Count x (y :: nil) = 0.
Proof.
  intros x y Hxy. unfold Count.
  apply set_card_empty_value. intros i [Hi Heq].
  change (0 <= i < 1) in Hi.
  assert (i = 0) by lia. subst i.
  simpl in Heq. apply Hxy. symmetry. exact Heq.
Qed.

Lemma ExactPGoodCount_single_zero :
  ExactPGoodCount (48 :: nil) 0.
Proof.
  unfold ExactPGoodCount.
  exists (48 :: nil).
  split.
  - unfold PGood. split; [reflexivity |].
    split.
    + constructor; [left; reflexivity | constructor].
    + intros i Hi. change (0 <= i < 1) in Hi.
      assert (i = 0) by lia. subst i.
      exists 0, 1. split; [lia |].
      unfold Mode. split; [lia |]. split.
      * change (1 <= 1). lia.
      *
      replace (Znth 0 (48 :: nil) 0) with 48 by reflexivity.
      replace (sublist 0 1 (48 :: nil)) with (48 :: nil).
      2: { symmetry. apply sublist_self. reflexivity. }
      replace ((1 - 0 + 1) / 2) with 1 by reflexivity.
      rewrite Count_single_same. lia.
  - split.
    + rewrite Count_single_different by lia. reflexivity.
    + intros q Hgood. apply Count_nonnegative.
Qed.

Lemma ExactPGoodCount_single_one :
  ExactPGoodCount (49 :: nil) 1.
Proof.
  unfold ExactPGoodCount.
  exists (49 :: nil).
  split.
  - unfold PGood. split; [reflexivity |].
    split.
    + constructor; [right; reflexivity | constructor].
    + intros i Hi. change (0 <= i < 1) in Hi.
      assert (i = 0) by lia. subst i.
      exists 0, 1. split; [lia |].
      unfold Mode. split; [lia |]. split.
      * change (1 <= 1). lia.
      *
      replace (Znth 0 (49 :: nil) 0) with 49 by reflexivity.
      replace (sublist 0 1 (49 :: nil)) with (49 :: nil).
      2: { symmetry. apply sublist_self. reflexivity. }
      replace ((1 - 0 + 1) / 2) with 1 by reflexivity.
      rewrite Count_single_same. lia.
  - split.
    + rewrite Count_single_same. reflexivity.
    + intros q Hgood.
    destruct Hgood as [Hlen [_ Hall]].
    specialize (Hall 0 ltac:(change (0 <= 0 < 1); lia)).
    destruct Hall as [l [r [Hcontains Hmode]]].
    unfold Mode in Hmode.
    destruct Hmode as [Hlr [Hr Hcount]].
    change (Zlength q = 1) in Hlen.
    assert (l = 0 /\ r = 1) by lia.
    destruct H as [-> ->].
    rewrite sublist_self in Hcount by lia.
    replace (Znth 0 (49 :: nil) 0) with 49 in Hcount by reflexivity.
    replace ((1 - 0 + 1) / 2) with 1 in Hcount by reflexivity.
    apply Z.ge_le. exact Hcount.
Qed.

(* The packing argument starts by turning the spacing condition into genuine
   distinctness.  This is deliberately separate from any cardinality
   arithmetic, so later interval assignments can use ordinary [NoDup]. *)
Lemma ThreeSeparated_NoDup :
  forall positions, ThreeSeparated positions -> NoDup positions.
Proof.
  induction positions as [| x positions IH]; intros Hseparated.
  - constructor.
  - simpl in Hseparated.
    destruct Hseparated as [Hlater Htail].
    constructor.
    + intros Hin.
      apply Forall_forall with (x := x) in Hlater; [lia | exact Hin].
    + apply IH. exact Htail.
Qed.

Lemma Mode_one_count_positive :
  forall q l r, Mode 49 q l r -> 0 < Count 49 (sublist l r q).
Proof.
  intros q l r Hmode.
  unfold Mode in Hmode.
  destruct Hmode as [Hlr [Hr Hcount]].
  apply Z.ge_le in Hcount.
  assert (Hhalf : 1 <= (r - l + 1) / 2).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

Lemma set_card_positive_witness {A : Type} :
  forall (P : A -> Prop) (finiteP : Finite P),
    0 < @set_card A P finiteP -> exists x, P x.
Proof.
  intros P [items Hitems Hnodup] Hpositive.
  destruct items as [| x items].
  - unfold set_card, sum in Hpositive. simpl in Hpositive. lia.
  - exists x. apply (proj2 (Hitems x)). simpl. auto.
Qed.

Lemma Count_positive_witness :
  forall x xs,
    0 < Count x xs ->
    exists i, 0 <= i < Zlength xs /\ Znth i xs 0 = x.
Proof.
  intros x xs Hpositive.
  unfold Count in Hpositive.
  apply set_card_positive_witness in Hpositive.
  exact Hpositive.
Qed.

(* Every abstract majority witness contains a concrete one of [q].  The
   position is returned in global coordinates; this is the resource that a
   future injective interval assignment must allocate. *)
Lemma MajorityOneAt_contains_one :
  forall q i,
    MajorityOneAt q i ->
    exists l r j,
      l <= i < r /\
      0 <= l < r /\ r <= Zlength q /\
      l <= j < r /\ Znth j q 0 = 49.
Proof.
  intros q i [l [r [Hcontains Hmode]]].
  assert (Hpositive : 0 < Count 49 (sublist l r q)).
  { apply Mode_one_count_positive. exact Hmode. }
  destruct (Count_positive_witness 49 (sublist l r q) Hpositive)
    as [offset [Hoffset Hvalue]].
  unfold Mode in Hmode.
  destruct Hmode as [Hlr [Hr Hcount]].
  rewrite Zlength_sublist in Hoffset by lia.
  exists l, r, (l + offset).
  repeat split; try lia.
  rewrite Znth_sublist in Hvalue by lia.
  rewrite Z.add_comm.
  exact Hvalue.
Qed.

(* An ordered family keeps each selected centre aligned with its independently
   chosen majority interval.  Unlike the failed endpoint-deletion argument,
   the matching below allocates all interval resources simultaneously. *)
Definition MajorityIntervalWitness
    (q : list Z) (centre : Z) (bounds : Z * Z) : Prop :=
  let '(l, r) := bounds in l <= centre < r /\ Mode 49 q l r.

Definition MajorityIntervalFamily
    (q : list Z) (positions : list Z) (intervals : list (Z * Z)) : Prop :=
  Forall2 (MajorityIntervalWitness q) positions intervals.

Lemma MajorityIntervalFamily_exists :
  forall q positions,
    Forall (MajorityOneAt q) positions ->
    exists intervals, MajorityIntervalFamily q positions intervals.
Proof.
  intros q positions Hmajority.
  induction Hmajority as [| centre positions Hcentre Htail
                              [intervals Hintervals]].
  - exists nil. constructor.
  - destruct Hcentre as [l [r [Hcontains Hmode]]].
    exists ((l, r) :: intervals).
    constructor.
    + unfold MajorityIntervalWitness. simpl. auto.
    + exact Hintervals.
Qed.

Lemma MajorityIntervalFamily_same_length :
  forall q positions intervals,
    MajorityIntervalFamily q positions intervals ->
    Zlength positions = Zlength intervals.
Proof.
  intros q positions intervals Hfamily.
  unfold MajorityIntervalFamily in Hfamily.
  apply Forall2_length in Hfamily.
  rewrite !Zlength_correct, Hfamily. reflexivity.
Qed.

Definition IntervalOne
    (q : list Z) (bounds : Z * Z) (assigned : Z) : Prop :=
  let '(l, r) := bounds in
    0 <= l < r /\ r <= Zlength q /\
    l <= assigned < r /\ Znth assigned q 0 = 49.

Definition IntervalMatching
    (q : list Z) (intervals : list (Z * Z)) (assigned : list Z) : Prop :=
  Zlength assigned = Zlength intervals /\
  NoDup assigned /\
  Forall2 (IntervalOne q) intervals assigned.

Lemma set_card_as_Zlength_enum :
  forall {A : Type} (P : A -> Prop) (finiteP : Finite P),
    @set_card A P finiteP = Zlength (@enum A P finiteP).
Proof.
  intros A P finiteP.
  unfold set_card, SumLib.Sum.sum.
  induction (@enum A P finiteP) as [| x xs IH].
  - reflexivity.
  - cbn [fold_right]. rewrite Zlength_cons, IH. lia.
Qed.

Lemma NoDup_Forall_set_card_lower_bound {A : Type} :
  forall (P : A -> Prop) (finiteP : Finite P) xs,
    NoDup xs ->
    Forall P xs ->
    Zlength xs <= @set_card A P finiteP.
Proof.
  intros P finiteP xs Hnodup Hforall.
  rewrite set_card_as_Zlength_enum.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_le.
  eapply NoDup_incl_length.
  - exact Hnodup.
  - intros x Hin.
    apply (proj1 (@enum_ok A P finiteP x)).
    apply Forall_forall with (x := x) in Hforall; assumption.
Qed.

Lemma IntervalMatching_values :
  forall q intervals assigned,
    Forall2 (IntervalOne q) intervals assigned ->
    Forall
      (fun j => 0 <= j < Zlength q /\ Znth j q 0 = 49)
      assigned.
Proof.
  intros q intervals assigned Hmatching.
  induction Hmatching as [| [l r] j intervals assigned Hone Htail IH].
  - constructor.
  - constructor.
    + unfold IntervalOne in Hone. simpl in Hone.
      destruct Hone as [Hlr [Hr [Hj Hvalue]]]. split; [lia | exact Hvalue].
    + exact IH.
Qed.

Lemma IntervalMatching_Count_bound :
  forall q intervals assigned,
    IntervalMatching q intervals assigned ->
    Zlength intervals <= Count 49 q.
Proof.
  intros q intervals assigned Hmatching.
  unfold IntervalMatching in Hmatching.
  destruct Hmatching as [Hlength [Hnodup Haligned]].
  rewrite <- Hlength.
  unfold Count.
  apply NoDup_Forall_set_card_lower_bound.
  - exact Hnodup.
  - apply IntervalMatching_values with (intervals := intervals).
    exact Haligned.
Qed.

Lemma MajorityIntervalFamily_matching_implies_packing :
  forall q positions intervals assigned,
    MajorityIntervalFamily q positions intervals ->
    IntervalMatching q intervals assigned ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions intervals assigned Hfamily Hmatching.
  rewrite (MajorityIntervalFamily_same_length q positions intervals Hfamily).
  apply IntervalMatching_Count_bound with (assigned := assigned).
  exact Hmatching.
Qed.

(* The geometric half of the component argument is independent of [q]: a
   three-separated list contained in a half-open span uses at most one centre
   per three positions, with the two endpoint positions accounting for the
   usual ceiling. *)
Lemma ThreeSeparated_span_bound :
  forall positions left right,
    left <= right ->
    ThreeSeparated positions ->
    Forall (fun centre => left <= centre < right) positions ->
    3 * Zlength positions <= right - left + 2.
Proof.
  induction positions as [| centre positions IH];
    intros left right Hspan Hseparated Hinside.
  - rewrite Zlength_nil. lia.
  - destruct positions as [| next positions].
    + rewrite Zlength_cons, Zlength_nil.
      inversion Hinside as [| ? ? Hcentre _]; subst. lia.
    + simpl in Hseparated.
      destruct Hseparated as [Hlater Htail].
      inversion Hinside as [| ? ? Hcentre Hinsidetail]; subst.
      assert (Hnext : centre + 3 <= next).
      { apply Forall_forall with (x := next) in Hlater; [exact Hlater |].
        simpl. auto. }
      assert (Hnextright : next < right).
      { inversion Hinsidetail as [| ? ? Hnextinside _]; subst.
        exact (proj2 Hnextinside). }
      assert (Hnewinside :
        Forall (fun x => centre + 3 <= x < right) (next :: positions)).
      { apply Forall_forall. intros x Hin.
        split.
        - apply Forall_forall with (x := x) in Hlater; [exact Hlater | exact Hin].
        - apply Forall_forall with (x := x) in Hinsidetail;
            [exact (proj2 Hinsidetail) | exact Hin]. }
      specialize (IH (centre + 3) right ltac:(lia) Htail Hnewinside).
      rewrite !Zlength_cons in *. lia.
Qed.

Lemma component_span_density_implies_cardinality :
  forall centres span ones,
    0 <= centres ->
    3 * centres <= span + 2 ->
    span <= 3 * ones ->
    centres <= ones.
Proof.
  intros centres span ones Hcentres Hpacking Hdensity. lia.
Qed.

(* Counting algebra for overlap components.  Exposing [Count] as an indicator
   sum makes disjoint-span additivity and density estimates explicit. *)
Lemma set_card_Z_as_indicator_sum :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  { induction zs as [| z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH. }
  apply Hfilter.
Qed.

Lemma Count_as_indicator_sum :
  forall x xs,
    Count x xs =
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength xs)
      (fun i => if Z.eq_dec (Znth i xs 0) x then 1 else 0).
Proof.
  intros x xs.
  unfold Count.
  rewrite set_card_Z_as_indicator_sum.
  apply SumLib.Sum.sum_ext.
  intros i Hi.
  destruct (prop_dec (Znth i xs 0 = x));
    destruct (Z.eq_dec (Znth i xs 0) x); try contradiction; reflexivity.
Qed.

Lemma Count_le_Zlength :
  forall x xs, Count x xs <= Zlength xs.
Proof.
  intros x xs.
  rewrite Count_as_indicator_sum.
  eapply Z.le_trans.
  - apply SumLib.ZRange.sum_Z_range_upper_bound with (b := 1).
    + pose proof (Zlength_nonneg xs). lia.
    + intros i Hi. destruct (Z.eq_dec (Znth i xs 0) x); lia.
  - lia.
Qed.

Lemma Count_sublist_as_range_sum :
  forall x q left right,
    0 <= left <= right ->
    right <= Zlength q ->
    Count x (sublist left right q) =
    SumLib.Sum.sum (fun i : Z => left <= i < right)
      (fun i => if Z.eq_dec (Znth i q 0) x then 1 else 0).
Proof.
  intros x q left right Hleft Hright.
  rewrite Count_as_indicator_sum.
  rewrite Zlength_sublist by lia.
  transitivity
    (SumLib.Sum.sum (fun i : Z => 0 <= i < right - left)
      (fun i => if Z.eq_dec (Znth (i + left) q 0) x then 1 else 0)).
  - apply SumLib.ZRange.sum_Z_range_ext. intros i Hi.
    rewrite Znth_sublist by lia.
    reflexivity.
  - pose proof
      (SumLib.ZRange.sum_Z_range_shift 0 (right - left) left
        (fun i => if Z.eq_dec (Znth i q 0) x then 1 else 0)) as Hshift.
    replace (0 + left) with left in Hshift by lia.
    replace (right - left + left) with right in Hshift by lia.
    symmetry. exact Hshift.
Qed.

Lemma Count_sublist_split :
  forall x q left mid right,
    0 <= left <= mid /\ mid <= right ->
    right <= Zlength q ->
    Count x (sublist left right q) =
      Count x (sublist left mid q) + Count x (sublist mid right q).
Proof.
  intros x q left mid right Horder Hright.
  rewrite !Count_sublist_as_range_sum by lia.
  apply SumLib.ZRange.sum_Z_range_split. lia.
Qed.

Lemma Mode_span_le_twice_Count :
  forall q left right,
    Mode 49 q left right ->
    right - left <= 2 * Count 49 (sublist left right q).
Proof.
  intros q left right Hmode.
  unfold Mode in Hmode.
  destruct Hmode as [Hlr [Hr Hcount]].
  apply Z.ge_le in Hcount.
  pose proof (Z.div_mod (right - left + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (right - left + 1) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

(* The first component merge: two ordered overlapping majority intervals need
   not have a majority union, but their union is always one-third dense. *)
Lemma two_overlapping_modes_union_density :
  forall q left1 left2 right1 right2,
    0 <= left1 <= left2 /\ left2 < right1 <= right2 ->
    right2 <= Zlength q ->
    Mode 49 q left1 right1 ->
    Mode 49 q left2 right2 ->
    right2 - left1 <= 3 * Count 49 (sublist left1 right2 q).
Proof.
  intros q left1 left2 right1 right2 Horder Hright Hmode1 Hmode2.
  pose proof (Mode_span_le_twice_Count q left1 right1 Hmode1) as Hspan1.
  pose proof (Mode_span_le_twice_Count q left2 right2 Hmode2) as Hspan2.
  pose proof
    (Count_sublist_split 49 q left1 left2 right1 ltac:(lia) ltac:(lia))
    as Hsplit1.
  pose proof
    (Count_sublist_split 49 q left2 right1 right2 ltac:(lia) ltac:(lia))
    as Hsplit2.
  pose proof
    (Count_sublist_split 49 q left1 left2 right2 ltac:(lia) ltac:(lia))
    as Hsplit_union.
  pose proof (Count_le_Zlength 49 (sublist left2 right1 q)) as Hoverlap.
  pose proof (Count_nonnegative 49 (sublist left1 left2 q)) as Hleft_count.
  pose proof (Count_nonnegative 49 (sublist right1 right2 q)) as Hright_count.
  rewrite Zlength_sublist in Hoverlap by lia.
  rewrite Hsplit1 in Hspan1.
  rewrite Hsplit2 in Hspan2.
  rewrite Hsplit2 in Hsplit_union.
  lia.
Qed.

Lemma Count_sublist_le_Count :
  forall x q left right,
    0 <= left <= right ->
    right <= Zlength q ->
    Count x (sublist left right q) <= Count x q.
Proof.
  intros x q left right Hleft Hright.
  pose proof
    (Count_sublist_split x q 0 left (Zlength q) ltac:(lia) ltac:(lia))
    as Hprefix.
  pose proof
    (Count_sublist_split x q left right (Zlength q) ltac:(lia) ltac:(lia))
    as Hsuffix.
  pose proof (Count_nonnegative x (sublist 0 left q)) as Hnonneg_prefix.
  pose proof
    (Count_nonnegative x (sublist right (Zlength q) q)) as Hnonneg_suffix.
  rewrite sublist_self in Hprefix by reflexivity.
  lia.
Qed.

Lemma two_overlapping_modes_centres_bound :
  forall q positions left1 left2 right1 right2,
    0 <= left1 <= left2 /\ left2 < right1 <= right2 ->
    right2 <= Zlength q ->
    Mode 49 q left1 right1 ->
    Mode 49 q left2 right2 ->
    ThreeSeparated positions ->
    Forall (fun centre => left1 <= centre < right2) positions ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions left1 left2 right1 right2 Horder Hright
    Hmode1 Hmode2 Hseparated Hinside.
  pose proof
    (ThreeSeparated_span_bound positions left1 right2 ltac:(lia)
      Hseparated Hinside) as Hpacking.
  pose proof
    (two_overlapping_modes_union_density q left1 left2 right1 right2
      Horder Hright Hmode1 Hmode2) as Hdensity.
  pose proof (Zlength_nonneg positions) as Hlength.
  pose proof (Count_nonnegative 49 (sublist left1 right2 q)) as Hcount.
  assert (Hcomponent :
    Zlength positions <= Count 49 (sublist left1 right2 q)).
  { eapply component_span_density_implies_cardinality; eauto. }
  pose proof (Count_sublist_le_Count 49 q left1 right2 ltac:(lia) Hright)
    as Hglobal.
  lia.
Qed.

(* [3 * ones - length] is the density slack of a component.  To make right
   extension inductive, it must dominate the ordinary one-minus-zero balance
   of every suffix ending at the current right frontier. *)
Definition RightDensitySlack (q : list Z) (left right : Z) : Prop :=
  0 <= left < right /\ right <= Zlength q /\
  0 <= 3 * Count 49 (sublist left right q) - (right - left) /\
  forall start,
    left <= start <= right ->
    2 * Count 49 (sublist start right q) - (right - start) <=
      3 * Count 49 (sublist left right q) - (right - left).

Lemma Mode_RightDensitySlack :
  forall q left right,
    Mode 49 q left right ->
    RightDensitySlack q left right.
Proof.
  intros q left right Hmode.
  unfold RightDensitySlack.
  unfold Mode in Hmode.
  destruct Hmode as [Hlr [Hright Hmajority]].
  assert (Hmode_again : Mode 49 q left right).
  { unfold Mode. auto. }
  pose proof (Mode_span_le_twice_Count q left right Hmode_again) as Hspan.
  pose proof (Count_nonnegative 49 (sublist left right q)) as Htotal_nonneg.
  repeat split; try assumption; try lia.
  intros start Hstart.
  pose proof
    (Count_sublist_split 49 q left start right ltac:(lia) ltac:(lia))
    as Hsplit.
  pose proof (Count_nonnegative 49 (sublist left start q)) as Hprefix_nonneg.
  pose proof (Count_le_Zlength 49 (sublist start right q)) as Hsuffix_len.
  rewrite Zlength_sublist in Hsuffix_len by lia.
  lia.
Qed.

Lemma RightDensitySlack_extend_right :
  forall q component_left component_right interval_left interval_right,
    RightDensitySlack q component_left component_right ->
    component_left <= interval_left < component_right /\
      component_right < interval_right ->
    Mode 49 q interval_left interval_right ->
    RightDensitySlack q component_left interval_right.
Proof.
  intros q component_left component_right interval_left interval_right
    Hcomponent Hextends Hmode.
  unfold RightDensitySlack in Hcomponent |- *.
  destruct Hcomponent as [Hcomponent_bounds
    [Hcomponent_right [Hslack Hsuffixes]]].
  unfold Mode in Hmode.
  destruct Hmode as [Hinterval_bounds [Hinterval_right Hmajority]].
  assert (Hmode_again : Mode 49 q interval_left interval_right).
  { unfold Mode. auto. }
  pose proof
    (Mode_span_le_twice_Count q interval_left interval_right Hmode_again)
    as Hmode_span.
  pose proof
    (Count_sublist_split 49 q component_left component_right interval_right
      ltac:(lia) ltac:(lia)) as Htotal_split.
  pose proof
    (Count_sublist_split 49 q interval_left component_right interval_right
      ltac:(lia) ltac:(lia)) as Hinterval_split.
  pose proof
    (Hsuffixes interval_left ltac:(lia)) as Hoverlap_balance.
  pose proof
    (Count_nonnegative 49 (sublist component_right interval_right q))
    as Htail_nonneg.
  assert (Hnew_slack :
    0 <= 3 * Count 49 (sublist component_left interval_right q) -
      (interval_right - component_left)).
  { lia. }
  split; [lia |].
  split; [exact Hinterval_right |].
  split; [exact Hnew_slack |].
  intros start Hstart.
    destruct (Z_lt_ge_dec start component_right) as [Hbefore | Hafter].
  - pose proof (Hsuffixes start ltac:(lia)) as Hold_suffix.
    pose proof
      (Count_sublist_split 49 q start component_right interval_right
        ltac:(lia) ltac:(lia)) as Hsuffix_split.
    lia.
  - pose proof
      (Count_sublist_split 49 q component_right start interval_right
        ltac:(lia) ltac:(lia)) as Htail_split.
    pose proof (Count_nonnegative 49 (sublist component_right start q))
      as Htail_prefix_nonneg.
    pose proof (Count_le_Zlength 49 (sublist start interval_right q))
      as Hsuffix_len.
    rewrite Zlength_sublist in Hsuffix_len by lia.
    lia.
Qed.

Inductive RightOverlapChain (q : list Z) :
    Z -> Z -> list (Z * Z) -> Prop :=
| right_overlap_chain_single :
    forall left right,
      Mode 49 q left right ->
      RightOverlapChain q left right ((left, right) :: nil)
| right_overlap_chain_extend :
    forall component_left component_right intervals interval_left interval_right,
      RightOverlapChain q component_left component_right intervals ->
      component_left <= interval_left < component_right /\
        component_right < interval_right ->
      Mode 49 q interval_left interval_right ->
      RightOverlapChain q component_left interval_right
        (intervals ++ (interval_left, interval_right) :: nil).

Lemma RightOverlapChain_slack :
  forall q left right intervals,
    RightOverlapChain q left right intervals ->
    RightDensitySlack q left right.
Proof.
  intros q left right intervals Hchain.
  induction Hchain.
  - apply Mode_RightDensitySlack. exact H.
  - eapply RightDensitySlack_extend_right; eauto.
Qed.

Lemma RightOverlapChain_density :
  forall q left right intervals,
    RightOverlapChain q left right intervals ->
    right - left <= 3 * Count 49 (sublist left right q).
Proof.
  intros q left right intervals Hchain.
  pose proof (RightOverlapChain_slack q left right intervals Hchain)
    as Hcomponent.
  unfold RightDensitySlack in Hcomponent. lia.
Qed.

Lemma RightOverlapChain_centres_bound :
  forall q positions left right intervals,
    RightOverlapChain q left right intervals ->
    ThreeSeparated positions ->
    Forall (fun centre => left <= centre < right) positions ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions left right intervals Hchain Hseparated Hinside.
  pose proof (RightOverlapChain_slack q left right intervals Hchain)
    as Hcomponent.
  pose proof (RightOverlapChain_density q left right intervals Hchain)
    as Hdensity.
  unfold RightDensitySlack in Hcomponent.
  destruct Hcomponent as [Hbounds [Hright [Hslack Hsuffix]]].
  pose proof
    (ThreeSeparated_span_bound positions left right ltac:(lia)
      Hseparated Hinside) as Hpacking.
  pose proof (Zlength_nonneg positions) as Hlength.
  pose proof (Count_nonnegative 49 (sublist left right q)) as Hcount.
  assert (Hlocal : Zlength positions <= Count 49 (sublist left right q)).
  { eapply component_span_density_implies_cardinality; eauto. }
  pose proof (Count_sublist_le_Count 49 q left right ltac:(lia) Hright)
    as Hglobal.
  lia.
Qed.

(* A normalized overlap component must also retain majority witnesses which
   are contained in the span already reached.  Such a witness contributes a
   centre, but it neither changes the span nor consumes density slack.  This
   inductive presentation makes that fact explicit instead of silently
   dropping contained intervals during endpoint normalization. *)
Inductive RightOverlapComponent (q : list Z) :
    Z -> Z -> list (Z * Z) -> Prop :=
| right_overlap_component_single :
    forall left right,
      Mode 49 q left right ->
      RightOverlapComponent q left right ((left, right) :: nil)
| right_overlap_component_absorb :
    forall component_left component_right intervals interval_left interval_right,
      RightOverlapComponent q component_left component_right intervals ->
      component_left <= interval_left /\
        interval_left < interval_right /\
        interval_right <= component_right ->
      Mode 49 q interval_left interval_right ->
      RightOverlapComponent q component_left component_right
        (intervals ++ (interval_left, interval_right) :: nil)
| right_overlap_component_extend :
    forall component_left component_right intervals interval_left interval_right,
      RightOverlapComponent q component_left component_right intervals ->
      component_left <= interval_left < component_right /\
        component_right < interval_right ->
      Mode 49 q interval_left interval_right ->
      RightOverlapComponent q component_left interval_right
        (intervals ++ (interval_left, interval_right) :: nil).

Lemma RightOverlapChain_is_component :
  forall q left right intervals,
    RightOverlapChain q left right intervals ->
    RightOverlapComponent q left right intervals.
Proof.
  intros q left right intervals Hchain.
  induction Hchain.
  - apply right_overlap_component_single. exact H.
  - eapply right_overlap_component_extend; eauto.
Qed.

Lemma RightOverlapComponent_slack :
  forall q left right intervals,
    RightOverlapComponent q left right intervals ->
    RightDensitySlack q left right.
Proof.
  intros q left right intervals Hcomponent.
  induction Hcomponent.
  - apply Mode_RightDensitySlack. exact H.
  - exact IHHcomponent.
  - eapply RightDensitySlack_extend_right; eauto.
Qed.

Lemma RightOverlapComponent_density :
  forall q left right intervals,
    RightOverlapComponent q left right intervals ->
    right - left <= 3 * Count 49 (sublist left right q).
Proof.
  intros q left right intervals Hcomponent.
  pose proof
    (RightOverlapComponent_slack q left right intervals Hcomponent) as Hslack.
  unfold RightDensitySlack in Hslack. lia.
Qed.

Lemma RightOverlapComponent_bounds :
  forall q left right intervals,
    RightOverlapComponent q left right intervals ->
    0 <= left < right /\ right <= Zlength q.
Proof.
  intros q left right intervals Hcomponent.
  pose proof
    (RightOverlapComponent_slack q left right intervals Hcomponent) as Hslack.
  unfold RightDensitySlack in Hslack. tauto.
Qed.

Lemma RightOverlapComponent_centres_local_bound :
  forall q positions left right intervals,
    RightOverlapComponent q left right intervals ->
    ThreeSeparated positions ->
    Forall (fun centre => left <= centre < right) positions ->
    Zlength positions <= Count 49 (sublist left right q).
Proof.
  intros q positions left right intervals Hcomponent Hseparated Hinside.
  pose proof
    (RightOverlapComponent_bounds q left right intervals Hcomponent)
    as Hbounds.
  pose proof
    (RightOverlapComponent_density q left right intervals Hcomponent)
    as Hdensity.
  pose proof
    (ThreeSeparated_span_bound positions left right ltac:(lia)
      Hseparated Hinside) as Hpacking.
  pose proof (Zlength_nonneg positions) as Hlength.
  pose proof (Count_nonnegative 49 (sublist left right q)) as Hcount.
  eapply component_span_density_implies_cardinality; eauto.
Qed.

Lemma RightOverlapComponent_centres_bound :
  forall q positions left right intervals,
    RightOverlapComponent q left right intervals ->
    ThreeSeparated positions ->
    Forall (fun centre => left <= centre < right) positions ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions left right intervals Hcomponent Hseparated Hinside.
  pose proof
    (RightOverlapComponent_bounds q left right intervals Hcomponent)
    as Hbounds.
  pose proof
    (RightOverlapComponent_centres_local_bound
      q positions left right intervals Hcomponent Hseparated Hinside)
    as Hlocal.
  pose proof
    (Count_sublist_le_Count 49 q left right ltac:(lia) ltac:(lia))
    as Hglobal.
  lia.
Qed.

(* Coverage is deliberately insensitive to the order of the interval list.
   It is the bridge between the centre-aligned input family and an endpoint-
   sorted component: sorting may permute witnesses, but cannot lose the fact
   that every selected centre belongs to one of them. *)
Definition CentresCoveredByIntervals
    (positions : list Z) (intervals : list (Z * Z)) : Prop :=
  Forall
    (fun centre => exists bounds,
       In bounds intervals /\
       let '(interval_start, interval_end) := bounds in
         interval_start <= centre < interval_end)
    positions.

Lemma MajorityIntervalFamily_centres_covered :
  forall q positions intervals,
    MajorityIntervalFamily q positions intervals ->
    CentresCoveredByIntervals positions intervals.
Proof.
  intros q positions intervals Hfamily.
  induction Hfamily as
    [| centre [left right] positions intervals Hhead Htail IH].
  - constructor.
  - constructor.
    + exists (left, right). split; [simpl; auto |].
      unfold MajorityIntervalWitness in Hhead. simpl in Hhead. tauto.
    + unfold CentresCoveredByIntervals in IH.
      eapply Forall_impl; [| exact IH].
      intros other [bounds [Hin Hcontains]].
      exists bounds. split; [simpl; auto | exact Hcontains].
Qed.

Lemma CentresCoveredByIntervals_permutation :
  forall positions intervals intervals',
    Permutation intervals intervals' ->
    CentresCoveredByIntervals positions intervals ->
    CentresCoveredByIntervals positions intervals'.
Proof.
  intros positions intervals intervals' Hperm Hcovered.
  unfold CentresCoveredByIntervals in *.
  apply Forall_forall. intros centre Hcentre.
  apply Forall_forall with (x := centre) in Hcovered; [| exact Hcentre].
  destruct Hcovered as [bounds [Hin Hcontains]].
  exists bounds. split; [| exact Hcontains].
  eapply Permutation_in; eauto.
Qed.

Lemma RightOverlapComponent_interval_bounds :
  forall q component_left component_right intervals bounds,
    RightOverlapComponent q component_left component_right intervals ->
    In bounds intervals ->
    let '(interval_left, interval_right) := bounds in
      component_left <= interval_left /\ interval_right <= component_right.
Proof.
  intros q component_left component_right intervals bounds Hcomponent Hin.
  induction Hcomponent as
    [left right Hmode
    | component_left component_right intervals interval_left interval_right
        Hcomponent IH Hcontained Hmode
    | component_left component_right intervals interval_left interval_right
        Hcomponent IH Hextends Hmode].
  - simpl in Hin. destruct Hin as [Heq | Hfalse]; [| contradiction].
    inversion Heq; subst. simpl. lia.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | Hfalse]; [| contradiction].
      inversion Heq; subst. simpl. lia.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + specialize (IH Hin).
      destruct bounds as [left right]. simpl in *. lia.
    + simpl in Hin. destruct Hin as [Heq | Hfalse]; [| contradiction].
      inversion Heq; subst. simpl. lia.
Qed.

Lemma RightOverlapComponent_centres_inside :
  forall q positions left right intervals,
    RightOverlapComponent q left right intervals ->
    CentresCoveredByIntervals positions intervals ->
    Forall (fun centre => left <= centre < right) positions.
Proof.
  intros q positions left right intervals Hcomponent Hcovered.
  unfold CentresCoveredByIntervals in Hcovered.
  apply Forall_forall. intros centre Hcentre.
  apply Forall_forall with (x := centre) in Hcovered; [| exact Hcentre].
  destruct Hcovered as [[interval_left interval_right] [Hin Hcontains]].
  pose proof
    (RightOverlapComponent_interval_bounds q left right intervals
      (interval_left, interval_right) Hcomponent Hin) as Hbounds.
  simpl in Hcontains, Hbounds. lia.
Qed.

Lemma RightOverlapComponent_covered_centres_bound :
  forall q positions left right intervals,
    RightOverlapComponent q left right intervals ->
    ThreeSeparated positions ->
    CentresCoveredByIntervals positions intervals ->
    Zlength positions <= Count 49 (sublist left right q).
Proof.
  intros q positions left right intervals Hcomponent Hseparated Hcovered.
  apply RightOverlapComponent_centres_local_bound with (intervals := intervals);
    try assumption.
  eapply RightOverlapComponent_centres_inside; eauto.
Qed.

(* The partition certificate keeps centre sublists consecutive by construction.
   Its component spans are ordered and disjoint; gaps are allowed and carry a
   nonnegative number of ones.  Consequently Count additivity can sum the
   checked local component bounds without any matching assumption. *)
Inductive OrderedOverlapPartition (q : list Z) :
    list Z -> Z -> Z -> Prop :=
| ordered_overlap_partition_single :
    forall positions left right intervals,
      RightOverlapComponent q left right intervals ->
      ThreeSeparated positions ->
      CentresCoveredByIntervals positions intervals ->
      OrderedOverlapPartition q positions left right
| ordered_overlap_partition_append :
    forall positions positions' left previous_right component_left right
      intervals,
      OrderedOverlapPartition q positions left previous_right ->
      previous_right <= component_left ->
      RightOverlapComponent q component_left right intervals ->
      ThreeSeparated positions' ->
      CentresCoveredByIntervals positions' intervals ->
      OrderedOverlapPartition q (positions ++ positions') left right.

Lemma OrderedOverlapPartition_bounds :
  forall q positions left right,
    OrderedOverlapPartition q positions left right ->
    0 <= left < right /\ right <= Zlength q.
Proof.
  intros q positions left right Hpartition.
  induction Hpartition as
    [positions left right intervals Hcomponent Hseparated Hcovered
    | positions positions' left previous_right component_left right intervals
        Hpartition IH Hordered Hcomponent Hseparated Hcovered].
  - eapply RightOverlapComponent_bounds; eauto.
  - pose proof
      (RightOverlapComponent_bounds q component_left right intervals Hcomponent)
      as Hcomponent_bounds.
    lia.
Qed.

Lemma OrderedOverlapPartition_local_bound :
  forall q positions left right,
    OrderedOverlapPartition q positions left right ->
    Zlength positions <= Count 49 (sublist left right q).
Proof.
  intros q positions left right Hpartition.
  induction Hpartition as
    [positions left right intervals Hcomponent Hseparated Hcovered
    | positions positions' left previous_right component_left right intervals
        Hpartition IH Hordered Hcomponent Hseparated Hcovered].
  - eapply RightOverlapComponent_covered_centres_bound; eauto.
  - pose proof
      (OrderedOverlapPartition_bounds q positions left previous_right Hpartition)
      as Hpartition_bounds.
    pose proof
      (RightOverlapComponent_bounds q component_left right intervals Hcomponent)
      as Hcomponent_bounds.
    pose proof
      (RightOverlapComponent_covered_centres_bound q positions'
        component_left right intervals Hcomponent Hseparated Hcovered)
      as Hnew_bound.
    pose proof
      (Count_sublist_split 49 q left previous_right right ltac:(lia)
        ltac:(lia)) as Hsplit_previous.
    pose proof
      (Count_sublist_split 49 q previous_right component_left right
        ltac:(lia) ltac:(lia)) as Hsplit_gap.
    pose proof
      (Count_nonnegative 49
        (sublist previous_right component_left q)) as Hgap_nonnegative.
    rewrite Zlength_app. lia.
Qed.

Lemma OrderedOverlapPartition_global_bound :
  forall q positions left right,
    OrderedOverlapPartition q positions left right ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions left right Hpartition.
  pose proof
    (OrderedOverlapPartition_bounds q positions left right Hpartition)
    as Hbounds.
  pose proof
    (OrderedOverlapPartition_local_bound q positions left right Hpartition)
    as Hlocal.
  pose proof
    (Count_sublist_le_Count 49 q left right ltac:(lia) ltac:(lia))
    as Hglobal.
  lia.
Qed.

Lemma MajorityIntervalFamily_permuted_component_partition :
  forall q positions intervals normalized left right,
    MajorityIntervalFamily q positions intervals ->
    Permutation intervals normalized ->
    RightOverlapComponent q left right normalized ->
    ThreeSeparated positions ->
    OrderedOverlapPartition q positions left right.
Proof.
  intros q positions intervals normalized left right
    Hfamily Hpermutation Hcomponent Hseparated.
  apply ordered_overlap_partition_single with (intervals := normalized);
    try assumption.
  apply CentresCoveredByIntervals_permutation with (intervals := intervals).
  - exact Hpermutation.
  - apply MajorityIntervalFamily_centres_covered with (q := q).
    exact Hfamily.
Qed.

Lemma MajorityIntervalFamily_permuted_component_bound :
  forall q positions intervals normalized left right,
    MajorityIntervalFamily q positions intervals ->
    Permutation intervals normalized ->
    RightOverlapComponent q left right normalized ->
    ThreeSeparated positions ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions intervals normalized left right
    Hfamily Hpermutation Hcomponent Hseparated.
  apply OrderedOverlapPartition_global_bound with (left := left) (right := right).
  eapply MajorityIntervalFamily_permuted_component_partition; eauto.
Qed.

Definition MajorityBounds (q : list Z) (bounds : Z * Z) : Prop :=
  let '(interval_left, interval_right) := bounds in
    Mode 49 q interval_left interval_right.

Lemma MajorityIntervalFamily_intervals_are_modes :
  forall q positions intervals,
    MajorityIntervalFamily q positions intervals ->
    Forall (MajorityBounds q) intervals.
Proof.
  intros q positions intervals Hfamily.
  induction Hfamily as
    [| centre [interval_left interval_right] positions intervals
        Hhead Htail IH].
  - constructor.
  - constructor; [| exact IH].
    unfold MajorityIntervalWitness in Hhead.
    unfold MajorityBounds. simpl in Hhead. tauto.
Qed.

Lemma MajorityBounds_permutation :
  forall q intervals intervals',
    Permutation intervals intervals' ->
    Forall (MajorityBounds q) intervals ->
    Forall (MajorityBounds q) intervals'.
Proof.
  intros q intervals intervals' Hpermutation Hmodes.
  apply Forall_forall. intros bounds Hin.
  apply Forall_forall with (x := bounds) in Hmodes.
  - exact Hmodes.
  - eapply Permutation_in; [apply Permutation_sym; exact Hpermutation |].
    exact Hin.
Qed.

(* A transparent finite endpoint sort.  Sorting only by the left endpoint is
   sufficient for the component scan: among intervals with the same left
   endpoint, a shorter interval is either absorbed before a later extension,
   or absorbed after the longer interval has established the frontier. *)
Definition BoundsLeft (bounds : Z * Z) : Z := fst bounds.

Fixpoint InsertBoundsByLeft
    (bounds : Z * Z) (intervals : list (Z * Z)) : list (Z * Z) :=
  match intervals with
  | nil => bounds :: nil
  | first :: rest =>
      if Z_le_dec (BoundsLeft bounds) (BoundsLeft first)
      then bounds :: intervals
      else first :: InsertBoundsByLeft bounds rest
  end.

Fixpoint SortBoundsByLeft
    (intervals : list (Z * Z)) : list (Z * Z) :=
  match intervals with
  | nil => nil
  | first :: rest => InsertBoundsByLeft first (SortBoundsByLeft rest)
  end.

Fixpoint BoundsLeftOrdered (intervals : list (Z * Z)) : Prop :=
  match intervals with
  | nil => True
  | first :: rest =>
      Forall (fun bounds => BoundsLeft first <= BoundsLeft bounds) rest /\
      BoundsLeftOrdered rest
  end.

Lemma InsertBoundsByLeft_permutation :
  forall bounds intervals,
    Permutation (bounds :: intervals) (InsertBoundsByLeft bounds intervals).
Proof.
  intros bounds intervals.
  induction intervals as [| first rest IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (Z_le_dec (BoundsLeft bounds) (BoundsLeft first)).
    + apply Permutation_refl.
    + eapply Permutation_trans.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Lemma SortBoundsByLeft_permutation :
  forall intervals,
    Permutation intervals (SortBoundsByLeft intervals).
Proof.
  induction intervals as [| first rest IH].
  - simpl. apply Permutation_refl.
  - simpl. eapply Permutation_trans.
    + apply perm_skip. exact IH.
    + apply InsertBoundsByLeft_permutation.
Qed.

Lemma Forall_under_permutation {A : Type} :
  forall (P : A -> Prop) xs ys,
    Permutation xs ys ->
    Forall P xs ->
    Forall P ys.
Proof.
  intros P xs ys Hpermutation Hforall.
  apply Forall_forall. intros x Hin.
  apply Forall_forall with (x := x) in Hforall.
  - exact Hforall.
  - eapply Permutation_in; [apply Permutation_sym; exact Hpermutation |].
    exact Hin.
Qed.

Lemma InsertBoundsByLeft_ordered :
  forall bounds intervals,
    BoundsLeftOrdered intervals ->
    BoundsLeftOrdered (InsertBoundsByLeft bounds intervals).
Proof.
  intros bounds intervals.
  induction intervals as [| first rest IH]; intros Hordered.
  - simpl. auto.
  - simpl in Hordered |- *.
    destruct Hordered as [Hfirst Hrest].
    destruct (Z_le_dec (BoundsLeft bounds) (BoundsLeft first)) as
      [Hbefore | Hafter].
    + split.
      * constructor; [exact Hbefore |].
        apply Forall_forall. intros other Hin.
        apply Forall_forall with (x := other) in Hfirst; [lia | exact Hin].
      * split; assumption.
    + split.
      * apply Forall_under_permutation with (xs := bounds :: rest).
        -- apply InsertBoundsByLeft_permutation.
        -- constructor; [lia | exact Hfirst].
      * apply IH. exact Hrest.
Qed.

Lemma SortBoundsByLeft_ordered :
  forall intervals,
    BoundsLeftOrdered (SortBoundsByLeft intervals).
Proof.
  induction intervals as [| first rest IH].
  - simpl. auto.
  - simpl. apply InsertBoundsByLeft_ordered. exact IH.
Qed.

Lemma SortBoundsByLeft_preserves_modes :
  forall q intervals,
    Forall (MajorityBounds q) intervals ->
    Forall (MajorityBounds q) (SortBoundsByLeft intervals).
Proof.
  intros q intervals Hmodes.
  apply MajorityBounds_permutation with (intervals := intervals).
  - apply SortBoundsByLeft_permutation.
  - exact Hmodes.
Qed.

Lemma SortBoundsByLeft_preserves_coverage :
  forall positions intervals,
    CentresCoveredByIntervals positions intervals ->
    CentresCoveredByIntervals positions (SortBoundsByLeft intervals).
Proof.
  intros positions intervals Hcovered.
  apply CentresCoveredByIntervals_permutation with (intervals := intervals).
  - apply SortBoundsByLeft_permutation.
  - exact Hcovered.
Qed.

(* Consume exactly the next connected component of a left-ordered interval
   list.  The frontier is the maximum right endpoint reached so far; the first
   interval beginning at or beyond it is left untouched for the next
   component. *)
Fixpoint SplitOverlappingPrefix
    (frontier : Z) (intervals : list (Z * Z))
    : list (Z * Z) * list (Z * Z) :=
  match intervals with
  | nil => (nil, nil)
  | (interval_left, interval_right) :: rest =>
      if Z_lt_dec interval_left frontier
      then
        let '(inside, after) :=
          SplitOverlappingPrefix (Z.max frontier interval_right) rest in
        ((interval_left, interval_right) :: inside, after)
      else (nil, intervals)
  end.

Lemma SplitOverlappingPrefix_partition :
  forall frontier intervals,
    let result := SplitOverlappingPrefix frontier intervals in
      intervals = fst result ++ snd result.
Proof.
  intros frontier intervals. revert frontier.
  induction intervals as [| [interval_left interval_right] rest IH];
    intros frontier; simpl.
  - reflexivity.
  - destruct (Z_lt_dec interval_left frontier) as [Hoverlap | Hgap].
    + destruct
        (SplitOverlappingPrefix (Z.max frontier interval_right) rest)
        as [inside after] eqn:Hsplit.
      specialize (IH (Z.max frontier interval_right)).
      rewrite Hsplit in IH. simpl in IH. rewrite IH. reflexivity.
    + reflexivity.
Qed.

Lemma SplitOverlappingPrefix_builds_component :
  forall q component_left frontier current rest,
    RightOverlapComponent q component_left frontier current ->
    Forall (MajorityBounds q) rest ->
    Forall (fun bounds => component_left <= BoundsLeft bounds) rest ->
    exists inside after final_frontier,
      SplitOverlappingPrefix frontier rest = (inside, after) /\
      RightOverlapComponent q component_left final_frontier
        (current ++ inside) /\
      (after = nil \/
       exists next remaining,
         after = next :: remaining /\
         final_frontier <= BoundsLeft next).
Proof.
  intros q component_left frontier current rest.
  revert frontier current.
  induction rest as [| [interval_left interval_right] rest IH];
    intros frontier current Hcomponent Hmodes Hlefts.
  - exists nil, nil, frontier. simpl.
    rewrite app_nil_r. auto.
  - inversion Hmodes as [| ? ? Hmode Hmodes_tail]; subst.
    inversion Hlefts as [| ? ? Hleft Hlefts_tail]; subst.
    simpl in Hleft.
    unfold MajorityBounds in Hmode. simpl in Hmode.
    assert (Hinterval_nonempty : interval_left < interval_right).
    { unfold Mode in Hmode. lia. }
    destruct (Z_lt_dec interval_left frontier) as [Hoverlap | Hgap].
    + assert (Hextended :
        RightOverlapComponent q component_left
          (Z.max frontier interval_right)
          (current ++ (interval_left, interval_right) :: nil)).
      { destruct (Z_le_dec interval_right frontier) as
          [Hcontained | Hextends].
        - replace (Z.max frontier interval_right) with frontier by lia.
          eapply right_overlap_component_absorb.
          * exact Hcomponent.
          * repeat split; assumption.
          * exact Hmode.
        - replace (Z.max frontier interval_right) with interval_right by lia.
          eapply right_overlap_component_extend.
          * exact Hcomponent.
          * split; [lia | lia].
          * exact Hmode.
      }
      destruct
        (IH (Z.max frontier interval_right)
          (current ++ (interval_left, interval_right) :: nil)
          Hextended Hmodes_tail Hlefts_tail)
        as [inside [after [final_frontier
          [Hsplit [Hfinal Hafter]]]]].
      exists ((interval_left, interval_right) :: inside), after,
        final_frontier.
      split.
      * simpl. destruct (Z_lt_dec interval_left frontier);
          [rewrite Hsplit; reflexivity | contradiction].
      * split.
        -- replace
             (current ++ (interval_left, interval_right) :: inside)
             with
             ((current ++ (interval_left, interval_right) :: nil) ++ inside)
             by (rewrite <- app_assoc; reflexivity).
           exact Hfinal.
        -- exact Hafter.
    + exists nil, ((interval_left, interval_right) :: rest), frontier.
      split.
      * simpl. destruct (Z_lt_dec interval_left frontier);
          [contradiction | reflexivity].
      * split.
        -- rewrite app_nil_r. exact Hcomponent.
        -- right. exists (interval_left, interval_right), rest.
           split; [reflexivity |]. simpl. lia.
Qed.

Lemma LeftOrderedMajorityFamily_first_component :
  forall q interval_left interval_right rest,
    BoundsLeftOrdered ((interval_left, interval_right) :: rest) ->
    Forall (MajorityBounds q) ((interval_left, interval_right) :: rest) ->
    exists inside after final_frontier,
      SplitOverlappingPrefix interval_right rest = (inside, after) /\
      RightOverlapComponent q interval_left final_frontier
        ((interval_left, interval_right) :: inside) /\
      (after = nil \/
       exists next remaining,
         after = next :: remaining /\
         final_frontier <= BoundsLeft next).
Proof.
  intros q interval_left interval_right rest Hordered Hmodes.
  simpl in Hordered. destruct Hordered as [Hlefts Hordered_tail].
  inversion Hmodes as [| ? ? Hmode Hmodes_tail]; subst.
  unfold MajorityBounds in Hmode. simpl in Hmode.
  assert (Hsingle :
    RightOverlapComponent q interval_left interval_right
      ((interval_left, interval_right) :: nil)).
  { apply right_overlap_component_single. exact Hmode. }
  destruct
    (SplitOverlappingPrefix_builds_component q interval_left interval_right
      ((interval_left, interval_right) :: nil) rest Hsingle
      Hmodes_tail Hlefts)
    as [inside [after [final_frontier
      [Hsplit [Hcomponent Hafter]]]]].
  exists inside, after, final_frontier.
  split; [exact Hsplit |].
  split; [simpl in Hcomponent; exact Hcomponent | exact Hafter].
Qed.

Lemma BoundsLeftOrdered_app_right :
  forall prefix suffix,
    BoundsLeftOrdered (prefix ++ suffix) ->
    BoundsLeftOrdered suffix.
Proof.
  induction prefix as [| first prefix IH]; intros suffix Hordered.
  - simpl in Hordered. exact Hordered.
  - simpl in Hordered. destruct Hordered as [Hfirst Htail].
    apply IH. exact Htail.
Qed.

Lemma SplitOverlappingPrefix_after_ordered :
  forall frontier intervals inside after,
    BoundsLeftOrdered intervals ->
    SplitOverlappingPrefix frontier intervals = (inside, after) ->
    BoundsLeftOrdered after.
Proof.
  intros frontier intervals inside after Hordered Hsplit.
  pose proof (SplitOverlappingPrefix_partition frontier intervals) as Hparts.
  rewrite Hsplit in Hparts. simpl in Hparts. rewrite Hparts in Hordered.
  eapply BoundsLeftOrdered_app_right; eauto.
Qed.

Lemma SplitOverlappingPrefix_after_modes :
  forall q frontier intervals inside after,
    Forall (MajorityBounds q) intervals ->
    SplitOverlappingPrefix frontier intervals = (inside, after) ->
    Forall (MajorityBounds q) after.
Proof.
  intros q frontier intervals inside after Hmodes Hsplit.
  pose proof (SplitOverlappingPrefix_partition frontier intervals) as Hparts.
  rewrite Hsplit in Hparts. simpl in Hparts. rewrite Hparts in Hmodes.
  apply Forall_app in Hmodes. tauto.
Qed.

Lemma SplitOverlappingPrefix_after_length :
  forall frontier intervals inside after,
    SplitOverlappingPrefix frontier intervals = (inside, after) ->
    Zlength after <= Zlength intervals.
Proof.
  intros frontier intervals inside after Hsplit.
  pose proof (SplitOverlappingPrefix_partition frontier intervals) as Hparts.
  rewrite Hsplit in Hparts. simpl in Hparts.
  rewrite Hparts, Zlength_app.
  pose proof (Zlength_nonneg inside). lia.
Qed.

Lemma SplitOverlappingPrefix_after_nat_length :
  forall frontier intervals inside after,
    SplitOverlappingPrefix frontier intervals = (inside, after) ->
    (length after <= length intervals)%nat.
Proof.
  intros frontier intervals inside after Hsplit.
  pose proof (SplitOverlappingPrefix_partition frontier intervals) as Hparts.
  rewrite Hsplit in Hparts. simpl in Hparts.
  rewrite Hparts, length_app. lia.
Qed.

Inductive EndpointOverlapPartition (q : list Z) :
    list (Z * Z) -> Z -> Z -> Prop :=
| endpoint_overlap_partition_single :
    forall intervals left right,
      RightOverlapComponent q left right intervals ->
      EndpointOverlapPartition q intervals left right
| endpoint_overlap_partition_prepend :
    forall intervals intervals' left component_right next_left right,
      RightOverlapComponent q left component_right intervals ->
      component_right <= next_left ->
      EndpointOverlapPartition q intervals' next_left right ->
      EndpointOverlapPartition q (intervals ++ intervals') left right.

Lemma RightOverlapComponent_first_interval :
  forall q left right intervals,
    RightOverlapComponent q left right intervals ->
    exists first_right rest,
      intervals = (left, first_right) :: rest.
Proof.
  intros q left right intervals Hcomponent.
  induction Hcomponent as
    [left right Hmode
    | component_left component_right intervals interval_left interval_right
        Hcomponent IH Hcontained Hmode
    | component_left component_right intervals interval_left interval_right
        Hcomponent IH Hextends Hmode].
  - exists right, nil. reflexivity.
  - destruct IH as [first_right [rest Heq]].
    rewrite Heq. exists first_right,
      (rest ++ (interval_left, interval_right) :: nil).
    reflexivity.
  - destruct IH as [first_right [rest Heq]].
    rewrite Heq. exists first_right,
      (rest ++ (interval_left, interval_right) :: nil).
    reflexivity.
Qed.

Lemma EndpointOverlapPartition_first_interval :
  forall q intervals left right,
    EndpointOverlapPartition q intervals left right ->
    exists first_right rest,
      intervals = (left, first_right) :: rest.
Proof.
  intros q intervals left right Hpartition.
  induction Hpartition as
    [intervals left right Hcomponent
    | intervals intervals' left component_right next_left right
        Hcomponent Hgap Hpartition IH].
  - eapply RightOverlapComponent_first_interval; eauto.
  - destruct
      (RightOverlapComponent_first_interval q left component_right
        intervals Hcomponent) as [first_right [rest Heq]].
    rewrite Heq. exists first_right, (rest ++ intervals'). reflexivity.
Qed.

Require Import Coq.Arith.Arith.

Lemma LeftOrderedMajorityIntervals_partition :
  forall q intervals,
    BoundsLeftOrdered intervals ->
    Forall (MajorityBounds q) intervals ->
    intervals = nil \/
    exists left right,
      EndpointOverlapPartition q intervals left right.
Proof.
  intros q intervals.
  remember (length intervals) as n eqn:Hn.
  revert intervals Hn.
  refine
    (well_founded_induction_type lt_wf
      (fun n => forall intervals,
        n = length intervals ->
        BoundsLeftOrdered intervals ->
        Forall (MajorityBounds q) intervals ->
        intervals = nil \/
        exists left right,
          EndpointOverlapPartition q intervals left right)
      _ n).
  intros k IH intervals Hlength Hordered Hmodes.
  destruct intervals as [| [interval_left interval_right] rest].
  - left. reflexivity.
  - right.
    destruct
      (LeftOrderedMajorityFamily_first_component q interval_left
        interval_right rest Hordered Hmodes)
      as [inside [after [final_frontier
        [Hsplit [Hcomponent Hafter]]]]].
    pose proof
      (SplitOverlappingPrefix_partition interval_right rest) as Hparts.
    rewrite Hsplit in Hparts. simpl in Hparts.
    assert (Hrest_ordered : BoundsLeftOrdered rest).
    { simpl in Hordered. tauto. }
    assert (Hrest_modes : Forall (MajorityBounds q) rest).
    { inversion Hmodes; subst. assumption. }
    destruct Hafter as [Hafter_empty |
      [next [remaining [Hafter_shape Hgap]]]].
    + subst after. rewrite app_nil_r in Hparts.
      rewrite Hparts.
      exists interval_left, final_frontier.
      apply endpoint_overlap_partition_single. exact Hcomponent.
    + rewrite Hparts.
      assert (Hafter_ordered : BoundsLeftOrdered after).
      { exact
          (SplitOverlappingPrefix_after_ordered interval_right rest inside
            after Hrest_ordered Hsplit). }
      assert (Hafter_modes : Forall (MajorityBounds q) after).
      { exact
          (SplitOverlappingPrefix_after_modes q interval_right rest inside
            after Hrest_modes Hsplit). }
      assert (Hafter_short : (length after < k)%nat).
      { pose proof
          (SplitOverlappingPrefix_after_nat_length interval_right rest
            inside after Hsplit) as Hafter_length.
        simpl in Hlength. lia. }
      specialize
        (IH (length after) Hafter_short after eq_refl
          Hafter_ordered Hafter_modes).
      destruct IH as [Hafter_nil |
        [next_left [partition_right Hpartition]]].
      * rewrite Hafter_shape in Hafter_nil. discriminate.
      * destruct
          (EndpointOverlapPartition_first_interval q after next_left
            partition_right Hpartition)
          as [next_right [partition_rest Hfirst]].
        destruct next as [next_interval_left next_interval_right].
        rewrite Hafter_shape in Hfirst. inversion Hfirst; subst.
        exists interval_left, partition_right.
        change
          (EndpointOverlapPartition q
            (((interval_left, interval_right) :: inside) ++
              ((next_left, next_right) :: partition_rest))
            interval_left partition_right).
        eapply endpoint_overlap_partition_prepend.
        -- exact Hcomponent.
        -- simpl in Hgap. exact Hgap.
        -- exact Hpartition.
Qed.

Lemma EndpointOverlapPartition_bounds :
  forall q intervals left right,
    EndpointOverlapPartition q intervals left right ->
    0 <= left < right /\ right <= Zlength q.
Proof.
  intros q intervals left right Hpartition.
  induction Hpartition as
    [intervals left right Hcomponent
    | intervals intervals' left component_right next_left right
        Hcomponent Hgap Hpartition IH].
  - eapply RightOverlapComponent_bounds; eauto.
  - pose proof
      (RightOverlapComponent_bounds q left component_right intervals Hcomponent)
      as Hcomponent_bounds.
    lia.
Qed.

Lemma EndpointOverlapPartition_interval_bounds :
  forall q intervals left right bounds,
    EndpointOverlapPartition q intervals left right ->
    In bounds intervals ->
    let '(interval_left, interval_right) := bounds in
      left <= interval_left /\ interval_right <= right.
Proof.
  intros q intervals left right bounds Hpartition Hin.
  induction Hpartition as
    [intervals left right Hcomponent
    | intervals intervals' left component_right next_left right
        Hcomponent Hgap Hpartition IH].
  - eapply RightOverlapComponent_interval_bounds; eauto.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + pose proof
        (RightOverlapComponent_interval_bounds q left component_right
          intervals bounds Hcomponent Hin) as Hbounds.
      pose proof
        (EndpointOverlapPartition_bounds q intervals' next_left right
          Hpartition) as Hrest_bounds.
      destruct bounds as [interval_left interval_right]. simpl in *. lia.
    + specialize (IH Hin).
      pose proof
        (RightOverlapComponent_bounds q left component_right intervals
          Hcomponent) as Hcomponent_bounds.
      destruct bounds as [interval_left interval_right]. simpl in *. lia.
Qed.

Lemma ThreeSeparated_app_parts :
  forall prefix suffix,
    ThreeSeparated (prefix ++ suffix) ->
    ThreeSeparated prefix /\ ThreeSeparated suffix.
Proof.
  induction prefix as [| first prefix IH]; intros suffix Hseparated.
  - simpl in Hseparated. split; [simpl; trivial | exact Hseparated].
  - simpl in Hseparated.
    destruct Hseparated as [Hlater Htail].
    destruct (IH suffix Htail) as [Hprefix Hsuffix].
    split; [| exact Hsuffix].
    simpl. split; [| exact Hprefix].
    apply Forall_app in Hlater. tauto.
Qed.

Fixpoint SplitCentresAt
    (boundary : Z) (positions : list Z) : list Z * list Z :=
  match positions with
  | nil => (nil, nil)
  | first :: rest =>
      if Z_lt_dec first boundary
      then
        let '(before, after) := SplitCentresAt boundary rest in
        (first :: before, after)
      else (nil, positions)
  end.

Lemma SplitCentresAt_partition :
  forall boundary positions,
    let result := SplitCentresAt boundary positions in
      positions = fst result ++ snd result.
Proof.
  intros boundary positions. revert boundary.
  induction positions as [| first rest IH]; intros boundary; simpl.
  - reflexivity.
  - destruct (Z_lt_dec first boundary) as [Hbefore | Hafter].
    + destruct (SplitCentresAt boundary rest) as [before after] eqn:Hsplit.
      specialize (IH boundary). rewrite Hsplit in IH. simpl in IH.
      rewrite IH. reflexivity.
    + reflexivity.
Qed.

Lemma SplitCentresAt_before :
  forall boundary positions before after,
    SplitCentresAt boundary positions = (before, after) ->
    Forall (fun centre => centre < boundary) before.
Proof.
  intros boundary positions. revert boundary.
  induction positions as [| first rest IH];
    intros boundary before after Hsplit; simpl in Hsplit.
  - inversion Hsplit. constructor.
  - destruct (Z_lt_dec first boundary) as [Hfirst | Hfirst].
    + destruct (SplitCentresAt boundary rest) as [before' after'] eqn:Htail.
      inversion Hsplit; subst. constructor; [exact Hfirst |].
      eapply IH; eauto.
    + inversion Hsplit; subst. constructor.
Qed.

Lemma SplitCentresAt_after :
  forall boundary positions before after,
    ThreeSeparated positions ->
    SplitCentresAt boundary positions = (before, after) ->
    Forall (fun centre => boundary <= centre) after.
Proof.
  intros boundary positions. revert boundary.
  induction positions as [| first rest IH];
    intros boundary before after Hseparated Hsplit; simpl in Hsplit.
  - inversion Hsplit. constructor.
  - simpl in Hseparated. destruct Hseparated as [Hlater Htail].
    destruct (Z_lt_dec first boundary) as [Hfirst | Hfirst].
    + destruct (SplitCentresAt boundary rest) as [before' after'] eqn:Htail_split.
      inversion Hsplit; subst. eapply IH; eauto.
    + inversion Hsplit; subst. constructor; [lia |].
      apply Forall_forall. intros centre Hin.
      apply Forall_forall with (x := centre) in Hlater; [lia | exact Hin].
Qed.

Lemma OrderedOverlapPartition_prepend :
  forall q positions positions' left component_right next_left right intervals,
    RightOverlapComponent q left component_right intervals ->
    component_right <= next_left ->
    ThreeSeparated positions ->
    CentresCoveredByIntervals positions intervals ->
    OrderedOverlapPartition q positions' next_left right ->
    OrderedOverlapPartition q (positions ++ positions') left right.
Proof.
  intros q positions positions' left component_right next_left right intervals
    Hcomponent Hgap Hseparated Hcovered Hpartition.
  induction Hpartition as
    [positions' next_left right intervals' Hcomponent' Hseparated' Hcovered'
    | prefix suffix next_left previous_right component_left right intervals'
        Hpartition IH Hordered Hcomponent' Hseparated' Hcovered'].
  - eapply ordered_overlap_partition_append.
    + apply ordered_overlap_partition_single with (intervals := intervals).
      * exact Hcomponent.
      * exact Hseparated.
      * exact Hcovered.
    + exact Hgap.
    + exact Hcomponent'.
    + exact Hseparated'.
    + exact Hcovered'.
  - rewrite app_assoc.
    eapply ordered_overlap_partition_append.
    + exact (IH Hgap).
    + exact Hordered.
    + exact Hcomponent'.
    + exact Hseparated'.
    + exact Hcovered'.
Qed.

Lemma SplitCentresAt_component_coverage :
  forall q positions before after intervals intervals'
    left component_right next_left right,
    SplitCentresAt component_right positions = (before, after) ->
    ThreeSeparated positions ->
    CentresCoveredByIntervals positions (intervals ++ intervals') ->
    RightOverlapComponent q left component_right intervals ->
    component_right <= next_left ->
    EndpointOverlapPartition q intervals' next_left right ->
    positions = before ++ after /\
    ThreeSeparated before /\
    ThreeSeparated after /\
    CentresCoveredByIntervals before intervals /\
    CentresCoveredByIntervals after intervals'.
Proof.
  intros q positions before after intervals intervals'
    left component_right next_left right Hsplit Hseparated Hcovered
    Hcomponent Hgap Hpartition.
  pose proof (SplitCentresAt_partition component_right positions) as Hparts.
  rewrite Hsplit in Hparts. simpl in Hparts.
  assert (Hbefore_range : Forall (fun centre => centre < component_right) before).
  { eapply SplitCentresAt_before; eauto. }
  assert (Hafter_range : Forall (fun centre => component_right <= centre) after).
  { eapply SplitCentresAt_after; eauto. }
  assert (Hseparated_parts : ThreeSeparated before /\ ThreeSeparated after).
  { rewrite Hparts in Hseparated.
    apply ThreeSeparated_app_parts in Hseparated. exact Hseparated. }
  repeat split; try tauto.
  - unfold CentresCoveredByIntervals in *.
    apply Forall_forall. intros centre Hin.
    apply Forall_forall with (x := centre) in Hbefore_range; [| exact Hin].
    apply Forall_forall with (x := centre) in Hcovered.
    2: { rewrite Hparts. apply in_or_app. left. exact Hin. }
    destruct Hcovered as [[interval_left interval_right]
      [Hinterval Hcontains]].
    apply in_app_or in Hinterval. destruct Hinterval as [Hhere | Hlater].
    + exists (interval_left, interval_right). auto.
    + pose proof
        (EndpointOverlapPartition_interval_bounds q intervals' next_left right
          (interval_left, interval_right) Hpartition Hlater) as Hbounds.
      simpl in Hcontains, Hbounds. lia.
  - unfold CentresCoveredByIntervals in *.
    apply Forall_forall. intros centre Hin.
    apply Forall_forall with (x := centre) in Hafter_range; [| exact Hin].
    apply Forall_forall with (x := centre) in Hcovered.
    2: { rewrite Hparts. apply in_or_app. right. exact Hin. }
    destruct Hcovered as [[interval_left interval_right]
      [Hinterval Hcontains]].
    apply in_app_or in Hinterval. destruct Hinterval as [Hhere | Hlater].
    + pose proof
        (RightOverlapComponent_interval_bounds q left component_right
          intervals (interval_left, interval_right) Hcomponent Hhere)
        as Hbounds.
      simpl in Hcontains, Hbounds. lia.
    + exists (interval_left, interval_right). auto.
Qed.

Lemma EndpointOverlapPartition_assign_centres :
  forall q intervals left right,
    EndpointOverlapPartition q intervals left right ->
    forall positions,
      ThreeSeparated positions ->
      CentresCoveredByIntervals positions intervals ->
      OrderedOverlapPartition q positions left right.
Proof.
  intros q intervals left right Hpartition.
  induction Hpartition as
    [intervals left right Hcomponent
    | intervals intervals' left component_right next_left right
        Hcomponent Hgap Hpartition IH];
    intros positions Hseparated Hcovered.
  - apply ordered_overlap_partition_single with (intervals := intervals);
      assumption.
  - destruct (SplitCentresAt component_right positions)
      as [before after] eqn:Hsplit.
    pose proof
      (SplitCentresAt_component_coverage q positions before after
        intervals intervals' left component_right next_left right
        Hsplit Hseparated Hcovered Hcomponent Hgap Hpartition)
      as [Hparts [Hbefore_separated [Hafter_separated
        [Hbefore_covered Hafter_covered]]]].
    rewrite Hparts.
    eapply OrderedOverlapPartition_prepend.
    + exact Hcomponent.
    + exact Hgap.
    + exact Hbefore_separated.
    + exact Hbefore_covered.
    + apply IH; assumption.
Qed.

Lemma MajorityIntervalFamily_partition_exists :
  forall q positions intervals,
    MajorityIntervalFamily q positions intervals ->
    ThreeSeparated positions ->
    positions = nil \/
    exists left right,
      OrderedOverlapPartition q positions left right.
Proof.
  intros q positions intervals Hfamily Hseparated.
  destruct positions as [| centre positions].
  - left. reflexivity.
  - right.
    destruct intervals as [| first intervals].
    { inversion Hfamily. }
    remember (SortBoundsByLeft (first :: intervals)) as normalized eqn:Hnormalized.
    assert (Hpermutation :
      Permutation (first :: intervals) normalized).
    { rewrite Hnormalized. apply SortBoundsByLeft_permutation. }
    assert (Hordered : BoundsLeftOrdered normalized).
    { rewrite Hnormalized. apply SortBoundsByLeft_ordered. }
    assert (Hmodes : Forall (MajorityBounds q) normalized).
    { apply MajorityBounds_permutation with
        (intervals := first :: intervals).
      - exact Hpermutation.
      - eapply MajorityIntervalFamily_intervals_are_modes; eauto. }
    assert (Hcovered :
      CentresCoveredByIntervals (centre :: positions) normalized).
    { apply CentresCoveredByIntervals_permutation with
        (intervals := first :: intervals).
      - exact Hpermutation.
      - eapply MajorityIntervalFamily_centres_covered; eauto. }
    destruct
      (LeftOrderedMajorityIntervals_partition q normalized Hordered Hmodes)
      as [Hnil | [left [right Hpartition]]].
    + pose proof (Permutation_length Hpermutation) as Hlength.
      rewrite Hnil in Hlength. simpl in Hlength. lia.
    + exists left, right.
      eapply EndpointOverlapPartition_assign_centres; eauto.
Qed.

Lemma ThreeSeparated_MajorityOneAt_bound :
  forall q positions,
    ThreeSeparated positions ->
    Forall (MajorityOneAt q) positions ->
    Zlength positions <= Count 49 q.
Proof.
  intros q positions Hseparated Hmajority.
  destruct (MajorityIntervalFamily_exists q positions Hmajority)
    as [intervals Hfamily].
  destruct
    (MajorityIntervalFamily_partition_exists q positions intervals
      Hfamily Hseparated)
    as [Hnil | [left [right Hpartition]]].
  - subst positions. rewrite Zlength_nil. apply Count_nonnegative.
  - eapply OrderedOverlapPartition_global_bound; eauto.
Qed.

Lemma PGood_ThreeSeparated_ones_lower_bound :
  forall p q positions,
    PGood p q ->
    ThreeSeparated positions ->
    Forall
      (fun centre =>
        0 <= centre < Zlength p /\ Znth centre p 0 = 49)
      positions ->
    Zlength positions <= Count 49 q.
Proof.
  intros p q positions Hgood Hseparated Hpositions.
  apply ThreeSeparated_MajorityOneAt_bound.
  - exact Hseparated.
  - eapply PGood_selected_ones_have_majority_intervals; eauto.
Qed.

(* The matching upper bound is realized by moving every greedy centre one
   position to the right, except at the right endpoint.  The output below is
   an entirely transparent finite list, rather than an abstract update map. *)
Definition CanonicalRep (n x : Z) : Z := Z.min (x + 1) (n - 1).

Definition CanonicalReps (n : Z) (positions : list Z) : list Z :=
  map (CanonicalRep n) positions.

Definition CanonicalOutput (n : Z) (positions : list Z) : list Z :=
  map
    (fun i =>
      if in_dec Z.eq_dec i (CanonicalReps n positions) then 49 else 48)
    (Zrange 0 n).

Lemma Zlength_Zrange_aux_canonical :
  forall low m, Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low.
  induction m as [| m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.

Lemma Zlength_Zrange_canonical :
  forall low high,
    low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux_canonical. lia.
Qed.

Lemma Znth_Zrange_aux_canonical :
  forall m low i,
    0 <= i < Z.of_nat m ->
    Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [| m IH]; intros low i Hi; [lia |].
  simpl.
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia).
    lia.
Qed.

Lemma Znth_Zrange_canonical :
  forall low high i,
    low <= high -> 0 <= i < high - low ->
    Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux_canonical by lia. lia.
Qed.

Lemma Zlength_map_canonical :
  forall {A B : Type} (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros A B f xs. rewrite !Zlength_correct, length_map. reflexivity.
Qed.

Lemma Znth_map_canonical :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [| x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.

Lemma CanonicalOutput_length :
  forall n positions,
    0 <= n -> Zlength (CanonicalOutput n positions) = n.
Proof.
  intros n positions Hn. unfold CanonicalOutput.
  rewrite Zlength_map_canonical, Zlength_Zrange_canonical by lia. lia.
Qed.

Lemma CanonicalOutput_Znth :
  forall n positions i,
    0 <= n -> 0 <= i < n ->
    Znth i (CanonicalOutput n positions) 0 =
      if in_dec Z.eq_dec i (CanonicalReps n positions) then 49 else 48.
Proof.
  intros n positions i Hn Hi. unfold CanonicalOutput.
  rewrite Znth_map_canonical with (da := 0) by
    (rewrite Zlength_Zrange_canonical by lia; lia).
  rewrite Znth_Zrange_canonical by lia. replace (0 + i) with i by lia.
  reflexivity.
Qed.

Lemma CanonicalOutput_binary :
  forall n positions,
    Forall (fun c => c = 48 \/ c = 49) (CanonicalOutput n positions).
Proof.
  intros n positions. unfold CanonicalOutput.
  apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc. destruct Hc as [i [Hci _]].
  rewrite <- Hci.
  destruct (in_dec Z.eq_dec i (CanonicalReps n positions)); auto.
Qed.

Lemma CanonicalRep_range :
  forall n x,
    0 < n -> 0 <= x < n -> 0 <= CanonicalRep n x < n.
Proof.
  intros n x Hn Hx. unfold CanonicalRep.
  destruct (Z.min_spec (x + 1) (n - 1)) as [[Hle ->] | [Hlt ->]]; lia.
Qed.

Lemma CanonicalRep_near_centre :
  forall n x,
    0 < n -> 0 <= x < n ->
    x <= CanonicalRep n x <= x + 1.
Proof.
  intros n x Hn Hx. unfold CanonicalRep.
  destruct (Z.min_spec (x + 1) (n - 1)) as [[Hle ->] | [Hlt ->]]; lia.
Qed.

Lemma CanonicalRep_strict_order :
  forall n x y,
    0 < n -> 0 <= x < n -> 0 <= y < n -> x + 3 <= y ->
    CanonicalRep n x < CanonicalRep n y.
Proof.
  intros n x y Hn Hx Hy Hxy.
  pose proof (CanonicalRep_near_centre n x Hn Hx) as Hrx.
  pose proof (CanonicalRep_near_centre n y Hn Hy) as Hry. lia.
Qed.

Lemma CanonicalReps_range :
  forall n positions,
    0 < n ->
    Forall (fun x => 0 <= x < n) positions ->
    Forall (fun i => 0 <= i < n) (CanonicalReps n positions).
Proof.
  intros n positions Hn Hvalid. unfold CanonicalReps.
  apply Forall_forall. intros i Hi.
  apply in_map_iff in Hi. destruct Hi as [x [Hrep Hx]].
  rewrite <- Hrep.
  apply CanonicalRep_range; [exact Hn |].
  apply Forall_forall with (x := x) in Hvalid; assumption.
Qed.

Lemma CanonicalReps_NoDup :
  forall n positions,
    0 < n ->
    ThreeSeparated positions ->
    Forall (fun x => 0 <= x < n) positions ->
    NoDup (CanonicalReps n positions).
Proof.
  intros n positions Hn Hseparated Hvalid.
  induction positions as [| x positions IH].
  - constructor.
  - simpl in Hseparated. destruct Hseparated as [Hlater Htail].
    inversion Hvalid as [| ? ? Hx Hvalid_tail]; subst.
    unfold CanonicalReps. simpl. constructor.
    + intros Hin. apply in_map_iff in Hin.
      destruct Hin as [y [Heq Hy]].
      apply Forall_forall with (x := y) in Hlater; [| exact Hy].
      apply Forall_forall with (x := y) in Hvalid_tail; [| exact Hy].
      pose proof
        (CanonicalRep_strict_order n x y Hn Hx Hvalid_tail Hlater).
      lia.
    + apply IH; assumption.
Qed.

Lemma ThreeSeparated_members_apart :
  forall positions x y,
    ThreeSeparated positions ->
    In x positions -> In y positions ->
    x = y \/ x + 3 <= y \/ y + 3 <= x.
Proof.
  induction positions as [| first positions IH];
    intros x y Hseparated Hx Hy.
  - contradiction.
  - simpl in Hseparated. destruct Hseparated as [Hlater Htail].
    simpl in Hx, Hy. destruct Hx as [-> | Hx]; destruct Hy as [-> | Hy].
    + auto.
    + right. left. apply Forall_forall with (x := y) in Hlater; assumption.
    + right. right. apply Forall_forall with (x := x) in Hlater; assumption.
    + apply IH; assumption.
Qed.

Lemma Selected_not_representative :
  forall n positions x,
    0 < n ->
    ThreeSeparated positions ->
    Forall (fun y => 0 <= y < n) positions ->
    In x positions ->
    CanonicalRep n x <> x ->
    ~ In x (CanonicalReps n positions).
Proof.
  intros n positions x Hn Hseparated Hvalid Hxin Hnotfixed Hin.
  unfold CanonicalReps in Hin. apply in_map_iff in Hin.
  destruct Hin as [y [Hrep Hyin]].
  pose proof
    (ThreeSeparated_members_apart positions x y Hseparated Hxin Hyin)
    as [-> | [Hxy | Hyx]].
  - contradiction.
  - pose proof Hvalid as Hvalid_x. pose proof Hvalid as Hvalid_y.
    apply Forall_forall with (x := x) in Hvalid_x; [| exact Hxin].
    apply Forall_forall with (x := y) in Hvalid_y; [| exact Hyin].
    pose proof
      (CanonicalRep_strict_order n x y Hn Hvalid_x Hvalid_y Hxy).
    pose proof (CanonicalRep_near_centre n x Hn Hvalid_x). lia.
  - pose proof Hvalid as Hvalid_x. pose proof Hvalid as Hvalid_y.
    apply Forall_forall with (x := x) in Hvalid_x; [| exact Hxin].
    apply Forall_forall with (x := y) in Hvalid_y; [| exact Hyin].
    pose proof
      (CanonicalRep_strict_order n y x Hn Hvalid_y Hvalid_x Hyx).
    pose proof (CanonicalRep_near_centre n y Hn Hvalid_y). lia.
Qed.

Lemma CanonicalRep_not_fixed_is_successor :
  forall n x,
    0 < n -> 0 <= x < n -> CanonicalRep n x <> x ->
    CanonicalRep n x = x + 1.
Proof.
  intros n x Hn Hx Hnotfixed.
  pose proof (CanonicalRep_near_centre n x Hn Hx). lia.
Qed.

Lemma CanonicalRep_fixed_is_last :
  forall n x,
    0 < n -> 0 <= x < n -> CanonicalRep n x = x -> x = n - 1.
Proof.
  intros n x Hn Hx Hfixed. unfold CanonicalRep in Hfixed.
  destruct (Z.min_spec (x + 1) (n - 1)) as [[Hle Heq] | [Hlt Heq]];
    rewrite Heq in Hfixed; lia.
Qed.

Lemma set_card_eq_Zlength_list :
  forall {A : Type} (P : A -> Prop) (finiteP : Finite P) xs,
    NoDup xs ->
    (forall x, P x <-> In x xs) ->
    @set_card A P finiteP = Zlength xs.
Proof.
  intros A P finiteP xs Hnodup Hmembers.
  rewrite set_card_as_Zlength_enum, !Zlength_correct.
  f_equal. apply Permutation_length.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - exact Hnodup.
  - intros x. rewrite <- enum_ok. apply Hmembers.
Qed.

Lemma CanonicalOutput_value_iff :
  forall n positions i,
    0 <= n -> 0 <= i < n ->
    Znth i (CanonicalOutput n positions) 0 = 49 <->
    In i (CanonicalReps n positions).
Proof.
  intros n positions i Hn Hi.
  rewrite CanonicalOutput_Znth by assumption.
  destruct (in_dec Z.eq_dec i (CanonicalReps n positions)) as [Hin | Hnot].
  - split; intros; [exact Hin | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

Lemma CanonicalOutput_Count :
  forall n positions,
    0 < n ->
    ThreeSeparated positions ->
    Forall (fun x => 0 <= x < n) positions ->
    Count 49 (CanonicalOutput n positions) = Zlength positions.
Proof.
  intros n positions Hn Hseparated Hvalid.
  unfold Count.
  rewrite (set_card_eq_Zlength_list
    (fun i : Z =>
      0 <= i < Zlength (CanonicalOutput n positions) /\
      Znth i (CanonicalOutput n positions) 0 = 49)
    _ (CanonicalReps n positions)).
  - unfold CanonicalReps. rewrite Zlength_map_canonical. reflexivity.
  - apply CanonicalReps_NoDup; assumption.
  - intros i. rewrite CanonicalOutput_length by lia.
    split.
    + intros [Hi Hvalue].
      apply (proj1 (CanonicalOutput_value_iff n positions i ltac:(lia) Hi)).
      exact Hvalue.
    + intros Hin. split.
      * pose proof (CanonicalReps_range n positions Hn Hvalid) as Hrange.
        apply Forall_forall with (x := i) in Hrange; assumption.
      * pose proof (CanonicalReps_range n positions Hn Hvalid) as Hrange.
        apply Forall_forall with (x := i) in Hrange; [| exact Hin].
        apply (proj2
          (CanonicalOutput_value_iff n positions i ltac:(lia) Hrange)).
        exact Hin.
Qed.

Lemma Count_sublist_contains_value :
  forall c q left right j,
    0 <= left < right -> right <= Zlength q ->
    left <= j < right -> Znth j q 0 = c ->
    1 <= Count c (sublist left right q).
Proof.
  intros c q left right j Hlr Hright Hj Hvalue.
  unfold Count.
  apply NoDup_Forall_set_card_lower_bound with (xs := (j - left) :: nil).
  - constructor; [simpl; lia | constructor].
  - constructor; [| constructor]. split.
    + rewrite Zlength_sublist by lia. lia.
    + rewrite Znth_sublist by lia.
      replace (j - left + left) with j by lia. exact Hvalue.
Qed.

Lemma Mode_from_short_interval_value :
  forall c q left right j,
    0 <= left < right -> right <= Zlength q ->
    right - left <= 2 ->
    left <= j < right -> Znth j q 0 = c ->
    Mode c q left right.
Proof.
  intros c q left right j Hlr Hright Hshort Hj Hvalue.
  unfold Mode. split; [exact Hlr |]. split; [exact Hright |].
  pose proof
    (Count_sublist_contains_value c q left right j Hlr Hright Hj Hvalue)
    as Hcount.
  assert (Hdifference : right - left = 1 \/ right - left = 2) by lia.
  assert (Hhalf : (right - left + 1) / 2 = 1).
  { destruct Hdifference as [Hdifference | Hdifference].
    - replace (right - left + 1) with 2 by lia. reflexivity.
    - replace (right - left + 1) with 3 by lia. reflexivity. }
  lia.
Qed.

Lemma CanonicalOutput_PGood :
  forall p positions,
    0 < Zlength p ->
    Forall (fun c => c = 48 \/ c = 49) p ->
    ThreeSeparated positions ->
    Forall
      (fun x => 0 <= x < Zlength p /\ Znth x p 0 = 49)
      positions ->
    (forall i,
      0 <= i < Zlength p -> Znth i p 0 = 49 -> CoveredBy positions i) ->
    PGood p (CanonicalOutput (Zlength p) positions).
Proof.
  intros p positions Hn Hbinary Hseparated Hvalid Hcovered.
  unfold PGood. split.
  - apply CanonicalOutput_length. lia.
  - split.
    + apply CanonicalOutput_binary.
    + intros i Hi.
      apply Forall_Znth with (i := i) (d := 0) in Hbinary; [| exact Hi].
      destruct Hbinary as [Hbit | Hbit].
      * destruct
          (in_dec Z.eq_dec i (CanonicalReps (Zlength p) positions))
          as [Hirep | Hinotrep].
        -- unfold CanonicalReps in Hirep. apply in_map_iff in Hirep.
           destruct Hirep as [x [Hrep Hxin]].
           pose proof Hvalid as Hvalid_all.
           apply Forall_forall with (x := x) in Hvalid; [| exact Hxin].
           destruct Hvalid as [Hx Hxbit].
           assert (Hxne : x <> i).
           { intros ->. rewrite Hbit in Hxbit. discriminate. }
           assert (Hnotfixed : CanonicalRep (Zlength p) x <> x).
           { intros Hfixed. apply Hxne. rewrite <- Hrep, Hfixed. reflexivity. }
           pose proof
             (CanonicalRep_not_fixed_is_successor (Zlength p) x Hn Hx Hnotfixed)
             as Hsucc.
           assert (Hqzero :
             Znth x (CanonicalOutput (Zlength p) positions) 0 = 48).
           { rewrite CanonicalOutput_Znth by lia.
             destruct (in_dec Z.eq_dec x
               (CanonicalReps (Zlength p) positions)) as [Hbad | _].
             - exfalso. eapply Selected_not_representative; eauto.
               eapply Forall_impl; [| exact Hvalid_all].
               intros y Hy. exact (proj1 Hy).
             - reflexivity. }
           exists x, (x + 2). split.
           ++ rewrite <- Hrep, Hsucc. lia.
           ++ apply Mode_from_short_interval_value with (j := x); try lia.
              rewrite CanonicalOutput_length by lia. lia.
        -- assert (Hqzero :
             Znth i (CanonicalOutput (Zlength p) positions) 0 = 48).
           { rewrite CanonicalOutput_Znth by lia.
             destruct (in_dec Z.eq_dec i
               (CanonicalReps (Zlength p) positions));
               [contradiction | reflexivity]. }
           exists i, (i + 1). split; [lia |].
           apply Mode_from_short_interval_value with (j := i); try lia.
           rewrite CanonicalOutput_length by lia. lia.
      * destruct (Hcovered i Hi Hbit) as [x [Hxin Hxi]].
        apply Forall_forall with (x := x) in Hvalid; [| exact Hxin].
        destruct Hvalid as [Hx Hxbit].
        set (representative := CanonicalRep (Zlength p) x).
        assert (Hrep_range : 0 <= representative < Zlength p).
        { unfold representative. apply CanonicalRep_range; assumption. }
        assert (Hrep_near : x <= representative <= x + 1).
        { unfold representative. apply CanonicalRep_near_centre; assumption. }
        assert (Hrep_distance :
          i <= representative + 1 /\ representative <= i + 1).
        { destruct (Z.eq_dec representative x) as [Hfixed | Hnotfixed].
          - assert (x = Zlength p - 1).
            { apply CanonicalRep_fixed_is_last.
              - exact Hn.
              - exact Hx.
              - unfold representative in Hfixed. exact Hfixed. }
            lia.
          - assert (representative = x + 1).
            { unfold representative in *.
              apply CanonicalRep_not_fixed_is_successor; assumption. }
            lia. }
        assert (Hqone :
          Znth representative (CanonicalOutput (Zlength p) positions) 0 = 49).
        { apply (proj2 (CanonicalOutput_value_iff
            (Zlength p) positions representative ltac:(lia) Hrep_range)).
          unfold representative, CanonicalReps. apply in_map. exact Hxin. }
        exists (Z.min i representative), (Z.max i representative + 1).
        split.
        -- pose proof (Z.le_min_l i representative).
           pose proof (Z.le_min_r i representative).
           pose proof (Z.le_max_l i representative).
           pose proof (Z.le_max_r i representative). lia.
        -- apply Mode_from_short_interval_value with (j := representative).
           ++ pose proof (Z.le_min_l i representative).
              pose proof (Z.le_min_r i representative).
              pose proof (Z.le_max_l i representative).
              pose proof (Z.le_max_r i representative).
              destruct (Z.min_spec i representative) as [[_ Hmin] | [_ Hmin]];
                destruct (Z.max_spec i representative) as [[_ Hmax] | [_ Hmax]];
                rewrite Hmin, Hmax; lia.
           ++ rewrite CanonicalOutput_length by lia.
              pose proof (Z.le_max_l i representative).
              pose proof (Z.le_max_r i representative). lia.
           ++ pose proof (Z.le_min_l i representative).
              pose proof (Z.le_min_r i representative).
              pose proof (Z.le_max_l i representative).
              pose proof (Z.le_max_r i representative).
              destruct (Z.min_spec i representative) as [[_ Hmin] | [_ Hmin]];
                destruct (Z.max_spec i representative) as [[_ Hmax] | [_ Hmax]];
                rewrite Hmin, Hmax; lia.
           ++ pose proof (Z.le_min_r i representative).
              pose proof (Z.le_max_r i representative). lia.
           ++ rewrite Hbit. exact Hqone.
Qed.

Lemma CanonicalPGood_realization :
  forall p positions,
    0 < Zlength p ->
    Forall (fun c => c = 48 \/ c = 49) p ->
    ThreeSeparated positions ->
    Forall
      (fun x => 0 <= x < Zlength p /\ Znth x p 0 = 49)
      positions ->
    (forall i,
      0 <= i < Zlength p -> Znth i p 0 = 49 -> CoveredBy positions i) ->
    exists q,
      PGood p q /\ Count 49 q = Zlength positions.
Proof.
  intros p positions Hn Hbinary Hseparated Hvalid Hcovered.
  exists (CanonicalOutput (Zlength p) positions). split.
  - eapply CanonicalOutput_PGood; eauto.
  - apply CanonicalOutput_Count.
    + exact Hn.
    + exact Hseparated.
    + eapply Forall_impl; [| exact Hvalid].
      intros x Hx. exact (proj1 Hx).
Qed.

Lemma GreedyCover_ExactPGoodCount :
  forall p positions,
    0 < Zlength p ->
    Forall (fun c => c = 48 \/ c = 49) p ->
    ThreeSeparated positions ->
    Forall
      (fun x => 0 <= x < Zlength p /\ Znth x p 0 = 49)
      positions ->
    (forall i,
      0 <= i < Zlength p -> Znth i p 0 = 49 -> CoveredBy positions i) ->
    ExactPGoodCount p (Zlength positions).
Proof.
  intros p positions Hn Hbinary Hseparated Hvalid Hcovered.
  destruct
    (CanonicalPGood_realization p positions Hn Hbinary Hseparated Hvalid Hcovered)
    as [q [Hgood Hcount]].
  exists q. split; [exact Hgood |]. split; [exact Hcount |].
  intros q' Hgood'.
  eapply PGood_ThreeSeparated_ones_lower_bound; eauto.
Qed.

Lemma GreedyCover_FValue :
  forall p positions,
    0 < Zlength p ->
    Forall (fun c => c = 48 \/ c = 49) p ->
    ThreeSeparated positions ->
    Forall
      (fun x => 0 <= x < Zlength p /\ Znth x p 0 = 49)
      positions ->
    (forall i,
      0 <= i < Zlength p -> Znth i p 0 = 49 -> CoveredBy positions i) ->
    FValue p (Zlength positions).
Proof.
  intros p positions Hn Hbinary Hseparated Hvalid Hcovered.
  apply ExactPGoodCount_FValue.
  eapply GreedyCover_ExactPGoodCount; eauto.
Qed.

Lemma Forall_firstn_greedy_bridge :
  forall {A : Type} (P : A -> Prop) n (xs : list A),
    Forall P xs -> Forall P (firstn n xs).
Proof.
  intros A P n. induction n as [| n IH]; intros xs Hforall.
  - constructor.
  - destruct xs as [| x xs]; [constructor |].
    inversion Hforall; subst. simpl. constructor; auto.
Qed.

Lemma Forall_skipn_greedy_bridge :
  forall {A : Type} (P : A -> Prop) n (xs : list A),
    Forall P xs -> Forall P (skipn n xs).
Proof.
  intros A P n. induction n as [| n IH]; intros xs Hforall.
  - exact Hforall.
  - destruct xs as [| x xs]; [constructor |].
    inversion Hforall; subst. simpl. apply IH. assumption.
Qed.

Lemma Forall_sublist_greedy_bridge :
  forall {A : Type} (P : A -> Prop) left right (xs : list A),
    Forall P xs -> Forall P (sublist left right xs).
Proof.
  intros A P left right xs Hforall. unfold sublist.
  apply Forall_skipn_greedy_bridge.
  apply Forall_firstn_greedy_bridge. exact Hforall.
Qed.

Lemma ThreeSeparated_shift_left :
  forall positions left,
    ThreeSeparated positions ->
    ThreeSeparated (map (fun x => x - left) positions).
Proof.
  induction positions as [| x positions IH]; intros left Hseparated.
  - constructor.
  - simpl in Hseparated |- *. destruct Hseparated as [Hlater Htail].
    split.
    + apply Forall_forall. intros shifted Hin.
      apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
      rewrite <- Heq. apply Forall_forall with (x := y) in Hlater;
        [lia | exact Hy].
    + apply IH. exact Htail.
Qed.

Lemma AbsoluteGreedyCover_FValue :
  forall s left right positions,
    0 <= left < right -> right <= Zlength s ->
    Forall (fun c => c = 48 \/ c = 49) s ->
    ThreeSeparated positions ->
    Forall
      (fun x => left <= x < right /\ Znth x s 0 = 49)
      positions ->
    (forall i,
      left <= i < right -> Znth i s 0 = 49 -> CoveredBy positions i) ->
    FValue (sublist left right s) (Zlength positions).
Proof.
  intros s left right positions Hleft Hright Hbinary Hseparated
    Hvalid Hcovered.
  set (relative := map (fun x => x - left) positions).
  replace (Zlength positions) with (Zlength relative).
  2: { unfold relative. rewrite Zlength_map_canonical. reflexivity. }
  apply GreedyCover_FValue with (positions := relative).
  - rewrite Zlength_sublist by lia. lia.
  - apply Forall_sublist_greedy_bridge. exact Hbinary.
  - unfold relative. apply ThreeSeparated_shift_left. exact Hseparated.
  - unfold relative. apply Forall_forall. intros shifted Hin.
    apply in_map_iff in Hin. destruct Hin as [x [Heq Hxin]].
    apply Forall_forall with (x := x) in Hvalid; [| exact Hxin].
    destruct Hvalid as [Hx Hvalue]. rewrite <- Heq.
    split.
    + rewrite Zlength_sublist by lia. lia.
    + rewrite Znth_sublist by lia.
      replace (x - left + left) with x by lia. exact Hvalue.
  - intros i Hi Hvalue. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist in Hvalue by lia.
    destruct (Hcovered (i + left) ltac:(lia) Hvalue)
      as [x [Hxin Hcovers]].
    unfold CoveredBy. exists (x - left). split.
    + change (In (x - left) (map (fun y => y - left) positions)).
      apply in_map_iff. exists x. split; [reflexivity | exact Hxin].
    + lia.
Qed.

Lemma PrefixCoverSummary_uncovered_one_FValue :
  forall s left upto cover count,
    PrefixCoverSummary s left upto cover count ->
    0 <= left ->
    upto < Zlength s ->
    Forall (fun c => c = 48 \/ c = 49) s ->
    Znth upto s 0 = 49 ->
    cover < upto ->
    FValue (sublist left (upto + 1) s) (count + 1).
Proof.
  intros s left upto cover count Hsummary Hleft0 Hlen Hbinary Hbit Huncovered.
  unfold PrefixCoverSummary in Hsummary.
  destruct Hsummary as [Hrange [positions
    [Hcount [Hvalid [Hseparated [Hcovered [Hfrontier _]]]]]]].
  assert (Hleft : left < upto + 1) by lia.
  pose proof (AbsoluteGreedyCover_FValue s left (upto + 1)
    (positions ++ upto :: nil) ltac:(lia) ltac:(lia) Hbinary) as Hvalue.
  rewrite Zlength_app, Zlength_cons, Zlength_nil, Hcount in Hvalue.
  apply Hvalue.
  - apply ThreeSeparated_app_last; [exact Hseparated |].
    apply Forall_forall. intros x Hxin.
    destruct Hfrontier as [[Hnil Hcover] |
      [prefix [last [Hpositions Hcover]]]].
    + subst positions. contradiction.
    + pose proof
        (ThreeSeparated_last_dominates positions prefix last Hseparated
          Hpositions x Hxin) as [-> | Hbefore]; lia.
  - apply Forall_app. split.
    + eapply Forall_impl; [| exact Hvalid]. intros x Hx.
      destruct Hx as [Hx Hxbit]. split; [lia | exact Hxbit].
    + constructor; [split; lia | constructor].
  - intros i Hi Hone.
    destruct (Z_lt_ge_dec i upto) as [Hold | Hnew].
    + destruct (Hcovered i ltac:(lia) Hone) as [x [Hxin Hcovers]].
      unfold CoveredBy. exists x. split.
      * apply in_or_app. left. exact Hxin.
      * exact Hcovers.
    + assert (i = upto) by lia. subst i.
      unfold CoveredBy. exists upto. split.
      * apply in_or_app. right. simpl. auto.
      * lia.
Qed.

Lemma PrefixCoverSummary_no_new_cover_FValue :
  forall s left upto cover count,
    PrefixCoverSummary s left upto cover count ->
    0 <= left ->
    upto < Zlength s ->
    Forall (fun c => c = 48 \/ c = 49) s ->
    (Znth upto s 0 <> 49 \/ upto <= cover) ->
    FValue (sublist left (upto + 1) s) count.
Proof.
  intros s left upto cover count Hsummary Hleft0 Hlen Hbinary Hno_new.
  unfold PrefixCoverSummary in Hsummary.
  destruct Hsummary as [Hrange [positions
    [Hcount [Hvalid [Hseparated [Hcovered [Hfrontier _]]]]]]].
  rewrite <- Hcount.
  apply AbsoluteGreedyCover_FValue; try assumption; try lia.
  - eapply Forall_impl; [| exact Hvalid]. intros x Hx.
    destruct Hx as [Hx Hxbit]. split; [lia | exact Hxbit].
  - intros i Hi Hone.
    destruct (Z_lt_ge_dec i upto) as [Hold | Hnew].
    + apply Hcovered; [lia | exact Hone].
    + assert (i = upto) by lia. subst i.
      destruct Hno_new as [Hnot_one | Hwithin].
      * contradiction.
      * destruct Hfrontier as [[Hnil Hcover] |
          [prefix [last [Hpositions Hcover]]]].
        -- subst positions. lia.
        -- unfold CoveredBy. exists last. split.
           ++ rewrite Hpositions. apply in_or_app. right. simpl. auto.
           ++ apply Forall_forall with (x := last) in Hvalid.
              2: { rewrite Hpositions. apply in_or_app. right. simpl. auto. }
              destruct Hvalid. lia.
Qed.

Lemma CurrentRow_initial :
  forall s left, CurrentRow s left left 0.
Proof.
  intros s left. unfold CurrentRow.
  exists (fun _ => 0). split.
  - intros right Hright. exfalso. lia.
  - unfold sum_range. rewrite SumLib.ZRange.sum_Z_range_empty by lia.
    reflexivity.
Qed.

Lemma PrefixCoverSummary_initial :
  forall s left,
    0 <= left <= Zlength s ->
    PrefixCoverSummary s left left (left - 1) 0.
Proof.
  intros s left Hleft. unfold PrefixCoverSummary.
  split; [lia |]. exists nil.
  split; [reflexivity |].
  split; [constructor |].
  split; [constructor |].
  split.
  - intros q Hq _. exfalso. lia.
  - split.
    + left. auto.
    + intros Hbad. lia.
Qed.

Lemma CompletedRows_initial :
  forall s, CompletedRows s 0 0.
Proof.
  intros s. unfold CompletedRows.
  exists (fun _ _ => 0). split.
  - intros i j Hi _. exfalso. lia.
  - unfold sum_range. rewrite SumLib.ZRange.sum_Z_range_empty by lia.
    reflexivity.
Qed.

Lemma CompletedRows_extend :
  forall s upto base row_total,
    0 <= upto < Zlength s ->
    CompletedRows s upto base ->
    CurrentRow s upto (Zlength s) row_total ->
    CompletedRows s (upto + 1) (base + row_total).
Proof.
  intros s upto base row_total Hupto Hcompleted Hrow.
  unfold CompletedRows in Hcompleted |- *.
  unfold CurrentRow in Hrow.
  destruct Hcompleted as [f [Hf Hbase]].
  destruct Hrow as [g [Hg Hrow]].
  exists (fun i j => if Z.eq_dec i upto then g j else f i j).
  split.
  - intros i j Hi Hj.
    destruct (Z.eq_dec i upto) as [-> | Hneq].
    + simpl. destruct (Z.eq_dec upto upto); [| contradiction].
      apply Hg. lia.
    + simpl. destruct (Z.eq_dec i upto); [contradiction |].
      apply Hf; lia.
  - replace (upto + 1 - 1) with upto by lia.
    unfold sum_range in *.
    replace (upto - 1 + 1) with upto in Hbase by lia.
    change (row_total =
      SumLib.Sum.sum
        (fun x : Z => upto + 1 <= x < Zlength s + 1)
        (fun j => g j)) in Hrow.
    rewrite (SumLib.ZRange.sum_Z_range_extend_right 0 upto) by lia.
    assert (Hold :
      SumLib.Sum.sum (fun x : Z => 0 <= x < upto)
        (fun i =>
          SumLib.Sum.sum (fun x : Z => i + 1 <= x < Zlength s + 1)
            (fun j => if Z.eq_dec i upto then g j else f i j)) =
      SumLib.Sum.sum (fun x : Z => 0 <= x < upto)
        (fun i =>
          SumLib.Sum.sum (fun x : Z => i + 1 <= x < Zlength s + 1)
            (fun j => f i j))).
    { apply SumLib.ZRange.sum_Z_range_ext. intros i Hi.
      destruct (Z.eq_dec i upto); [lia | reflexivity]. }
    rewrite Hold, <- Hbase.
    destruct (Z.eq_dec upto upto); [| contradiction].
    rewrite <- Hrow. ring.
Qed.

Lemma CompletedRows_final_Spec :
  forall s total,
    CompletedRows s (Zlength s) total -> Spec s total.
Proof.
  intros s total Hcompleted.
  unfold CompletedRows in Hcompleted. unfold Spec.
  destruct Hcompleted as [f [Hf Htotal]]. exists f. split.
  - intros i j Hij. apply Hf; lia.
  - exact Htotal.
Qed.
