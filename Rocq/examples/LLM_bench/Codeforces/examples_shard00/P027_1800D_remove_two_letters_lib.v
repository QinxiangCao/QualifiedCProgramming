Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ObtainedByRemovingTwo (s result : list Z) : Prop :=
  exists i, 0 <= i < Zlength s - 1 /\
    result = sublist 0 i s ++ sublist (i + 2) (Zlength s) s.

Definition Pre (s : list Z) : Prop :=
  3 <= Zlength s <= 200000 /\
  Forall (fun c => 97 <= c <= 122) s.

#[local] Instance finite_lowercase : Finite (fun c : Z => 97 <= c < 123) :=
  finite_Z_range 97 123.

#[local] Instance finite_result_string (size : Z) :
    Finite (fun result : list Z =>
      Zlength result = size /\ Forall (fun c => 97 <= c < 123) result) :=
  Finite_bounded_lists size (fun c : Z => 97 <= c < 123).

Definition Spec (s : list Z) (out : Z) : Prop :=
  out = #(fun result : list Z =>
    (Zlength result = Zlength s - 2 /\
     Forall (fun c => 97 <= c < 123) result) /\
    ObtainedByRemovingTwo s result).

Definition EqualGapTwoCount (s : list Z) (upto : Z) : Z :=
  #(fun i : Z =>
    0 <= i < upto /\
    Znth i s 0 = Znth (i + 2) s 0).

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Lemma set_card_Z_as_sum__gap_count_transitions :
  forall (low high : Z) (P : Z -> Prop),
    #(fun i : Z => low <= i < high /\ P i) =
    SumLib.Sum.sum (fun i : Z => low <= i < high)
      (fun i => if prop_dec (P i) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun i => if prop_dec (P i) then true else false) xs) =
    fold_right (fun i acc : Z =>
      (if prop_dec (P i) then 1 else 0) + acc) 0 xs).
  {
    induction xs as [|i xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P i)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma EqualGapTwoCount_bounds__gap_count_transitions :
  forall (s : list Z) (upto : Z),
    0 <= upto ->
    0 <= EqualGapTwoCount s upto <= upto.
Proof.
  intros s upto Hupto.
  unfold EqualGapTwoCount.
  rewrite set_card_Z_as_sum__gap_count_transitions.
  pose proof
    (SumLib.ZRange.sum_Z_range_bounds 0 upto
      (fun i =>
        if prop_dec (Znth i s 0 = Znth (i + 2) s 0) then 1 else 0)
      0 1 Hupto) as Hbounds.
  assert (Hpoint : forall i, 0 <= i < upto ->
    0 <= (if prop_dec (Znth i s 0 = Znth (i + 2) s 0) then 1 else 0) <= 1).
  {
    intros i Hi.
    destruct (prop_dec (Znth i s 0 = Znth (i + 2) s 0)); lia.
  }
  specialize (Hbounds Hpoint).
  lia.
Qed.
Lemma EqualGapTwoCount_step_eq__gap_count_transitions :
  forall (s : list Z) (i : Z),
    0 <= i ->
    Znth i s 0 = Znth (i + 2) s 0 ->
    EqualGapTwoCount s (i + 1) = EqualGapTwoCount s i + 1.
Proof.
  intros s i Hi Heq.
  unfold EqualGapTwoCount.
  rewrite !set_card_Z_as_sum__gap_count_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hi.
  destruct (prop_dec (Znth i s 0 = Znth (i + 2) s 0));
    [lia | contradiction].
Qed.
Lemma EqualGapTwoCount_step_neq__gap_count_transitions :
  forall (s : list Z) (i : Z),
    0 <= i ->
    Znth i s 0 <> Znth (i + 2) s 0 ->
    EqualGapTwoCount s (i + 1) = EqualGapTwoCount s i.
Proof.
  intros s i Hi Hneq.
  unfold EqualGapTwoCount.
  rewrite !set_card_Z_as_sum__gap_count_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hi.
  destruct (prop_dec (Znth i s 0 = Znth (i + 2) s 0));
    [contradiction | lia].
Qed.
Lemma Znth_app_left__gap_count_transitions :
  forall {A : Type} (default : A) (left right : list A) (i : Z),
    0 <= i < Zlength left ->
    Znth i (left ++ right) default = Znth i left default.
Proof.
  intros A default left right i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Forall_Znth_intro__final_cardinality :
  forall {A : Type} (P : A -> Prop) (l : list A) (d : A),
    (forall i, 0 <= i < Zlength l -> P (Znth i l d)) ->
    Forall P l.
Proof.
  intros A P l.
  induction l as [|a l IH]; intros d Hnth.
  - constructor.
  - constructor.
    + pose proof (Hnth 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia))
        as Hhead.
      rewrite Znth0_cons in Hhead.
      exact Hhead.
    + apply (IH d).
      intros i Hi.
      pose proof
        (Hnth (i + 1)
          ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia))
        as Htail.
      rewrite Znth_cons in Htail by lia.
      replace (i + 1 - 1) with i in Htail by lia.
      exact Htail.
Qed.
Lemma removal_at_Zlength__final_cardinality :
  forall (s : list Z) (i : Z),
    0 <= i < Zlength s - 1 ->
    Zlength (sublist 0 i s ++ sublist (i + 2) (Zlength s) s) =
      Zlength s - 2.
Proof.
  intros s i Hi.
  rewrite Zlength_app.
  rewrite Zlength_sublist by lia.
  rewrite Zlength_sublist by lia.
  lia.
Qed.
Lemma removal_at_Znth__final_cardinality :
  forall (s : list Z) (i k : Z),
    0 <= i < Zlength s - 1 ->
    0 <= k < Zlength s - 2 ->
    Znth k (sublist 0 i s ++ sublist (i + 2) (Zlength s) s) 0 =
      if Z_lt_dec k i then Znth k s 0 else Znth (k + 2) s 0.
Proof.
  intros s i k Hi Hk.
  destruct (Z_lt_dec k i) as [Hki | Hki].
  - rewrite app_Znth1.
    + apply Znth_sublist0. lia.
    + rewrite Zlength_sublist0 by lia. lia.
  - rewrite app_Znth2.
    + rewrite Zlength_sublist0 by lia.
      rewrite Znth_sublist by lia.
      f_equal. lia.
    + rewrite Zlength_sublist0 by lia. lia.
Qed.
Lemma removal_at_preserves_lowercase__final_cardinality :
  forall (s : list Z) (i : Z),
    0 <= i < Zlength s - 1 ->
    Forall (fun c => 97 <= c < 123) s ->
    Zlength (sublist 0 i s ++ sublist (i + 2) (Zlength s) s) =
      Zlength s - 2 /\
    Forall (fun c => 97 <= c < 123)
      (sublist 0 i s ++ sublist (i + 2) (Zlength s) s).
Proof.
  intros s i Hi Hlower.
  pose proof (removal_at_Zlength__final_cardinality s i Hi) as Hlen.
  split; [exact Hlen |].
  apply (Forall_Znth_intro__final_cardinality
    (fun c => 97 <= c < 123)
    (sublist 0 i s ++ sublist (i + 2) (Zlength s) s) 0).
  intros k Hk.
  rewrite Hlen in Hk.
  rewrite removal_at_Znth__final_cardinality by assumption.
  destruct (Z_lt_dec k i).
  - eapply Forall_Znth_Zlength; [exact Hlower | lia].
  - eapply Forall_Znth_Zlength; [exact Hlower | lia].
Qed.
Lemma removal_at_collision_iff_chain__final_cardinality :
  forall (s : list Z) (i j : Z),
    0 <= i < Zlength s - 1 ->
    0 <= j < Zlength s - 1 ->
    i < j ->
    (sublist 0 i s ++ sublist (i + 2) (Zlength s) s =
       sublist 0 j s ++ sublist (j + 2) (Zlength s) s <->
     forall k, i <= k < j ->
       Znth k s 0 = Znth (k + 2) s 0).
Proof.
  intros s i j Hi Hj Hij.
  split.
  - intros Heq k Hk.
    assert (Hout : 0 <= k < Zlength s - 2) by lia.
    pose proof
      (f_equal (fun l => Znth k l 0) Heq) as Hnth.
    cbn beta in Hnth.
    rewrite (removal_at_Znth__final_cardinality s i k Hi Hout) in Hnth.
    rewrite (removal_at_Znth__final_cardinality s j k Hj Hout) in Hnth.
    destruct (Z_lt_dec k i); [lia |].
    destruct (Z_lt_dec k j); [| lia].
    symmetry. exact Hnth.
  - intros Hchain.
    apply (proj2 (list_eq_ext
      (sublist 0 i s ++ sublist (i + 2) (Zlength s) s)
      (sublist 0 j s ++ sublist (j + 2) (Zlength s) s) 0)).
    split.
    + rewrite !removal_at_Zlength__final_cardinality by assumption.
      reflexivity.
    + intros k Hk.
      rewrite (removal_at_Zlength__final_cardinality s i Hi) in Hk.
      rewrite (removal_at_Znth__final_cardinality s i k Hi Hk).
      rewrite (removal_at_Znth__final_cardinality s j k Hj Hk).
      destruct (Z_lt_dec k i) as [Hki | Hki].
      * destruct (Z_lt_dec k j); [reflexivity | lia].
      * destruct (Z_lt_dec k j) as [Hkj | Hkj].
        -- symmetry. apply Hchain. lia.
        -- reflexivity.
Qed.
Lemma removal_representative_exists__final_cardinality :
  forall (s : list Z) (i : Z),
    0 <= i < Zlength s - 1 ->
    exists r,
      (0 <= r < Zlength s - 1 /\
       (r = 0 \/ Znth (r - 1) s 0 <> Znth (r + 1) s 0)) /\
      r <= i /\
      sublist 0 r s ++ sublist (r + 2) (Zlength s) s =
        sublist 0 i s ++ sublist (i + 2) (Zlength s) s.
Proof.
  intros s i Hi_initial.
  assert (Hi_nonneg : 0 <= i) by lia.
  revert Hi_initial.
  pattern i.
  apply Z_lt_induction; [| exact Hi_nonneg].
  intros i0 IH Hi.
  destruct (Z.eq_dec i0 0) as [Hi0 | Hi0].
  - subst i0.
    exists 0.
    split.
    + split; [exact Hi | tauto].
    + split; [lia | reflexivity].
  - destruct (prop_dec
      (Znth (i0 - 1) s 0 = Znth (i0 + 1) s 0)) as [Hgap | Hgap].
    + destruct (IH (i0 - 1) ltac:(lia) ltac:(lia))
        as [r [Hr [Hri Hrem]]].
      exists r.
      split; [exact Hr |].
      split; [lia |].
      transitivity
        (sublist 0 (i0 - 1) s ++
         sublist (i0 - 1 + 2) (Zlength s) s);
        [exact Hrem |].
      apply (proj2
        (removal_at_collision_iff_chain__final_cardinality
          s (i0 - 1) i0 ltac:(lia) ltac:(lia) ltac:(lia))).
      intros k Hk.
      replace k with (i0 - 1) by lia.
      replace (i0 - 1 + 2) with (i0 + 1) by lia.
      exact Hgap.
    + exists i0.
      split.
      * split; [exact Hi | right].
        exact Hgap.
      * split; [lia | reflexivity].
Qed.
Lemma removal_representative_injective__final_cardinality :
  forall (s : list Z) (i j : Z),
    (0 <= i < Zlength s - 1 /\
     (i = 0 \/ Znth (i - 1) s 0 <> Znth (i + 1) s 0)) ->
    (0 <= j < Zlength s - 1 /\
     (j = 0 \/ Znth (j - 1) s 0 <> Znth (j + 1) s 0)) ->
    sublist 0 i s ++ sublist (i + 2) (Zlength s) s =
      sublist 0 j s ++ sublist (j + 2) (Zlength s) s ->
    i = j.
Proof.
  intros s i j [Hi Hri] [Hj Hrj] Heq.
  destruct (Z.lt_trichotomy i j) as [Hij | [Hij | Hij]];
    [| exact Hij |].
  - pose proof
      (proj1 (removal_at_collision_iff_chain__final_cardinality
        s i j Hi Hj Hij) Heq (j - 1) ltac:(lia)) as Hgap.
    replace (j - 1 + 2) with (j + 1) in Hgap by lia.
    destruct Hrj as [Hj0 | Hnot]; [lia | contradiction].
  - pose proof
      (proj1 (removal_at_collision_iff_chain__final_cardinality
        s j i Hj Hi Hij) (eq_sym Heq) (i - 1) ltac:(lia)) as Hgap.
    replace (i - 1 + 2) with (i + 1) in Hgap by lia.
    destruct Hri as [Hi0 | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_bijection__final_cardinality :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> exists x, P x /\ f x = y) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmap Hsurj Hinj.
  assert (Hperm :
    Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  {
    apply NoDup_Permutation.
    - apply Injective_map_NoDup_in.
      + intros x y Hx Hy Hxy.
        apply Hinj.
        * apply (proj2 (@enum_ok A P FP x)). exact Hx.
        * apply (proj2 (@enum_ok A P FP y)). exact Hy.
        * exact Hxy.
      + exact (@enum_nodup A P FP).
    - exact (@enum_nodup B Q FQ).
    - intros y.
      rewrite in_map_iff.
      rewrite <- (@enum_ok B Q FQ y).
      split.
      + intros [x [Hfx Hxin]].
        subst y.
        apply Hmap.
        apply (proj2 (@enum_ok A P FP x)). exact Hxin.
      + intros Hy.
        destruct (Hsurj y Hy) as [x [Hx Hfx]].
        exists x. split; [exact Hfx |].
        apply (proj1 (@enum_ok A P FP x)). exact Hx.
  }
  unfold set_card, SumLib.Sum.sum.
  assert (Hmap_fold :
    fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0
      (map f (@enum A P FP)) =
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
      (@enum A P FP)).
  {
    assert (Haux : forall xs : list A,
      fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 (map f xs) =
      fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs).
    {
      induction xs as [|x xs IH].
      - reflexivity.
      - change
          (1 + fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0
            (map f xs) =
           1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs).
        rewrite IH. reflexivity.
    }
    apply Haux.
  }
  rewrite <- Hmap_fold.
  clear Hmap_fold.
  induction Hperm.
  - reflexivity.
  - change
      (1 + fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 l =
       1 + fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__final_cardinality :
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
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma removal_representative_count__final_cardinality :
  forall (s : list Z),
    3 <= Zlength s ->
    #(fun i : Z =>
        0 <= i < Zlength s - 1 /\
        (i = 0 \/ Znth (i - 1) s 0 <> Znth (i + 1) s 0)) =
      (Zlength s - 1) - EqualGapTwoCount s (Zlength s - 2).
Proof.
  intros s Hlen.
  unfold EqualGapTwoCount.
  rewrite !set_card_Z_as_sum__final_cardinality.
  rewrite (SumLib.ZRange.sum_Z_range_cons 0 (Zlength s - 1)) by lia.
  replace
    (if prop_dec
       (0 = 0 \/ Znth (0 - 1) s 0 <> Znth (0 + 1) s 0)
     then 1 else 0) with 1.
  2:{ destruct (prop_dec
        (0 = 0 \/ Znth (0 - 1) s 0 <> Znth (0 + 1) s 0));
      [reflexivity | tauto]. }
  assert (Hshift :
    SumLib.Sum.sum (fun z : Z => 0 + 1 <= z < Zlength s - 1)
      (fun z =>
        if prop_dec
          (z = 0 \/ Znth (z - 1) s 0 <> Znth (z + 1) s 0)
        then 1 else 0) =
    SumLib.Sum.sum (fun z : Z => 0 <= z < Zlength s - 2)
      (fun z =>
        if prop_dec
          (z + 1 = 0 \/
           Znth (z + 1 - 1) s 0 <> Znth (z + 1 + 1) s 0)
        then 1 else 0)).
  {
    replace (Zlength s - 1) with (Zlength s - 2 + 1) by lia.
    apply SumLib.ZRange.sum_Z_range_shift_1.
  }
  rewrite Hshift.
  assert (Hpoint :
    forall z, 0 <= z < Zlength s - 2 ->
      (if prop_dec
        (z + 1 = 0 \/
         Znth (z + 1 - 1) s 0 <> Znth (z + 1 + 1) s 0)
       then 1 else 0) =
      1 - (if prop_dec (Znth z s 0 = Znth (z + 2) s 0)
           then 1 else 0)).
  {
    intros z Hz.
    replace (z + 1 - 1) with z by lia.
    replace (z + 1 + 1) with (z + 2) by lia.
    destruct (prop_dec (Znth z s 0 = Znth (z + 2) s 0)) as [Heq | Hneq];
      destruct (prop_dec (z + 1 = 0 \/
        Znth z s 0 <> Znth (z + 2) s 0)) as [Hrep | Hrep];
      try lia; exfalso; tauto.
  }
  rewrite (SumLib.ZRange.sum_Z_range_ext
    0 (Zlength s - 2)
    (fun z =>
      if prop_dec
        (z + 1 = 0 \/
         Znth (z + 1 - 1) s 0 <> Znth (z + 1 + 1) s 0)
      then 1 else 0)
    (fun z =>
      1 - (if prop_dec (Znth z s 0 = Znth (z + 2) s 0)
           then 1 else 0)) Hpoint).
  rewrite SumLib.ZRange.sum_Z_range_sub.
  rewrite SumLib.ZRange.sum_Z_range_const by lia.
  lia.
Qed.
Lemma remove_two_spec_count__final_cardinality :
  forall (s : list Z),
    3 <= Zlength s ->
    Forall (fun c => 97 <= c <= 122) s ->
    Spec s ((Zlength s - 1) -
      EqualGapTwoCount s (Zlength s - 2)).
Proof.
  intros s Hlen Hchars.
  assert (Hlower : Forall (fun c => 97 <= c < 123) s).
  {
    apply (Forall_Znth_intro__final_cardinality
      (fun c => 97 <= c < 123) s 0).
    intros k Hk.
    pose proof (Forall_Znth_Zlength
      (fun c => 97 <= c <= 122) s 0 k Hchars Hk) as Hchar.
    destruct Hchar as [Hlo Hhi]. split; lia.
  }
  unfold Spec.
  rewrite <- removal_representative_count__final_cardinality by exact Hlen.
  eapply set_card_bijection__final_cardinality
    with (f := fun i =>
      sublist 0 i s ++ sublist (i + 2) (Zlength s) s).
  - intros i [Hi Hrep].
    split.
    + apply removal_at_preserves_lowercase__final_cardinality;
        assumption.
    + exists i. split; [exact Hi | reflexivity].
  - intros result [[Hresult_len Hresult_chars] Hresult].
    destruct Hresult as [i [Hi Hresult]].
    destruct (removal_representative_exists__final_cardinality s i Hi)
      as [r [Hr [Hri Hrem]]].
    exists r. split; [exact Hr |].
    rewrite Hresult. exact Hrem.
  - intros i j Hi Hj Heq.
    eapply removal_representative_injective__final_cardinality;
      eassumption.
Qed.
