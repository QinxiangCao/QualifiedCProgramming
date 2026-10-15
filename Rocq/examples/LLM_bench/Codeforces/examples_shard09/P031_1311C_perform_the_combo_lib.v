Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Count (x : Z) (xs : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x).

Definition Pre (s tries : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P031 solver Require, which
     therefore omits the Pre(text, tries) call:
       2 <= Zlength s <= 200000 /\
       1 <= Zlength tries <= 200000 /\
       Forall (fun c => 97 <= c <= 122) s /\
       Forall (fun p => 1 <= p < Zlength s) tries. *)
  True.

Definition Spec (s tries out : list Z) : Prop :=
  Zlength out = 26 /\
  forall c, 97 <= c <= 122 ->
    Znth (c - 97) out 0 =
      Count c s +
      (fold_right Z.add 0) (map (fun p => Count c (sublist 0 p s)) tries).

Definition DifferencePrefix
    (tries : list Z) (n i : Z) (diff_values : list Z) : Prop :=
  Zlength diff_values = n + 1 /\
  Znth 0 diff_values 0 = i /\
  forall k, 1 <= k <= n ->
    Znth k diff_values 0 = - Count k (sublist 0 i tries).

Definition DifferenceReady
    (tries : list Z) (n : Z) (diff_values : list Z) : Prop :=
  Zlength diff_values = n + 1 /\
  Znth 0 diff_values 0 = Zlength tries + 1 /\
  forall k, 1 <= k <= n ->
    Znth k diff_values 0 = - Count k tries.

Definition PartialSpec
    (s tries : list Z) (done : Z) (out : list Z) : Prop :=
  Zlength out = 26 /\
  forall c, 97 <= c <= 122 ->
    Znth (c - 97) out 0 =
      Count c (sublist 0 done s) +
      (fold_right Z.add 0)
        (map (fun p => Count c (sublist 0 (Z.min p done) s)) tries).

Require Import Coq.micromega.Lia.
Lemma replace_nth_length__difference_updates :
  forall (i : nat) (value : Z) (xs : list Z),
    length (replace_nth i xs value) = length xs.
Proof.
  intros i value xs.
  revert xs.
  induction i as [|i IH]; intros xs; destruct xs; simpl; auto.
Qed.
Lemma Zlength_replace_Znth__difference_updates :
  forall (i value : Z) (xs : list Z),
    Zlength (replace_Znth i value xs) = Zlength xs.
Proof.
  intros i value xs.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length__difference_updates.
  reflexivity.
Qed.
Lemma set_card_iff__difference_updates :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros z.
      rewrite <- (@enum_ok A P FP z), <- (@enum_ok A Q FQ z).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__difference_updates :
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
Lemma set_card_Z_extend_true__difference_updates :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__difference_updates.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__difference_updates :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__difference_updates.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma count_sublist_succ_eq__difference_updates :
  forall (x : Z) (xs : list Z) (i : Z),
    0 <= i < Zlength xs ->
    Znth i xs 0 = x ->
    Count x (sublist 0 (i + 1) xs) =
    Count x (sublist 0 i xs) + 1.
Proof.
  intros x xs i Hi Heq.
  unfold Count.
  rewrite !Zlength_sublist0 by lia.
  assert (Hsucc :
    #(fun z : Z => 0 <= z < i + 1 /\
      Znth z (sublist 0 (i + 1) xs) 0 = x) =
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z xs 0 = x)).
  {
    apply set_card_iff__difference_updates.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  assert (Hold :
    #(fun z : Z => 0 <= z < i /\ Znth z (sublist 0 i xs) 0 = x) =
    #(fun z : Z => 0 <= z < i /\ Znth z xs 0 = x)).
  {
    apply set_card_iff__difference_updates.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  rewrite Hsucc, Hold.
  apply set_card_Z_extend_true__difference_updates; [lia | exact Heq].
Qed.
Lemma count_sublist_succ_neq__difference_updates :
  forall (x : Z) (xs : list Z) (i : Z),
    0 <= i < Zlength xs ->
    Znth i xs 0 <> x ->
    Count x (sublist 0 (i + 1) xs) =
    Count x (sublist 0 i xs).
Proof.
  intros x xs i Hi Hneq.
  unfold Count.
  rewrite !Zlength_sublist0 by lia.
  assert (Hsucc :
    #(fun z : Z => 0 <= z < i + 1 /\
      Znth z (sublist 0 (i + 1) xs) 0 = x) =
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z xs 0 = x)).
  {
    apply set_card_iff__difference_updates.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  assert (Hold :
    #(fun z : Z => 0 <= z < i /\ Znth z (sublist 0 i xs) 0 = x) =
    #(fun z : Z => 0 <= z < i /\ Znth z xs 0 = x)).
  {
    apply set_card_iff__difference_updates.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  rewrite Hsucc, Hold.
  apply set_card_Z_extend_false__difference_updates; [lia | exact Hneq].
Qed.
Lemma difference_prefix_step__difference_updates :
  forall (tries : list Z) (n i : Z) (diff_values : list Z),
    0 <= i < Zlength tries ->
    (forall j, 0 <= j < Zlength tries ->
      1 <= Znth j tries 0 < n) ->
    DifferencePrefix tries n i diff_values ->
    DifferencePrefix tries n (i + 1)
      (replace_Znth (Znth i tries 0)
        (Znth (Znth i tries 0)
          (replace_Znth 0 (Znth 0 diff_values 0 + 1) diff_values) 0 - 1)
        (replace_Znth 0 (Znth 0 diff_values 0 + 1) diff_values)).
Proof.
  intros tries n i diff_values Hi Htries Hprefix.
  destruct Hprefix as [Hlen [Hzero Hpoint]].
  specialize (Htries i Hi) as Hbucket.
  unfold DifferencePrefix.
  split.
  - rewrite !Zlength_replace_Znth__difference_updates. exact Hlen.
  - split.
    + rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth__difference_updates; lia).
      rewrite Znth_replace_Znth_Same by lia.
      lia.
    + intros k Hk.
      destruct (Z.eq_dec k (Znth i tries 0)) as [Heq | Hneq].
      * subst k.
        rewrite Znth_replace_Znth_Same by
          (rewrite ?Zlength_replace_Znth__difference_updates; lia).
        rewrite Znth_replace_Znth_Diff by lia.
        rewrite Hpoint by lia.
        rewrite count_sublist_succ_eq__difference_updates by auto.
        lia.
      * rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth__difference_updates; lia).
        rewrite Znth_replace_Znth_Diff by lia.
        rewrite Hpoint by lia.
        rewrite count_sublist_succ_neq__difference_updates by auto.
        reflexivity.
Qed.
Lemma difference_ready_at_exit__difference_updates :
  forall (tries : list Z) (n i : Z) (diff_values : list Z),
    0 <= n ->
    i = Zlength tries ->
    DifferencePrefix tries n i diff_values ->
    DifferenceReady tries n
      (replace_Znth 0 (Znth 0 diff_values 0 + 1) diff_values).
Proof.
  intros tries n i diff_values Hn Hi Hprefix.
  destruct Hprefix as [Hlen [Hzero Hpoint]].
  pose proof (Zlength_nonneg diff_values) as Hlen_nonneg.
  unfold DifferenceReady.
  split.
  - rewrite Zlength_replace_Znth__difference_updates. exact Hlen.
  - split.
    + rewrite Znth_replace_Znth_Same by lia. lia.
    + intros k Hk.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hpoint by lia.
      subst i.
      rewrite sublist_self by reflexivity.
      reflexivity.
Qed.
Lemma Count_nil__count_initialization :
  forall x, Count x (@nil Z) = 0.
Proof.
  intros x.
  unfold Count, set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  reflexivity.
Qed.
Lemma set_card_Z_as_sum__coverage_and_output_step :
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
Lemma fold_sum_zero__coverage_and_output_step :
  forall {A : Type} (xs : list A),
    fold_right (fun _ acc => 0 + acc) 0 xs = 0.
Proof.
  intros A xs. induction xs; simpl; auto.
Qed.
Lemma fold_sum_add__coverage_and_output_step :
  forall {A : Type} (xs : list A) (f g : A -> Z),
    fold_right (fun x acc => (f x + g x) + acc) 0 xs =
    fold_right (fun x acc => f x + acc) 0 xs +
    fold_right (fun x acc => g x + acc) 0 xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros f g; simpl; [lia |].
  rewrite IH. lia.
Qed.
Lemma fold_sum_nested_swap__coverage_and_output_step :
  forall {A B : Type} (xs : list A) (ys : list B) (f : A -> B -> Z),
    fold_right
      (fun x acc => fold_right (fun y acc' => f x y + acc') 0 ys + acc)
      0 xs =
    fold_right
      (fun y acc => fold_right (fun x acc' => f x y + acc') 0 xs + acc)
      0 ys.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - rewrite fold_sum_zero__coverage_and_output_step. reflexivity.
  - rewrite IH.
    rewrite <- fold_sum_add__coverage_and_output_step.
    reflexivity.
Qed.
Lemma sum_Z_range_swap__coverage_and_output_step :
  forall (xlow xhigh ylow yhigh : Z) (f : Z -> Z -> Z),
    SumLib.Sum.sum (fun x => xlow <= x < xhigh)
      (fun x => SumLib.Sum.sum (fun y => ylow <= y < yhigh) (fun y => f x y)) =
    SumLib.Sum.sum (fun y => ylow <= y < yhigh)
      (fun y => SumLib.Sum.sum (fun x => xlow <= x < xhigh) (fun x => f x y)).
Proof.
  intros.
  unfold SumLib.Sum.sum.
  apply fold_sum_nested_swap__coverage_and_output_step.
Qed.
Lemma Count_as_index_sum__coverage_and_output_step :
  forall x xs,
    Count x xs =
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength xs)
      (fun i => if Z.eq_dec (Znth i xs 0) x then 1 else 0).
Proof.
  intros x xs.
  unfold Count.
  rewrite set_card_Z_as_sum__coverage_and_output_step.
  apply SumLib.Sum.sum_ext.
  intros i Hi.
  destruct (prop_dec (Znth i xs 0 = x));
    destruct (Z.eq_dec (Znth i xs 0) x); try contradiction; reflexivity.
Qed.
Lemma indicator_range_sum__coverage_and_output_step :
  forall p j,
    1 <= p -> 0 <= j ->
    SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
      (fun k => if Z.eq_dec p k then 1 else 0) =
    if Z_le_dec p j then 1 else 0.
Proof.
  intros p j Hp Hj.
  destruct (Z_le_dec p j) as [Hpj | Hpj].
  - rewrite (SumLib.ZRange.sum_Z_range_split 1 p (j + 1)) by lia.
    rewrite (SumLib.ZRange.sum_Z_range_split p (p + 1) (j + 1)) by lia.
    rewrite SumLib.ZRange.sum_Z_range_single.
    rewrite !SumLib.ZRange.sum_Z_range_eq_zero.
    + destruct (Z.eq_dec p p); lia.
    + intros k Hk. destruct (Z.eq_dec p k); lia.
    + intros k Hk. destruct (Z.eq_dec p k); lia.
  - rewrite SumLib.ZRange.sum_Z_range_eq_zero.
    + reflexivity.
    + intros k Hk. destruct (Z.eq_dec p k); lia.
Qed.
Lemma sum_Count_prefix_bounds__coverage_and_output_step :
  forall tries j,
    0 <= j ->
    (forall i, 0 <= i < Zlength tries -> 1 <= Znth i tries 0) ->
    0 <= SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
           (fun k => Count k tries) <= Zlength tries.
Proof.
  intros tries j Hj Htries.
  assert (Hswap :
    SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
      (fun k => Count k tries) =
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i => if Z_le_dec (Znth i tries 0) j then 1 else 0)).
  {
    transitivity
      (SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
        (fun k => SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
          (fun i => if Z.eq_dec (Znth i tries 0) k then 1 else 0))).
    - apply SumLib.Sum.sum_ext. intros k Hk.
      apply Count_as_index_sum__coverage_and_output_step.
    - rewrite sum_Z_range_swap__coverage_and_output_step.
      apply SumLib.Sum.sum_ext. intros i Hi.
      rewrite indicator_range_sum__coverage_and_output_step by
          (try apply Htries; lia).
      reflexivity.
  }
  rewrite Hswap.
  assert (Hpoint : forall i, 0 <= i < Zlength tries ->
    0 <= (if Z_le_dec (Znth i tries 0) j then 1 else 0) <= 1).
  {
    intros i Hi. destruct (Z_le_dec (Znth i tries 0) j); simpl; lia.
  }
  pose proof (SumLib.ZRange.sum_Z_range_bounds
    0 (Zlength tries)
    (fun i => if Z_le_dec (Znth i tries 0) j then 1 else 0)
    0 1 ltac:(pose proof (Zlength_nonneg tries); lia)
    Hpoint) as Hbounds.
  nia.
Qed.
Lemma coverage_prefix_formula__coverage_and_output_step :
  forall tries n diff j,
    DifferenceReady tries n diff ->
    0 <= j < n ->
    ListLib.sum (sublist 0 (j + 1) diff) =
      Zlength tries + 1 -
      SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
        (fun k => Count k tries).
Proof.
  intros tries n diff j Hready Hj.
  unfold DifferenceReady in Hready.
  destruct Hready as [Hlen [Hzero Hpoint]].
  rewrite SumLib.ZRange.list_sum_sublist_as_Z_range_sum by lia.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 1 (j + 1)) by lia.
  rewrite SumLib.ZRange.sum_Z_range_single.
  rewrite Hzero.
  assert (Hrest :
    SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
      (fun k => Znth k diff 0) =
    SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
      (fun k => - Count k tries)).
  {
    apply SumLib.Sum.sum_ext. intros k Hk.
    apply Hpoint. lia.
  }
  rewrite Hrest, SumLib.Sum.sum_opp.
  ring.
Qed.
Lemma coverage_prefix_step__coverage_and_output_step :
  forall tries n diff j cover,
    DifferenceReady tries n diff ->
    0 <= j < n ->
    (forall i, 0 <= i < Zlength tries -> 1 <= Znth i tries 0) ->
    cover = ListLib.sum (sublist 0 j diff) ->
    cover + Znth j diff 0 = ListLib.sum (sublist 0 (j + 1) diff) /\
    0 <= cover + Znth j diff 0 <= Zlength tries + 1.
Proof.
  intros tries n diff j cover Hready Hj Htries Hcover.
  assert (Hlen : Zlength diff = n + 1).
  { unfold DifferenceReady in Hready. tauto. }
  assert (Hstep :
    ListLib.sum (sublist 0 (j + 1) diff) =
    ListLib.sum (sublist 0 j diff) + Znth j diff 0).
  {
    rewrite (sublist_split 0 (j + 1) j diff) by lia.
    rewrite ListLib.sum_app.
    rewrite (sublist_single 0 j diff) by lia.
    simpl; lia.
  }
  assert (Hformula := coverage_prefix_formula__coverage_and_output_step
    tries n diff j Hready Hj).
  assert (Hbounds := sum_Count_prefix_bounds__coverage_and_output_step
    tries j ltac:(lia) Htries).
  split; [lia |].
  rewrite Hstep in Hformula.
  lia.
Qed.
Lemma sum_Count_prefix_as_indicators__coverage_and_output_step :
  forall tries j,
    0 <= j ->
    (forall i, 0 <= i < Zlength tries -> 1 <= Znth i tries 0) ->
    SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
      (fun k => Count k tries) =
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i => if Z_le_dec (Znth i tries 0) j then 1 else 0).
Proof.
  intros tries j Hj Htries.
  transitivity
    (SumLib.Sum.sum (fun k : Z => 1 <= k < j + 1)
      (fun k => SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
        (fun i => if Z.eq_dec (Znth i tries 0) k then 1 else 0))).
  - apply SumLib.Sum.sum_ext. intros k Hk.
    apply Count_as_index_sum__coverage_and_output_step.
  - rewrite sum_Z_range_swap__coverage_and_output_step.
    apply SumLib.Sum.sum_ext. intros i Hi.
    rewrite indicator_range_sum__coverage_and_output_step by
        (try apply Htries; lia).
    reflexivity.
Qed.
Lemma indicator_partition__coverage_and_output_step :
  forall tries j,
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i => if Z_le_dec (Znth i tries 0) j then 1 else 0) +
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i => if Z_lt_dec j (Znth i tries 0) then 1 else 0) =
    Zlength tries.
Proof.
  intros tries j.
  rewrite <- SumLib.ZRange.sum_Z_range_add.
  transitivity
    (SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries) (fun _ => 1)).
  - apply SumLib.Sum.sum_ext. intros i Hi.
    destruct (Z_le_dec (Znth i tries 0) j);
      destruct (Z_lt_dec j (Znth i tries 0)); simpl; lia.
  - rewrite SumLib.ZRange.sum_Z_range_const by
        (pose proof (Zlength_nonneg tries); lia).
    ring.
Qed.
Lemma Count_sublist_step__coverage_and_output_step :
  forall c s j,
    0 <= j < Zlength s ->
    Count c (sublist 0 (j + 1) s) =
    Count c (sublist 0 j s) +
      (if Z.eq_dec (Znth j s 0) c then 1 else 0).
Proof.
  intros c s j Hj.
  unfold Count.
  rewrite !set_card_Z_as_sum__coverage_and_output_step.
  rewrite !Zlength_sublist0 by lia.
  assert (Hnew :
    SumLib.Sum.sum (fun i : Z => 0 <= i < j + 1)
      (fun i => if prop_dec (Znth i (sublist 0 (j + 1) s) 0 = c)
                then 1 else 0) =
    SumLib.Sum.sum (fun i : Z => 0 <= i < j + 1)
      (fun i => if Z.eq_dec (Znth i s 0) c then 1 else 0)).
  {
    apply SumLib.Sum.sum_ext. intros i Hi.
    rewrite Znth_sublist0 by lia.
    destruct (prop_dec (Znth i s 0 = c));
      destruct (Z.eq_dec (Znth i s 0) c); try contradiction; reflexivity.
  }
  assert (Hold :
    SumLib.Sum.sum (fun i : Z => 0 <= i < j)
      (fun i => if prop_dec (Znth i (sublist 0 j s) 0 = c)
                then 1 else 0) =
    SumLib.Sum.sum (fun i : Z => 0 <= i < j)
      (fun i => if Z.eq_dec (Znth i s 0) c then 1 else 0)).
  {
    apply SumLib.Sum.sum_ext. intros i Hi.
    rewrite Znth_sublist0 by lia.
    destruct (prop_dec (Znth i s 0 = c));
      destruct (Z.eq_dec (Znth i s 0) c); try contradiction; reflexivity.
  }
  rewrite Hnew, Hold.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
  reflexivity.
Qed.
Lemma fold_min_prefix_step__coverage_and_output_step :
  forall s tries j c,
    0 <= j < Zlength s ->
    fold_right Z.add 0
      (map (fun p => Count c (sublist 0 (Z.min p (j + 1)) s)) tries) =
    fold_right Z.add 0
      (map (fun p => Count c (sublist 0 (Z.min p j) s)) tries) +
    (if Z.eq_dec (Znth j s 0) c then 1 else 0) *
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i => if Z_lt_dec j (Znth i tries 0) then 1 else 0).
Proof.
  intros s tries j c Hj.
  change (
    ListLib.sum
      (map (fun p : Z => Count c (sublist 0 (Z.min p (j + 1)) s)) tries) =
    ListLib.sum
      (map (fun p : Z => Count c (sublist 0 (Z.min p j) s)) tries) +
    (if Z.eq_dec (Znth j s 0) c then 1 else 0) *
    SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i => if Z_lt_dec j (Znth i tries 0) then 1 else 0)).
  rewrite !SumLib.ZRange.list_sum_map_as_Z_range_sum with (default := 0).
  transitivity
    (SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
      (fun i =>
        Count c (sublist 0 (Z.min (Znth i tries 0) j) s) +
        (if Z.eq_dec (Znth j s 0) c then 1 else 0) *
        (if Z_lt_dec j (Znth i tries 0) then 1 else 0))).
  - apply SumLib.Sum.sum_ext. intros i Hi.
    destruct (Z_lt_dec j (Znth i tries 0)) as [Hgt | Hle].
    + replace (Z.min (Znth i tries 0) (j + 1)) with (j + 1) by
          (symmetry; apply Z.min_r; lia).
      replace (Z.min (Znth i tries 0) j) with j by
          (symmetry; apply Z.min_r; lia).
      rewrite Count_sublist_step__coverage_and_output_step by exact Hj.
      destruct (Z.eq_dec (Znth j s 0) c); simpl; lia.
    + assert (Hp : Znth i tries 0 <= j) by lia.
      replace (Z.min (Znth i tries 0) (j + 1)) with (Znth i tries 0) by
          (symmetry; apply Z.min_l; lia).
      replace (Z.min (Znth i tries 0) j) with (Znth i tries 0) by
          (symmetry; apply Z.min_l; lia).
      simpl. destruct (Z_lt_dec j (Znth i tries 0)); [lia | ring].
  - rewrite SumLib.ZRange.sum_Z_range_add.
    rewrite SumLib.ZRange.sum_Z_range_factor_l.
    ring.
Qed.
Lemma Zlength_replace_Znth__coverage_and_output_step :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l as [|a l IH]; intros n; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. rewrite !Zlength_cons. lia.
  - simpl. rewrite !Zlength_cons.
    specialize (IH (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    rewrite IH. lia.
Qed.
Lemma partial_spec_step__coverage_and_output_step :
  forall s tries diff n j cover out,
    DifferenceReady tries n diff ->
    0 <= j < n ->
    n = Zlength s ->
    (forall i, 0 <= i < Zlength tries -> 1 <= Znth i tries 0) ->
    97 <= Znth j s 0 <= 122 ->
    cover = ListLib.sum (sublist 0 (j + 1) diff) ->
    PartialSpec s tries j out ->
    PartialSpec s tries (j + 1)
      (replace_Znth (Znth j s 0 - 97)
        (Znth (Znth j s 0 - 97) out 0 + cover) out).
Proof.
  intros s tries diff n j cover out Hready Hj Hslen Htries Hchar
    Hcover Hpartial.
  unfold PartialSpec in Hpartial |- *.
  destruct Hpartial as [Hout Hpartial].
  split.
  - rewrite Zlength_replace_Znth__coverage_and_output_step. exact Hout.
  - intros c Hc.
    specialize (Hpartial c Hc).
    assert (Hjlen : 0 <= j < Zlength s) by lia.
    pose proof (Count_sublist_step__coverage_and_output_step c s j Hjlen)
      as Hcount.
    pose proof (fold_min_prefix_step__coverage_and_output_step
      s tries j c Hjlen) as Hfold.
    pose proof (coverage_prefix_formula__coverage_and_output_step
      tries n diff j Hready Hj) as Hformula.
    pose proof (sum_Count_prefix_as_indicators__coverage_and_output_step
      tries j ltac:(lia) Htries) as Hcountsum.
    pose proof (indicator_partition__coverage_and_output_step tries j)
      as Hpartition.
    assert (Hcoverage :
      cover = 1 +
        SumLib.Sum.sum (fun i : Z => 0 <= i < Zlength tries)
          (fun i => if Z_lt_dec j (Znth i tries 0) then 1 else 0)) by lia.
    destruct (Z.eq_dec (Znth j s 0) c) as [Heq | Hneq].
    + subst c.
      rewrite Znth_replace_Znth_Same by lia.
      destruct (Z.eq_dec (Znth j s 0) (Znth j s 0)); [| contradiction].
      lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      destruct (Z.eq_dec (Znth j s 0) c); [contradiction |].
      lia.
Qed.
Lemma In_Znth_Zlength__final_result {A : Type} :
  forall (l : list A) (x d : A),
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros l x d Hin.
  pose proof (@In_nth A l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
Qed.
Lemma partial_spec_complete__final_result :
  forall s tries done out,
    done = Zlength s ->
    (forall k, 0 <= k < Zlength tries ->
       1 <= Znth k tries 0 < Zlength s) ->
    PartialSpec s tries done out ->
    Spec s tries out.
Proof.
  intros s tries done out Hdone Htries Hpartial.
  unfold PartialSpec in Hpartial.
  unfold Spec.
  destruct Hpartial as [Hlength Hcount].
  split.
  - exact Hlength.
  - intros c Hc.
    specialize (Hcount c Hc).
    rewrite (sublist_self s done Hdone) in Hcount.
    rewrite Hcount.
    f_equal.
    apply f_equal.
    apply map_ext_in.
    intros p Hp.
    rewrite Z.min_l.
    + reflexivity.
    + rewrite Hdone.
      destruct (In_Znth_Zlength__final_result tries p 0 Hp)
        as (i & Hi & Hip).
      specialize (Htries i Hi).
      rewrite Hip in Htries.
      lia.
Qed.
