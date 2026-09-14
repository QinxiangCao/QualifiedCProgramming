Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SumLib Require Import Sum.

Import ListNotations.
Local Open Scope Z_scope.

(** A valid climbing-stairs path consists only of one-step and two-step
    moves, and its moves add up to the target stair. *)
Definition IsClimbingStep (x : Z) : Prop := x = 1 \/ x = 2.

Definition ValidClimbingWay (n : Z) (xs : list Z) : Prop :=
  Forall IsClimbingStep xs /\ ListLib.sum xs = n.

(** This enumeration is used only to discharge the finiteness requirement
    of [SumLib.Sum.sum].  Its elements are the mathematical paths. *)
Fixpoint climbing_way_enum_pair (n : nat) :
    list (list Z) * list (list Z) :=
  match n with
  | O => ([[]], [[1]])
  | S k =>
      let previous := climbing_way_enum_pair k in
      (snd previous,
       map (cons 1) (snd previous) ++ map (cons 2) (fst previous))
  end.

Definition climbing_way_enum_nat (n : nat) : list (list Z) :=
  fst (climbing_way_enum_pair n).

Lemma climbing_way_enum_nat_S_S :
  forall n,
    climbing_way_enum_nat (S (S n)) =
    map (cons 1) (climbing_way_enum_nat (S n)) ++
    map (cons 2) (climbing_way_enum_nat n).
Proof.
  intro n.
  unfold climbing_way_enum_nat.
  simpl climbing_way_enum_pair.
  destruct (climbing_way_enum_pair n).
  reflexivity.
Qed.

Lemma climbing_steps_sum_nonnegative :
  forall xs,
    Forall IsClimbingStep xs -> 0 <= ListLib.sum xs.
Proof.
  intros xs Hsteps.
  induction Hsteps as [|x xs Hx Hsteps IH]; simpl.
  - lia.
  - unfold IsClimbingStep in Hx.
    destruct Hx as [-> | ->]; lia.
Qed.

Lemma climbing_steps_sum_zero_nil :
  forall xs,
    Forall IsClimbingStep xs ->
    ListLib.sum xs = 0 ->
    xs = [].
Proof.
  intros xs Hsteps Hsum.
  destruct xs as [|x tail]; [reflexivity |].
  inversion Hsteps as [|? ? Hx Htail]; subst.
  pose proof (climbing_steps_sum_nonnegative tail Htail).
  unfold IsClimbingStep in Hx.
  destruct Hx as [-> | ->].
  - change (1 + ListLib.sum tail = 0) in Hsum.
    exfalso. lia.
  - change (2 + ListLib.sum tail = 0) in Hsum.
    exfalso. lia.
Qed.

Lemma in_climbing_way_enum_nat :
  forall n xs,
    In xs (climbing_way_enum_nat n) <->
    Forall IsClimbingStep xs /\ ListLib.sum xs = Z.of_nat n.
Proof.
  assert (Hpair :
    forall n,
      (forall xs,
        In xs (climbing_way_enum_nat n) <->
        Forall IsClimbingStep xs /\ ListLib.sum xs = Z.of_nat n) /\
      (forall xs,
        In xs (climbing_way_enum_nat (S n)) <->
        Forall IsClimbingStep xs /\ ListLib.sum xs = Z.of_nat (S n))).
  {
    induction n as [|n [IHn IHSn]].
    - split.
      + intros xs. simpl.
        split.
        * intros [Heq | Hfalse].
          -- symmetry in Heq. subst xs.
             split; [constructor | reflexivity].
          -- contradiction.
        * intros [Hsteps Hsum].
          rewrite (climbing_steps_sum_zero_nil xs Hsteps Hsum).
          left. reflexivity.
      + intros xs. simpl.
        split.
        * intros [Heq | Hfalse].
          -- symmetry in Heq. subst xs.
             split.
             ++ constructor; [left; reflexivity | constructor].
             ++ reflexivity.
          -- contradiction.
        * intros [Hsteps Hsum].
          destruct xs as [|x tail]; [simpl in Hsum; lia |].
          inversion Hsteps as [|? ? Hx Htail]; subst.
          unfold IsClimbingStep in Hx.
          destruct Hx as [-> | ->].
          -- change (1 + ListLib.sum tail = 1) in Hsum.
             assert (Htail_sum : ListLib.sum tail = 0) by lia.
             rewrite (climbing_steps_sum_zero_nil tail Htail Htail_sum).
             left. reflexivity.
          -- pose proof (climbing_steps_sum_nonnegative tail Htail).
             change (2 + ListLib.sum tail = 1) in Hsum.
             exfalso. lia.
    - split.
      + exact IHSn.
      + intros xs. rewrite climbing_way_enum_nat_S_S.
        rewrite in_app_iff.
        split.
        * intros [Hin | Hin].
          -- apply in_map_iff in Hin as [tail [Heq Htail]].
             symmetry in Heq. subst xs.
             apply IHSn in Htail as [Hsteps Hsum].
             split.
             ++ constructor; [left; reflexivity | exact Hsteps].
             ++ change (1 + ListLib.sum tail = Z.of_nat (S (S n))).
                rewrite Hsum, !Nat2Z.inj_succ. lia.
          -- apply in_map_iff in Hin as [tail [Heq Htail]].
             symmetry in Heq. subst xs.
             apply IHn in Htail as [Hsteps Hsum].
             split.
             ++ constructor; [right; reflexivity | exact Hsteps].
             ++ change (2 + ListLib.sum tail = Z.of_nat (S (S n))).
                rewrite Hsum, !Nat2Z.inj_succ. lia.
        * intros [Hsteps Hsum].
          destruct xs as [|x tail].
          -- change (0 = Z.of_nat (S (S n))) in Hsum.
             rewrite !Nat2Z.inj_succ in Hsum.
             pose proof (Nat2Z.is_nonneg n).
             exfalso. lia.
          -- inversion Hsteps as [|? ? Hhead Htail]; subst.
             unfold IsClimbingStep in Hhead.
             destruct Hhead as [-> | ->].
             ++ left. apply in_map_iff. exists tail. split; [reflexivity |].
             apply IHSn. split; [exact Htail |].
             change (1 + ListLib.sum tail = Z.of_nat (S (S n))) in Hsum.
             rewrite !Nat2Z.inj_succ in Hsum |- *. lia.
             ++ right. apply in_map_iff. exists tail. split; [reflexivity |].
             apply IHn. split; [exact Htail |].
             change (2 + ListLib.sum tail = Z.of_nat (S (S n))) in Hsum.
             rewrite !Nat2Z.inj_succ in Hsum. lia.
  }
  intros n xs.
  exact ((proj1 (Hpair n)) xs).
Qed.

Lemma NoDup_climbing_way_enum_nat :
  forall n, NoDup (climbing_way_enum_nat n).
Proof.
  assert (Hpair :
    forall n,
      NoDup (climbing_way_enum_nat n) /\
      NoDup (climbing_way_enum_nat (S n))).
  {
    induction n as [|n [IHn IHSn]].
    - split; repeat constructor; simpl; intuition discriminate.
    - split.
      + exact IHSn.
      + rewrite climbing_way_enum_nat_S_S.
        apply NoDup_app.
        * apply FinFun.Injective_map_NoDup; [| exact IHSn].
          intros x y Heq. injection Heq. auto.
        * apply FinFun.Injective_map_NoDup; [| exact IHn].
          intros x y Heq. injection Heq. auto.
        * intros xs Hin1 Hin2.
          apply in_map_iff in Hin1 as [a [Ha _]].
          apply in_map_iff in Hin2 as [b [Hb _]].
          subst xs.
          discriminate.
  }
  intro n.
  exact (proj1 (Hpair n)).
Qed.

Definition climbing_way_enum (n : Z) : list (list Z) :=
  if Z.ltb n 0 then [] else climbing_way_enum_nat (Z.to_nat n).

Lemma climbing_way_enum_nonnegative :
  forall n,
    0 <= n ->
    climbing_way_enum n = climbing_way_enum_nat (Z.to_nat n).
Proof.
  intros n Hn.
  unfold climbing_way_enum.
  destruct (Z.ltb n 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

Lemma valid_climbing_way_sum_nonnegative :
  forall xs n,
    ValidClimbingWay n xs -> 0 <= n.
Proof.
  intros xs n [Hsteps <-].
  induction Hsteps as [|x xs Hx Hsteps IH]; simpl.
  - lia.
  - unfold IsClimbingStep in Hx.
    destruct Hx as [-> | ->]; lia.
Qed.

Lemma valid_climbing_way_enum_ok :
  forall n xs,
    ValidClimbingWay n xs <-> In xs (climbing_way_enum n).
Proof.
  intros n xs.
  unfold climbing_way_enum.
  destruct (Z.ltb n 0) eqn:Hneg.
  - apply Z.ltb_lt in Hneg.
    split.
    + intro Hvalid.
      pose proof (valid_climbing_way_sum_nonnegative xs n Hvalid).
      lia.
    + intros [].
  - apply Z.ltb_ge in Hneg.
    rewrite in_climbing_way_enum_nat.
    unfold ValidClimbingWay.
    rewrite Z2Nat.id by lia.
    tauto.
Qed.

Lemma NoDup_climbing_way_enum :
  forall n, NoDup (climbing_way_enum n).
Proof.
  intro n.
  unfold climbing_way_enum.
  destruct (Z.ltb n 0).
  - constructor.
  - apply NoDup_climbing_way_enum_nat.
Qed.

#[export] Instance finite_valid_climbing_ways (n : Z) :
  Finite (ValidClimbingWay n).
Proof.
  refine {| enum := climbing_way_enum n |}.
  - apply valid_climbing_way_enum_ok.
  - apply NoDup_climbing_way_enum.
Defined.

(** This is the direct problem specification: the result is the cardinality
    of the finite set of 1/2-step lists whose repository list sum is [n]. *)
Definition ClimbingWays (n : Z) : Z :=
  @SumLib.Sum.sum
    (list Z)
    (ValidClimbingWay n)
    (finite_valid_climbing_ways n)
    (fun _ => 1).

Definition ClimbingStairsCount (n result : Z) : Prop :=
  result = ClimbingWays n.

Lemma fold_count_is_length :
  forall (A : Type) (xs : list A),
    fold_right (fun _ acc => 1 + acc) 0 xs = Z.of_nat (length xs).
Proof.
  intros A xs.
  induction xs as [|x xs IH].
  - reflexivity.
  - change
      (1 + fold_right (fun _ acc => 1 + acc) 0 xs =
       Z.of_nat (S (length xs))).
    rewrite IH, Nat2Z.inj_succ.
    lia.
Qed.

Lemma ClimbingWays_enum_length :
  forall n,
    ClimbingWays n = Z.of_nat (length (climbing_way_enum n)).
Proof.
  intro n.
  unfold ClimbingWays, SumLib.Sum.sum.
  simpl.
  apply fold_count_is_length.
Qed.

Lemma Z_to_nat_plus_one :
  forall z, 0 <= z -> Z.to_nat (z + 1) = S (Z.to_nat z).
Proof.
  intros z Hz.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_succ.
  rewrite !Z2Nat.id by lia.
  lia.
Qed.

Lemma ClimbingWays_zero : ClimbingWays 0 = 1.
Proof.
  rewrite ClimbingWays_enum_length.
  reflexivity.
Qed.

Lemma ClimbingWays_one : ClimbingWays 1 = 1.
Proof.
  rewrite ClimbingWays_enum_length.
  reflexivity.
Qed.

Lemma ClimbingWays_next :
  forall n,
    0 <= n ->
    ClimbingWays (n + 2) = ClimbingWays (n + 1) + ClimbingWays n.
Proof.
  intros n Hn.
  rewrite !ClimbingWays_enum_length.
  rewrite (climbing_way_enum_nonnegative (n + 2)) by lia.
  rewrite (climbing_way_enum_nonnegative (n + 1)) by lia.
  rewrite (climbing_way_enum_nonnegative n) by lia.
  pose proof (Z_to_nat_plus_one n Hn) as Hnat1.
  assert (Hnat2 : Z.to_nat (n + 2) = S (S (Z.to_nat n))).
  {
    replace (n + 2) with ((n + 1) + 1) by lia.
    rewrite (Z_to_nat_plus_one (n + 1)) by lia.
    rewrite Hnat1.
    reflexivity.
  }
  rewrite Hnat2, Hnat1.
  rewrite climbing_way_enum_nat_S_S.
  rewrite length_app, !length_map.
  rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma ClimbingStairsCount_zero : ClimbingStairsCount 0 1.
Proof.
  unfold ClimbingStairsCount.
  rewrite ClimbingWays_zero.
  reflexivity.
Qed.

Lemma ClimbingStairsCount_one : ClimbingStairsCount 1 1.
Proof.
  unfold ClimbingStairsCount.
  rewrite ClimbingWays_one.
  reflexivity.
Qed.

Lemma ClimbingStairsCount_next :
  forall n prev curr,
    0 <= n ->
    ClimbingStairsCount n prev ->
    ClimbingStairsCount (n + 1) curr ->
    ClimbingStairsCount (n + 2) (prev + curr).
Proof.
  intros n prev curr Hn Hprev Hcurr.
  unfold ClimbingStairsCount in *.
  rewrite ClimbingWays_next by exact Hn.
  lia.
Qed.

Lemma ClimbingStairsCount_int_range_upto_45__loop_transition :
  forall n result,
    0 <= n ->
    n <= 45 ->
    ClimbingStairsCount n result ->
    result <= 2147483647.
Proof.
  intros n result Hn Hn45 Hcount.
  unfold ClimbingStairsCount in Hcount.
  subst result.
  assert (Hnonnegative : forall k, 0 <= ClimbingWays k).
  {
    intro k.
    rewrite ClimbingWays_enum_length.
    apply Nat2Z.is_nonneg.
  }
  assert (Hmonotone : forall k, 0 <= k -> ClimbingWays k <= ClimbingWays (k + 1)).
  {
    intros k Hk.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    - change (ClimbingWays 0 <= ClimbingWays 1).
      rewrite ClimbingWays_zero, ClimbingWays_one.
      lia.
    - pose proof (ClimbingWays_next (k - 1) ltac:(lia)) as Hnext.
      pose proof (Hnonnegative (k - 1)) as Hprev_nonnegative.
      replace (k - 1 + 2) with (k + 1) in Hnext by lia.
      replace (k - 1 + 1) with k in Hnext by lia.
      lia.
  }
  assert (Hupto45 : forall k, 0 <= k -> k <= 45 ->
      ClimbingWays k <= ClimbingWays 45).
  {
    intros k Hk Hk45.
    remember (Z.to_nat (45 - k)) as distance eqn:Hdistance.
    assert (Hdifference : 45 - k = Z.of_nat distance).
    {
      rewrite Hdistance.
      rewrite Z2Nat.id by lia.
      reflexivity.
    }
    clear Hdistance.
    revert k Hk Hk45 Hdifference.
    induction distance as [|distance IH]; intros k Hk Hk45 Hdifference.
    - change (45 - k = 0) in Hdifference.
      assert (k = 45) by lia.
      subst k.
      lia.
    - rewrite Nat2Z.inj_succ in Hdifference.
      eapply Z.le_trans.
      + apply Hmonotone.
        exact Hk.
      + apply IH; lia.
  }
  assert (Hstep : forall k a b,
      0 <= k ->
      ClimbingWays k = a ->
      ClimbingWays (k + 1) = b ->
      ClimbingWays (k + 2) = b + a).
  {
    intros k a b Hk Ha Hb.
    rewrite ClimbingWays_next by exact Hk.
    rewrite Ha, Hb.
    reflexivity.
  }
  pose proof ClimbingWays_zero as H0.
  pose proof ClimbingWays_one as H1.
  pose proof (Hstep 0 1 1 ltac:(lia) H0 H1) as H2.
  change (ClimbingWays 2 = 2) in H2.
  pose proof (Hstep 1 1 2 ltac:(lia) H1 H2) as H3.
  change (ClimbingWays 3 = 3) in H3.
  pose proof (Hstep 2 2 3 ltac:(lia) H2 H3) as H4.
  change (ClimbingWays 4 = 5) in H4.
  pose proof (Hstep 3 3 5 ltac:(lia) H3 H4) as H5.
  change (ClimbingWays 5 = 8) in H5.
  pose proof (Hstep 4 5 8 ltac:(lia) H4 H5) as H6.
  change (ClimbingWays 6 = 13) in H6.
  pose proof (Hstep 5 8 13 ltac:(lia) H5 H6) as H7.
  change (ClimbingWays 7 = 21) in H7.
  pose proof (Hstep 6 13 21 ltac:(lia) H6 H7) as H8.
  change (ClimbingWays 8 = 34) in H8.
  pose proof (Hstep 7 21 34 ltac:(lia) H7 H8) as H9.
  change (ClimbingWays 9 = 55) in H9.
  pose proof (Hstep 8 34 55 ltac:(lia) H8 H9) as H10.
  change (ClimbingWays 10 = 89) in H10.
  pose proof (Hstep 9 55 89 ltac:(lia) H9 H10) as H11.
  change (ClimbingWays 11 = 144) in H11.
  pose proof (Hstep 10 89 144 ltac:(lia) H10 H11) as H12.
  change (ClimbingWays 12 = 233) in H12.
  pose proof (Hstep 11 144 233 ltac:(lia) H11 H12) as H13.
  change (ClimbingWays 13 = 377) in H13.
  pose proof (Hstep 12 233 377 ltac:(lia) H12 H13) as H14.
  change (ClimbingWays 14 = 610) in H14.
  pose proof (Hstep 13 377 610 ltac:(lia) H13 H14) as H15.
  change (ClimbingWays 15 = 987) in H15.
  pose proof (Hstep 14 610 987 ltac:(lia) H14 H15) as H16.
  change (ClimbingWays 16 = 1597) in H16.
  pose proof (Hstep 15 987 1597 ltac:(lia) H15 H16) as H17.
  change (ClimbingWays 17 = 2584) in H17.
  pose proof (Hstep 16 1597 2584 ltac:(lia) H16 H17) as H18.
  change (ClimbingWays 18 = 4181) in H18.
  pose proof (Hstep 17 2584 4181 ltac:(lia) H17 H18) as H19.
  change (ClimbingWays 19 = 6765) in H19.
  pose proof (Hstep 18 4181 6765 ltac:(lia) H18 H19) as H20.
  change (ClimbingWays 20 = 10946) in H20.
  pose proof (Hstep 19 6765 10946 ltac:(lia) H19 H20) as H21.
  change (ClimbingWays 21 = 17711) in H21.
  pose proof (Hstep 20 10946 17711 ltac:(lia) H20 H21) as H22.
  change (ClimbingWays 22 = 28657) in H22.
  pose proof (Hstep 21 17711 28657 ltac:(lia) H21 H22) as H23.
  change (ClimbingWays 23 = 46368) in H23.
  pose proof (Hstep 22 28657 46368 ltac:(lia) H22 H23) as H24.
  change (ClimbingWays 24 = 75025) in H24.
  pose proof (Hstep 23 46368 75025 ltac:(lia) H23 H24) as H25.
  change (ClimbingWays 25 = 121393) in H25.
  pose proof (Hstep 24 75025 121393 ltac:(lia) H24 H25) as H26.
  change (ClimbingWays 26 = 196418) in H26.
  pose proof (Hstep 25 121393 196418 ltac:(lia) H25 H26) as H27.
  change (ClimbingWays 27 = 317811) in H27.
  pose proof (Hstep 26 196418 317811 ltac:(lia) H26 H27) as H28.
  change (ClimbingWays 28 = 514229) in H28.
  pose proof (Hstep 27 317811 514229 ltac:(lia) H27 H28) as H29.
  change (ClimbingWays 29 = 832040) in H29.
  pose proof (Hstep 28 514229 832040 ltac:(lia) H28 H29) as H30.
  change (ClimbingWays 30 = 1346269) in H30.
  pose proof (Hstep 29 832040 1346269 ltac:(lia) H29 H30) as H31.
  change (ClimbingWays 31 = 2178309) in H31.
  pose proof (Hstep 30 1346269 2178309 ltac:(lia) H30 H31) as H32.
  change (ClimbingWays 32 = 3524578) in H32.
  pose proof (Hstep 31 2178309 3524578 ltac:(lia) H31 H32) as H33.
  change (ClimbingWays 33 = 5702887) in H33.
  pose proof (Hstep 32 3524578 5702887 ltac:(lia) H32 H33) as H34.
  change (ClimbingWays 34 = 9227465) in H34.
  pose proof (Hstep 33 5702887 9227465 ltac:(lia) H33 H34) as H35.
  change (ClimbingWays 35 = 14930352) in H35.
  pose proof (Hstep 34 9227465 14930352 ltac:(lia) H34 H35) as H36.
  change (ClimbingWays 36 = 24157817) in H36.
  pose proof (Hstep 35 14930352 24157817 ltac:(lia) H35 H36) as H37.
  change (ClimbingWays 37 = 39088169) in H37.
  pose proof (Hstep 36 24157817 39088169 ltac:(lia) H36 H37) as H38.
  change (ClimbingWays 38 = 63245986) in H38.
  pose proof (Hstep 37 39088169 63245986 ltac:(lia) H37 H38) as H39.
  change (ClimbingWays 39 = 102334155) in H39.
  pose proof (Hstep 38 63245986 102334155 ltac:(lia) H38 H39) as H40.
  change (ClimbingWays 40 = 165580141) in H40.
  pose proof (Hstep 39 102334155 165580141 ltac:(lia) H39 H40) as H41.
  change (ClimbingWays 41 = 267914296) in H41.
  pose proof (Hstep 40 165580141 267914296 ltac:(lia) H40 H41) as H42.
  change (ClimbingWays 42 = 433494437) in H42.
  pose proof (Hstep 41 267914296 433494437 ltac:(lia) H41 H42) as H43.
  change (ClimbingWays 43 = 701408733) in H43.
  pose proof (Hstep 42 433494437 701408733 ltac:(lia) H42 H43) as H44.
  change (ClimbingWays 44 = 1134903170) in H44.
  pose proof (Hstep 43 701408733 1134903170 ltac:(lia) H43 H44) as H45.
  change (ClimbingWays 45 = 1836311903) in H45.
  assert (Hmax : ClimbingWays 45 <= 2147483647).
  {
    rewrite H45.
    lia.
  }
  eapply Z.le_trans.
  - apply Hupto45; assumption.
  - exact Hmax.
Qed.
