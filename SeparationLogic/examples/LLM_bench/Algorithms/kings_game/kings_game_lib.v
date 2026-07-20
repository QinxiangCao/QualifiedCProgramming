Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** A minister is modelled independently of the flat C representation.  The
    two components are respectively the left- and right-hand positive
    integers. *)
Definition minister : Type := (Z * Z)%type.

Definition mk_minister (left right : Z) : minister := (left, right).
Definition minister_left (p : minister) : Z := fst p.
Definition minister_right (p : minister) : Z := snd p.
Definition minister_product (p : minister) : Z :=
  minister_left p * minister_right p.
Definition default_minister : minister := mk_minister 1 1.

(** The memory relation deliberately says only how a mathematical sequence
    of ministers is flattened into the C int array. *)
Definition minister_flatten (ps : list minister) : list Z :=
  flat_map (fun p => [minister_left p; minister_right p]) ps.

Definition FlatMinisters (flat : list Z) (ps : list minister) : Prop :=
  flat = minister_flatten ps.

Definition MinisterHandsBound (ps : list minister) : Prop :=
  Forall
    (fun p =>
       1 <= minister_left p <= 10 /\
       1 <= minister_right p <= 10)
    ps.

Definition MinisterPermutation : list minister -> list minister -> Prop :=
  @Permutation minister.

(** The greedy key and its mathematical sortedness property. *)
Definition MinisterProductLe (p q : minister) : Prop :=
  minister_product p <= minister_product q.

Definition MinisterSorted (ps : list minister) : Prop :=
  forall i j,
    0 <= i -> i <= j -> j < Zlength ps ->
    MinisterProductLe
      (Znth i ps default_minister)
      (Znth j ps default_minister).

(** Product of all left hands strictly before [i].  This is a mathematical
    prefix product, not a mirror of either sorting loop in the C program. *)
Definition PrefixLeftProduct (ps : list minister) (i : Z) : Z :=
  fold_right Z.mul 1
    (map minister_left (sublist 0 i ps)).

Definition MinisterReward
    (king_left : Z) (ps : list minister) (i : Z) : Z :=
  (king_left * PrefixLeftProduct ps i) /
  minister_right (Znth i ps default_minister).

(** The largest reward for one fixed order is defined with MaxMinLib. *)
Definition OrderMaxReward
    (king_left : Z) (ps : list minister) (reward : Z) : Prop :=
  max_value_of_subset Z.le
    (fun i : Z => 0 <= i < Zlength ps)
    (fun i => MinisterReward king_left ps i)
    reward.

(** Candidates for the outer minimization pair an order with the maximum
    reward realised by that order. *)
Definition ValidOrderReward
    (input : list minister) (king_left : Z)
    (candidate : list minister * Z) : Prop :=
  MinisterPermutation input (fst candidate) /\
  OrderMaxReward king_left (fst candidate) (snd candidate).

(** The problem's minimax optimum: minimum, over every permutation of the
    input ministers, of that order's maximum reward. *)
Definition KingsGameOptimum
    (input : list minister) (king_left optimum : Z) : Prop :=
  min_value_of_subset Z.le
    (ValidOrderReward input king_left)
    (@snd (list minister) Z)
    optimum.

(** Final business predicate exposed to the C specification.  In particular,
    the output itself realises the MaxMinLib-defined optimum; sortedness alone
    is not accepted as the result. *)
Definition KingsGameResult
    (input : list minister) (king_left : Z) (output : list minister) : Prop :=
  MinisterPermutation input output /\
  MinisterSorted output /\
  exists reward,
    OrderMaxReward king_left output reward /\
    KingsGameOptimum input king_left reward.

(** Exact mathematical effects of swapping two flat minister records. *)
Definition minister_swap
    (ps : list minister) (i j : Z) : list minister :=
  replace_Znth j (Znth i ps default_minister)
    (replace_Znth i (Znth j ps default_minister) ps).

Definition minister_swap_flat
    (flat : list Z) (i j : Z) : list Z :=
  let il := Znth (2 * i) flat 0 in
  let ir := Znth (2 * i + 1) flat 0 in
  let jl := Znth (2 * j) flat 0 in
  let jr := Znth (2 * j + 1) flat 0 in
  replace_Znth (2 * j + 1) ir
    (replace_Znth (2 * j) il
      (replace_Znth (2 * i + 1) jr
        (replace_Znth (2 * i) jl flat))).

(** Predicate-first bubble-sort invariants.  [BubbleOuterProperty] says that
    the last [pass] records are sorted and dominate the remaining prefix.
    [BubbleScanProperty] says that position [j] contains a maximum greedy key
    of the scanned prefix. *)
Definition BubbleOuterProperty
    (ps : list minister) (n pass : Z) : Prop :=
  Zlength ps = n /\
  (forall i j,
      n - pass <= i -> i <= j -> j < n ->
      MinisterProductLe
        (Znth i ps default_minister)
        (Znth j ps default_minister)) /\
  (forall i j,
      0 <= i -> i < n - pass ->
      n - pass <= j -> j < n ->
      MinisterProductLe
        (Znth i ps default_minister)
        (Znth j ps default_minister)).

Definition BubbleScanProperty
    (ps : list minister) (n pass j : Z) : Prop :=
  0 <= j < n - pass /\
  forall k,
    0 <= k -> k <= j ->
    MinisterProductLe
      (Znth k ps default_minister)
      (Znth j ps default_minister).

Require Import Coq.micromega.Lia.
Lemma minister_flatten_Zlength__flat_bubble :
  forall ps,
    Zlength (minister_flatten ps) = 2 * Zlength ps.
Proof.
  unfold minister_flatten.
  induction ps as [| [x y] ps IH]; simpl.
  - reflexivity.
  - rewrite !Zlength_cons, IH.
    change (Z.succ (Z.succ (2 * Zlength ps)) =
      2 * Z.succ (Zlength ps)).
    rewrite Z.mul_succ_r.
    lia.
Qed.
Lemma minister_flatten_Znth_pair__flat_bubble :
  forall ps i,
    0 <= i < Zlength ps ->
    Znth (2 * i) (minister_flatten ps) 0 =
      minister_left (Znth i ps default_minister) /\
    Znth (2 * i + 1) (minister_flatten ps) 0 =
      minister_right (Znth i ps default_minister).
Proof.
  unfold minister_flatten.
  induction ps as [| [x y] ps IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + unfold Znth, minister_left, minister_right, default_minister,
        mk_minister.
      cbn.
      auto.
    + assert (0 < i) by lia.
      change
        (Znth (2 * i) (x :: y :: flat_map
          (fun p : minister => [minister_left p; minister_right p]) ps) 0 =
           minister_left (Znth i ((x, y) :: ps) default_minister) /\
         Znth (2 * i + 1) (x :: y :: flat_map
          (fun p : minister => [minister_left p; minister_right p]) ps) 0 =
           minister_right (Znth i ((x, y) :: ps) default_minister)).
      repeat rewrite Znth_cons by lia.
      replace (2 * i - 1 - 1) with (2 * (i - 1)) by lia.
      replace (2 * i + 1 - 1 - 1) with (2 * (i - 1) + 1) by lia.
      apply IH.
      lia.
Qed.
Lemma minister_hands_bound_Znth__flat_bubble :
  forall ps i,
    MinisterHandsBound ps ->
    0 <= i < Zlength ps ->
    1 <= minister_left (Znth i ps default_minister) <= 10 /\
    1 <= minister_right (Znth i ps default_minister) <= 10.
Proof.
  induction ps as [| p ps IH]; intros i Hbound Hi.
  - rewrite Zlength_nil in Hi. lia.
  - unfold MinisterHandsBound in Hbound.
    inversion Hbound as [| p' ps' Hp Htail]; subst.
    rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons. exact Hp.
    + rewrite Znth_cons by lia.
      apply IH; auto; lia.
Qed.
Lemma flat_ministers_Zlength__flat_bubble :
  forall flat ps,
    FlatMinisters flat ps ->
    Zlength flat = 2 * Zlength ps.
Proof.
  intros flat ps Hflat.
  unfold FlatMinisters in Hflat.
  subst flat.
  apply minister_flatten_Zlength__flat_bubble.
Qed.
Lemma flat_minister_product_bounds__flat_bubble :
  forall flat ps i,
    FlatMinisters flat ps ->
    MinisterHandsBound ps ->
    0 <= i < Zlength ps ->
    1 <= Znth (2 * i) flat 0 * Znth (2 * i + 1) flat 0 <= 100.
Proof.
  intros flat ps i Hflat Hbound Hi.
  unfold FlatMinisters in Hflat.
  subst flat.
  pose proof (minister_flatten_Znth_pair__flat_bubble ps i Hi)
    as [Hleft Hright].
  pose proof (minister_hands_bound_Znth__flat_bubble ps i Hbound Hi)
    as [[Hleft_lo Hleft_hi] [Hright_lo Hright_hi]].
  rewrite Hleft, Hright.
  nia.
Qed.
Lemma flat_minister_product_eq__flat_bubble :
  forall flat ps i,
    FlatMinisters flat ps ->
    0 <= i < Zlength ps ->
    Znth (2 * i) flat 0 * Znth (2 * i + 1) flat 0 =
      minister_product (Znth i ps default_minister).
Proof.
  intros flat ps i Hflat Hi.
  unfold FlatMinisters in Hflat.
  subst flat.
  pose proof (minister_flatten_Znth_pair__flat_bubble ps i Hi)
    as [Hleft Hright].
  unfold minister_product.
  rewrite Hleft, Hright.
  reflexivity.
Qed.
Lemma minister_flatten_replace_nth__flat_bubble :
  forall ps p n,
    (n < List.length ps)%nat ->
    flat_map (fun q => [minister_left q; minister_right q])
      (replace_nth n ps p) =
    replace_nth (2 * n + 1)%nat
      (replace_nth (2 * n)%nat
        (flat_map (fun q => [minister_left q; minister_right q]) ps)
        (minister_left p))
      (minister_right p).
Proof.
  induction ps as [| q ps IH]; intros p n Hn.
  - simpl in Hn. lia.
  - destruct n as [| n].
    + reflexivity.
    + replace (2 * S n)%nat with (S (S (2 * n))) by lia.
      replace (2 * S n + 1)%nat with (S (S (2 * n + 1))) by lia.
      simpl.
      f_equal.
      f_equal.
      apply IH.
      simpl in Hn. lia.
Qed.
Lemma minister_flatten_replace_Znth__flat_bubble :
  forall ps p i,
    0 <= i < Zlength ps ->
    minister_flatten (replace_Znth i p ps) =
    replace_Znth (2 * i + 1) (minister_right p)
      (replace_Znth (2 * i) (minister_left p) (minister_flatten ps)).
Proof.
  intros ps p i Hi.
  unfold minister_flatten, replace_Znth.
  replace (Z.to_nat (2 * i)) with (2 * Z.to_nat i)%nat by lia.
  replace (Z.to_nat (2 * i + 1)) with (2 * Z.to_nat i + 1)%nat by lia.
  apply minister_flatten_replace_nth__flat_bubble.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma replace_Znth_swap_form_minister__flat_bubble :
  forall (l1 l2 l3 : list minister) (xi xj : minister),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := minister) n1 l1 xj)
    by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  change (replace_Znth 0 xj (xi :: l2 ++ xj :: l3))
    with (xj :: l2 ++ xj :: l3).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := minister)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := minister) (Zlength l2) l2 xi)
    by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  reflexivity.
Qed.
Lemma minister_swap_permutation_lt__flat_bubble :
  forall ps i j,
    0 <= i < j ->
    j < Zlength ps ->
    MinisterPermutation ps (minister_swap ps i j).
Proof.
  intros ps i j Hij Hj.
  remember (Znth i ps default_minister) as xi.
  remember (Znth j ps default_minister) as xj.
  unfold MinisterPermutation, minister_swap.
  rewrite <- Heqxi, <- Heqxj.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni ps).
  set (lr := skipn (S ni) ps).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : ps = l1 ++ xi :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) ps default_minister) at 1.
    2: { rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi.
    reflexivity.
  }
  assert (Hj_lr : (nj < List.length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr default_minister) at 1 by exact Hj_lr.
    replace xj with (nth nj lr default_minister).
    2: {
      subst nj lr ni.
      rewrite Heqxj.
      unfold Znth.
      rewrite nth_skipn.
      assert ((Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm, H.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hshape : ps = l1 ++ xi :: l2 ++ xj :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace ps with (l1 ++ xi :: l2 ++ xj :: l3)
    by (symmetry; exact Hshape).
  replace i with (Zlength l1).
  2: {
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2: {
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct, !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form_minister__flat_bubble.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma replace_nth_comm_minister__flat_bubble :
  forall ni nj (ps : list minister) (a b : minister),
    ni <> nj ->
    replace_nth nj (replace_nth ni ps a) b =
    replace_nth ni (replace_nth nj ps b) a.
Proof.
  induction ni as [| ni IH]; intros nj ps a b Hneq;
    destruct ps as [| x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + exfalso. apply Hneq. reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal. apply IH. congruence.
Qed.
Lemma replace_Znth_comm_minister__flat_bubble :
  forall (ps : list minister) i j (a b : minister),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a ps) =
    replace_Znth i a (replace_Znth j b ps).
Proof.
  intros ps i j a b Hi Hj Hij.
  unfold replace_Znth.
  apply replace_nth_comm_minister__flat_bubble.
  intro Heq.
  apply Hij.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma minister_swap_permutation__flat_bubble :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    MinisterPermutation ps (minister_swap ps i j).
Proof.
  intros ps i j Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hij].
  - apply minister_swap_permutation_lt__flat_bubble; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + unfold minister_swap.
      rewrite replace_Znth_comm_minister__flat_bubble by lia.
      apply minister_swap_permutation_lt__flat_bubble; lia.
    + assert (i = j) by lia. subst j.
      unfold MinisterPermutation, minister_swap.
      repeat rewrite replace_Znth_Znth with (a0 := default_minister).
      apply Permutation_refl.
Qed.
Lemma minister_swap_Zlength__flat_bubble :
  forall ps i j,
    Zlength (minister_swap ps i j) = Zlength ps.
Proof.
  intros. unfold minister_swap.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.
Lemma minister_swap_hands_bound__flat_bubble :
  forall ps i j,
    MinisterHandsBound ps ->
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    MinisterHandsBound (minister_swap ps i j).
Proof.
  intros ps i j Hbound Hi Hj.
  eapply Permutation_Forall.
  - apply minister_swap_permutation__flat_bubble; eauto.
  - exact Hbound.
Qed.
Lemma minister_flatten_swap__flat_bubble :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    minister_flatten (minister_swap ps i j) =
    replace_Znth (2 * j + 1)
      (minister_right (Znth i ps default_minister))
      (replace_Znth (2 * j)
        (minister_left (Znth i ps default_minister))
        (replace_Znth (2 * i + 1)
          (minister_right (Znth j ps default_minister))
          (replace_Znth (2 * i)
            (minister_left (Znth j ps default_minister))
            (minister_flatten ps)))).
Proof.
  intros ps i j Hi Hj.
  unfold minister_swap.
  rewrite minister_flatten_replace_Znth__flat_bubble.
  2: { rewrite Zlength_replace_Znth. exact Hj. }
  rewrite minister_flatten_replace_Znth__flat_bubble by exact Hi.
  reflexivity.
Qed.
Lemma flat_ministers_swap__flat_bubble :
  forall flat ps i j,
    FlatMinisters flat ps ->
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    FlatMinisters (minister_swap_flat flat i j) (minister_swap ps i j).
Proof.
  intros flat ps i j Hflat Hi Hj.
  unfold FlatMinisters in Hflat |- *.
  subst flat.
  pose proof (minister_flatten_Znth_pair__flat_bubble ps i Hi)
    as [Hi_left Hi_right].
  pose proof (minister_flatten_Znth_pair__flat_bubble ps j Hj)
    as [Hj_left Hj_right].
  unfold minister_swap_flat.
  rewrite Hi_left, Hi_right, Hj_left, Hj_right.
  symmetry.
  apply minister_flatten_swap__flat_bubble; assumption.
Qed.
Lemma minister_swap_flat_preprocess_form__flat_bubble :
  forall flat n i j,
    Zlength flat = 2 * n ->
    0 <= i < n ->
    0 <= j < n ->
    replace_Znth (2 * j + 1) (Znth (2 * i + 1) flat 0)
      (replace_Znth (2 * j) (Znth (2 * i) flat 0)
        (replace_Znth (2 * i + 1)
          (Znth (2 * j + 1)
            (replace_Znth (2 * i) (Znth (2 * j) flat 0) flat) 0)
          (replace_Znth (2 * i) (Znth (2 * j) flat 0) flat))) =
    minister_swap_flat flat i j.
Proof.
  intros flat n i j Hlen Hi Hj.
  unfold minister_swap_flat.
  rewrite Znth_replace_Znth_Diff with (i := 2 * i) (j := 2 * j + 1).
  - reflexivity.
  - lia.
  - repeat rewrite Zlength_replace_Znth. lia.
  - lia.
Qed.
Lemma minister_swap_Znth_left__flat_bubble :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    Znth i (minister_swap ps i j) default_minister =
      Znth j ps default_minister.
Proof.
  intros ps i j Hi Hj.
  unfold minister_swap.
  destruct (Z.eq_dec i j) as [-> | Hij].
  - repeat rewrite replace_Znth_Znth with (a0 := default_minister).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := j) (j := i).
    + rewrite Znth_replace_Znth_Same by exact Hi.
      apply Znth_indep. exact Hj.
    + rewrite Zlength_replace_Znth. exact Hj.
    + rewrite Zlength_replace_Znth. exact Hi.
    + congruence.
Qed.
Lemma minister_swap_Znth_right__flat_bubble :
  forall ps i j,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    Znth j (minister_swap ps i j) default_minister =
      Znth i ps default_minister.
Proof.
  intros ps i j Hi Hj.
  unfold minister_swap.
  destruct (Z.eq_dec i j) as [-> | Hij].
  - repeat rewrite replace_Znth_Znth with (a0 := default_minister).
    reflexivity.
  - rewrite Znth_replace_Znth_Same.
    + apply Znth_indep. exact Hi.
    + rewrite Zlength_replace_Znth. exact Hj.
Qed.
Lemma minister_swap_Znth_other__flat_bubble :
  forall ps i j k,
    0 <= i < Zlength ps ->
    0 <= j < Zlength ps ->
    0 <= k < Zlength ps ->
    k <> i ->
    k <> j ->
    Znth k (minister_swap ps i j) default_minister =
      Znth k ps default_minister.
Proof.
  intros ps i j k Hi Hj Hk Hki Hkj.
  unfold minister_swap.
  rewrite Znth_replace_Znth_Diff with (i := j) (j := k).
  2: { rewrite Zlength_replace_Znth. exact Hj. }
  2: { rewrite Zlength_replace_Znth. exact Hk. }
  2: congruence.
  rewrite Znth_replace_Znth_Diff with (i := i) (j := k); auto.
Qed.
Lemma bubble_outer_initial__flat_bubble :
  forall ps n,
    Zlength ps = n ->
    BubbleOuterProperty ps n 0.
Proof.
  intros ps n Hlen.
  unfold BubbleOuterProperty.
  split; [exact Hlen |].
  split; intros i j; unfold MinisterProductLe; intros; lia.
Qed.
Lemma bubble_scan_initial__flat_bubble :
  forall ps n pass,
    0 < n - pass ->
    BubbleScanProperty ps n pass 0.
Proof.
  intros ps n pass Hrange.
  unfold BubbleScanProperty.
  split; [lia |].
  intros k Hk Hk0.
  assert (k = 0) by lia. subst k.
  unfold MinisterProductLe. lia.
Qed.
Lemma bubble_scan_step_no_swap__flat_bubble :
  forall ps n pass j,
    Zlength ps = n ->
    j + 1 < n - pass ->
    BubbleScanProperty ps n pass j ->
    MinisterProductLe
      (Znth j ps default_minister)
      (Znth (j + 1) ps default_minister) ->
    BubbleScanProperty ps n pass (j + 1).
Proof.
  intros ps n pass j Hlen Hnext Hscan Hle.
  destruct Hscan as [Hj Hmax].
  split; [lia |].
  intros k Hk Hkj.
  destruct (Z.eq_dec k (j + 1)) as [-> | Hneq].
  - unfold MinisterProductLe. lia.
  - specialize (Hmax k Hk ltac:(lia)).
    unfold MinisterProductLe in *.
    lia.
Qed.
Lemma bubble_outer_swap_prefix__flat_bubble :
  forall ps n pass j,
    Zlength ps = n ->
    0 <= pass ->
    0 <= j ->
    j + 1 < n - pass ->
    BubbleOuterProperty ps n pass ->
    BubbleOuterProperty (minister_swap ps j (j + 1)) n pass.
Proof.
  intros ps n pass j Hlen Hpass Hj Hbefore Houter.
  destruct Houter as [Houter_len [Hsuffix Hcross]].
  assert (Hj0 : 0 <= j < Zlength ps) by lia.
  assert (Hj1 : 0 <= j + 1 < Zlength ps) by lia.
  unfold BubbleOuterProperty.
  split.
  - rewrite minister_swap_Zlength__flat_bubble. exact Hlen.
  - split.
    + intros x y Hx Hxy Hy.
      rewrite minister_swap_Znth_other__flat_bubble with
        (i := j) (j := j + 1) (k := x); try lia.
      rewrite minister_swap_Znth_other__flat_bubble with
        (i := j) (j := j + 1) (k := y); try lia.
      apply Hsuffix; lia.
    + intros x y Hx0 Hx Hy0 Hy.
      rewrite minister_swap_Znth_other__flat_bubble with
        (i := j) (j := j + 1) (k := y); try lia.
      destruct (Z.eq_dec x j) as [-> | Hxj].
      * rewrite minister_swap_Znth_left__flat_bubble; try lia.
        apply Hcross; lia.
      * destruct (Z.eq_dec x (j + 1)) as [-> | Hxj1].
        -- rewrite minister_swap_Znth_right__flat_bubble; try lia.
           apply Hcross; lia.
        -- rewrite minister_swap_Znth_other__flat_bubble with
             (i := j) (j := j + 1) (k := x); try lia.
           apply Hcross; lia.
Qed.
Lemma bubble_scan_step_swap__flat_bubble :
  forall ps n pass j,
    Zlength ps = n ->
    0 <= pass ->
    0 <= j ->
    j + 1 < n - pass ->
    BubbleScanProperty ps n pass j ->
    MinisterProductLe
      (Znth (j + 1) ps default_minister)
      (Znth j ps default_minister) ->
    BubbleScanProperty (minister_swap ps j (j + 1)) n pass (j + 1).
Proof.
  intros ps n pass j Hlen Hpass Hj Hnext Hscan Hguard.
  destruct Hscan as [Hscan_range Hmax].
  assert (Hj0 : 0 <= j < Zlength ps) by lia.
  assert (Hj1 : 0 <= j + 1 < Zlength ps) by lia.
  split; [lia |].
  intros k Hk Hkj.
  rewrite minister_swap_Znth_right__flat_bubble with (i := j); try lia.
  destruct (Z.eq_dec k j) as [-> | Hkj0].
  - rewrite minister_swap_Znth_left__flat_bubble; try lia.
    exact Hguard.
  - destruct (Z.eq_dec k (j + 1)) as [-> | Hkj1].
    + rewrite minister_swap_Znth_right__flat_bubble; try lia.
      unfold MinisterProductLe. lia.
    + rewrite minister_swap_Znth_other__flat_bubble with
        (i := j) (j := j + 1) (k := k); try lia.
      apply Hmax; lia.
Qed.
Lemma bubble_outer_finish_pass__flat_bubble :
  forall ps n pass j,
    j = n - 1 - pass ->
    BubbleOuterProperty ps n pass ->
    BubbleScanProperty ps n pass j ->
    BubbleOuterProperty ps n (pass + 1).
Proof.
  intros ps n pass j Hj Houter Hscan.
  subst j.
  destruct Houter as [Hlen [Hsuffix Hcross]].
  destruct Hscan as [Hscan_range Hmax].
  unfold BubbleOuterProperty.
  split; [exact Hlen |].
  split.
  - intros i j Hi Hij Hjlen.
    destruct (Z.eq_dec i (n - (pass + 1))) as [-> | Hineq].
    + destruct (Z.eq_dec j (n - (pass + 1))) as [-> | Hjneq].
      * unfold MinisterProductLe. lia.
      * apply Hcross; lia.
    + apply Hsuffix; lia.
  - intros i j Hi0 Hi Hj0 Hjlen.
    destruct (Z.eq_dec j (n - (pass + 1))) as [-> | Hjneq].
    + replace (n - (pass + 1)) with (n - 1 - pass) by lia.
      apply Hmax; lia.
    + apply Hcross; lia.
Qed.
Lemma bubble_outer_final_sorted__greedy_optimum :
  forall ps n pass,
    pass >= n - 1 ->
    pass <= n - 1 ->
    BubbleOuterProperty ps n pass ->
    MinisterSorted ps.
Proof.
  intros ps n pass Hge Hle [Hlen [Hsuffix Hcross]].
  assert (Hpass : pass = n - 1) by lia.
  subst pass.
  unfold MinisterSorted.
  intros i j Hi Hij Hj.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - destruct (Z.eq_dec j 0) as [-> | Hj0].
    + unfold MinisterProductLe; lia.
    + apply Hcross; lia.
  - apply Hsuffix; lia.
Qed.
Lemma minister_sorted_cons__greedy_optimum :
  forall x xs,
    MinisterSorted (x :: xs) ->
    Forall (MinisterProductLe x) xs /\ MinisterSorted xs.
Proof.
  intros x xs Hsorted.
  split.
  - apply Forall_forall.
    intros y Hy.
    apply In_nth with (d := default_minister) in Hy.
    destruct Hy as [i [Hi Hy]].
    subst y.
    specialize (Hsorted 0 (Z.of_nat i + 1)).
    rewrite Zlength_cons in Hsorted.
    rewrite Znth0_cons in Hsorted.
    rewrite Znth_cons in Hsorted by lia.
    replace (Z.of_nat i + 1 - 1) with (Z.of_nat i) in Hsorted by lia.
    unfold Znth in Hsorted.
    rewrite Nat2Z.id in Hsorted.
    apply Hsorted; try lia.
    rewrite Zlength_correct.
    lia.
  - unfold MinisterSorted in *.
    intros i j Hi Hij Hj.
    specialize (Hsorted (i + 1) (j + 1)).
    rewrite Zlength_cons in Hsorted.
    rewrite !Znth_cons in Hsorted by lia.
    replace (i + 1 - 1) with i in Hsorted by lia.
    replace (j + 1 - 1) with j in Hsorted by lia.
    apply Hsorted; lia.
Qed.
Lemma minister_reward_cons_zero__greedy_optimum :
  forall king x xs,
    MinisterReward king (x :: xs) 0 = king / minister_right x.
Proof.
  intros.
  unfold MinisterReward, PrefixLeftProduct.
  rewrite Znth0_cons.
  unfold sublist.
  simpl.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.
Lemma minister_reward_cons_succ__greedy_optimum :
  forall king x xs i,
    0 <= i < Zlength xs ->
    MinisterReward king (x :: xs) (i + 1) =
    MinisterReward (king * minister_left x) xs i.
Proof.
  intros king x xs i Hi.
  unfold MinisterReward, PrefixLeftProduct.
  rewrite sublist_cons1 by lia.
  rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  simpl.
  f_equal.
  ring.
Qed.
Lemma minister_reward_two_cons_tail__greedy_optimum :
  forall king x y xs i,
    0 <= i < Zlength xs ->
    MinisterReward king (x :: y :: xs) (i + 2) =
    MinisterReward
      (king * minister_left x * minister_left y) xs i.
Proof.
  intros king x y xs i Hi.
  replace (i + 2) with ((i + 1) + 1) by lia.
  rewrite minister_reward_cons_succ__greedy_optimum by
      (rewrite Zlength_cons; lia).
  rewrite minister_reward_cons_succ__greedy_optimum by exact Hi.
  f_equal.
Qed.
Lemma positive_cross_div_le__greedy_optimum :
  forall king lx rx ly ry,
    0 <= king ->
    0 < rx ->
    0 < ry ->
    lx * rx <= ly * ry ->
    king * lx / ry <= king * ly / rx.
Proof.
  intros king lx rx ly ry Hking Hrx Hry Hkey.
  rewrite <- (Zdiv_mult_cancel_r (king * lx) ry rx) by lia.
  rewrite <- (Zdiv_mult_cancel_r (king * ly) rx ry) by lia.
  replace (rx * ry) with (ry * rx) by ring.
  apply Z.div_le_mono; nia.
Qed.
Lemma positive_adjacent_exchange_bound__greedy_optimum :
  forall king x y xs cap,
    0 <= king ->
    1 <= minister_left x ->
    1 <= minister_right x ->
    1 <= minister_left y ->
    1 <= minister_right y ->
    MinisterProductLe x y ->
    (forall i,
        0 <= i < Zlength (y :: x :: xs) ->
        MinisterReward king (y :: x :: xs) i <= cap) ->
    forall i,
      0 <= i < Zlength (x :: y :: xs) ->
      MinisterReward king (x :: y :: xs) i <= cap.
Proof.
  intros king x y xs cap Hking Hxl Hxr Hyl Hyr Hkey Hbound i Hi.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - specialize (Hbound 1 ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg xs); lia)).
    rewrite minister_reward_cons_zero__greedy_optimum.
    replace 1 with (0 + 1) in Hbound by lia.
    rewrite minister_reward_cons_succ__greedy_optimum in Hbound by
        (rewrite Zlength_cons; pose proof (Zlength_nonneg xs); lia).
    rewrite minister_reward_cons_zero__greedy_optimum in Hbound.
    eapply Z.le_trans; [|exact Hbound].
    apply Z.div_le_mono; nia.
  - destruct (Z.eq_dec i 1) as [-> | Hi1].
    + specialize (Hbound 1 ltac:(rewrite !Zlength_cons; pose proof (Zlength_nonneg xs); lia)).
      replace 1 with (0 + 1) in Hbound |- * by lia.
      rewrite minister_reward_cons_succ__greedy_optimum in Hbound by
          (rewrite Zlength_cons; pose proof (Zlength_nonneg xs); lia).
      rewrite minister_reward_cons_succ__greedy_optimum by
          (rewrite Zlength_cons; pose proof (Zlength_nonneg xs); lia).
      rewrite !minister_reward_cons_zero__greedy_optimum in Hbound |- *.
      eapply Z.le_trans; [|exact Hbound].
      apply positive_cross_div_le__greedy_optimum; try lia.
      exact Hkey.
    + assert (Hitail : 0 <= i - 2 < Zlength xs).
      { rewrite !Zlength_cons in Hi. lia. }
      specialize (Hbound i ltac:(rewrite !Zlength_cons; rewrite !Zlength_cons in Hi; lia)).
      replace i with ((i - 2) + 2) in Hbound |- * by lia.
      rewrite !minister_reward_two_cons_tail__greedy_optimum in Hbound |- *
        by exact Hitail.
      replace (king * minister_left x * minister_left y)
        with (king * minister_left y * minister_left x) by ring.
      exact Hbound.
Qed.
Lemma positive_move_minimum_to_front_bound__greedy_optimum :
  forall pre x post king cap,
    0 <= king ->
    MinisterHandsBound (x :: pre ++ post) ->
    Forall (MinisterProductLe x) pre ->
    (forall i,
        0 <= i < Zlength (pre ++ x :: post) ->
        MinisterReward king (pre ++ x :: post) i <= cap) ->
    forall i,
      0 <= i < Zlength (x :: pre ++ post) ->
      MinisterReward king (x :: pre ++ post) i <= cap.
Proof.
  induction pre as [|y pre IH];
    intros x post king cap Hking Hhands Hminimum Hbound i Hi.
  - simpl in *.
    apply Hbound; exact Hi.
  - simpl in Hhands, Hminimum, Hbound, Hi |- *.
    inversion Hhands as [|? ? Hx Hhands_y]; subst.
    inversion Hhands_y as [|? ? Hy Hhands_rest]; subst.
    inversion Hminimum as [|? ? Hxy Hminimum_rest]; subst.
    destruct Hx as [[Hxl Hxlmax] [Hxr Hxrmax]].
    destruct Hy as [[Hyl Hylmax] [Hyr Hyrmax]].
    assert (Htail_bound :
      forall q,
        0 <= q < Zlength (pre ++ x :: post) ->
        MinisterReward (king * minister_left y) (pre ++ x :: post) q <= cap).
    {
      intros q Hq.
      specialize (Hbound (q + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite minister_reward_cons_succ__greedy_optimum in Hbound by exact Hq.
      exact Hbound.
    }
    assert (Hhands_recursive : MinisterHandsBound (x :: pre ++ post)).
    {
      constructor.
      - repeat split; assumption.
      - exact Hhands_rest.
    }
    assert (Hking_recursive : 0 <= king * minister_left y) by nia.
    pose proof
      (IH x post (king * minister_left y) cap Hking_recursive
        Hhands_recursive Hminimum_rest Htail_bound)
      as Hmoved_tail.
    assert (Hbefore_swap :
      forall q,
        0 <= q < Zlength (y :: x :: pre ++ post) ->
        MinisterReward king (y :: x :: pre ++ post) q <= cap).
    {
      intros q Hq.
      destruct (Z.eq_dec q 0) as [-> | Hq0].
      - rewrite minister_reward_cons_zero__greedy_optimum.
        specialize (Hbound 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg (pre ++ x :: post)); lia)).
        rewrite minister_reward_cons_zero__greedy_optimum in Hbound.
        exact Hbound.
      - replace q with ((q - 1) + 1) by lia.
        rewrite minister_reward_cons_succ__greedy_optimum by
          (rewrite Zlength_cons in Hq; lia).
        apply Hmoved_tail.
        replace (Zlength (y :: x :: pre ++ post))
          with (Zlength (x :: pre ++ post) + 1) in Hq by
          (rewrite !Zlength_cons; lia).
        lia.
    }
    eapply positive_adjacent_exchange_bound__greedy_optimum; eauto.
Qed.
Lemma positive_sorted_global_bound__greedy_optimum :
  forall sorted other king cap,
    0 <= king ->
    MinisterHandsBound sorted ->
    MinisterSorted sorted ->
    Permutation sorted other ->
    (forall i,
        0 <= i < Zlength other ->
        MinisterReward king other i <= cap) ->
    forall i,
      0 <= i < Zlength sorted ->
      MinisterReward king sorted i <= cap.
Proof.
  induction sorted as [|x xs IH];
    intros other king cap Hking Hhands Hsorted Hperm Hbound i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - assert (Hin : In x other).
    { eapply Permutation_in; [exact Hperm | left; reflexivity]. }
    destruct (in_split x other Hin) as [pre [post Hother]].
    subst other.
    assert (Hperm_tail : Permutation xs (pre ++ post)).
    { eapply Permutation_cons_app_inv; exact Hperm. }
    destruct (minister_sorted_cons__greedy_optimum x xs Hsorted)
      as [Hminimum_xs Hsorted_xs].
    assert (Hminimum_rest : Forall (MinisterProductLe x) (pre ++ post)).
    {
      eapply Permutation_Forall.
      - exact Hperm_tail.
      - exact Hminimum_xs.
    }
    apply Forall_app in Hminimum_rest.
    destruct Hminimum_rest as [Hminimum_pre Hminimum_post].
    assert (Hhands_front : MinisterHandsBound (x :: pre ++ post)).
    {
      unfold MinisterHandsBound in *.
      eapply Permutation_Forall.
      - apply perm_skip; exact Hperm_tail.
      - exact Hhands.
    }
    pose proof
      (positive_move_minimum_to_front_bound__greedy_optimum
        pre x post king cap Hking Hhands_front Hminimum_pre Hbound)
      as Hmoved.
    assert (Hhead : MinisterReward king (x :: xs) 0 <= cap).
    {
      specialize (Hmoved 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg (pre ++ post)); lia)).
      rewrite !minister_reward_cons_zero__greedy_optimum in Hmoved |- *.
      exact Hmoved.
    }
    assert (Htail_bound :
      forall q,
        0 <= q < Zlength (pre ++ post) ->
        MinisterReward (king * minister_left x) (pre ++ post) q <= cap).
    {
      intros q Hq.
      specialize (Hmoved (q + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite minister_reward_cons_succ__greedy_optimum in Hmoved by exact Hq.
      exact Hmoved.
    }
    assert (Hhands_xs : MinisterHandsBound xs).
    {
      unfold MinisterHandsBound in Hhands.
      inversion Hhands; assumption.
    }
    assert (Hxleft : 1 <= minister_left x).
    {
      unfold MinisterHandsBound in Hhands.
      inversion Hhands as [|? ? Hx Hrest]; subst.
      destruct Hx as [[? ?] [? ?]]; assumption.
    }
    pose proof
      (IH (pre ++ post) (king * minister_left x) cap ltac:(nia)
        Hhands_xs Hsorted_xs Hperm_tail Htail_bound)
      as Htail_sorted.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + exact Hhead.
    + replace i with ((i - 1) + 1) by lia.
      rewrite minister_reward_cons_succ__greedy_optimum by
        (rewrite Zlength_cons in Hi; lia).
      apply Htail_sorted.
      rewrite Zlength_cons in Hi.
      lia.
Qed.
Lemma finite_nonempty_index_max__greedy_optimum :
  forall n (f : Z -> Z),
    1 <= n ->
    exists m,
      max_value_of_subset Z.le
        (fun i : Z => 0 <= i < n) f m.
Proof.
  intros n f Hn.
  assert (Hfinite :
    forall k : nat,
      exists m,
        max_value_of_subset Z.le
          (fun i : Z => 0 <= i < Z.of_nat (S k)) f m).
  {
    induction k as [|k IH].
    - exists (f 0), 0.
      split.
      + unfold max_object_of_subset; simpl.
        split.
        * change (0 <= 0 < Z.of_nat (S O)); lia.
        * intros b Hb.
          change (0 <= b < Z.of_nat (S O)) in Hb.
          assert (b = 0) by lia.
          subst; lia.
      + reflexivity.
    - destruct IH as [m [a [[Ha_range Ha_max] Hfa]]].
      set (last := Z.of_nat (S k)).
      destruct (Z_le_dec m (f last)) as [Hnew | Hnew].
      + exists (f last), last.
        split.
        * unfold max_object_of_subset; simpl.
          split.
          -- change (0 <= last < Z.of_nat (S (S k))).
             unfold last; lia.
          -- intros b Hb.
             change (0 <= b < Z.of_nat (S (S k))) in Hb.
             destruct (Z.eq_dec b last) as [-> | Hb_last]; [lia |].
             assert (Hb_old : 0 <= b < Z.of_nat (S k)).
             { unfold last in *; lia. }
             specialize (Ha_max b Hb_old).
             rewrite Hfa in Ha_max.
             lia.
        * reflexivity.
      + exists m, a.
        split.
        * unfold max_object_of_subset; simpl.
          split.
          -- change (0 <= a < Z.of_nat (S (S k))).
             change (0 <= a < Z.of_nat (S k)) in Ha_range.
             unfold last in *; lia.
          -- intros b Hb.
             change (0 <= b < Z.of_nat (S (S k))) in Hb.
             destruct (Z.eq_dec b last) as [-> | Hb_last].
             ++ rewrite Hfa; lia.
             ++ apply Ha_max.
                change (0 <= b < Z.of_nat (S k)).
                unfold last in *; lia.
        * exact Hfa.
  }
  replace n with (Z.of_nat (Z.to_nat n)) by lia.
  destruct (Z.to_nat n) as [|k] eqn:Hnat.
  - lia.
  - apply Hfinite.
Qed.
Lemma positive_sorted_realizes_kings_optimum__greedy_optimum :
  forall input output king,
    0 <= king ->
    1 <= Zlength output ->
    MinisterHandsBound output ->
    MinisterSorted output ->
    MinisterPermutation input output ->
    KingsGameResult input king output.
Proof.
  intros input output king Hking Hnonempty Hhands Hsorted Hperm.
  unfold KingsGameResult.
  split; [exact Hperm |].
  split; [exact Hsorted |].
  destruct
    (finite_nonempty_index_max__greedy_optimum
      (Zlength output) (fun i => MinisterReward king output i) Hnonempty)
    as [reward Horder_output].
  exists reward.
  split; [exact Horder_output |].
  unfold KingsGameOptimum.
  exists (output, reward).
  split.
  - unfold min_object_of_subset.
    split.
    + unfold ValidOrderReward; simpl.
      split; assumption.
    + intros candidate Hcandidate.
      destruct candidate as [other other_reward].
      unfold ValidOrderReward in Hcandidate; simpl in Hcandidate |- *.
      destruct Hcandidate as [Hinput_other Horder_other].
      assert (Houtput_other : Permutation output other).
      {
        unfold MinisterPermutation in *.
        eapply Permutation_trans.
        - apply Permutation_sym; exact Hperm.
        - exact Hinput_other.
      }
      assert (Hother_bound :
        forall i,
          0 <= i < Zlength other ->
          MinisterReward king other i <= other_reward).
      {
        intros i Hi.
        unfold OrderMaxReward, max_value_of_subset,
          max_object_of_subset in Horder_other.
        destruct Horder_other as [j [[Hj_range Hj_max] Hj_reward]].
        specialize (Hj_max i Hi).
        rewrite Hj_reward in Hj_max.
        exact Hj_max.
      }
      pose proof
        (positive_sorted_global_bound__greedy_optimum
          output other king other_reward Hking Hhands Hsorted
          Houtput_other Hother_bound)
        as Hsorted_bound.
      unfold OrderMaxReward, max_value_of_subset,
        max_object_of_subset in Horder_output.
      destruct Horder_output as [j [[Hj_range Hj_max] Hj_reward]].
      specialize (Hsorted_bound j Hj_range).
      rewrite Hj_reward in Hsorted_bound.
      exact Hsorted_bound.
  - reflexivity.
Qed.
