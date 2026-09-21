From Coq Require Import ZArith List Lia.
Require Import Coq.ZArith.Zbitwise.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.

Import ListNotations.
Local Open Scope Z_scope.

(** The C expression [x & (-x)] is interpreted as [Z.land x (-x)]. *)
Definition FenwickLowbit (x : Z) : Z :=
  Z.land x (-x).

(** A Fenwick node [i] covers the closed 1-based interval
    [[i - lowbit(i) + 1, i]]. *)
Definition FenwickNodeLo (i : Z) : Z :=
  i - FenwickLowbit i + 1.

Definition FenwickNodeSum (a : list Z) (i : Z) : Z :=
  sum (sublist (FenwickNodeLo i) (i + 1) a).

(** [FenwickPrefixSum a pos] is exactly the sum of the closed interval
    [[1,pos]].  In particular, [pos = 0] denotes the empty interval. *)
Definition FenwickPrefixSum (a : list Z) (pos : Z) : Z :=
  sum (sublist 1 (pos + 1) a).

Definition FenwickAddArray
    (a : list Z) (pos delta : Z) : list Z :=
  replace_Znth pos (Znth pos a 0 + delta) a.

(** A length-[n+1] concrete tree represents the 1-based logical array
    [a[1..n]].  Slot zero is reserved and is not part of any represented
    sum.  Every node equation below names its exact closed interval. *)
Definition FenwickRep
    (a bit : list Z) (n : Z) : Prop :=
  Zlength a = n + 1 /\
  Zlength bit = n + 1 /\
  Znth 0 a 0 = 0 /\
  forall i,
    1 <= i <= n ->
    Znth i bit 0 = FenwickNodeSum a i.

Definition FenwickCovers (node target : Z) : Prop :=
  FenwickNodeLo node <= target <= node.

(** Internal state of [add].  Nodes are ordered by their 1-based node
    index: covering nodes already below [cursor] have received [delta], and
    every other node is still equal to the entry tree.  If [cursor] is live,
    it is itself the next covering node. *)
Definition FenwickUpdated (node target cursor : Z) : bool :=
  andb (andb (FenwickNodeLo node <=? target) (target <=? node))
       (node <? cursor).

Definition FenwickAddProgress
    (entry current : list Z) (n target cursor delta : Z) : Prop :=
  Zlength current = Zlength entry /\
  Znth 0 current 0 = Znth 0 entry 0 /\
  (cursor <= n -> FenwickCovers cursor target) /\
  Forall2 (fun after before => after = before + delta)
    (map (fun node => Znth node current 0)
      (filter (fun node => FenwickUpdated node target cursor) (Zrange 1 (n + 1))))
    (map (fun node => Znth node entry 0)
      (filter (fun node => FenwickUpdated node target cursor) (Zrange 1 (n + 1)))) /\
  Forall2 eq
    (map (fun node => Znth node current 0)
      (filter (fun node => negb (FenwickUpdated node target cursor)) (Zrange 1 (n + 1))))
    (map (fun node => Znth node entry 0)
      (filter (fun node => negb (FenwickUpdated node target cursor)) (Zrange 1 (n + 1)))).

(** An unconditional bridge preserves the original indexed proof interface.
    Both projections enumerate precisely the same mathematical node domain. *)
Lemma Fenwick_Forall2_filtered {A B : Type} (R : A -> B -> Prop)
    (f : Z -> A) (g : Z -> B) (keep : Z -> bool) lo hi :
  Forall2 R (map f (filter keep (Zrange lo hi)))
    (map g (filter keep (Zrange lo hi))) <->
  forall node, lo <= node < hi -> keep node = true -> R (f node) (g node).
Proof.
  assert (Hmap : forall xs, Forall2 R (map f xs) (map g xs) <->
    Forall (fun node => R (f node) (g node)) xs).
  { induction xs as [|x xs IH]; cbn.
    - split; intros; constructor.
    - split; intro H; inversion H; subst; constructor; try assumption;
      apply IH; assumption. }
  rewrite Hmap, Forall_forall. split; intros H node Hnode.
  - intro Hkeep. apply H. apply filter_In. split; [apply In_Zrange|]; assumption.
  - apply filter_In in Hnode. destruct Hnode as [Hnode Hkeep].
    apply H; [apply In_Zrange|]; assumption.
Qed.

Lemma FenwickAddProgress_unfold entry current n target cursor delta :
  FenwickAddProgress entry current n target cursor delta <->
  Zlength current = Zlength entry /\
  Znth 0 current 0 = Znth 0 entry 0 /\
  (cursor <= n -> FenwickCovers cursor target) /\
  forall node, 1 <= node <= n ->
    ((FenwickCovers node target /\ node < cursor) ->
       Znth node current 0 = Znth node entry 0 + delta) /\
    ((~ FenwickCovers node target \/ cursor <= node) ->
       Znth node current 0 = Znth node entry 0).
Proof.
  unfold FenwickAddProgress, FenwickUpdated.
  rewrite !Fenwick_Forall2_filtered. cbn beta.
  setoid_rewrite Bool.negb_true_iff.
  repeat setoid_rewrite Bool.andb_true_iff.
  repeat setoid_rewrite Bool.andb_false_iff.
  setoid_rewrite Z.leb_le. setoid_rewrite Z.leb_gt.
  setoid_rewrite Z.ltb_lt. setoid_rewrite Z.ltb_ge.
  repeat apply and_iff_compat_l.
  split.
  - intros [Hupdated Hunchanged] node Hnode. split; intro Hcondition.
    + apply Hupdated; [lia | unfold FenwickCovers in Hcondition; tauto].
    + apply Hunchanged; [lia | unfold FenwickCovers in Hcondition; lia].
  - intros H. split; intros node Hnode Hcondition.
    + apply (proj1 (H node ltac:(lia))). unfold FenwickCovers; tauto.
    + apply (proj2 (H node ltac:(lia))). unfold FenwickCovers; lia.
Qed.

(** Internal state of [query].  The accumulator contains the disjoint
    closed node intervals already removed from the original closed prefix;
    [[1,cursor]] is exactly the unconsumed prefix. *)
Definition FenwickQueryState
    (a : list Z) (target cursor accumulator : Z) : Prop :=
  accumulator + FenwickPrefixSum a cursor = FenwickPrefixSum a target.

(** The following lemmas are integer-level bridges for symbolic execution;
    they do not assume a machine-specific bit-vector axiom. *)
Lemma FenwickLowbit_eq_land :
  forall x, FenwickLowbit x = Z.land x (-x).
Proof.
  reflexivity.
Qed.

Lemma FenwickLowbit_positive :
  forall x, 0 < x -> 0 < FenwickLowbit x.
Proof.
  intros x Hx.
  unfold FenwickLowbit.
  assert (Hnonneg : 0 <= Z.land x (-x)).
  { apply Z.land_nonneg. left. lia. }
  assert (Hnonzero : Z.land x (-x) <> 0).
  {
    intros Hzero.
    pose proof (Z.add_nocarry_lxor x (-x) Hzero) as Hxor.
    assert (Z.lxor x (-x) = 0) by lia.
    apply Z.lxor_eq in H.
    lia.
  }
  lia.
Qed.

Lemma FenwickLowbit_nonnegative :
  forall x, 0 <= x -> 0 <= FenwickLowbit x.
Proof.
  intros x Hx.
  unfold FenwickLowbit.
  apply Z.land_nonneg.
  left; exact Hx.
Qed.

Lemma FenwickLowbit_le :
  forall x, 0 <= x -> FenwickLowbit x <= x.
Proof.
  intros x Hx.
  unfold FenwickLowbit.
  set (u := Z.land x (-x)).
  set (v := Z.ldiff x (-x)).
  assert (Hu : 0 <= u).
  { subst u. apply Z.land_nonneg. left; exact Hx. }
  assert (Hv : 0 <= v).
  { subst v. apply Z.ldiff_nonneg. left; exact Hx. }
  assert (Hdisjoint : Z.land v u = 0).
  {
    subst u v.
    rewrite Z.land_assoc.
    rewrite (Z.land_comm (Z.ldiff x (-x)) x).
    rewrite <- Z.land_assoc.
    rewrite Z.land_ldiff.
    apply Z.land_0_r.
  }
  assert (Hsum : v + u = x).
  {
    rewrite Z.add_nocarry_lxor by exact Hdisjoint.
    rewrite Z.lxor_lor by exact Hdisjoint.
    subst u v.
    apply Z.lor_ldiff_and.
  }
  lia.
Qed.

Lemma FenwickLowbit_bounds :
  forall x, 0 < x -> 1 <= FenwickLowbit x <= x.
Proof.
  intros x Hx.
  split.
  - pose proof (FenwickLowbit_positive x Hx); lia.
  - apply FenwickLowbit_le; lia.
Qed.

Lemma Fenwick_query_index_decreases :
  forall x,
    0 < x ->
    0 <= x - FenwickLowbit x < x.
Proof.
  intros x Hx.
  pose proof (FenwickLowbit_bounds x Hx).
  lia.
Qed.

Lemma Fenwick_add_index_increases :
  forall x,
    0 < x ->
    x < x + FenwickLowbit x <= 2 * x.
Proof.
  intros x Hx.
  pose proof (FenwickLowbit_bounds x Hx).
  lia.
Qed.

Lemma Fenwick_add_index_int_safe :
  forall n x,
    1 <= x <= n ->
    2 * n <= 2147483647 ->
    x + FenwickLowbit x <= 2147483647.
Proof.
  intros n x Hx Hn.
  pose proof (FenwickLowbit_bounds x ltac:(lia)).
  lia.
Qed.

Lemma FenwickNodeLo_bounds :
  forall i,
    0 < i ->
    1 <= FenwickNodeLo i <= i.
Proof.
  intros i Hi.
  unfold FenwickNodeLo.
  pose proof (FenwickLowbit_bounds i Hi).
  lia.
Qed.

Lemma FenwickCovers_self :
  forall i,
    0 < i ->
    FenwickCovers i i.
Proof.
  intros i Hi.
  unfold FenwickCovers.
  pose proof (FenwickNodeLo_bounds i Hi).
  lia.
Qed.

Lemma Fenwick_prefix_node_partition :
  forall a i,
    0 < i ->
    i < Zlength a ->
    FenwickPrefixSum a i =
      FenwickPrefixSum a (i - FenwickLowbit i) + FenwickNodeSum a i.
Proof.
  intros a i Hi Hilen.
  unfold FenwickPrefixSum, FenwickNodeSum, FenwickNodeLo.
  pose proof (FenwickLowbit_bounds i Hi) as Hlow.
  rewrite (sublist_split 1 (i + 1)
            (i - FenwickLowbit i + 1) a) by lia.
  apply sum_app.
Qed.

Lemma FenwickPrefixSum_zero :
  forall a, FenwickPrefixSum a 0 = 0.
Proof.
  intros a.
  unfold FenwickPrefixSum.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.

Lemma FenwickQueryState_initial :
  forall a target,
    FenwickQueryState a target target 0.
Proof.
  intros a target.
  unfold FenwickQueryState.
  lia.
Qed.

Lemma FenwickQueryState_step :
  forall a bit n target cursor accumulator,
    FenwickRep a bit n ->
    0 < cursor <= n ->
    FenwickQueryState a target cursor accumulator ->
    FenwickQueryState a target
      (cursor - FenwickLowbit cursor)
      (accumulator + Znth cursor bit 0).
Proof.
  intros a bit n target cursor accumulator Hrep Hcursor Hstate.
  unfold FenwickRep in Hrep.
  destruct Hrep as [Halen [Hbitlen [Ha0 Hnodes]]].
  specialize (Hnodes cursor ltac:(lia)).
  unfold FenwickQueryState in *.
  rewrite Hnodes.
  pose proof (Fenwick_prefix_node_partition a cursor ltac:(lia) ltac:(lia))
    as Hpartition.
  lia.
Qed.

Lemma FenwickLowbit_double__add_progress_bitwise :
  forall x,
    0 < x ->
    FenwickLowbit (2 * x) = 2 * FenwickLowbit x.
Proof.
  intros x Hx.
  unfold FenwickLowbit.
  apply Z.bits_inj'; intros n Hn.
  replace (- (2 * x)) with (2 * (-x)) by ring.
  rewrite Z.land_spec.
  rewrite !Z.double_bits.
  rewrite Z.land_spec.
  reflexivity.
Qed.
Lemma FenwickLowbit_double_plus_one__add_progress_bitwise :
  forall x,
    0 <= x ->
    FenwickLowbit (2 * x + 1) = 1.
Proof.
  intros x Hx.
  unfold FenwickLowbit.
  apply Z.bits_inj'; intros n Hn.
  destruct (Z.eq_dec n 0) as [-> | Hnz].
  - rewrite Z.land_spec.
    replace (- (2 * x + 1)) with (2 * (-x - 1) + 1) by ring.
    rewrite !Z.testbit_odd_0.
    reflexivity.
  - assert (Hpos : 0 < n) by lia.
    rewrite Z.land_spec.
    rewrite Z.bits_opp by exact Hn.
    replace (Z.pred (2 * x + 1)) with (2 * x) by lia.
    replace n with (Z.succ (Z.pred n)) by lia.
    rewrite Z.testbit_odd_succ by lia.
    rewrite Z.testbit_even_succ by lia.
    rewrite (Z.bits_above_log2 1 (Z.succ (Z.pred n))) by (simpl; lia).
    destruct (Z.testbit x (Z.pred n)); reflexivity.
Qed.
Lemma FenwickLowbit_successor_growth__add_progress_bitwise :
  forall x,
    0 < x ->
    2 * FenwickLowbit x <=
      FenwickLowbit (x + FenwickLowbit x).
Proof.
  intros [|p|p] Hx; try lia.
  clear Hx.
  revert p.
  fix IH 1.
  intros [p|p|].
  - rewrite Pos2Z.pos_xI.
    rewrite FenwickLowbit_double_plus_one__add_progress_bitwise by lia.
    replace (2 * Z.pos p + 1 + 1) with (2 * (Z.pos p + 1)) by ring.
    rewrite FenwickLowbit_double__add_progress_bitwise by lia.
    pose proof (FenwickLowbit_positive (Z.pos p + 1) ltac:(lia)).
    lia.
  - assert (Hdouble : FenwickLowbit (Z.pos p~0) =
        2 * FenwickLowbit (Z.pos p)).
    {
      rewrite Pos2Z.pos_xO.
      apply FenwickLowbit_double__add_progress_bitwise; lia.
    }
    rewrite Hdouble.
    assert (Harg : Z.pos p~0 + 2 * FenwickLowbit (Z.pos p) =
        2 * (Z.pos p + FenwickLowbit (Z.pos p))).
    {
      rewrite Pos2Z.pos_xO.
      ring.
    }
    rewrite Harg.
    assert (Hnextpos : 0 < Z.pos p + FenwickLowbit (Z.pos p)).
    {
      pose proof (FenwickLowbit_positive (Z.pos p) ltac:(lia)).
      lia.
    }
    pose proof
      (FenwickLowbit_double__add_progress_bitwise
         (Z.pos p + FenwickLowbit (Z.pos p)) Hnextpos) as Hnextdouble.
    pose proof (IH p) as Hrec.
    rewrite Hnextdouble.
    lia.
  - change (2 * FenwickLowbit 1 <=
      FenwickLowbit (1 + FenwickLowbit 1)).
    vm_compute.
  all: try lia.
  all: easy.
Qed.
Lemma FenwickLowbit_gap_bound__add_progress_bitwise :
  forall x node,
    0 < x ->
    x < node < x + FenwickLowbit x ->
    FenwickLowbit node <= node - x.
Proof.
  intros [|p|p] node Hx; try lia.
  clear Hx.
  revert node.
  induction p as [p IHp | p IHp |]; intros node Hgap.
  - rewrite Pos2Z.pos_xI in Hgap.
    rewrite FenwickLowbit_double_plus_one__add_progress_bitwise in Hgap
      by lia.
    lia.
  - rewrite Pos2Z.pos_xO in Hgap |- *.
    rewrite FenwickLowbit_double__add_progress_bitwise in Hgap by lia.
    destruct node as [|q|q]; try lia.
    destruct q as [q|q|].
    + rewrite Pos2Z.pos_xI.
      rewrite FenwickLowbit_double_plus_one__add_progress_bitwise by lia.
      lia.
    + rewrite Pos2Z.pos_xO.
      rewrite FenwickLowbit_double__add_progress_bitwise by lia.
      specialize (IHp (Z.pos q) ltac:(lia)).
      lia.
    + lia.
  - change (1 < node < 1 + FenwickLowbit 1) in Hgap.
    change (1 < node < 1 + FenwickLowbit (2 * 0 + 1)) in Hgap.
    rewrite FenwickLowbit_double_plus_one__add_progress_bitwise in Hgap by lia.
    lia.
  all: easy.
Qed.
Lemma Fenwick_add_successor_covers__add_progress_bitwise :
  forall cursor target,
    0 < cursor ->
    FenwickCovers cursor target ->
    FenwickCovers (cursor + FenwickLowbit cursor) target.
Proof.
  intros cursor target Hcursor Hcovers.
  unfold FenwickCovers, FenwickNodeLo in *.
  pose proof
    (FenwickLowbit_successor_growth__add_progress_bitwise cursor Hcursor)
    as Hgrowth.
  pose proof (FenwickLowbit_positive cursor Hcursor) as Hpositive.
  lia.
Qed.
Lemma Fenwick_add_successor_gap__add_progress_bitwise :
  forall cursor node,
    0 < cursor ->
    cursor < node < cursor + FenwickLowbit cursor ->
    cursor < FenwickNodeLo node.
Proof.
  intros cursor node Hcursor Hgap.
  unfold FenwickNodeLo.
  pose proof
    (FenwickLowbit_gap_bound__add_progress_bitwise
       cursor node Hcursor Hgap) as Hbound.
  lia.
Qed.
Lemma FenwickNodeSum_add_point__add_node_update :
  forall a target delta node,
    0 <= target < Zlength a ->
    0 < node < Zlength a ->
    (FenwickCovers node target ->
       FenwickNodeSum (FenwickAddArray a target delta) node =
       FenwickNodeSum a node + delta) /\
    (~ FenwickCovers node target ->
       FenwickNodeSum (FenwickAddArray a target delta) node =
       FenwickNodeSum a node).
Proof.
  intros a target delta node Htarget Hnode.
  pose proof (FenwickNodeLo_bounds node ltac:(lia)) as Hlo.
  unfold FenwickNodeSum, FenwickAddArray.
  split.
  - intros Hcovers.
    unfold FenwickCovers in Hcovers.
    assert (Hbefore :
      sublist (FenwickNodeLo node) target
        (replace_Znth target (Znth target a 0 + delta) a) =
      sublist (FenwickNodeLo node) target a).
    {
      apply (proj2 (list_eq_ext _ _ 0)).
      split.
      - rewrite !Zlength_sublist by
          (try rewrite Zlength_replace_Znth; lia).
        reflexivity.
      - intros i Hi.
        rewrite Zlength_sublist in Hi by
          (rewrite Zlength_replace_Znth; lia).
        rewrite !Znth_sublist by lia.
        apply Znth_replace_Znth_Diff; lia.
    }
    assert (Hafter :
      sublist (target + 1) (node + 1)
        (replace_Znth target (Znth target a 0 + delta) a) =
      sublist (target + 1) (node + 1) a).
    {
      apply (proj2 (list_eq_ext _ _ 0)).
      split.
      - rewrite !Zlength_sublist by
          (try rewrite Zlength_replace_Znth; lia).
        reflexivity.
      - intros i Hi.
        rewrite Zlength_sublist in Hi by
          (rewrite Zlength_replace_Znth; lia).
        rewrite !Znth_sublist by lia.
        apply Znth_replace_Znth_Diff; lia.
    }
    rewrite (sublist_split (FenwickNodeLo node) (node + 1) target
              (replace_Znth target (Znth target a 0 + delta) a))
      by (try rewrite Zlength_replace_Znth; lia).
    rewrite (sublist_split target (node + 1) (target + 1)
              (replace_Znth target (Znth target a 0 + delta) a))
      by (try rewrite Zlength_replace_Znth; lia).
    rewrite (sublist_split (FenwickNodeLo node) (node + 1) target a)
      by lia.
    rewrite (sublist_split target (node + 1) (target + 1) a)
      by lia.
    rewrite Hbefore, Hafter.
    rewrite (sublist_single 0 target
              (replace_Znth target (Znth target a 0 + delta) a))
      by (try rewrite Zlength_replace_Znth; lia).
    rewrite (Znth_replace_Znth_Same 0) by lia.
    rewrite (sublist_single 0 target a) by lia.
    repeat rewrite sum_app.
    simpl.
    lia.
  - intros Hnotcovers.
    unfold FenwickCovers in Hnotcovers.
    assert (Hsame :
      sublist (FenwickNodeLo node) (node + 1)
        (replace_Znth target (Znth target a 0 + delta) a) =
      sublist (FenwickNodeLo node) (node + 1) a).
    {
      apply (proj2 (list_eq_ext _ _ 0)).
      split.
      - rewrite !Zlength_sublist by
          (try rewrite Zlength_replace_Znth; lia).
        reflexivity.
      - intros i Hi.
        rewrite Zlength_sublist in Hi by
          (rewrite Zlength_replace_Znth; lia).
        rewrite !Znth_sublist by lia.
        apply Znth_replace_Znth_Diff; lia.
    }
    rewrite Hsame.
    reflexivity.
Qed.
Lemma Fenwick_query_step_int_safe__query_step :
  forall a bit n target cursor accumulator,
    FenwickRep a bit n ->
    (forall lo hi, 1 <= lo <= hi /\ hi <= n ->
       -2147483648 <= sum (sublist lo (hi + 1) a) <= 2147483647) ->
    0 < cursor ->
    cursor <= target ->
    target <= n ->
    FenwickQueryState a target cursor accumulator ->
    -2147483648 <= accumulator + Znth cursor bit 0 <= 2147483647.
Proof.
  intros a bit n target cursor accumulator
    Hrep Hsafe Hcursor Hcursor_target Htarget_n Hstate.
  pose proof (Fenwick_query_index_decreases cursor Hcursor) as Hdecrease.
  unfold FenwickRep in Hrep.
  destruct Hrep as [Halen [Hbitlen [Ha0 Hnodes]]].
  specialize (Hnodes cursor ltac:(lia)).
  assert (Htarget_partition :
    FenwickPrefixSum a target =
      FenwickPrefixSum a (cursor - FenwickLowbit cursor) +
      sum (sublist (cursor - FenwickLowbit cursor + 1)
                   (target + 1) a)).
  {
    unfold FenwickPrefixSum.
    rewrite (sublist_split 1 (target + 1)
               (cursor - FenwickLowbit cursor + 1) a) by lia.
    rewrite sum_app.
    reflexivity.
  }
  assert (Hstep_value :
    accumulator + Znth cursor bit 0 =
      sum (sublist (cursor - FenwickLowbit cursor + 1)
                   (target + 1) a)).
  {
    rewrite Hnodes.
    pose proof
      (Fenwick_prefix_node_partition a cursor ltac:(lia) ltac:(lia))
      as Hcursor_partition.
    unfold FenwickQueryState in Hstate.
    lia.
  }
  specialize
    (Hsafe (cursor - FenwickLowbit cursor + 1) target ltac:(lia)).
  lia.
Qed.
