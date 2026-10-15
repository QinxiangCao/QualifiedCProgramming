Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition RaiseCost (b c from target cost : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists blogs comments, blogs >= 0 /\ comments >= 0 /\
 target = from + 5 * blogs + comments /\ v = blogs * b + comments * c) (fun x => x) cost.
(* The k bloggers whose contributions are raised to one common value. *)
Definition ChosenBloggers (values : list Z) (k : Z) (chosen : list Z) : Prop :=
  Zlength chosen = k /\ NoDup chosen /\
  Forall (fun i => 0 <= i < Zlength values) chosen.

(* What bringing them to a common target costs altogether. *)
Definition TieCost (values : list Z) (k b c cost : Z) : Prop :=
  exists (chosen costs : list Z) (target : Z),
    ChosenBloggers values k chosen /\ Zlength costs = k /\
    (forall i, 0 <= i < k ->
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) /\
    cost = fold_right Z.add 0 costs.
Definition Pre (k b c : Z) (values : list Z) : Prop :=
  (* Stated explicitly in the P086 solver Require, so dropped here:
       Zlength values <= 200000 /\
       Forall (fun x => - 1000000000 <= x <= 1000000000) values /\
       2 <= k <= Zlength values /\
       1 <= b <= 1000 /\
       1 <= c <= 1000  *)
  True.

Definition Spec (k b c : Z) (values : list Z) (out : Z) : Prop := min_value_of_subset Z.le (TieCost values k b c) (fun x => x) out.

(* ------------------------------------------------------------------ *)
(* Contract-surface declarations for the four helper functions.        *)
(* ------------------------------------------------------------------ *)

(* Plain list sum, matching the [fold_right Z.add 0] used by [TieCost]. *)
Definition ZSum (l : list Z) : Z := fold_right Z.add 0 l.

(* Array-embedded binary max-heap: index arithmetic follows C's [(i-1)/2],
   which the generated goals read as [Z.quot]. *)
Definition HeapParent (child : Z) : Z := Z.quot (child - 1) 2.

(* Every parent/child edge whose parent index is at least [lo] is ordered.
   [lo = 0] is a full max-heap; [lo = root + 1] is the state in which only
   the subtrees strictly below [root] are known to be heaps, which is the
   precondition both sift-down callers establish. *)
Definition HeapOrderedFrom (l : list Z) (size lo : Z) : Prop :=
  forall child,
    0 < child ->
    child < size ->
    lo <= HeapParent child ->
    Znth (HeapParent child) l 0 >= Znth child l 0.

Definition HeapOrdered (l : list Z) (size : Z) : Prop :=
  HeapOrderedFrom l size 0.

(* Two parallel arrays abstracted as one list of pairs.  Permuting the two
   arrays independently would be unsound, so the sort contract is stated on
   the zipped list.  [combine] truncates at the shorter argument, hence the
   explicit length conjuncts. *)
Definition ZipPerm (t0 b0 t1 b1 : list Z) : Prop :=
  Zlength b0 = Zlength t0 /\
  Zlength t1 = Zlength t0 /\
  Zlength b1 = Zlength t0 /\
  Permutation (combine t0 b0) (combine t1 b1).

Definition Nondecreasing (l : list Z) : Prop :=
  forall i j,
    0 <= i ->
    i <= j ->
    j < Zlength l ->
    Znth i l 0 <= Znth j l 0.

(* ------------------------------------------------------------------ *)
(* Internal (body-only) declarations.                                  *)
(* ------------------------------------------------------------------ *)

(* --- hpush: sift-up ------------------------------------------------ *)

Definition HeapOrderExceptUp (l : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node -> node < size -> node <> child ->
    Znth (HeapParent node) l 0 >= Znth node l 0.

Definition PushHoleGuard (l : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node -> node < size -> HeapParent node = child ->
    Znth (HeapParent child) l 0 >= Znth node l 0.

Definition PushSiftState (l cur : list Z) (size child x : Z) : Prop :=
  Zlength cur = Zlength l /\
  Znth child cur 0 = x /\
  Permutation (sublist 0 (size + 1) cur) (x :: sublist 0 size l) /\
  HeapOrderExceptUp cur (size + 1) child /\
  PushHoleGuard cur (size + 1) child.

(* --- hpop: sift-down ----------------------------------------------- *)

Definition HeapOrderExceptDown (l : list Z) (size index : Z) : Prop :=
  forall child,
    0 < child -> child < size -> HeapParent child <> index ->
    Znth (HeapParent child) l 0 >= Znth child l 0.

Definition PopHoleGuard (l : list Z) (size index : Z) : Prop :=
  index = 0 \/
  (forall child,
     0 < child -> child < size -> HeapParent child = index ->
     Znth (HeapParent index) l 0 >= Znth child l 0).

Definition PopSiftState (l cur : list Z) (size index : Z) : Prop :=
  Zlength cur = Zlength l /\
  Permutation (sublist 0 (size - 1) cur) (sublist 1 size l) /\
  HeapOrderExceptDown cur (size - 1) index /\
  PopHoleGuard cur (size - 1) index.

(* --- sift_candidates: sift-down on zipped pairs --------------------- *)

Definition SiftState (t0 b0 t b : list Z) (size lo index : Z) : Prop :=
  ZipPerm t0 b0 t b /\
  sublist size (Zlength t0) t = sublist size (Zlength t0) t0 /\
  sublist size (Zlength b0) b = sublist size (Zlength b0) b0 /\
  (forall child,
     0 < child -> child < size -> lo <= HeapParent child ->
     HeapParent child <> index ->
     Znth (HeapParent child) t 0 >= Znth child t 0) /\
  (index = lo \/
   (forall child,
      0 < child -> child < size -> HeapParent child = index ->
      Znth (HeapParent index) t 0 >= Znth child t 0)).

(* --- sort_candidates: extraction phase ------------------------------ *)

Definition HeapSortState (t : list Z) (n hi : Z) : Prop :=
  Nondecreasing (sublist (hi + 1) n t) /\
  (forall p q,
     0 <= p -> p <= hi -> hi < q -> q < n ->
     Znth p t 0 <= Znth q t 0).

(* --- solver: shift and candidate normalisation ---------------------- *)

Definition ShiftedPrefix (values sh : list Z) (cnt : Z) : Prop :=
  forall i, 0 <= i < cnt -> Znth i sh 0 = Znth i values 0 + 2000000000.

(* Marginal price of one further block of five. *)
Definition WCost (b c : Z) : Z := Z.min b (5 * c).

(* Least value congruent to [j] mod 5 that is at least [s]. *)
Definition TargetPoint (s j : Z) : Z := s + (j - s) mod 5.

(* The part of blogger [s]'s raise cost that does not depend on the target. *)
Definition NormalizedBase (s j W c : Z) : Z :=
  ((j - s) mod 5) * c - ((TargetPoint s j - j) / 5) * W.

Definition CandPrefix (sh : list Z) (j W c cnt : Z) (t b : list Z) : Prop :=
  forall i, 0 <= i < cnt ->
    Znth i t 0 = TargetPoint (Znth i sh 0) j /\
    Znth i b 0 = NormalizedBase (Znth i sh 0) j W c.

(* --- solver: the k smallest bases ----------------------------------- *)

Definition SubMultiset (m l : list Z) : Prop :=
  exists rest, Permutation l (m ++ rest).

Definition MinSubMultiset (l m : list Z) : Prop :=
  SubMultiset m l /\
  (forall m',
     SubMultiset m' l -> Zlength m' = Zlength m -> ZSum m <= ZSum m').

Definition KSmallSum (l : list Z) (k s : Z) : Prop :=
  exists m, MinSubMultiset l m /\ Zlength m = k /\ s = ZSum m.

Definition HeapContent (sb : list Z) (i : Z) (H : list Z) (hsum : Z) : Prop :=
  MinSubMultiset (sublist 0 i sb) H /\ hsum = ZSum H.

(* --- solver: residue classes, the sweep and the running best -------- *)

Definition TieCostAtResidue (values : list Z) (k b c j cost : Z) : Prop :=
  exists (chosen costs : list Z) (target : Z),
    target mod 5 = j /\
    ChosenBloggers values k chosen /\
    Zlength costs = k /\
    (forall i, 0 <= i < k ->
       RaiseCost b c (Znth (Znth i chosen 0) values 0) target (Znth i costs 0)) /\
    cost = fold_right Z.add 0 costs.

Definition SweepValue (st sb : list Z) (k j W i v : Z) : Prop :=
  exists s,
    KSmallSum (sublist 0 (i + 1) sb) k s /\
    v = s + k * ((Znth i st 0 - j) / 5) * W.

Definition BestState (P : Z -> Prop) (best : Z) : Prop :=
  (best = -1 /\ forall v, ~ P v) \/
  (0 <= best /\ min_value_of_subset Z.le P (fun x => x) best).

Definition ResidueBest (values : list Z) (k b c j best : Z) : Prop :=
  BestState
    (fun v => exists j', 0 <= j' < j /\ TieCostAtResidue values k b c j' v)
    best.

Definition SweepSet
    (values : list Z) (k b c j : Z) (st sb : list Z) (W i : Z) (v : Z) : Prop :=
  (exists j', 0 <= j' < j /\ TieCostAtResidue values k b c j' v) \/
  (exists i', k - 1 <= i' /\ i' < i /\ SweepValue st sb k j W i' v).

Definition SweepBest
    (values : list Z) (k b c j : Z) (st sb : list Z) (W i best : Z) : Prop :=
  BestState (SweepSet values k b c j st sb W i) best.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Logic.Classical.
Require Import Coq.ZArith.Zcomplements.
Lemma Zlength_replace_Znth__hpush_sift_up :
  forall {A : Type} (l : list A) (n : Z) (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  revert n.
  induction l ; simpl in * ; intros ; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  + simpl. do 2 rewrite Zlength_cons. lia.
  + simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma replace_nth_comm__hpush_sift_up :
  forall {A : Type} ni nj (l : list A) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni. induction ni as [|ni IH]; intros nj l a b Hneq;
    destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl; [contradiction Hneq; reflexivity | reflexivity].
  - destruct nj; reflexivity.
  - destruct nj; simpl; [reflexivity |].
    f_equal. apply IH. intros Heq. apply Hneq. now f_equal.
Qed.
Lemma replace_Znth_swap_form__hpush_sift_up :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  pose proof (Zlength_nonneg l2).
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  change (replace_Znth 0 xj (xi :: l2 ++ xj :: l3))
    with (xj :: l2 ++ xj :: l3).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__hpush_sift_up :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < j ->
    j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hij Hj.
  remember (Znth i l d) as xi.
  remember (Znth j l d) as xj.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi :: lr).
  {
    subst l1 lr ni.
    rewrite (firstn_skipSn d (Z.to_nat i) l) at 1.
    2: { rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi. reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj :: l3).
  {
    subst l2 l3.
    rewrite (firstn_skipSn d nj lr) at 1 by exact Hj_lr.
    replace xj with (nth nj lr d).
    2: {
      subst nj lr ni. rewrite Heqxj. unfold Znth.
      rewrite nth_skipn.
      assert ((Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat =
              Z.to_nat j).
      {
        apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia. lia.
      }
      rewrite Nat.add_comm, H. reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi :: l2 ++ xj :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi :: l2 ++ xj :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2: {
    subst l1 ni. rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2: {
    subst l1 l2 lr ni nj. rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  rewrite replace_Znth_swap_form__hpush_sift_up.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma permutation_swap_Znth__hpush_sift_up :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hij].
  - apply permutation_swap_Znth_lt__hpush_sift_up; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + assert (Hcomm : forall a b,
        replace_Znth j b (replace_Znth i a l) =
        replace_Znth i a (replace_Znth j b l)).
      {
        intros a b. unfold replace_Znth.
        apply replace_nth_comm__hpush_sift_up. intro Heq.
        apply Z2Nat.inj in Heq; lia.
      }
      rewrite Hcomm.
      apply permutation_swap_Znth_lt__hpush_sift_up; lia.
    + assert (i = j) by lia. subst j.
      rewrite replace_Znth_Znth, replace_Znth_Znth.
      apply Permutation_refl.
Qed.
Lemma sublist_replace_Znth_lt__hpush_sift_up :
  forall (l : list Z) (n i v : Z),
    0 <= i < n ->
    n <= Zlength l ->
    sublist 0 n (replace_Znth i v l) = replace_Znth i v (sublist 0 n l).
Proof.
  intros l n i v Hi Hn.
  assert (HL : Zlength (replace_Znth i v l) = Zlength l)
    by apply Zlength_replace_Znth__hpush_sift_up.
  assert (HS : Zlength (sublist 0 n l) = n)
    by (apply Zlength_sublist0; lia).
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite Zlength_sublist0 by lia.
    rewrite Zlength_replace_Znth__hpush_sift_up.
    lia.
  - intros k Hk.
    rewrite Zlength_sublist0 in Hk by lia.
    rewrite Znth_sublist0 by lia.
    destruct (Z.eq_dec k i) as [Heq | Hne].
    + subst k.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_sublist0 by lia.
      reflexivity.
Qed.
Lemma sublist_replace_Znth_ge__hpush_sift_up :
  forall (l : list Z) (n i v : Z),
    0 <= n ->
    n <= i ->
    i < Zlength l ->
    sublist 0 n (replace_Znth i v l) = sublist 0 n l.
Proof.
  intros l n i v Hn Hni Hi.
  assert (HL : Zlength (replace_Znth i v l) = Zlength l)
    by apply Zlength_replace_Znth__hpush_sift_up.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite Zlength_sublist0 by lia.
    rewrite Zlength_sublist0 by lia.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist0 in Hk by lia.
    rewrite Znth_sublist0 by lia.
    rewrite Znth_sublist0 by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.
Lemma znth_replace_bounds__hpush_sift_up :
  forall (l : list Z) (i v lo hi n : Z),
    0 <= i < Zlength l ->
    n <= Zlength l ->
    lo <= v <= hi ->
    (forall q, 0 <= q < n -> q <> i -> lo <= Znth q l 0 <= hi) ->
    forall q, 0 <= q < n -> lo <= Znth q (replace_Znth i v l) 0 <= hi.
Proof.
  intros l i v lo hi n Hi Hn Hv Hall q Hq.
  destruct (Z.eq_dec q i) as [Heq | Hne].
  - subst q. rewrite Znth_replace_Znth_Same by lia. lia.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hall; lia.
Qed.
Lemma heap_parent_range__hpush_sift_up :
  forall n : Z, 0 < n -> 0 <= HeapParent n < n.
Proof.
  intros n Hn. unfold HeapParent. split.
  - apply Z.quot_pos; lia.
  - apply Z.le_lt_trans with (m := n - 1); [| lia].
    apply Z.quot_le_upper_bound; lia.
Qed.
Lemma heap_parent_zero__hpush_sift_up : HeapParent 0 = 0.
Proof. unfold HeapParent. reflexivity. Qed.
Lemma push_sift_state_init__hpush_sift_up :
  forall (l : list Z) (hs v : Z),
    0 <= hs ->
    hs < Zlength l ->
    HeapOrdered l hs ->
    PushSiftState l (replace_Znth hs v l) hs hs v.
Proof.
  intros l hs v Hhs0 Hhs Hord.
  unfold HeapOrdered, HeapOrderedFrom in Hord.
  assert (HL : Zlength (replace_Znth hs v l) = Zlength l)
    by apply Zlength_replace_Znth__hpush_sift_up.
  unfold PushSiftState. split; [exact HL | ].
  split; [apply Znth_replace_Znth_Same; lia | ].
  split.
  - rewrite (sublist_split 0 (hs + 1) hs) by lia.
    rewrite sublist_replace_Znth_ge__hpush_sift_up by lia.
    rewrite (sublist_single 0) by lia.
    rewrite Znth_replace_Znth_Same by lia.
    apply Permutation_sym. apply Permutation_cons_append.
  - split.
    + unfold HeapOrderExceptUp. intros node Hn0 Hnlt Hne.
      pose proof (heap_parent_range__hpush_sift_up node Hn0) as Hpr.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hord; lia.
    + unfold PushHoleGuard. intros node Hn0 Hnlt Hpar.
      pose proof (heap_parent_range__hpush_sift_up node Hn0) as Hpr.
      lia.
Qed.
Lemma push_sift_state_swap__hpush_sift_up :
  forall (l cur : list Z) (hs i p v : Z),
    0 <= hs ->
    hs < Zlength l ->
    0 < i ->
    i <= hs ->
    p = HeapParent i ->
    Znth p cur 0 < Znth i cur 0 ->
    PushSiftState l cur hs i v ->
    PushSiftState l
      (replace_Znth i (Znth p cur 0) (replace_Znth p (Znth i cur 0) cur))
      hs p v.
Proof.
  intros l cur hs i p v Hhs0 Hhs Hi0 Hihs Hp Hlt HS.
  pose proof (heap_parent_range__hpush_sift_up i Hi0) as Hpr.
  rewrite <- Hp in Hpr.
  destruct HS as (HLen & HZnth & HPerm & HExc & HGuard).
  assert (HLcur : Zlength cur = Zlength l) by exact HLen.
  remember (Znth p cur 0) as a eqn:Ha.
  remember (Znth i cur 0) as b eqn:Hb.
  assert (HLin : Zlength (replace_Znth p b cur) = Zlength cur)
    by apply Zlength_replace_Znth__hpush_sift_up.
  assert (HLout : Zlength (replace_Znth i a (replace_Znth p b cur)) = Zlength cur)
    by (rewrite Zlength_replace_Znth__hpush_sift_up; exact HLin).
  assert (Hatp : Znth p (replace_Znth i a (replace_Znth p b cur)) 0 = b).
  { rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hati : Znth i (replace_Znth i a (replace_Znth p b cur)) 0 = a).
  { rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (Hoth : forall q, 0 <= q < Zlength cur -> q <> p -> q <> i ->
                 Znth q (replace_Znth i a (replace_Znth p b cur)) 0 = Znth q cur 0).
  { intros q Hq Hqp Hqi.
    rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  unfold PushSiftState. split; [lia | ].
  split; [rewrite Hatp; exact HZnth | ].
  split.
  - apply Permutation_trans with (l' := sublist 0 (hs + 1) cur); [| exact HPerm].
    rewrite sublist_replace_Znth_lt__hpush_sift_up by lia.
    rewrite sublist_replace_Znth_lt__hpush_sift_up by lia.
    assert (HSL : Zlength (sublist 0 (hs + 1) cur) = hs + 1)
      by (apply Zlength_sublist0; lia).
    assert (Hpa : a = Znth p (sublist 0 (hs + 1) cur) 0)
      by (rewrite Znth_sublist0 by lia; exact Ha).
    assert (Hib : b = Znth i (sublist 0 (hs + 1) cur) 0)
      by (rewrite Znth_sublist0 by lia; exact Hb).
    rewrite Hpa at 1. rewrite Hib at 1.
    apply Permutation_sym.
    apply permutation_swap_Znth__hpush_sift_up; lia.
  - split.
    + unfold HeapOrderExceptUp. intros node Hn0 Hnlt Hne.
      pose proof (heap_parent_range__hpush_sift_up node Hn0) as Hprn.
      destruct (Z.eq_dec node i) as [Hni | Hni].
      * subst node. rewrite <- Hp. rewrite Hatp, Hati. lia.
      * rewrite (Hoth node) by lia.
        destruct (Z.eq_dec (HeapParent node) p) as [Hep | Hep].
        { rewrite Hep, Hatp.
          assert (Znth (HeapParent node) cur 0 >= Znth node cur 0)
            by (apply HExc; lia).
          rewrite Hep in H. lia. }
        destruct (Z.eq_dec (HeapParent node) i) as [Hei | Hei].
        { rewrite Hei, Hati.
          assert (Znth (HeapParent i) cur 0 >= Znth node cur 0)
            by (apply HGuard; lia).
          rewrite <- Hp in H. lia. }
        { rewrite (Hoth (HeapParent node)) by lia.
          apply HExc; lia. }
    + unfold PushHoleGuard. intros node Hn0 Hnlt Hpar.
      pose proof (heap_parent_range__hpush_sift_up node Hn0) as Hprn.
      destruct (Z.eq_dec p 0) as [Hp0 | Hp0].
      * assert (Hgpp : HeapParent p = p)
          by (rewrite Hp0; apply heap_parent_zero__hpush_sift_up).
        rewrite Hgpp, Hatp.
        destruct (Z.eq_dec node i) as [Hni | Hni].
        { subst node. rewrite Hati. lia. }
        { rewrite (Hoth node) by lia.
          assert (Znth (HeapParent node) cur 0 >= Znth node cur 0)
            by (apply HExc; lia).
          rewrite Hpar in H. lia. }
      * pose proof (heap_parent_range__hpush_sift_up p ltac:(lia)) as Hprp.
        rewrite (Hoth (HeapParent p)) by lia.
        assert (Hgp : Znth (HeapParent p) cur 0 >= Znth p cur 0)
          by (apply HExc; lia).
        destruct (Z.eq_dec node i) as [Hni | Hni].
        { subst node. rewrite Hati. lia. }
        { rewrite (Hoth node) by lia.
          assert (Znth (HeapParent node) cur 0 >= Znth node cur 0)
            by (apply HExc; lia).
          rewrite Hpar in H. lia. }
Qed.
Lemma push_sift_state_to_heap_ordered__hpush_sift_up :
  forall (l cur : list Z) (hs i v : Z),
    PushSiftState l cur hs i v ->
    (i = 0 \/ Znth (HeapParent i) cur 0 >= Znth i cur 0) ->
    HeapOrdered cur (hs + 1).
Proof.
  intros l cur hs i v HS Hedge.
  destruct HS as (_ & _ & _ & HExc & _).
  unfold HeapOrdered, HeapOrderedFrom. intros child Hc0 Hclt _.
  destruct (Z.eq_dec child i) as [Heq | Hne].
  - subst child. destruct Hedge as [He | He]; [lia | exact He].
  - apply HExc; auto.
Qed.
Lemma zlength_replace_Znth__hpop_sift_right_child :
  forall {A : Type} (l : list A) (i : Z) (v : A),
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
Lemma replace_Znth_0_cons__hpop_sift_right_child :
  forall {A : Type} (v x : A) (t : list A),
    replace_Znth 0 v (x :: t) = v :: t.
Proof.
  intros. reflexivity.
Qed.
Lemma perm_move_head__hpop_sift_right_child :
  forall (a : Z) (l : list Z) (j : Z),
    0 <= j < Zlength l ->
    Permutation (a :: l) (Znth j l 0 :: replace_Znth j a l).
Proof.
  intros a l. revert a.
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
Lemma perm_swap_replace_Znth__hpop_sift_right_child :
  forall (l : list Z) (i j : Z),
    0 <= i ->
    i < j ->
    j < Zlength l ->
    Permutation
      (replace_Znth i (Znth j l 0) (replace_Znth j (Znth i l 0) l)) l.
Proof.
  induction l as [|a l IH]; intros i j Hi Hij Hj.
  - rewrite Zlength_nil in Hj. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons.
      rewrite replace_Znth_cons by lia.
      rewrite replace_Znth_0_cons__hpop_sift_right_child.
      rewrite Znth_cons by lia.
      apply Permutation_sym.
      apply perm_move_head__hpop_sift_right_child.
      rewrite Zlength_cons in Hj. lia.
    + rewrite !Znth_cons by lia.
      rewrite replace_Znth_cons by lia.
      rewrite replace_Znth_cons by lia.
      apply perm_skip. apply IH; try lia.
      rewrite Zlength_cons in Hj. lia.
Qed.
Lemma sublist0_replace_Znth__hpop_sift_right_child :
  forall (l : list Z) (n i v : Z),
    0 <= i < n ->
    n <= Zlength l ->
    sublist 0 n (replace_Znth i v l) = replace_Znth i v (sublist 0 n l).
Proof.
  intros l n i v Hi Hn.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite zlength_replace_Znth__hpop_sift_right_child.
    rewrite Zlength_sublist0 by
      (rewrite ?zlength_replace_Znth__hpop_sift_right_child; lia).
    rewrite Zlength_sublist0 by lia. reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist0 in Hk by
      (rewrite ?zlength_replace_Znth__hpop_sift_right_child; lia).
    destruct (Z.eq_dec k i) as [-> | Hne].
    + rewrite Znth_sublist0 by lia.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_sublist0 by lia; lia).
      reflexivity.
    + rewrite Znth_sublist0 by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_sublist0 by lia; lia).
      rewrite Znth_sublist0 by lia. reflexivity.
Qed.
Lemma heap_parent_child__hpop_sift_right_child :
  forall (i child : Z),
    0 <= i ->
    0 < child ->
    HeapParent (2 * i + 1) = i /\
    HeapParent (2 * i + 1 + 1) = i /\
    0 <= HeapParent child < child.
Proof.
  intros i child Hi Hchild. unfold HeapParent.
  rewrite !Z.quot_div_nonneg by lia.
  assert (Hd : forall a b, 0 <= a < 2 -> (2 * b + a) / 2 = b).
  {
    intros a b Ha. rewrite Z.mul_comm. rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia. lia.
  }
  split; [| split].
  - replace (2 * i + 1 - 1) with (2 * i + 0) by ring.
    rewrite Hd by lia. reflexivity.
  - replace (2 * i + 1 + 1 - 1) with (2 * i + 1) by ring.
    rewrite Hd by lia. reflexivity.
  - assert (Hup : (child - 1) / 2 <= child - 1) by
      (apply Z.div_le_upper_bound; lia).
    assert (Hlo : 0 <= (child - 1) / 2) by
      (apply Z.div_pos; lia).
    lia.
Qed.
Lemma heap_parent_children__hpop_sift_right_child :
  forall (i child : Z),
    0 <= i ->
    0 < child ->
    HeapParent child = i ->
    child = 2 * i + 1 \/ child = 2 * i + 1 + 1.
Proof.
  intros i child Hi Hchild Hp. unfold HeapParent in Hp.
  rewrite Z.quot_div_nonneg in Hp by lia.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hrem.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hquot.
  rewrite Hp in Hquot.
  assert (Hcase : (child - 1) mod 2 = 0 \/ (child - 1) mod 2 = 1) by lia.
  lia.
Qed.
Lemma pop_sift_state_swap_right__hpop_sift_right_child :
  forall (l cur : list Z) (hs i : Z),
    0 <= i ->
    hs <= Zlength cur ->
    2 * i + 1 < hs - 1 ->
    2 * i + 1 + 1 < hs - 1 ->
    Znth (2 * i + 1 + 1) cur 0 > Znth i cur 0 ->
    Znth (2 * i + 1 + 1) cur 0 >= Znth (2 * i + 1) cur 0 ->
    PopSiftState l cur hs i ->
    PopSiftState l
      (replace_Znth i (Znth (2 * i + 1 + 1) cur 0)
         (replace_Znth (2 * i + 1 + 1) (Znth i cur 0) cur))
      hs (2 * i + 1 + 1).
Proof.
  intros l cur hs i Hi Hlen Hleft Hright Hgt Hsib HState.
  destruct HState as [Hzl [Hperm [Horder Hguard]]].
  unfold HeapOrderExceptDown in Horder.
  unfold PopHoleGuard in Hguard.
  assert (Hicur : 0 <= i < Zlength cur) by lia.
  assert (Hrcur : 0 <= 2 * i + 1 + 1 < Zlength cur) by lia.
  assert (Hnew_i :
    Znth i (replace_Znth i (Znth (2 * i + 1 + 1) cur 0)
              (replace_Znth (2 * i + 1 + 1) (Znth i cur 0) cur)) 0
    = Znth (2 * i + 1 + 1) cur 0).
  {
    rewrite Znth_replace_Znth_Same by
      (rewrite ?zlength_replace_Znth__hpop_sift_right_child; lia).
    reflexivity.
  }
  assert (Hnew_r :
    Znth (2 * i + 1 + 1) (replace_Znth i (Znth (2 * i + 1 + 1) cur 0)
              (replace_Znth (2 * i + 1 + 1) (Znth i cur 0) cur)) 0
    = Znth i cur 0).
  {
    rewrite Znth_replace_Znth_Diff by
      (rewrite ?zlength_replace_Znth__hpop_sift_right_child; lia).
    rewrite Znth_replace_Znth_Same by lia. reflexivity.
  }
  assert (Hnew_o : forall k,
    0 <= k < Zlength cur -> k <> i -> k <> 2 * i + 1 + 1 ->
    Znth k (replace_Znth i (Znth (2 * i + 1 + 1) cur 0)
              (replace_Znth (2 * i + 1 + 1) (Znth i cur 0) cur)) 0
    = Znth k cur 0).
  {
    intros k Hk Hk1 Hk2.
    rewrite Znth_replace_Znth_Diff by
      (rewrite ?zlength_replace_Znth__hpop_sift_right_child; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  unfold PopSiftState. split; [| split; [| split]].
  - rewrite !zlength_replace_Znth__hpop_sift_right_child. exact Hzl.
  - apply Permutation_trans with (l' := sublist 0 (hs - 1) cur);
      [| exact Hperm].
    rewrite sublist0_replace_Znth__hpop_sift_right_child by
      (rewrite ?zlength_replace_Znth__hpop_sift_right_child; lia).
    rewrite sublist0_replace_Znth__hpop_sift_right_child by lia.
    rewrite <- (Znth_sublist0 0 (2 * i + 1 + 1) (hs - 1) cur) by lia.
    rewrite <- (Znth_sublist0 0 i (hs - 1) cur) by lia.
    apply perm_swap_replace_Znth__hpop_sift_right_child.
    + lia.
    + lia.
    + rewrite Zlength_sublist0 by lia. lia.
  - unfold HeapOrderExceptDown. intros child Hc0 Hcn Hcp.
    pose proof (heap_parent_child__hpop_sift_right_child i child Hi Hc0)
      as [Hpl [Hpr Hpb]].
    assert (Hccur : 0 <= child < Zlength cur) by lia.
    destruct (Z.eq_dec child i) as [Hci | Hci].
    + subst child.
      rewrite Hnew_i.
      rewrite Hnew_o by lia.
      destruct Hguard as [Hi0 | Hg].
      * lia.
      * apply Hg; [lia | lia | exact Hpr].
    + destruct (Z.eq_dec child (2 * i + 1 + 1)) as [Hcr | Hcr].
      * subst child.
        rewrite Hpr. rewrite Hnew_i. rewrite Hnew_r. lia.
      * destruct (Z.eq_dec (HeapParent child) i) as [Hpi | Hpi].
        -- pose proof
             (heap_parent_children__hpop_sift_right_child i child Hi Hc0 Hpi)
             as [Hc | Hc]; [| lia].
           rewrite Hpi. rewrite Hnew_i.
           rewrite Hnew_o by lia.
           rewrite Hc. lia.
        -- rewrite !Hnew_o by lia.
           apply Horder; [lia | lia | exact Hpi].
  - unfold PopHoleGuard. right. intros child Hc0 Hcn Hcp.
    pose proof (heap_parent_child__hpop_sift_right_child i child Hi Hc0)
      as [Hpl [Hpr Hpb]].
    assert (Hccur : 0 <= child < Zlength cur) by lia.
    rewrite Hpr. rewrite Hnew_i.
    rewrite Hnew_o by lia.
    rewrite <- Hcp.
    apply Horder; [lia | lia | lia].
Qed.
Lemma Zlength_replace_Znth__hpop_sift_left_child :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  + simpl. do 2 rewrite Zlength_cons. lia.
  + simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma heap_parent_bounds__hpop_sift_left_child :
  forall child, 0 < child -> 0 <= HeapParent child < child.
Proof.
  intros child Hchild.
  unfold HeapParent.
  split.
  - apply Z.quot_pos; lia.
  - apply Z.quot_lt_upper_bound; lia.
Qed.
Lemma heap_parent_left__hpop_sift_left_child :
  forall i, HeapParent (2 * i + 1) = i.
Proof.
  intros i.
  unfold HeapParent.
  replace (2 * i + 1 - 1) with (i * 2) by lia.
  apply Z.quot_mul.
  lia.
Qed.
Lemma heap_children_char__hpop_sift_left_child :
  forall index child,
    0 < child ->
    HeapParent child = index ->
    child = 2 * index + 1 \/ child = 2 * index + 2.
Proof.
  intros index child Hchild Hparent.
  unfold HeapParent in Hparent.
  pose proof (Z.rem_bound_pos_pos (child - 1) 2 ltac:(lia) ltac:(lia)) as Hrem.
  pose proof (Z.quot_rem (child - 1) 2 ltac:(lia)) as Hquot.
  rewrite Hparent in Hquot.
  lia.
Qed.
Lemma heap_root_is_max__hpop_sift_left_child :
  forall (l : list Z) (size q : Z),
    HeapOrdered l size ->
    0 <= q < size ->
    Znth q l 0 <= Znth 0 l 0.
Proof.
  intros l size q Hordered Hq.
  unfold HeapOrdered, HeapOrderedFrom in Hordered.
  remember (Z.to_nat q) as n eqn:Hn.
  assert (Hqn : q = Z.of_nat n).
  { subst n. symmetry. apply Z2Nat.id. lia. }
  subst q.
  clear Hn.
  revert Hq.
  induction n as [n IH] using lt_wf_ind.
  intro Hq.
  destruct n as [| n].
  - simpl. lia.
  - assert (Hpos : 0 < Z.of_nat (S n)) by lia.
    pose proof (heap_parent_bounds__hpop_sift_left_child _ Hpos) as Hpb.
    assert (Hnat : (Z.to_nat (HeapParent (Z.of_nat (S n))) < S n)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    specialize (IH _ Hnat).
    rewrite Z2Nat.id in IH by lia.
    specialize (IH ltac:(lia)).
    pose proof (Hordered (Z.of_nat (S n)) Hpos ltac:(lia) ltac:(lia)) as Hedge.
    lia.
Qed.
Lemma replace_nth_comm__hpop_sift_left_child :
  forall ni nj (l : list Z) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [| x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.
Lemma replace_Znth_comm__hpop_sift_left_child :
  forall (l : list Z) i j (a b : Z),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm__hpop_sift_left_child.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.
Lemma replace_Znth_swap_form__hpop_sift_left_child :
  forall (l1 l2 l3 : list Z) (xi xj : Z),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r
    with (l1 := l1) (l2 := xi :: l2 ++ xj :: l3)
    by (subst n1; lia).
  rewrite (replace_Znth_nothing n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) = xj :: l2 ++ xj :: l3)
    by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r
    with (l1 := l1) (l2 := xj :: l2 ++ xj :: l3)
    by (subst n2; lia).
  rewrite (replace_Znth_nothing (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__hpop_sift_left_child :
  forall (l : list Z) i j (d : Z),
    0 <= i ->
    i < j ->
    j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hij Hj.
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (firstn_skipSn d (Z.to_nat i) l) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (firstn_skipSn d nj lr) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat : (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form__hpop_sift_left_child.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.
Lemma permutation_swap_Znth__hpop_sift_left_child :
  forall (l : list Z) i j (d : Z),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt__hpop_sift_left_child; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm__hpop_sift_left_child by lia.
      apply permutation_swap_Znth_lt__hpop_sift_left_child; lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth.
      rewrite replace_Znth_Znth.
      apply Permutation_refl.
Qed.
Lemma sublist0_replace_Znth_inside__hpop_sift_left_child :
  forall (l : list Z) hi i value,
    0 <= i < hi ->
    hi <= Zlength l ->
    sublist 0 hi (replace_Znth i value l) =
    replace_Znth i value (sublist 0 hi l).
Proof.
  intros l hi i value Hi Hhi.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Zlength_sublist0 by (rewrite Zlength_replace_Znth__hpop_sift_left_child; lia).
    rewrite Zlength_replace_Znth__hpop_sift_left_child.
    rewrite Zlength_sublist0 by lia.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist0 in Hk by (rewrite Zlength_replace_Znth__hpop_sift_left_child; lia).
    rewrite Znth_sublist0 by lia.
    destruct (Z.eq_dec k i) as [-> | Hki].
    + rewrite !Znth_replace_Znth_Same.
      * reflexivity.
      * rewrite Zlength_sublist0 by lia. lia.
      * lia.
    + rewrite !Znth_replace_Znth_Diff.
      * rewrite Znth_sublist0 by lia. reflexivity.
      * rewrite Zlength_sublist0 by lia. lia.
      * rewrite Zlength_sublist0 by lia. lia.
      * lia.
      * lia.
      * lia.
      * lia.
Qed.
Lemma pop_init_permutation__hpop_sift_left_child :
  forall (l : list Z) (hs cap : Z),
    1 <= hs ->
    hs <= cap ->
    Zlength l = cap ->
    Permutation
      (sublist 0 (hs - 1) (replace_Znth 0 (Znth (hs - 1) l 0) l))
      (sublist 1 hs l).
Proof.
  intros l hs cap Hhs Hcap Hlen.
  destruct (Z.eq_dec hs 1) as [Heq | Hneq].
  - subst hs.
    rewrite (Zsublist_nil (replace_Znth 0 (Znth (1 - 1) l 0) l) 0 (1 - 1)) by lia.
    rewrite (Zsublist_nil l 1 1) by lia.
    apply Permutation_refl.
  - destruct l as [| h t].
    { rewrite Zlength_nil in Hlen. lia. }
    rewrite Zlength_cons in Hlen.
    rewrite Znth_cons by lia.
    assert (Hrep :
      replace_Znth 0 (Znth (hs - 1 - 1) t 0) (h :: t) =
      Znth (hs - 1 - 1) t 0 :: t) by reflexivity.
    rewrite Hrep.
    rewrite sublist_cons1 by lia.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons; lia).
    replace (1 - 1) with 0 by lia.
    replace (hs - 1 - 1) with (hs - 2) by lia.
    rewrite (sublist_split 0 (hs - 1) (hs - 2) t) by lia.
    replace (hs - 1) with (hs - 2 + 1) by lia.
    rewrite (sublist_single 0 (hs - 2) t) by lia.
    change
      (Permutation
         ((Znth (hs - 2) t 0 :: nil) ++ sublist 0 (hs - 2) t)
         (sublist 0 (hs - 2) t ++ (Znth (hs - 2) t 0 :: nil))).
    apply Permutation_app_comm.
Qed.
Lemma pop_init_bounds__hpop_sift_left_child :
  forall (l : list Z) (hs cap q : Z),
    1 <= hs ->
    hs <= cap ->
    Zlength l = cap ->
    (forall x, 0 <= x < hs -> -1000000000000 <= Znth x l 0 <= 1000000000000) ->
    0 <= q < hs - 1 ->
    -1000000000000 <= Znth q (replace_Znth 0 (Znth (hs - 1) l 0) l) 0
      <= 1000000000000.
Proof.
  intros l hs cap q Hhs Hcap Hlen Hbnd Hq.
  destruct (Z.eq_dec q 0) as [-> | Hq0].
  - rewrite Znth_replace_Znth_Same by lia.
    apply Hbnd. lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hbnd. lia.
Qed.
Lemma pop_sift_state_init__hpop_sift_left_child :
  forall (l : list Z) (hs cap : Z),
    1 <= hs ->
    hs <= cap ->
    Zlength l = cap ->
    HeapOrdered l hs ->
    PopSiftState l (replace_Znth 0 (Znth (hs - 1) l 0) l) hs 0.
Proof.
  intros l hs cap Hhs Hcap Hlen Hord.
  unfold PopSiftState.
  split; [| split; [| split]].
  - rewrite Zlength_replace_Znth__hpop_sift_left_child. reflexivity.
  - eapply pop_init_permutation__hpop_sift_left_child; eauto.
  - unfold HeapOrderExceptDown.
    intros child Hc0 Hchs Hpne.
    pose proof (heap_parent_bounds__hpop_sift_left_child child Hc0) as Hpb.
    rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    unfold HeapOrdered, HeapOrderedFrom in Hord.
    apply Hord; lia.
  - unfold PopHoleGuard. left. reflexivity.
Qed.
Lemma pop_sift_state_swap_left__hpop_sift_left_child :
  forall (l cur : list Z) (hs cap i : Z),
    Zlength l = cap ->
    Zlength cur = cap ->
    hs <= cap ->
    0 <= i ->
    2 * i + 1 < hs - 1 ->
    Znth (2 * i + 1) cur 0 > Znth i cur 0 ->
    (2 * i + 2 < hs - 1 ->
       Znth (2 * i + 2) cur 0 <= Znth (2 * i + 1) cur 0) ->
    PopSiftState l cur hs i ->
    PopSiftState l
      (replace_Znth i (Znth (2 * i + 1) cur 0)
        (replace_Znth (2 * i + 1) (Znth i cur 0) cur))
      hs (2 * i + 1).
Proof.
  intros l cur hs cap i Hl Hcur Hhs Hi Hchild Hlt Hsib Hstate.
  destruct Hstate as [Hlen [Hperm [Hexcept Hhole]]].
  assert (Hsw_i :
    Znth i (replace_Znth i (Znth (2 * i + 1) cur 0)
             (replace_Znth (2 * i + 1) (Znth i cur 0) cur)) 0
    = Znth (2 * i + 1) cur 0).
  { rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth__hpop_sift_left_child; lia).
    reflexivity. }
  assert (Hsw_c :
    Znth (2 * i + 1) (replace_Znth i (Znth (2 * i + 1) cur 0)
             (replace_Znth (2 * i + 1) (Znth i cur 0) cur)) 0
    = Znth i cur 0).
  { rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth__hpop_sift_left_child; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity. }
  assert (Hsw_o : forall k,
    0 <= k < Zlength cur -> k <> i -> k <> 2 * i + 1 ->
    Znth k (replace_Znth i (Znth (2 * i + 1) cur 0)
             (replace_Znth (2 * i + 1) (Znth i cur 0) cur)) 0
    = Znth k cur 0).
  { intros k Hk H1 H2.
    rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth__hpop_sift_left_child; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity. }
  unfold PopSiftState.
  split; [| split; [| split]].
  - rewrite !Zlength_replace_Znth__hpop_sift_left_child. exact Hlen.
  - assert (Hpre :
      sublist 0 (hs - 1)
        (replace_Znth i (Znth (2 * i + 1) cur 0)
          (replace_Znth (2 * i + 1) (Znth i cur 0) cur))
      = replace_Znth i (Znth (2 * i + 1) cur 0)
          (replace_Znth (2 * i + 1) (Znth i cur 0) (sublist 0 (hs - 1) cur))).
    { rewrite sublist0_replace_Znth_inside__hpop_sift_left_child
        by (rewrite ?Zlength_replace_Znth__hpop_sift_left_child; lia).
      rewrite sublist0_replace_Znth_inside__hpop_sift_left_child by lia.
      reflexivity. }
    rewrite Hpre.
    eapply Permutation_trans; [| exact Hperm].
    apply Permutation_sym.
    replace (Znth i cur 0) with (Znth i (sublist 0 (hs - 1) cur) 0)
      by (rewrite Znth_sublist0 by lia; reflexivity).
    replace (Znth (2 * i + 1) cur 0)
      with (Znth (2 * i + 1) (sublist 0 (hs - 1) cur) 0)
      by (rewrite Znth_sublist0 by lia; reflexivity).
    apply permutation_swap_Znth__hpop_sift_left_child;
      rewrite Zlength_sublist0 by lia; lia.
  - unfold HeapOrderExceptDown.
    intros child Hc0 Hchs Hpne.
    pose proof (heap_parent_bounds__hpop_sift_left_child child Hc0) as Hpb.
    unfold HeapOrderExceptDown in Hexcept.
    destruct (Z.eq_dec (HeapParent child) i) as [Hpi | Hpni].
    + destruct (Z.eq_dec child (2 * i + 1)) as [Hcs | Hcns].
      * rewrite Hpi, Hcs, Hsw_i, Hsw_c. lia.
      * pose proof (heap_children_char__hpop_sift_left_child i child Hc0 Hpi)
          as Hcc.
        assert (Hc2 : child = 2 * i + 2) by (destruct Hcc; lia).
        rewrite Hpi, Hsw_i, Hc2.
        rewrite Hsw_o by lia.
        pose proof (Hsib ltac:(lia)). lia.
    + destruct (Z.eq_dec child i) as [Hci | Hcni].
      * assert (Hipos : 0 < i) by lia.
        pose proof (heap_parent_bounds__hpop_sift_left_child i Hipos) as Hpbi.
        rewrite Hci.
        rewrite Hsw_i.
        rewrite Hsw_o by lia.
        unfold PopHoleGuard in Hhole.
        destruct Hhole as [Hz | Hdom]; [lia |].
        pose proof
          (Hdom (2 * i + 1) ltac:(lia) ltac:(lia)
             (heap_parent_left__hpop_sift_left_child i)) as Hd.
        lia.
      * assert (Hcns : child <> 2 * i + 1).
        { intro Hc. rewrite Hc in Hpni.
          rewrite heap_parent_left__hpop_sift_left_child in Hpni.
          contradiction. }
        rewrite Hsw_o by lia.
        rewrite Hsw_o by lia.
        apply Hexcept; auto.
  - unfold PopHoleGuard.
    right.
    intros child Hc0 Hchs Hpc.
    pose proof (heap_parent_bounds__hpop_sift_left_child child Hc0) as Hpb.
    rewrite heap_parent_left__hpop_sift_left_child.
    rewrite Hsw_i.
    rewrite Hsw_o by lia.
    unfold HeapOrderExceptDown in Hexcept.
    assert (Hd : Znth (HeapParent child) cur 0 >= Znth child cur 0).
    { apply Hexcept; auto. rewrite Hpc. lia. }
    rewrite Hpc in Hd.
    exact Hd.
Qed.
Lemma sublist_root__hpop_return : forall (l : list Z) (hs : Z),
  1 <= hs -> hs <= Zlength l ->
  sublist 0 hs l = Znth 0 l 0 :: sublist 1 hs l.
Proof.
  intros l hs H1 H2.
  rewrite (sublist_split 0 hs 1 l) by lia.
  replace (sublist 0 1 l) with [Znth 0 l 0].
  - reflexivity.
  - rewrite <- (sublist_single 0 0 l) by lia.
    f_equal.
Qed.
Lemma pop_perm_extract_root__hpop_return : forall (l cur : list Z) (hs i : Z),
  PopSiftState l cur hs i ->
  1 <= hs -> hs <= Zlength l ->
  Permutation (sublist 0 hs l) (Znth 0 l 0 :: sublist 0 (hs - 1) cur).
Proof.
  intros l cur hs i Hst H1 H2.
  destruct Hst as [_ [Hperm _]].
  rewrite sublist_root__hpop_return by lia.
  apply perm_skip.
  apply Permutation_sym. exact Hperm.
Qed.
Lemma heap_parent_children__hpop_return : forall (child i : Z),
  0 < child -> HeapParent child = i -> child = 2 * i + 1 \/ child = 2 * i + 2.
Proof.
  intros child i Hc Hq.
  unfold HeapParent in Hq.
  rewrite Z.quot_div_nonneg in Hq by lia.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmb.
  lia.
Qed.
Lemma pop_sift_state_exit__hpop_return : forall (l cur : list Z) (hs i : Z),
  PopSiftState l cur hs i ->
  0 <= i ->
  (2 * i + 1 < hs - 1 -> Znth (2 * i + 1) cur 0 <= Znth i cur 0) ->
  (2 * i + 1 + 1 < hs - 1 -> Znth (2 * i + 1 + 1) cur 0 <= Znth i cur 0) ->
  HeapOrdered cur (hs - 1).
Proof.
  intros l cur hs i Hst Hi Hl Hr.
  destruct Hst as [_ [_ [Hexc _]]].
  unfold HeapOrdered, HeapOrderedFrom.
  intros child Hc0 Hcs _.
  destruct (Z.eq_dec (HeapParent child) i) as [Heq | Hne].
  - pose proof (heap_parent_children__hpop_return child i Hc0 Heq) as Hcase.
    rewrite Heq.
    destruct Hcase as [Hc | Hc]; subst child.
    + specialize (Hl ltac:(lia)). lia.
    + replace (2 * i + 2) with (2 * i + 1 + 1) in * by lia.
      specialize (Hr ltac:(lia)). lia.
  - apply Hexc; auto.
Qed.
Lemma Zlength_replace_Znth__sift_cand_step :
  forall {A : Type} (n : Z) (v : A) (l : list A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A n v l. unfold replace_Znth.
  set (m := Z.to_nat n). clearbody m. clear n.
  revert m. induction l as [| a l IH]; intros m.
  - destruct m; reflexivity.
  - destruct m as [| m']; simpl.
    + reflexivity.
    + rewrite !Zlength_cons. rewrite IH. reflexivity.
Qed.
Lemma Zlist_eq_ext__sift_cand_step :
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    (forall k, 0 <= k < Zlength l1 -> Znth k l1 0 = Znth k l2 0) ->
    l1 = l2.
Proof.
  intros l1 l2 Hlen Hnth.
  apply (nth_ext _ _ 0 0).
  - rewrite !Zlength_correct in Hlen. lia.
  - intros n Hn. specialize (Hnth (Z.of_nat n)).
    unfold Znth in Hnth. rewrite Nat2Z.id in Hnth.
    apply Hnth. rewrite Zlength_correct. lia.
Qed.
Lemma perm_cons_replace_nth__sift_cand_step :
  forall {A : Type} (d : A) (t : list A) (h : A) (m : nat),
    (m < length t)%nat ->
    Permutation (nth m t d :: replace_nth m t h) (h :: t).
Proof.
  intros A d t. induction t as [| a t IH]; intros h m Hm; simpl in Hm.
  - lia.
  - destruct m as [| m']; simpl.
    + apply perm_swap.
    + eapply Permutation_trans; [ apply perm_swap |].
      eapply Permutation_trans with (a :: h :: t).
      * apply perm_skip. apply IH. lia.
      * apply perm_swap.
Qed.
Lemma perm_replace_nth_swap__sift_cand_step :
  forall {A : Type} (d : A) (L : list A) (i j : nat),
    (i < j)%nat -> (j < length L)%nat ->
    Permutation (replace_nth j (replace_nth i L (nth j L d)) (nth i L d)) L.
Proof.
  intros A d L. induction L as [| a L IH]; intros i j Hij Hj; simpl in Hj.
  - lia.
  - destruct i as [| i']; destruct j as [| j']; try lia.
    + simpl. apply perm_cons_replace_nth__sift_cand_step. lia.
    + simpl. apply perm_skip. apply IH; lia.
Qed.
Lemma perm_replace_Znth_swap__sift_cand_step :
  forall {A : Type} (d : A) (L : list A) (i j : Z),
    0 <= i -> i < j -> j < Zlength L ->
    Permutation (replace_Znth j (Znth i L d) (replace_Znth i (Znth j L d) L)) L.
Proof.
  intros A d L i j Hi Hij Hj.
  unfold replace_Znth, Znth.
  apply (perm_replace_nth_swap__sift_cand_step d).
  - lia.
  - rewrite Zlength_correct in Hj. lia.
Qed.
Lemma combine_replace_nth__sift_cand_step :
  forall {A B : Type} (l1 : list A) (l2 : list B) (n : nat) (a : A) (b : B),
    combine (replace_nth n l1 a) (replace_nth n l2 b) =
    replace_nth n (combine l1 l2) (a, b).
Proof.
  intros A B l1. induction l1 as [| x l1 IH]; intros l2 n a b.
  - destruct n; destruct l2; reflexivity.
  - destruct l2 as [| y l2].
    + destruct n as [| n']; simpl; reflexivity.
    + destruct n as [| n']; simpl.
      * reflexivity.
      * rewrite IH. reflexivity.
Qed.
Lemma combine_replace_Znth__sift_cand_step :
  forall {A B : Type} (l1 : list A) (l2 : list B) (n : Z) (a : A) (b : B),
    combine (replace_Znth n a l1) (replace_Znth n b l2) =
    replace_Znth n (a, b) (combine l1 l2).
Proof.
  intros. unfold replace_Znth. apply combine_replace_nth__sift_cand_step.
Qed.
Lemma Znth_combine__sift_cand_step :
  forall (l1 l2 : list Z) (n : Z),
    Zlength l2 = Zlength l1 ->
    Znth n (combine l1 l2) (0, 0) = (Znth n l1 0, Znth n l2 0).
Proof.
  intros l1 l2 n Hlen. unfold Znth. apply combine_nth.
  rewrite !Zlength_correct in Hlen. lia.
Qed.
Lemma zip_perm_swap__sift_cand_step :
  forall (t0 b0 t b : list Z) (i j : Z),
    ZipPerm t0 b0 t b ->
    0 <= i -> i < j -> j < Zlength t ->
    ZipPerm t0 b0
      (replace_Znth j (Znth i t 0) (replace_Znth i (Znth j t 0) t))
      (replace_Znth j (Znth i b 0) (replace_Znth i (Znth j b 0) b)).
Proof.
  intros t0 b0 t b i j HZ Hi Hij Hj.
  destruct HZ as [Hb0 [Ht [Hb Hperm]]].
  assert (Hbt : Zlength b = Zlength t) by lia.
  assert (Hcl : Zlength (combine t b) = Zlength t).
  { rewrite !Zlength_correct in *. rewrite length_combine. lia. }
  unfold ZipPerm. split; [| split; [| split]].
  - exact Hb0.
  - rewrite !Zlength_replace_Znth__sift_cand_step. exact Ht.
  - rewrite !Zlength_replace_Znth__sift_cand_step. exact Hb.
  - eapply Permutation_trans; [ exact Hperm |].
    rewrite !combine_replace_Znth__sift_cand_step.
    replace (Znth i t 0, Znth i b 0) with (Znth i (combine t b) (0, 0))
      by (apply Znth_combine__sift_cand_step; lia).
    replace (Znth j t 0, Znth j b 0) with (Znth j (combine t b) (0, 0))
      by (apply Znth_combine__sift_cand_step; lia).
    apply Permutation_sym.
    apply perm_replace_Znth_swap__sift_cand_step; lia.
Qed.
Lemma sublist_replace_Znth_lo__sift_cand_step :
  forall (l : list Z) (i v lo hi : Z),
    0 <= i < lo -> lo <= hi -> hi <= Zlength l ->
    sublist lo hi (replace_Znth i v l) = sublist lo hi l.
Proof.
  intros l i v lo hi Hi Hlo Hhi.
  assert (HL : Zlength (replace_Znth i v l) = Zlength l)
    by apply Zlength_replace_Znth__sift_cand_step.
  apply Zlist_eq_ext__sift_cand_step.
  - rewrite !Zlength_sublist by lia. reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite !Znth_sublist by lia.
    apply Znth_replace_Znth_Diff; lia.
Qed.
Lemma Znth_swap_at_j__sift_cand_step :
  forall (l : list Z) (i j : Z),
    0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j ->
    Znth j (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0
      = Znth i l 0.
Proof.
  intros l i j Hi Hj Hij.
  apply Znth_replace_Znth_Same.
  rewrite Zlength_replace_Znth__sift_cand_step. lia.
Qed.
Lemma Znth_swap_at_i__sift_cand_step :
  forall (l : list Z) (i j : Z),
    0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j ->
    Znth i (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0
      = Znth j l 0.
Proof.
  intros l i j Hi Hj Hij.
  rewrite Znth_replace_Znth_Diff.
  - apply Znth_replace_Znth_Same. lia.
  - rewrite Zlength_replace_Znth__sift_cand_step. lia.
  - rewrite Zlength_replace_Znth__sift_cand_step. lia.
  - lia.
Qed.
Lemma Znth_swap_other__sift_cand_step :
  forall (l : list Z) (i j k : Z),
    0 <= i < Zlength l -> 0 <= j < Zlength l -> 0 <= k < Zlength l ->
    k <> i -> k <> j ->
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0
      = Znth k l 0.
Proof.
  intros l i j k Hi Hj Hk Hki Hkj.
  rewrite Znth_replace_Znth_Diff.
  - apply Znth_replace_Znth_Diff; lia.
  - rewrite Zlength_replace_Znth__sift_cand_step. lia.
  - rewrite Zlength_replace_Znth__sift_cand_step. lia.
  - lia.
Qed.
Lemma heap_parent_spec__sift_cand_step :
  forall c, 0 < c -> 2 * HeapParent c + 1 <= c <= 2 * HeapParent c + 2.
Proof.
  intros c Hc. unfold HeapParent.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (c - 1) 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (c - 1) 2 ltac:(lia)) as Hmb.
  lia.
Qed.
Lemma heap_parent_lt__sift_cand_step :
  forall c, 0 < c -> 0 <= HeapParent c < c.
Proof.
  intros c Hc. pose proof (heap_parent_spec__sift_cand_step c Hc). lia.
Qed.
Lemma heap_parent_child__sift_cand_step :
  forall c r, 0 <= r -> (c = 2 * r + 1 \/ c = 2 * r + 2) -> HeapParent c = r.
Proof.
  intros c r Hr Hc.
  pose proof (heap_parent_spec__sift_cand_step c ltac:(lia)). lia.
Qed.
Lemma heap_parent_inv__sift_cand_step :
  forall c r, 0 < c -> HeapParent c = r -> c = 2 * r + 1 \/ c = 2 * r + 2.
Proof.
  intros c r Hc Hr.
  pose proof (heap_parent_spec__sift_cand_step c Hc). lia.
Qed.
Lemma sift_state_init__sift_cand_step :
  forall (t0 b0 : list Z) (size lo : Z),
    Zlength b0 = Zlength t0 ->
    HeapOrderedFrom t0 size (lo + 1) ->
    SiftState t0 b0 t0 b0 size lo lo.
Proof.
  intros t0 b0 size lo Hlen Hord.
  unfold SiftState. split; [| split; [| split; [| split]]].
  - unfold ZipPerm.
    split; [assumption |].
    split; [reflexivity |].
    split; [assumption | apply Permutation_refl].
  - reflexivity.
  - reflexivity.
  - intros child Hc1 Hc2 Hc3 Hc4. apply Hord; [assumption | assumption | lia].
  - left. reflexivity.
Qed.
Lemma sift_state_swap__sift_cand_step :
  forall (t0 b0 t b : list Z) (size lo r ch : Z),
    0 <= lo -> lo <= r -> r < ch -> ch < size -> size <= Zlength t0 ->
    HeapParent ch = r ->
    Znth r t 0 <= Znth ch t 0 ->
    (forall s, 0 < s -> s < size -> HeapParent s = r ->
       Znth ch t 0 >= Znth s t 0) ->
    SiftState t0 b0 t b size lo r ->
    SiftState t0 b0
      (replace_Znth ch (Znth r t 0) (replace_Znth r (Znth ch t 0) t))
      (replace_Znth ch (Znth r b 0) (replace_Znth r (Znth ch b 0) b))
      size lo ch.
Proof.
  intros t0 b0 t b size lo r ch Hlo Hlor Hrch Hchs Hsz Hpch Hle Hsib HS.
  assert (HZ := HS).
  destruct HS as [HZP [Hst [Hsb [Horder Hguard]]]].
  destruct HZP as [Hzb0 [Hzt [Hzb Hzp]]].
  assert (Hlen1 : Zlength (replace_Znth r (Znth ch t 0) t) = Zlength t0)
    by (rewrite Zlength_replace_Znth__sift_cand_step; lia).
  assert (Hlen2 : Zlength (replace_Znth r (Znth ch b 0) b) = Zlength t0)
    by (rewrite Zlength_replace_Znth__sift_cand_step; lia).
  assert (Hch : Znth ch (replace_Znth ch (Znth r t 0)
                          (replace_Znth r (Znth ch t 0) t)) 0 = Znth r t 0)
    by (apply Znth_swap_at_j__sift_cand_step; lia).
  assert (Hrr : Znth r (replace_Znth ch (Znth r t 0)
                          (replace_Znth r (Znth ch t 0) t)) 0 = Znth ch t 0)
    by (apply Znth_swap_at_i__sift_cand_step; lia).
  assert (Hoth : forall k, 0 <= k < Zlength t -> k <> r -> k <> ch ->
            Znth k (replace_Znth ch (Znth r t 0)
                     (replace_Znth r (Znth ch t 0) t)) 0 = Znth k t 0)
    by (intros k Hk Hkr Hkch; apply Znth_swap_other__sift_cand_step; lia).
  unfold SiftState. split; [| split; [| split; [| split]]].
  - apply zip_perm_swap__sift_cand_step;
      [ unfold ZipPerm; repeat split; assumption | lia | lia | lia].
  - rewrite (sublist_replace_Znth_lo__sift_cand_step _ ch) by lia.
    rewrite (sublist_replace_Znth_lo__sift_cand_step _ r) by lia.
    exact Hst.
  - rewrite (sublist_replace_Znth_lo__sift_cand_step _ ch) by lia.
    rewrite (sublist_replace_Znth_lo__sift_cand_step _ r) by lia.
    exact Hsb.
  - intros child Hc1 Hc2 Hc3 Hc4.
    pose proof (heap_parent_lt__sift_cand_step child Hc1) as Hpl.
    destruct (Z.eq_dec (HeapParent child) r) as [Hpr | Hpr].
    + rewrite Hpr, Hrr.
      destruct (Z.eq_dec child ch) as [Hcc | Hcc].
      * subst child. rewrite Hch. lia.
      * rewrite Hoth by lia. apply Hsib; assumption.
    + rewrite (Hoth (HeapParent child)) by lia.
      destruct (Z.eq_dec child r) as [Hcr | Hcr].
      * subst child. rewrite Hrr.
        destruct Hguard as [Hg | Hg].
        -- exfalso. lia.
        -- apply Hg; [lia | lia | exact Hpch].
      * destruct (Z.eq_dec child ch) as [Hcc | Hcc].
        -- exfalso. subst child. congruence.
        -- rewrite Hoth by lia. apply Horder; assumption.
  - right. intros c Hc1 Hc2 Hpc.
    rewrite Hpch, Hrr.
    assert (Hcgt : ch < c)
      by (pose proof (heap_parent_inv__sift_cand_step c ch Hc1 Hpc); lia).
    rewrite (Hoth c) by lia.
    rewrite <- Hpc.
    apply Horder; [assumption | assumption | rewrite Hpc; lia | rewrite Hpc; lia].
Qed.
Lemma heap_parent_children__sift_cand_exit :
  forall (child root : Z),
    0 < child -> HeapParent child = root ->
    child = 2 * root + 1 \/ child = 2 * root + 1 + 1.
Proof.
  intros child root Hc Hp. unfold HeapParent in Hp.
  rewrite Z.quot_div_nonneg in Hp by lia.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmb.
  rewrite Hp in Hdm. lia.
Qed.
Lemma sift_state_exit__sift_cand_exit :
  forall (t0 b0 t b : list Z) (size lo root : Z),
    SiftState t0 b0 t b size lo root ->
    (forall child,
       0 < child -> child < size -> HeapParent child = root ->
       Znth root t 0 >= Znth child t 0) ->
    HeapOrderedFrom t size lo.
Proof.
  intros t0 b0 t b size lo root Hst Hdom.
  destruct Hst as [_ [_ [_ [Horder _]]]].
  unfold HeapOrderedFrom. intros child Hc0 Hcs Hlo.
  destruct (Z.eq_dec (HeapParent child) root) as [He | Hne].
  - rewrite He. apply Hdom; assumption.
  - apply Horder; assumption.
Qed.
Lemma quot2_bounds__sort_build_phase : forall n : Z,
  0 <= n ->
  0 <= Z.quot n 2 /\ 2 * Z.quot n 2 <= n /\ n <= 2 * Z.quot n 2 + 1.
Proof.
  intros n Hn.
  pose proof (Z.quot_rem n 2 ltac:(lia)) as Hq.
  pose proof (Z.rem_bound_pos n 2 ltac:(lia) ltac:(lia)) as Hr.
  lia.
Qed.
Lemma heap_ordered_from_half__sort_build_phase : forall (l : list Z) (n lo : Z),
  0 <= n -> Z.quot n 2 <= lo -> HeapOrderedFrom l n lo.
Proof.
  intros l n lo Hn Hlo.
  unfold HeapOrderedFrom, HeapParent.
  intros child Hc0 Hcn Hpar.
  pose proof (quot2_bounds__sort_build_phase n Hn) as Hn2.
  pose proof (Z.quot_rem (child - 1) 2 ltac:(lia)) as Hq1.
  pose proof (Z.rem_bound_pos (child - 1) 2 ltac:(lia) ltac:(lia)) as Hr1.
  exfalso. lia.
Qed.
Lemma zip_perm_trans__sort_build_phase : forall t0 b0 t b t1 b1 : list Z,
  ZipPerm t0 b0 t b -> ZipPerm t b t1 b1 -> ZipPerm t0 b0 t1 b1.
Proof.
  intros t0 b0 t b t1 b1 H1 H2.
  unfold ZipPerm in *.
  destruct H1 as [Ha [Hb [Hc Hd]]].
  destruct H2 as [He [Hf [Hg Hh]]].
  split; [ exact Ha | split; [ lia | split; [ lia | ] ] ].
  eapply Permutation_trans; [ exact Hd | exact Hh ].
Qed.
Lemma zip_perm_refl__sort_build_phase : forall t b : list Z,
  Zlength b = Zlength t -> ZipPerm t b t b.
Proof.
  intros t b H. unfold ZipPerm.
  split; [ exact H | split; [ reflexivity | split; [ exact H | ] ] ].
  apply Permutation_refl.
Qed.
Lemma heap_sort_state_full__sort_build_phase : forall (t : list Z) (n : Z),
  0 <= n -> HeapSortState t n (n - 1).
Proof.
  intros t n Hn. unfold HeapSortState. split.
  - unfold Nondecreasing. intros i j Hi Hij Hj.
    replace (n - 1 + 1) with n in Hj by lia.
    rewrite Zlength_correct in Hj. unfold sublist in Hj.
    rewrite length_skipn, length_firstn in Hj.
    exfalso. lia.
  - intros p q Hp Hph Hhq Hqn. exfalso. lia.
Qed.
Lemma length_replace_nth__sort_extract_phase :
  forall {A : Type} (l : list A) (n : nat) (a : A),
    length (replace_nth n l a) = length l.
Proof.
  intros A l. induction l as [| x l IH]; intros n a; destruct n; simpl; auto.
Qed.
Lemma length_replace_Znth__sort_extract_phase :
  forall {A : Type} (l : list A) (i : Z) (v : A),
    length (replace_Znth i v l) = length l.
Proof.
  intros. unfold replace_Znth. apply length_replace_nth__sort_extract_phase.
Qed.
Lemma Zlength_replace_Znth__sort_extract_phase :
  forall {A : Type} (l : list A) (n : Z) (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros. unfold replace_Znth.
  rewrite !Zlength_correct, length_replace_nth__sort_extract_phase. reflexivity.
Qed.
Lemma replace_nth_split__sort_extract_phase :
  forall {A : Type} (l : list A) (n : nat) (a : A),
    (n < length l)%nat ->
    replace_nth n l a = firstn n l ++ a :: skipn (S n) l.
Proof.
  intros A l. induction l as [| x l IH]; intros n a Hn; simpl in Hn; [ lia | ].
  destruct n as [| n]; simpl; auto.
  rewrite IH by lia. reflexivity.
Qed.
Lemma perm_move__sort_extract_phase :
  forall {A : Type} (d : A) (l : list A) (x : A) (m : nat),
    (m < length l)%nat ->
    Permutation (x :: l) (nth m l d :: replace_nth m l x).
Proof.
  intros A d l x m Hm.
  rewrite replace_nth_split__sort_extract_phase by lia.
  rewrite (firstn_skipSn d m l) at 1 by lia.
  remember (firstn m l) as L1.
  remember (skipn (S m) l) as L2.
  transitivity (x :: nth m l d :: (L1 ++ L2)).
  { apply perm_skip. apply Permutation_sym. apply Permutation_middle. }
  transitivity (nth m l d :: x :: (L1 ++ L2)).
  { apply perm_swap. }
  apply perm_skip. apply Permutation_middle.
Qed.
Lemma perm_swap0__sort_extract_phase :
  forall {A : Type} (d : A) (l : list A) (j : Z),
    0 < j < Zlength l ->
    Permutation l (replace_Znth j (Znth 0 l d) (replace_Znth 0 (Znth j l d) l)).
Proof.
  intros A d l j Hj.
  destruct l as [| h t].
  { rewrite Zlength_nil in Hj. lia. }
  rewrite Zlength_cons in Hj.
  unfold Znth, replace_Znth. simpl (Z.to_nat 0).
  simpl (nth 0 (h :: t) d).
  simpl (replace_nth 0 (h :: t) (nth (Z.to_nat j) (h :: t) d)).
  set (m := Z.to_nat j).
  assert (Hm : (1 <= m)%nat) by (unfold m; lia).
  assert (Hlt : (m - 1 < length t)%nat).
  { unfold m. rewrite Zlength_correct in Hj. lia. }
  replace m with (S (m - 1))%nat by lia.
  simpl (nth (S (m - 1)) (h :: t) d).
  simpl (replace_nth (S (m - 1)) (nth (m - 1) t d :: t) h).
  apply perm_move__sort_extract_phase. exact Hlt.
Qed.
Lemma combine_app__sort_extract_phase :
  forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B),
    length l1 = length l1' ->
    combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  intros A B l1. induction l1 as [| x l1 IH]; intros l2 l1' l2' Hlen;
    destruct l1' as [| y l1']; simpl in *; try lia; auto.
  f_equal. apply IH. lia.
Qed.
Lemma combine_firstn__sort_extract_phase :
  forall {A B : Type} (n : nat) (l1 : list A) (l2 : list B),
    firstn n (combine l1 l2) = combine (firstn n l1) (firstn n l2).
Proof.
  intros A B n. induction n as [| n IH]; intros l1 l2; simpl; auto.
  destruct l1 as [| x l1]; destruct l2 as [| y l2]; simpl; try reflexivity.
  f_equal. apply IH.
Qed.
Lemma combine_skipn__sort_extract_phase :
  forall {A B : Type} (n : nat) (l1 : list A) (l2 : list B),
    skipn n (combine l1 l2) = combine (skipn n l1) (skipn n l2).
Proof.
  intros A B n. induction n as [| n IH]; intros l1 l2; simpl; auto.
  destruct l1 as [| x l1]; destruct l2 as [| y l2]; simpl;
    rewrite ?skipn_nil; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (skipn n l1); reflexivity.
  - apply IH.
Qed.
Lemma sublist_combine__sort_extract_phase :
  forall {A B : Type} (lo hi : Z) (l1 : list A) (l2 : list B),
    sublist lo hi (combine l1 l2) = combine (sublist lo hi l1) (sublist lo hi l2).
Proof.
  intros. unfold sublist.
  rewrite combine_firstn__sort_extract_phase, combine_skipn__sort_extract_phase.
  reflexivity.
Qed.
Lemma map_fst_combine__sort_extract_phase :
  forall {A B : Type} (l1 : list A) (l2 : list B),
    length l1 = length l2 -> map fst (combine l1 l2) = l1.
Proof.
  intros A B l1. induction l1 as [| x l1 IH]; intros l2 Hlen;
    destruct l2 as [| y l2]; simpl in *; try lia; auto.
  f_equal. apply IH. lia.
Qed.
Lemma combine_replace_nth__sort_extract_phase :
  forall {A B : Type} (l1 : list A) (l2 : list B) (n : nat) (x : A) (y : B),
    length l1 = length l2 ->
    combine (replace_nth n l1 x) (replace_nth n l2 y)
      = replace_nth n (combine l1 l2) (x, y).
Proof.
  intros A B l1. induction l1 as [| a l1 IH]; intros l2 n x y Hlen;
    destruct l2 as [| b l2]; simpl in *; try lia.
  - destruct n; reflexivity.
  - destruct n as [| n]; simpl; auto.
    f_equal. apply IH. lia.
Qed.
Lemma combine_replace_Znth__sort_extract_phase :
  forall {A B : Type} (l1 : list A) (l2 : list B) (i : Z) (x : A) (y : B),
    length l1 = length l2 ->
    combine (replace_Znth i x l1) (replace_Znth i y l2)
      = replace_Znth i (x, y) (combine l1 l2).
Proof.
  intros. unfold replace_Znth.
  apply combine_replace_nth__sort_extract_phase. exact H.
Qed.
Lemma nth_combine__sort_extract_phase :
  forall {A B : Type} (d1 : A) (d2 : B) (l1 : list A) (l2 : list B) (n : nat),
    (n < length l1)%nat -> length l1 = length l2 ->
    nth n (combine l1 l2) (d1, d2) = (nth n l1 d1, nth n l2 d2).
Proof.
  intros A B d1 d2 l1. induction l1 as [| a l1 IH]; intros l2 n Hn Hlen;
    simpl in *; [ lia | ].
  destruct l2 as [| b l2]; simpl in *; [ lia | ].
  destruct n as [| n]; simpl; auto.
  apply IH; lia.
Qed.
Lemma Znth_combine__sort_extract_phase :
  forall {A B : Type} (d1 : A) (d2 : B) (l1 : list A) (l2 : list B) (i : Z),
    0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
    Znth i (combine l1 l2) (d1, d2) = (Znth i l1 d1, Znth i l2 d2).
Proof.
  intros. unfold Znth.
  apply nth_combine__sort_extract_phase; rewrite !Zlength_correct in *; lia.
Qed.
Lemma Zlength_combine__sort_extract_phase :
  forall {A B : Type} (l1 : list A) (l2 : list B),
    Zlength l1 = Zlength l2 -> Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros. rewrite !Zlength_correct in *.
  rewrite length_combine. lia.
Qed.
Lemma heap_parent_range__sort_extract_phase :
  forall child : Z, 0 < child -> 0 <= HeapParent child < child.
Proof.
  intros child Hc. unfold HeapParent.
  rewrite Z.quot_div_nonneg by lia.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
Lemma heap_root_max__sort_extract_phase :
  forall (l : list Z) (size j : Z),
    HeapOrderedFrom l size 0 ->
    0 <= j -> j < size ->
    Znth j l 0 <= Znth 0 l 0.
Proof.
  intros l size j Hheap Hj0 Hjs.
  revert Hjs.
  pattern j.
  apply Z_lt_induction; [ | exact Hj0 ].
  clear j Hj0. intros x IH Hxs.
  destruct (Z_le_gt_dec x 0) as [Hle | Hgt].
  - unfold Znth. replace (Z.to_nat x) with (Z.to_nat 0) by lia. apply Z.le_refl.
  - pose proof (heap_parent_range__sort_extract_phase x ltac:(lia)) as Hpr.
    specialize (Hheap x ltac:(lia) Hxs ltac:(lia)).
    specialize (IH (HeapParent x) ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma swap_Znth__sort_extract_phase :
  forall (t : list Z) (i j q : Z),
    0 <= i < Zlength t -> 0 <= j < Zlength t -> i <> j -> 0 <= q < Zlength t ->
    Znth q (replace_Znth j (Znth i t 0) (replace_Znth i (Znth j t 0) t)) 0 =
    (if Z.eq_dec q j then Znth i t 0
     else if Z.eq_dec q i then Znth j t 0 else Znth q t 0).
Proof.
  intros t i j q Hi Hj Hij Hq.
  assert (Hlen : Zlength (replace_Znth i (Znth j t 0) t) = Zlength t)
    by apply Zlength_replace_Znth__sort_extract_phase.
  destruct (Z.eq_dec q j) as [-> | Hqj].
  - rewrite Znth_replace_Znth_Same; [ reflexivity | lia ].
  - rewrite Znth_replace_Znth_Diff by lia.
    destruct (Z.eq_dec q i) as [-> | Hqi].
    + rewrite Znth_replace_Znth_Same; [ reflexivity | lia ].
    + rewrite Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma heap_sort_state_swap__sort_extract_phase :
  forall (t : list Z) (n hi : Z),
    Zlength t = n -> 1 <= hi -> hi <= n - 1 ->
    HeapOrdered t (hi + 1) ->
    HeapSortState t n hi ->
    HeapSortState (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t))
                  n (hi - 1).
Proof.
  intros t n hi Hlen Hhi1 Hhi2 Hheap Hstate.
  unfold HeapOrdered in Hheap.
  destruct Hstate as [Hnd Hcross].
  assert (Hlen' :
    Zlength (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t)) = n).
  { rewrite !Zlength_replace_Znth__sort_extract_phase. exact Hlen. }
  assert (Hsw : forall q : Z, 0 <= q < n ->
    Znth q (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t)) 0 =
    (if Z.eq_dec q hi then Znth 0 t 0
     else if Z.eq_dec q 0 then Znth hi t 0 else Znth q t 0)).
  { intros q Hq. apply swap_Znth__sort_extract_phase; lia. }
  assert (Hmax : forall p : Z, 0 <= p <= hi -> Znth p t 0 <= Znth 0 t 0).
  { intros p Hp. apply (heap_root_max__sort_extract_phase t (hi + 1) p); auto; lia. }
  assert (HZl2 : Zlength (sublist (hi + 1) n t) = n - hi - 1)
    by (rewrite Zlength_sublist by lia; lia).
  unfold Nondecreasing in Hnd.
  split.
  - replace (hi - 1 + 1) with hi by lia.
    unfold Nondecreasing. intros i j Hi Hij Hj.
    assert (HZl : Zlength (sublist hi n
        (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t))) = n - hi)
      by (rewrite Zlength_sublist by lia; lia).
    rewrite HZl in Hj.
    rewrite !Znth_sublist by lia.
    rewrite !Hsw by lia.
    destruct (Z.eq_dec (i + hi) hi) as [Hie | Hie];
      destruct (Z.eq_dec (j + hi) hi) as [Hje | Hje].
    + apply Z.le_refl.
    + destruct (Z.eq_dec (j + hi) 0); [ lia | ].
      apply Hcross; lia.
    + lia.
    + destruct (Z.eq_dec (i + hi) 0); [ lia | ].
      destruct (Z.eq_dec (j + hi) 0); [ lia | ].
      specialize (Hnd (i - 1) (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite !Znth_sublist in Hnd by lia.
      replace (i - 1 + (hi + 1)) with (i + hi) in Hnd by lia.
      replace (j - 1 + (hi + 1)) with (j + hi) in Hnd by lia.
      exact Hnd.
  - intros p q Hp0 Hphi Hqhi Hqn.
    rewrite !Hsw by lia.
    destruct (Z.eq_dec p hi); [ lia | ].
    destruct (Z.eq_dec q hi) as [Hqe | Hqe].
    + destruct (Z.eq_dec p 0) as [Hpe | Hpe].
      * apply Hmax; lia.
      * apply Hmax; lia.
    + destruct (Z.eq_dec q 0); [ lia | ].
      destruct (Z.eq_dec p 0) as [Hpe | Hpe].
      * apply Hcross; lia.
      * apply Hcross; lia.
Qed.
Lemma zip_perm_trans__sort_extract_phase :
  forall (t0 b0 t b t1 b1 : list Z),
    ZipPerm t0 b0 t b -> ZipPerm t b t1 b1 -> ZipPerm t0 b0 t1 b1.
Proof.
  intros t0 b0 t b t1 b1 [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  unfold ZipPerm. repeat split; try lia.
  apply Permutation_trans with (l' := combine t b); assumption.
Qed.
Lemma zip_perm_swap0__sort_extract_phase :
  forall (t0 b0 t b : list Z) (j : Z),
    ZipPerm t0 b0 t b -> 0 < j < Zlength t ->
    ZipPerm t0 b0
      (replace_Znth j (Znth 0 t 0) (replace_Znth 0 (Znth j t 0) t))
      (replace_Znth j (Znth 0 b 0) (replace_Znth 0 (Znth j b 0) b)).
Proof.
  intros t0 b0 t b j [H1 [H2 [H3 H4]]] Hj.
  assert (Htb : Zlength t = Zlength b) by lia.
  unfold ZipPerm. repeat split.
  - exact H1.
  - rewrite !Zlength_replace_Znth__sort_extract_phase. lia.
  - rewrite !Zlength_replace_Znth__sort_extract_phase. lia.
  - apply Permutation_trans with (l' := combine t b); [ assumption | ].
    rewrite combine_replace_Znth__sort_extract_phase
      by (rewrite !length_replace_Znth__sort_extract_phase;
          rewrite !Zlength_correct in Htb; lia).
    rewrite combine_replace_Znth__sort_extract_phase
      by (rewrite !Zlength_correct in Htb; lia).
    rewrite <- (Znth_combine__sort_extract_phase 0 0 t b 0) by lia.
    rewrite <- (Znth_combine__sort_extract_phase 0 0 t b j) by lia.
    apply perm_swap0__sort_extract_phase.
    rewrite Zlength_combine__sort_extract_phase by lia. lia.
Qed.
Lemma Zlength_length__sort_extract_phase :
  forall (u v : list Z), Zlength u = Zlength v -> length u = length v.
Proof.
  intros u v H. rewrite !Zlength_correct in H. lia.
Qed.
Lemma zip_prefix_perm__sort_extract_phase :
  forall (t b t' b' : list Z) (m n : Z),
    Zlength t = n -> Zlength b = n -> Zlength t' = n -> Zlength b' = n ->
    0 <= m <= n ->
    Permutation (combine t b) (combine t' b') ->
    sublist m n t' = sublist m n t ->
    sublist m n b' = sublist m n b ->
    Permutation (sublist 0 m t) (sublist 0 m t').
Proof.
  intros t b t' b' m n Ht Hb Ht' Hb' Hm Hperm Hst Hsb.
  assert (HZ : forall u : list Z, Zlength u = n -> Zlength (sublist 0 m u) = m).
  { intros u Hu. rewrite Zlength_sublist by lia. lia. }
  assert (Hsplit : forall u v : list Z, Zlength u = n -> Zlength v = n ->
      combine u v = combine (sublist 0 m u) (sublist 0 m v)
                    ++ combine (sublist m n u) (sublist m n v)).
  { intros u v Hu Hv.
    rewrite <- combine_app__sort_extract_phase
      by (apply Zlength_length__sort_extract_phase; rewrite !HZ by lia; reflexivity).
    rewrite <- !sublist_split by lia.
    rewrite !sublist_self by lia. reflexivity. }
  rewrite (Hsplit t b Ht Hb), (Hsplit t' b' Ht' Hb') in Hperm.
  rewrite Hst, Hsb in Hperm.
  apply Permutation_app_inv_r in Hperm.
  apply (Permutation_map fst) in Hperm.
  assert (E1 : map fst (combine (sublist 0 m t) (sublist 0 m b)) = sublist 0 m t).
  { apply map_fst_combine__sort_extract_phase.
    apply Zlength_length__sort_extract_phase. rewrite !HZ by lia. reflexivity. }
  assert (E2 : map fst (combine (sublist 0 m t') (sublist 0 m b')) = sublist 0 m t').
  { apply map_fst_combine__sort_extract_phase.
    apply Zlength_length__sort_extract_phase. rewrite !HZ by lia. reflexivity. }
  rewrite E1, E2 in Hperm. exact Hperm.
Qed.
Lemma heap_sort_state_after_sift__sort_extract_phase :
  forall (t b t1 b1 : list Z) (n m : Z),
    Zlength t = n -> Zlength b = n -> Zlength t1 = n -> Zlength b1 = n ->
    0 <= m <= n ->
    Permutation (combine t b) (combine t1 b1) ->
    sublist m n t1 = sublist m n t ->
    sublist m n b1 = sublist m n b ->
    HeapSortState t n (m - 1) ->
    HeapSortState t1 n (m - 1).
Proof.
  intros t b t1 b1 n m Ht Hb Ht1 Hb1 Hm Hperm Hst Hsb [Hnd Hcross].
  replace (m - 1 + 1) with m in Hnd by lia.
  assert (Hpp : Permutation (sublist 0 m t) (sublist 0 m t1))
    by (apply (zip_prefix_perm__sort_extract_phase t b t1 b1 m n
                 Ht Hb Ht1 Hb1 Hm Hperm Hst Hsb)).
  assert (HZ1 : Zlength (sublist 0 m t1) = m) by (rewrite Zlength_sublist by lia; lia).
  assert (HZ0 : Zlength (sublist 0 m t) = m) by (rewrite Zlength_sublist by lia; lia).
  split.
  - replace (m - 1 + 1) with m by lia. rewrite Hst. exact Hnd.
  - intros p q Hp0 Hpm Hqm Hqn.
    assert (Hq : Znth q t1 0 = Znth q t 0).
    { assert (Hx : Znth (q - m) (sublist m n t1) 0 = Znth (q - m) (sublist m n t) 0)
        by (rewrite Hst; reflexivity).
      rewrite !Znth_sublist in Hx by lia.
      replace (q - m + m) with q in Hx by lia. exact Hx. }
    rewrite Hq.
    assert (Heq : Znth p (sublist 0 m t1) 0 = Znth p t1 0)
      by (rewrite Znth_sublist by lia; f_equal; lia).
    assert (HIn : In (Znth p t1 0) (sublist 0 m t)).
    { apply Permutation_in with (l := sublist 0 m t1);
        [ apply Permutation_sym; exact Hpp | ].
      rewrite <- Heq. unfold Znth. apply nth_In.
      rewrite Zlength_correct in HZ1. lia. }
    apply In_nth with (d := 0) in HIn.
    destruct HIn as [k [Hk Hnth]].
    assert (Hk' : Znth (Z.of_nat k) (sublist 0 m t) 0 = Znth p t1 0).
    { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
    rewrite Znth_sublist in Hk' by (rewrite Zlength_correct in HZ0; lia).
    replace (Z.of_nat k + 0) with (Z.of_nat k) in Hk' by lia.
    rewrite <- Hk'.
    apply Hcross; try lia.
    rewrite Zlength_correct in HZ0. lia.
Qed.
Lemma heap_sort_done_nondecreasing__sort_extract_phase :
  forall (t : list Z) (n hi : Z),
    Zlength t = n -> -1 <= hi -> hi <= 0 ->
    HeapSortState t n hi -> Nondecreasing t.
Proof.
  intros t n hi Hlen Hhi1 Hhi2 [Hnd Hcross].
  unfold Nondecreasing in *.
  intros i j Hi Hij Hj.
  destruct (Z.eq_dec hi (-1)) as [He | He].
  - subst hi. replace (-1 + 1) with 0 in Hnd by lia.
    rewrite sublist_self in Hnd by lia.
    apply Hnd; lia.
  - assert (Hz : hi = 0) by lia. subst hi.
    replace (0 + 1) with 1 in Hnd by lia.
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
      * subst i. subst j. apply Z.le_refl.
      * subst i. apply Hcross; lia.
    + assert (HZ : Zlength (sublist 1 n t) = n - 1)
        by (rewrite Zlength_sublist by lia; lia).
      specialize (Hnd (i - 1) (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite !Znth_sublist in Hnd by lia.
      replace (i - 1 + 1) with i in Hnd by lia.
      replace (j - 1 + 1) with j in Hnd by lia.
      exact Hnd.
Qed.
Lemma heap_ordered_from_swap__sort_extract_phase :
  forall (t : list Z) (n hi : Z),
    Zlength t = n -> 1 <= hi -> hi <= n - 1 ->
    HeapOrdered t (hi + 1) ->
    HeapOrderedFrom
      (replace_Znth hi (Znth 0 t 0) (replace_Znth 0 (Znth hi t 0) t)) hi 1.
Proof.
  intros t n hi Hlen Hhi1 Hhi2 Hheap.
  unfold HeapOrdered, HeapOrderedFrom in *.
  intros child Hc0 Hch Hcp.
  pose proof (heap_parent_range__sort_extract_phase child Hc0) as Hpr.
  rewrite !swap_Znth__sort_extract_phase by lia.
  destruct (Z.eq_dec (HeapParent child) hi); [ lia | ].
  destruct (Z.eq_dec (HeapParent child) 0); [ lia | ].
  destruct (Z.eq_dec child hi); [ lia | ].
  destruct (Z.eq_dec child 0); [ lia | ].
  apply Hheap; lia.
Qed.
Lemma rem5_quot5_spec__solver_safety_cand_a : forall x : Z,
  x = 5 * Z.quot x 5 + Z.rem x 5 /\ - 5 < Z.rem x 5 < 5.
Proof.
  intros x. split.
  - apply Z.quot_rem. lia.
  - pose proof (Z.rem_bound_abs x 5 ltac:(lia)) as H. lia.
Qed.
Lemma rem5_to_mod5__solver_safety_cand_a : forall x : Z,
  Z.rem (Z.rem x 5 + 5) 5 = x mod 5 /\ 0 <= x mod 5 < 5.
Proof.
  intros x.
  destruct (rem5_quot5_spec__solver_safety_cand_a x) as [_ Hb].
  split.
  - rewrite Z.rem_mod_nonneg by lia.
    rewrite Z.rem_eq by lia.
    replace (x - 5 * Z.quot x 5 + 5) with (x + (1 - Z.quot x 5) * 5) by ring.
    rewrite Z.mod_add by lia.
    reflexivity.
  - apply Z.mod_pos_bound. lia.
Qed.
Lemma rem5_shift_bound__solver_safety_cand_a : forall x : Z,
  0 <= Z.rem (Z.rem x 5 + 5) 5 < 5.
Proof.
  intros x.
  destruct (rem5_to_mod5__solver_safety_cand_a x) as [Heq Hb].
  rewrite Heq. exact Hb.
Qed.
Lemma rem5_shift_bounds__solver_safety_cand_b : forall a : Z,
  0 <= Z.rem (Z.rem a 5 + 5) 5 < 5.
Proof.
  intros a.
  assert (Ha : Z.abs (Z.rem a 5) < Z.abs 5) by (apply Z.rem_bound_abs; lia).
  replace (Z.abs 5) with 5 in Ha by reflexivity.
  apply Z.abs_lt in Ha.
  apply Z.rem_bound_pos; lia.
Qed.
Lemma quot5_nonneg_bound__solver_safety_cand_b : forall x m : Z,
  0 <= x -> x <= 5 * m -> 0 <= Z.quot x 5 <= m.
Proof.
  intros x m Hx Hm.
  rewrite Z.quot_div_nonneg by lia.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; lia.
Qed.
Lemma target_quot_bounds__solver_safety_cand_b : forall s j : Z,
  1000000000 <= s <= 3000000000 ->
  0 <= j < 5 ->
  0 <= Z.quot (s + Z.rem (Z.rem (j - s) 5 + 5) 5 - j) 5 <= 600000001.
Proof.
  intros s j Hs Hj.
  pose proof (rem5_shift_bounds__solver_safety_cand_b (j - s)).
  apply quot5_nonneg_bound__solver_safety_cand_b; lia.
Qed.
Lemma sweep_total_int64_bounds__solver_safety_sweep_a :
  forall k W j x : Z,
    0 <= k ->
    k <= 200000 ->
    1 <= W ->
    W <= 1000 ->
    0 <= j ->
    j < 5 ->
    1000000000 <= x ->
    x <= 3000000004 ->
    0 <= Z.quot (x - j) 5 <= 600000001 /\
    0 <= k * Z.quot (x - j) 5 <= 120000000200000 /\
    0 <= k * Z.quot (x - j) 5 * W <= 120000000200000000.
Proof.
  intros k W j x Hk0 Hk1 HW0 HW1 Hj0 Hj1 Hx0 Hx1.
  assert (Hq : 0 <= Z.quot (x - j) 5 <= 600000001).
  { split.
    - apply Z.quot_pos; lia.
    - apply Z.quot_le_upper_bound; lia. }
  assert (Hkq : 0 <= k * Z.quot (x - j) 5 <= 120000000200000) by nia.
  repeat split; try lia; nia.
Qed.
Lemma sweep_total_int64_bounds__solver_safety_sweep_b :
  forall k W j T hsum : Z,
    2 <= k -> k <= 200000 ->
    1 <= W -> W <= 1000 ->
    0 <= j -> j < 5 ->
    1000000000 <= T -> T <= 3000000004 ->
    -300000000000000000 <= hsum -> hsum <= 300000000000000000 ->
    0 <= k * Z.quot (T - j) 5 /\
    k * Z.quot (T - j) 5 <= 120000000200000 /\
    0 <= k * Z.quot (T - j) 5 * W /\
    k * Z.quot (T - j) 5 * W <= 120000000200000000 /\
    -300000000000000000 <= hsum + k * Z.quot (T - j) 5 * W /\
    hsum + k * Z.quot (T - j) 5 * W <= 420000000200000000.
Proof.
  intros k W j T hsum Hk1 Hk2 HW1 HW2 Hj1 Hj2 HT1 HT2 Hs1 Hs2.
  assert (Hq0 : 0 <= Z.quot (T - j) 5) by (apply Z.quot_pos; lia).
  assert (Hq1 : Z.quot (T - j) 5 <= 600000001) by (apply Z.quot_le_upper_bound; lia).
  assert (Hkq0 : 0 <= k * Z.quot (T - j) 5) by nia.
  assert (Hkq1 : k * Z.quot (T - j) 5 <= 120000000200000) by nia.
  assert (Hp0 : 0 <= k * Z.quot (T - j) 5 * W) by nia.
  assert (Hp1 : k * Z.quot (T - j) 5 * W <= 120000000200000000) by nia.
  lia.
Qed.
Lemma replace_znth_length__solver_shift_loop :
  forall (A : Type) (n : nat) (l : list A) (a : A),
    length (replace_nth n l a) = length l.
Proof.
  intros A n l. revert n.
  induction l as [ | h t IH]; intros n a; destruct n as [ | n]; simpl; auto.
Qed.
Lemma zlength_replace_Znth__solver_shift_loop :
  forall (A : Type) (l : list A) (n : Z) (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. unfold replace_Znth.
  rewrite !Zlength_correct.
  rewrite replace_znth_length__solver_shift_loop. reflexivity.
Qed.
Lemma shifted_prefix_step__solver_shift_loop :
  forall (values sh : list Z) (i : Z),
    0 <= i < Zlength sh ->
    ShiftedPrefix values sh i ->
    ShiftedPrefix values
      (replace_Znth i (Znth i values 0 + 2000000000) sh) (i + 1).
Proof.
  intros values sh i Hi Hpre q Hq.
  destruct (Z.eq_dec q i) as [Heq | Hne].
  - subst q. rewrite Znth_replace_Znth_Same by lia. reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hpre. lia.
Qed.
Lemma residue_best_zero__solver_shift_loop :
  forall (values : list Z) (k b c : Z),
    ResidueBest values k b c 0 (-1).
Proof.
  intros values k b c. unfold ResidueBest, BestState.
  left. split; [reflexivity | ].
  intros v Hv. destruct Hv as [j' [[Hj0 Hj1] _]]. lia.
Qed.
Lemma rem_norm__solver_cand_fill :
  forall a, Z.rem (Z.rem a 5 + 5) 5 = a mod 5.
Proof.
  intros a. Z.to_euclidean_division_equations. lia.
Qed.
Lemma target_point_normal_form__solver_cand_fill :
  forall s j : Z,
    0 <= j < 5 ->
    j <= s ->
    s + Z.rem (Z.rem (j - s) 5 + 5) 5 = TargetPoint s j /\
    Z.quot (TargetPoint s j - j) 5 = (TargetPoint s j - j) / 5.
Proof.
  intros s j Hj Hs.
  pose proof (Z.mod_pos_bound (j - s) 5 ltac:(lia)) as Hb.
  unfold TargetPoint.
  split.
  - rewrite rem_norm__solver_cand_fill. reflexivity.
  - apply Z.quot_div_nonneg; lia.
Qed.
Lemma cand_prefix_step__solver_cand_fill :
  forall (sh t b : list Z) (j W c i : Z),
    0 <= j < 5 ->
    0 <= i ->
    i < Zlength t ->
    i < Zlength b ->
    j <= Znth i sh 0 ->
    CandPrefix sh j W c i t b ->
    CandPrefix sh j W c (i + 1)
      (replace_Znth i (Znth i sh 0 + Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5) t)
      (replace_Znth i (Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5 * c -
                       Z.quot (Znth i sh 0 + Z.rem (Z.rem (j - Znth i sh 0) 5 + 5) 5 - j) 5 * W) b).
Proof.
  intros sh t b j W c i Hj Hi0 Hit Hib Hjs Hpre.
  pose proof (target_point_normal_form__solver_cand_fill (Znth i sh 0) j Hj Hjs)
    as [Htp Hquot].
  unfold CandPrefix in *.
  intros q [Hq0 Hq1].
  destruct (Z.eq_dec q i) as [Heq | Hne].
  - subst q.
    rewrite (Znth_replace_Znth_Same 0 t i) by lia.
    rewrite (Znth_replace_Znth_Same 0 b i) by lia.
    split.
    + exact Htp.
    + unfold NormalizedBase, TargetPoint.
      pose proof (Z.mod_pos_bound (j - Znth i sh 0) 5 ltac:(lia)) as Hb.
      rewrite rem_norm__solver_cand_fill.
      rewrite Z.quot_div_nonneg by lia.
      reflexivity.
  - rewrite (Znth_replace_Znth_Diff 0 t i q) by lia.
    rewrite (Znth_replace_Znth_Diff 0 b i q) by lia.
    apply Hpre. lia.
Qed.
Lemma sublist_0_0_nil__solver_postsort_sweep_init :
  forall (l : list Z), sublist 0 0 l = [].
Proof.
  intros l. unfold sublist. simpl. reflexivity.
Qed.
Lemma heap_ordered_zero__solver_postsort_sweep_init :
  forall (l : list Z), HeapOrdered l 0.
Proof.
  intros l. unfold HeapOrdered, HeapOrderedFrom.
  intros child Hpos Hlt Hpar. lia.
Qed.
Lemma zsum_sublist_0_0__solver_postsort_sweep_init :
  forall (l : list Z), ZSum (sublist 0 0 l) = 0.
Proof.
  intros l. rewrite sublist_0_0_nil__solver_postsort_sweep_init.
  unfold ZSum. simpl. reflexivity.
Qed.
Lemma sub_multiset_nil_inv__solver_postsort_sweep_init :
  forall (m : list Z), SubMultiset m [] -> m = [].
Proof.
  intros m [rest Hperm].
  apply Permutation_nil in Hperm.
  apply app_eq_nil in Hperm.
  destruct Hperm as [Hm _]. exact Hm.
Qed.
Lemma heap_content_empty__solver_postsort_sweep_init :
  forall (sb hl : list Z), HeapContent sb 0 (sublist 0 0 hl) 0.
Proof.
  intros sb hl.
  unfold HeapContent.
  rewrite sublist_0_0_nil__solver_postsort_sweep_init.
  split; [| unfold ZSum; simpl; reflexivity].
  rewrite sublist_0_0_nil__solver_postsort_sweep_init.
  unfold MinSubMultiset. split.
  - unfold SubMultiset. exists (@nil Z). simpl. apply Permutation_refl.
  - intros m' Hm' Hlen.
    apply sub_multiset_nil_inv__solver_postsort_sweep_init in Hm'.
    subst m'. unfold ZSum. simpl. lia.
Qed.
Lemma best_state_ext__solver_postsort_sweep_init :
  forall (P Q : Z -> Prop) (best : Z),
    (forall v, P v <-> Q v) ->
    BestState P best ->
    BestState Q best.
Proof.
  intros P Q best Hiff HB.
  unfold BestState in *.
  destruct HB as [[Hb Hnone] | [Hb Hmin]].
  - left. split; [exact Hb |].
    intros v Hv. apply (Hnone v). apply Hiff. exact Hv.
  - right. split; [exact Hb |].
    unfold min_value_of_subset, min_object_of_subset in *.
    destruct Hmin as [a [[Ha Hle] Heq]].
    exists a. split; [split |].
    + sets_unfold. sets_unfold in Ha. apply Hiff. exact Ha.
    + intros b Hbb. apply Hle. sets_unfold. sets_unfold in Hbb.
      apply Hiff. exact Hbb.
    + exact Heq.
Qed.
Lemma sweep_best_at_zero__solver_postsort_sweep_init :
  forall (values : list Z) (k b c j : Z) (st sb : list Z) (W best : Z),
    2 <= k ->
    ResidueBest values k b c j best ->
    SweepBest values k b c j st sb W 0 best.
Proof.
  intros values k b c j st sb W best Hk HR.
  unfold SweepBest. unfold ResidueBest in HR.
  eapply best_state_ext__solver_postsort_sweep_init; [| exact HR].
  intros v. unfold SweepSet. split.
  - intros H. left. exact H.
  - intros [H | [i' [Hi1 [Hi2 _]]]].
    + exact H.
    + lia.
Qed.
Lemma zsum_cons__solver_heap_maintain :
  forall (x : Z) (l : list Z), ZSum (x :: l) = x + ZSum l.
Proof. intros. unfold ZSum. simpl. reflexivity. Qed.
Lemma zsum_permutation__solver_heap_maintain :
  forall (l1 l2 : list Z), Permutation l1 l2 -> ZSum l1 = ZSum l2.
Proof.
  intros l1 l2 H.
  induction H; unfold ZSum in *; simpl in *; lia.
Qed.
Lemma zsum_bounds__solver_heap_maintain :
  forall (l : list Z) (lo hi : Z),
    (forall y, In y l -> lo <= y <= hi) ->
    Zlength l * lo <= ZSum l /\ ZSum l <= Zlength l * hi.
Proof.
  induction l as [| a l IH]; intros lo hi H.
  - rewrite Zlength_nil. unfold ZSum. simpl. lia.
  - assert (Ha : lo <= a <= hi) by (apply H; simpl; auto).
    destruct (IH lo hi) as [H1 H2].
    { intros y Hy. apply H. simpl. auto. }
    rewrite Zlength_cons.
    pose proof (Zlength_correct l).
    unfold ZSum in *. simpl in *.
    nia.
Qed.
Lemma Znth_In__solver_heap_maintain :
  forall (l : list Z) (i : Z), 0 <= i < Zlength l -> In (Znth i l 0) l.
Proof.
  intros l i H.
  unfold Znth. apply nth_In.
  rewrite Zlength_correct in H. lia.
Qed.
Lemma In_Znth__solver_heap_maintain :
  forall (l : list Z) (y : Z),
    In y l -> exists i, 0 <= i < Zlength l /\ Znth i l 0 = y.
Proof.
  intros l y H.
  apply (In_nth l y 0) in H as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. auto.
Qed.
Lemma forall_bounds_permutation__solver_heap_maintain :
  forall (l1 l2 : list Z) (lo hi : Z),
    Permutation l1 l2 ->
    (forall y, In y l1 -> lo <= y <= hi) ->
    forall q, 0 <= q < Zlength l2 -> lo <= Znth q l2 0 <= hi.
Proof.
  intros l1 l2 lo hi Hp Hb q Hq.
  apply Hb.
  apply (Permutation_in _ (Permutation_sym Hp)).
  apply Znth_In__solver_heap_maintain. auto.
Qed.
Lemma sublist_In_bounds__solver_heap_maintain :
  forall (l : list Z) (n lo hi : Z),
    0 <= n <= Zlength l ->
    (forall q, 0 <= q < n -> lo <= Znth q l 0 <= hi) ->
    forall y, In y (sublist 0 n l) -> lo <= y <= hi.
Proof.
  intros l n lo hi Hn Hb y Hy.
  apply In_Znth__solver_heap_maintain in Hy as [i [Hi He]].
  rewrite Zlength_sublist0 in Hi by lia.
  rewrite Znth_sublist0 in He by lia.
  subst y. apply Hb. lia.
Qed.
Lemma perm_count__solver_heap_maintain :
  forall (l1 l2 : list Z), Permutation l1 l2 ->
    forall z, count_occ Z.eq_dec l1 z = count_occ Z.eq_dec l2 z.
Proof.
  intros l1 l2 H.
  induction H; intros z; simpl; auto.
  - destruct (Z.eq_dec x z); auto.
  - destruct (Z.eq_dec y z); destruct (Z.eq_dec x z); auto.
  - rewrite IHPermutation1; auto.
Qed.
Lemma count_app__solver_heap_maintain :
  forall (l1 l2 : list Z) (z : Z),
    count_occ Z.eq_dec (l1 ++ l2) z
      = (count_occ Z.eq_dec l1 z + count_occ Z.eq_dec l2 z)%nat.
Proof.
  induction l1 as [| a l1 IH]; intros l2 z; simpl; auto.
  destruct (Z.eq_dec a z); rewrite IH; lia.
Qed.
Lemma submultiset_count__solver_heap_maintain :
  forall (m l : list Z),
    SubMultiset m l ->
    forall z, (count_occ Z.eq_dec m z <= count_occ Z.eq_dec l z)%nat.
Proof.
  intros m l [rest Hp] z.
  pose proof (perm_count__solver_heap_maintain _ _ Hp z) as Hc.
  rewrite count_app__solver_heap_maintain in Hc. lia.
Qed.
Lemma count_submultiset__solver_heap_maintain :
  forall (m l : list Z),
    (forall z, (count_occ Z.eq_dec m z <= count_occ Z.eq_dec l z)%nat) ->
    SubMultiset m l.
Proof.
  induction m as [| a m IH]; intros l H.
  - exists l. simpl. apply Permutation_refl.
  - assert (Hin : In a l).
    { apply (count_occ_In Z.eq_dec).
      specialize (H a). simpl in H.
      destruct (Z.eq_dec a a); [lia | contradiction]. }
    apply in_split in Hin as [l1 [l2 Hl]].
    assert (Hperm : Permutation l (a :: (l1 ++ l2))).
    { rewrite Hl. apply Permutation_sym. apply Permutation_middle. }
    assert (Hrest : forall z, (count_occ Z.eq_dec m z <= count_occ Z.eq_dec (l1 ++ l2) z)%nat).
    { intro z. specialize (H z).
      pose proof (perm_count__solver_heap_maintain _ _ Hperm z) as Hc.
      simpl in *. destruct (Z.eq_dec a z); lia. }
    destruct (IH _ Hrest) as [rest Hr].
    exists rest.
    apply (Permutation_trans Hperm).
    simpl. apply perm_skip. exact Hr.
Qed.
Lemma submultiset_length__solver_heap_maintain :
  forall (m l : list Z), SubMultiset m l -> Zlength m <= Zlength l.
Proof.
  intros m l [rest Hp].
  apply Permutation_length in Hp.
  rewrite length_app in Hp.
  rewrite !Zlength_correct. lia.
Qed.
Lemma submultiset_full_perm__solver_heap_maintain :
  forall (m l : list Z),
    SubMultiset m l -> Zlength m = Zlength l -> Permutation l m.
Proof.
  intros m l [rest Hp] Hlen.
  assert (rest = nil).
  { pose proof (Permutation_length Hp) as Hl.
    rewrite length_app in Hl.
    rewrite !Zlength_correct in Hlen.
    destruct rest as [| z rest]; auto.
    simpl in Hl. lia. }
  subst rest. rewrite app_nil_r in Hp. auto.
Qed.
Lemma min_sub_multiset_whole__solver_heap_maintain :
  forall (l m : list Z), Permutation l m -> MinSubMultiset l m.
Proof.
  intros l m Hp. split.
  - exists nil. rewrite app_nil_r. auto.
  - intros m' [rest Hr] Hlen.
    assert (Hpm : Permutation m (m' ++ rest)).
    { apply Permutation_trans with l; [apply Permutation_sym; auto | auto]. }
    pose proof (Permutation_length Hpm) as Hl.
    rewrite length_app in Hl.
    rewrite !Zlength_correct in Hlen.
    assert (rest = nil).
    { destruct rest as [| z rest]; auto. simpl in Hl. lia. }
    subst rest. rewrite app_nil_r in Hpm.
    rewrite (zsum_permutation__solver_heap_maintain _ _ Hpm). lia.
Qed.
Lemma submultiset_extend__solver_heap_maintain :
  forall (L M N : list Z),
    SubMultiset M L -> SubMultiset N L -> Zlength N < Zlength M ->
    exists y, In y M /\ SubMultiset (y :: N) L.
Proof.
  intros L M N HM HN Hlt.
  apply NNPP. intro Hno.
  assert (Hall : forall z, (count_occ Z.eq_dec M z <= count_occ Z.eq_dec N z)%nat).
  { intro z.
    destruct (in_dec Z.eq_dec z M) as [Hin | Hnin].
    - assert (Hns : ~ SubMultiset (z :: N) L).
      { intro Hs. apply Hno. exists z. split; auto. }
      assert (Hnc : ~ (forall w, (count_occ Z.eq_dec (z :: N) w <= count_occ Z.eq_dec L w)%nat)).
      { intro Hc. apply Hns. apply count_submultiset__solver_heap_maintain. auto. }
      apply not_all_ex_not in Hnc as [w Hw].
      apply Nat.nle_gt in Hw.
      pose proof (submultiset_count__solver_heap_maintain _ _ HN w) as HNw.
      simpl in Hw. destruct (Z.eq_dec z w).
      + subst w.
        pose proof (submultiset_count__solver_heap_maintain _ _ HM z) as HMz.
        lia.
      + lia.
    - rewrite (count_occ_not_In Z.eq_dec) in Hnin. lia. }
  pose proof (count_submultiset__solver_heap_maintain M N Hall) as Hs.
  apply submultiset_length__solver_heap_maintain in Hs. lia.
Qed.
Lemma min_sub_multiset_push_pop__solver_heap_maintain :
  forall (L M M' : list Z) (x m : Z),
    MinSubMultiset L M ->
    Permutation (x :: M) (m :: M') ->
    (forall y, In y (x :: M) -> y <= m) ->
    MinSubMultiset (L ++ (x :: nil)) M'.
Proof.
  intros L M M' x m [HsubM Hmin] Hperm Hub.
  destruct HsubM as [rest Hrest].
  assert (HlenM' : Zlength M' = Zlength M).
  { pose proof (Permutation_length Hperm) as Hl. simpl in Hl.
    rewrite !Zlength_correct. lia. }
  assert (Hsum : ZSum M' = x + ZSum M - m).
  { pose proof (zsum_permutation__solver_heap_maintain _ _ Hperm) as Hz.
    rewrite !zsum_cons__solver_heap_maintain in Hz. lia. }
  assert (Hxm : x <= m) by (apply Hub; simpl; auto).
  split.
  - exists (m :: rest).
    apply Permutation_trans with ((M ++ rest) ++ (x :: nil)).
    { apply Permutation_app_tail. auto. }
    apply Permutation_trans with (x :: (M ++ rest)).
    { apply Permutation_sym. apply Permutation_cons_append. }
    apply Permutation_trans with ((m :: M') ++ rest).
    { change (x :: M ++ rest) with ((x :: M) ++ rest).
      apply Permutation_app_tail. auto. }
    simpl. apply Permutation_middle.
  - intros N HsubN HlenN.
    destruct (classic (SubMultiset N L)) as [HNL | HNL].
    + assert (HMN : ZSum M <= ZSum N) by (apply Hmin; auto; lia).
      lia.
    + assert (Hcnt : forall z,
        (count_occ Z.eq_dec N z
          <= count_occ Z.eq_dec L z + (if Z.eq_dec x z then 1 else 0))%nat).
      { intro z.
        pose proof (submultiset_count__solver_heap_maintain _ _ HsubN z) as Hc.
        rewrite count_app__solver_heap_maintain in Hc. simpl in Hc.
        destruct (Z.eq_dec x z); lia. }
      assert (HinxN : In x N).
      { apply NNPP. intro Hn.
        apply HNL. apply count_submultiset__solver_heap_maintain. intro z.
        specialize (Hcnt z). destruct (Z.eq_dec x z).
        - subst z. rewrite (count_occ_not_In Z.eq_dec) in Hn. lia.
        - lia. }
      apply in_split in HinxN as [N1 [N2 HN]].
      assert (HpN : Permutation N (x :: (N1 ++ N2))).
      { rewrite HN. apply Permutation_sym. apply Permutation_middle. }
      assert (HsubN0 : SubMultiset (N1 ++ N2) L).
      { apply count_submultiset__solver_heap_maintain. intro z.
        pose proof (perm_count__solver_heap_maintain _ _ HpN z) as Hpc.
        specialize (Hcnt z). simpl in Hpc.
        destruct (Z.eq_dec x z); lia. }
      assert (HlenN0 : Zlength (N1 ++ N2) + 1 = Zlength N).
      { pose proof (Permutation_length HpN) as Hl. simpl in Hl.
        rewrite !Zlength_correct. lia. }
      destruct (submultiset_extend__solver_heap_maintain L M (N1 ++ N2))
        as [y [HyM HsubY]].
      { exists rest; auto. }
      { auto. }
      { lia. }
      assert (HMy : ZSum M <= ZSum (y :: (N1 ++ N2))).
      { apply Hmin; auto. rewrite Zlength_cons. lia. }
      assert (Hym : y <= m) by (apply Hub; simpl; auto).
      rewrite zsum_cons__solver_heap_maintain in HMy.
      assert (HNsum : ZSum N = x + ZSum (N1 ++ N2)).
      { rewrite (zsum_permutation__solver_heap_maintain _ _ HpN).
        rewrite zsum_cons__solver_heap_maintain. reflexivity. }
      lia.
Qed.
Lemma perm_index__solver_sweep_value : forall (A : Type) (l l' : list A) (d : A),
  Permutation l l' ->
  exists f : Z -> Z,
    (forall x, 0 <= x < Zlength l' -> 0 <= f x < Zlength l) /\
    (forall x y, 0 <= x < Zlength l' -> 0 <= y < Zlength l' -> f x = f y -> x = y) /\
    (forall x, 0 <= x < Zlength l' -> Znth x l' d = Znth (f x) l d).
Proof.
  intros A l l' d Hp.
  apply (Permutation_nth l l' d) in Hp.
  destruct Hp as [Hlen [g [Hb [Hi Hn]]]].
  simpl in Hb, Hi, Hn.
  unfold FinFun.bFun in Hb. unfold FinFun.bInjective in Hi.
  rewrite !Zlength_correct.
  rewrite Hlen.
  exists (fun x => Z.of_nat (g (Z.to_nat x))).
  split; [| split].
  - intros x Hx. pose proof (Hb (Z.to_nat x)). lia.
  - intros x y Hx Hy He.
    assert (g (Z.to_nat x) = g (Z.to_nat y)) by lia.
    apply Hi in H; lia.
  - intros x Hx. unfold Znth. rewrite Nat2Z.id. apply Hn. lia.
Qed.
Lemma Znth_combine__solver_sweep_value : forall (A B : Type) (l1 : list A) (l2 : list B) (d1 : A) (d2 : B) q,
  Zlength l1 = Zlength l2 ->
  Znth q (combine l1 l2) (d1, d2) = (Znth q l1 d1, Znth q l2 d2).
Proof.
  intros. unfold Znth. apply combine_nth.
  rewrite !Zlength_correct in H. lia.
Qed.
Lemma Zlength_combine__solver_sweep_value : forall (A B : Type) (l1 : list A) (l2 : list B),
  Zlength l1 = Zlength l2 -> Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros. rewrite !Zlength_correct in *. rewrite length_combine. lia.
Qed.
Lemma nodup_Znth__solver_sweep_value : forall (l : list Z),
  (forall x y, 0 <= x < Zlength l -> 0 <= y < Zlength l -> Znth x l 0 = Znth y l 0 -> x = y) ->
  NoDup l.
Proof.
  intros l H. apply (NoDup_nth l 0). intros i j Hi Hj He.
  assert (Z.of_nat i = Z.of_nat j); [| lia].
  apply H; unfold Znth; rewrite ?Nat2Z.id; rewrite ?Zlength_correct; try lia.
Qed.
Lemma zsum_map_add__solver_sweep_value : forall (dd : Z) (l : list Z),
  ZSum (map (fun x => x + dd) l) = ZSum l + Zlength l * dd.
Proof.
  intros dd l. unfold ZSum. induction l as [| a l IH].
  - cbn [map fold_right]. rewrite Zlength_nil. lia.
  - cbn [map fold_right] in *. rewrite Zlength_cons. lia.
Qed.
Lemma zsum_bounds__solver_sweep_value : forall (lo hi : Z) (l : list Z),
  Forall (fun x => lo <= x <= hi) l ->
  Zlength l * lo <= ZSum l /\ ZSum l <= Zlength l * hi.
Proof.
  intros lo hi l H. unfold ZSum. induction l as [| a l IH].
  - cbn [fold_right]. rewrite Zlength_nil. lia.
  - inversion H; subst. specialize (IH H3).
    cbn [fold_right] in *. rewrite Zlength_cons.
    assert (0 <= Zlength l) by (rewrite Zlength_correct; lia).
    nia.
Qed.
Lemma raise_cost_normal_form__solver_sweep_value : forall b c from target,
  1 <= b -> 1 <= c -> from <= target ->
  RaiseCost b c from target
    (((target - from) mod 5) * c + ((target - from) / 5) * (WCost b c)).
Proof.
  intros b c from target Hb Hc Hle.
  assert (Hr : 0 <= (target - from) mod 5 < 5) by (apply Z.mod_pos_bound; lia).
  assert (Hq : target - from = 5 * ((target - from) / 5) + (target - from) mod 5)
    by (pose proof (Z.div_mod (target - from) 5); lia).
  assert (Hq0 : 0 <= (target - from) / 5) by (apply Z.div_pos; lia).
  unfold RaiseCost, min_value_of_subset, min_object_of_subset. sets_unfold.
  exists (((target - from) mod 5) * c + ((target - from) / 5) * (WCost b c)).
  split; [split |]; try reflexivity.
  - unfold WCost. destruct (Z.le_gt_cases b (5 * c)) as [Hm | Hm].
    + rewrite Z.min_l by lia.
      exists ((target - from) / 5), ((target - from) mod 5).
      repeat split; try lia; try nia.
    + rewrite Z.min_r by lia.
      exists 0, (target - from).
      repeat split; try lia; try nia.
  - intros v Hv. destruct Hv as [blogs [comments [H1 [H2 [H3 H4]]]]]. subst v.
    assert (Hbl : blogs <= (target - from) / 5) by lia.
    unfold WCost. destruct (Z.le_gt_cases b (5 * c)) as [Hm | Hm].
    + rewrite Z.min_l by lia. nia.
    + rewrite Z.min_r by lia. nia.
Qed.
Lemma target_point_mod__solver_sweep_value : forall s j,
  0 <= j < 5 -> (TargetPoint s j) mod 5 = j.
Proof.
  intros s j Hj. unfold TargetPoint.
  rewrite Zplus_mod, Zmod_mod, <- Zplus_mod.
  replace (s + (j - s)) with j by lia.
  apply Z.mod_small. lia.
Qed.
Lemma raise_cost_shifted__solver_sweep_value : forall b c W j s t',
  1 <= b -> 1 <= c -> W = WCost b c -> 0 <= j < 5 ->
  TargetPoint s j <= t' -> t' mod 5 = j ->
  RaiseCost b c (s - 2000000000) (t' - 2000000000)
    (NormalizedBase s j W c + ((t' - j) / 5) * W).
Proof.
  intros b c W j s t' Hb Hc HW Hj Hle Hmod. subst W.
  unfold NormalizedBase, TargetPoint in *.
  assert (Hr : 0 <= (j - s) mod 5 < 5) by (apply Z.mod_pos_bound; lia).
  assert (Ht : s + (j - s) mod 5 - j = 5 * (- ((j - s) / 5))).
  { pose proof (Z.div_mod (j - s) 5). lia. }
  assert (Ht' : t' - j = 5 * (t' / 5)).
  { pose proof (Z.div_mod t' 5). lia. }
  assert (Hfrom : s - 2000000000 <= t' - 2000000000) by lia.
  pose proof (raise_cost_normal_form__solver_sweep_value b c (s - 2000000000) (t' - 2000000000) Hb Hc Hfrom) as Hnf.
  assert (Hd : t' - 2000000000 - (s - 2000000000)
               = (j - s) mod 5 + (t' / 5 - (- ((j - s) / 5))) * 5) by lia.
  rewrite Hd in Hnf.
  rewrite Z_mod_plus_full, Z_div_plus_full in Hnf by lia.
  rewrite (Z.mod_small ((j - s) mod 5) 5) in Hnf by lia.
  rewrite (Z.div_small ((j - s) mod 5) 5) in Hnf by lia.
  replace ((s + (j - s) mod 5 - j) / 5) with (- ((j - s) / 5)).
  2:{ rewrite Ht. rewrite Z.mul_comm. rewrite Z.div_mul by lia. reflexivity. }
  replace ((t' - j) / 5) with (t' / 5).
  2:{ rewrite Ht'. rewrite Z.mul_comm. rewrite Z.div_mul by lia. reflexivity. }
  replace ((j - s) mod 5 * c - - ((j - s) / 5) * WCost b c + t' / 5 * WCost b c)
    with ((j - s) mod 5 * c + (0 + (t' / 5 - - ((j - s) / 5))) * WCost b c) by ring.
  exact Hnf.
Qed.
Lemma nth_map_len__solver_sweep_value : forall (A B : Type) (f : A -> B) (l : list A) n (da : A) (db : B),
  (n < length l)%nat -> nth n (map f l) db = f (nth n l da).
Proof.
  intros. rewrite (nth_indep (map f l) db (f da)) by (rewrite length_map; lia).
  apply map_nth.
Qed.
Lemma Forall_Znth__solver_sweep_value : forall (P : Z -> Prop) (l : list Z),
  (forall m, 0 <= m < Zlength l -> P (Znth m l 0)) -> Forall P l.
Proof.
  intros P l H. apply Forall_nth. intros idx dd Hidx.
  rewrite (nth_indep l dd 0) by lia.
  specialize (H (Z.of_nat idx)). unfold Znth in H. rewrite Nat2Z.id in H.
  apply H. rewrite Zlength_correct. lia.
Qed.
Lemma perm_Zlength__solver_sweep_value : forall (A : Type) (l l' : list A),
  Permutation l l' -> Zlength l = Zlength l'.
Proof.
  intros. rewrite !Zlength_correct. f_equal. apply Permutation_length. auto.
Qed.
Lemma norm_cost_bounds__solver_sweep_value : forall b c W j s t',
  1 <= b -> b <= 1000 -> 1 <= c -> c <= 1000 -> W = WCost b c -> 0 <= j < 5 ->
  TargetPoint s j <= t' -> t' mod 5 = j ->
  1000000000 <= s -> t' <= 3000000004 ->
  0 <= NormalizedBase s j W c + ((t' - j) / 5) * W <= 400000004000.
Proof.
  intros b c W j s t' Hb1 Hb2 Hc1 Hc2 HW Hj Hle Hmod Hs Ht'.
  assert (HW1 : 1 <= W <= 1000) by (subst W; unfold WCost; lia).
  unfold NormalizedBase, TargetPoint in *.
  assert (Hr : 0 <= (j - s) mod 5 < 5) by (apply Z.mod_pos_bound; lia).
  assert (Ht : s + (j - s) mod 5 - j = 5 * (- ((j - s) / 5))).
  { pose proof (Z.div_mod (j - s) 5). lia. }
  assert (Htp : t' - j = 5 * (t' / 5)).
  { pose proof (Z.div_mod t' 5). lia. }
  replace ((s + (j - s) mod 5 - j) / 5) with (- ((j - s) / 5)).
  2:{ rewrite Ht. rewrite Z.mul_comm. rewrite Z.div_mul by lia. reflexivity. }
  replace ((t' - j) / 5) with (t' / 5).
  2:{ rewrite Htp. rewrite Z.mul_comm. rewrite Z.div_mul by lia. reflexivity. }
  replace ((j - s) mod 5 * c - - ((j - s) / 5) * W + t' / 5 * W)
    with ((j - s) mod 5 * c + (t' / 5 - - ((j - s) / 5)) * W) by ring.
  assert (Hdiff : 0 <= t' / 5 - - ((j - s) / 5) <= 400000000) by lia.
  nia.
Qed.
Lemma tie_cost_from_sweep__solver_sweep_value :
  forall (contributions sh ct cb st sb hl : list Z) (n k b c W j i hsum : Z),
  2 <= k -> k <= n -> n <= 200000 -> n = Zlength contributions ->
  1 <= b -> b <= 1000 -> 1 <= c -> c <= 1000 ->
  W = WCost b c -> 0 <= j -> j < 5 -> 0 <= i -> i < n ->
  Zlength sh = n -> Zlength ct = n -> Zlength cb = n -> Zlength hl = n ->
  Zlength st = n -> Zlength sb = n ->
  ShiftedPrefix contributions sh n ->
  (forall q, 0 <= q < n -> 1000000000 <= Znth q sh 0 /\ Znth q sh 0 <= 3000000000) ->
  CandPrefix sh j W c n ct cb ->
  ZipPerm ct cb st sb ->
  Nondecreasing st ->
  (forall q, 0 <= q < n ->
     ((1000000000 <= Znth q st 0 /\ Znth q st 0 <= 3000000004) /\
      -600000000000 <= Znth q sb 0) /\ Znth q sb 0 <= 4000) ->
  HeapContent sb (i + 1) (sublist 0 k hl) hsum ->
  KSmallSum (sublist 0 (i + 1) sb) k hsum /\
  SweepValue st sb k j W i (hsum + (k * (Z.quot (Znth i st 0 - j) 5)) * W) /\
  TieCostAtResidue contributions k b c j (hsum + (k * (Z.quot (Znth i st 0 - j) 5)) * W) /\
  0 <= hsum + (k * (Z.quot (Znth i st 0 - j) 5)) * W <= 300000000000000000.
Proof.
  intros contributions sh ct cb st sb hl n k b c W j i hsum.
  intros Hk2 Hkn Hn200 Hncon Hb1 Hb2 Hc1 Hc2 HW Hj0 Hj5 Hi0 Hin.
  intros Hlsh Hlct Hlcb Hlhl Hlst Hlsb Hshift Hshb Hcand Hzip Hnd Hstb Hhc.
  assert (HW1 : 1 <= W <= 1000) by (subst W; unfold WCost; lia).
  assert (Hsti : 1000000000 <= Znth i st 0 <= 3000000004)
    by (destruct (Hstb i ltac:(lia)) as [[HA _] _]; lia).
  assert (Hquot : Z.quot (Znth i st 0 - j) 5 = (Znth i st 0 - j) / 5)
    by (apply Z.quot_div_nonneg; lia).
  rewrite Hquot.
  remember ((Znth i st 0 - j) / 5) as Q eqn:HQ.
  destruct Hhc as [Hmin Hsum].
  assert (HlH : Zlength (sublist 0 k hl) = k) by (apply Zlength_sublist0; lia).
  assert (Hks : KSmallSum (sublist 0 (i + 1) sb) k hsum).
  { unfold KSmallSum. exists (sublist 0 k hl). auto. }
  split; [exact Hks |].
  split.
  { unfold SweepValue. exists hsum. split; [exact Hks |].
    rewrite <- HQ. reflexivity. }
  (* index map from (st,sb) positions to (ct,cb) positions *)
  destruct Hzip as [Hz1 [Hz2 [Hz3 Hzp]]].
  assert (Hlcc : Zlength (combine ct cb) = n).
  { rewrite Zlength_combine__solver_sweep_value by lia. lia. }
  assert (Hlss : Zlength (combine st sb) = n).
  { rewrite Zlength_combine__solver_sweep_value by lia. lia. }
  destruct (perm_index__solver_sweep_value (Z * Z) (combine ct cb) (combine st sb) (0, 0) Hzp)
    as [f1 [Hf1r [Hf1i Hf1v]]].
  rewrite Hlcc in Hf1r. rewrite Hlss in Hf1r, Hf1i, Hf1v.
  assert (Hf1both : forall q, 0 <= q < n ->
      Znth q st 0 = Znth (f1 q) ct 0 /\ Znth q sb 0 = Znth (f1 q) cb 0).
  { intros q Hq. specialize (Hf1v q Hq).
    rewrite (Znth_combine__solver_sweep_value Z Z st sb 0 0) in Hf1v by lia.
    rewrite (Znth_combine__solver_sweep_value Z Z ct cb 0 0) in Hf1v by lia.
    inversion Hf1v. auto. }
  (* index map for the chosen sub-multiset *)
  destruct Hmin as [[rest Hperm] _].
  assert (Hlsub : Zlength (sublist 0 (i + 1) sb) = i + 1) by (apply Zlength_sublist0; lia).
  assert (Hlapp : Zlength (sublist 0 k hl ++ rest) = i + 1).
  { rewrite <- (perm_Zlength__solver_sweep_value Z _ _ Hperm). exact Hlsub. }
  assert (Hrest0 : 0 <= Zlength rest) by (rewrite Zlength_correct; lia).
  rewrite Zlength_app in Hlapp.
  assert (Hki : k <= i + 1) by lia.
  rewrite <- Zlength_app in Hlapp.
  destruct (perm_index__solver_sweep_value Z (sublist 0 (i + 1) sb) (sublist 0 k hl ++ rest) 0 Hperm)
    as [f2 [Hf2r [Hf2i Hf2v]]].
  rewrite Hlapp in Hf2r, Hf2i, Hf2v. rewrite Hlsub in Hf2r.
  assert (Hf2 : forall m, 0 <= m < k -> Znth m (sublist 0 k hl) 0 = Znth (f2 m) sb 0).
  { intros m Hm.
    assert (Hm' : 0 <= m < i + 1) by lia.
    specialize (Hf2v m Hm'). specialize (Hf2r m Hm').
    rewrite app_Znth1 in Hf2v by lia.
    rewrite Hf2v. apply Znth_sublist0. lia. }
  (* the k chosen contribution indices *)
  set (g := fun m => f1 (f2 m)).
  assert (Hgr : forall m, 0 <= m < k -> 0 <= g m < n).
  { intros m Hm. unfold g. apply Hf1r. specialize (Hf2r m ltac:(lia)). lia. }
  assert (Hgi : forall m1 m2, 0 <= m1 < k -> 0 <= m2 < k -> g m1 = g m2 -> m1 = m2).
  { intros m1 m2 H1 H2 He. unfold g in He.
    pose proof (Hf2r m1 ltac:(lia)). pose proof (Hf2r m2 ltac:(lia)).
    assert (Heq2 : f2 m1 = f2 m2) by (apply Hf1i; [lia | lia | exact He]).
    apply Hf2i; [lia | lia | exact Heq2]. }
  set (chosen := map (fun m : nat => g (Z.of_nat m)) (seq 0 (Z.to_nat k))).
  assert (Hlchosen : Zlength chosen = k).
  { unfold chosen. rewrite Zlength_correct, length_map, length_seq. lia. }
  assert (Hchosen : forall m, 0 <= m < k -> Znth m chosen 0 = g m).
  { intros m Hm. unfold chosen, Znth.
    rewrite (nth_map_len__solver_sweep_value nat Z _ _ _ 0%nat 0) by (rewrite length_seq; lia).
    rewrite seq_nth by lia. cbv beta. f_equal. lia. }
  assert (Hnodup : NoDup chosen).
  { apply nodup_Znth__solver_sweep_value. intros x y Hx Hy He.
    rewrite Hlchosen in Hx, Hy.
    rewrite (Hchosen x Hx), (Hchosen y Hy) in He.
    apply Hgi; auto. }
  assert (Hfa : Forall (fun p => 0 <= p < Zlength contributions) chosen).
  { apply Forall_Znth__solver_sweep_value. intros m Hm. rewrite Hlchosen in Hm.
    rewrite (Hchosen m Hm). pose proof (Hgr m Hm). lia. }
  (* the k costs *)
  set (costs := map (fun x => x + Q * W) (sublist 0 k hl)).
  assert (HlenH : Z.of_nat (length (sublist 0 k hl)) = k)
    by (rewrite <- Zlength_correct; exact HlH).
  assert (Hlcosts : Zlength costs = k).
  { unfold costs. rewrite Zlength_correct, length_map. lia. }
  assert (Hcosts : forall m, 0 <= m < k ->
      Znth m costs 0 = Znth m (sublist 0 k hl) 0 + Q * W).
  { intros m Hm. unfold costs, Znth.
    rewrite (nth_map_len__solver_sweep_value Z Z _ _ _ 0 0) by lia. reflexivity. }
  assert (Hsumcosts : ZSum costs = hsum + (k * Q) * W).
  { unfold costs. rewrite zsum_map_add__solver_sweep_value, HlH, <- Hsum.
    rewrite Z.mul_assoc. reflexivity. }
  (* the common target *)
  assert (Hmodsti : (Znth i st 0) mod 5 = j).
  { assert (Hi' : 0 <= i < n) by lia.
    destruct (Hf1both i Hi') as [Hst_i _].
    pose proof (Hf1r i Hi') as Hr_i.
    destruct (Hcand (f1 i) Hr_i) as [Hct_i _].
    rewrite Hst_i, Hct_i. apply target_point_mod__solver_sweep_value. lia. }
  assert (Htarget : (Znth i st 0 - 2000000000) mod 5 = j).
  { replace (Znth i st 0 - 2000000000) with (Znth i st 0 + (-400000000) * 5) by lia.
    rewrite Z_mod_plus_full. exact Hmodsti. }
  assert (Hmain : forall m, 0 <= m < k ->
      RaiseCost b c (Znth (Znth m chosen 0) contributions 0)
        (Znth i st 0 - 2000000000) (Znth m costs 0)
      /\ 0 <= Znth m costs 0 <= 400000004000).
  { intros m Hm.
    assert (Hq : 0 <= f2 m < i + 1) by (apply Hf2r; lia).
    assert (Hqn : 0 <= f2 m < n) by lia.
    assert (Hp : 0 <= f1 (f2 m) < n) by (apply Hf1r; lia).
    destruct (Hcand (f1 (f2 m)) Hp) as [Hctp Hcbp].
    destruct (Hf1both (f2 m) Hqn) as [Hst_q Hsb_q].
    assert (HHm : Znth m (sublist 0 k hl) 0 = NormalizedBase (Znth (f1 (f2 m)) sh 0) j W c).
    { rewrite (Hf2 m Hm), Hsb_q. exact Hcbp. }
    assert (Hlep : TargetPoint (Znth (f1 (f2 m)) sh 0) j <= Znth i st 0).
    { rewrite <- Hctp, <- Hst_q. apply Hnd; lia. }
    assert (Hshp : Znth (f1 (f2 m)) sh 0 = Znth (f1 (f2 m)) contributions 0 + 2000000000)
      by (apply Hshift; lia).
    assert (Hshpb : 1000000000 <= Znth (f1 (f2 m)) sh 0 <= 3000000000)
      by (apply Hshb; lia).
    rewrite (Hcosts m Hm), HHm, HQ.
    split.
    - rewrite (Hchosen m Hm). unfold g.
      replace (Znth (f1 (f2 m)) contributions 0)
        with (Znth (f1 (f2 m)) sh 0 - 2000000000) by lia.
      apply raise_cost_shifted__solver_sweep_value; try lia; try assumption.
    - apply (norm_cost_bounds__solver_sweep_value b c W j (Znth (f1 (f2 m)) sh 0) (Znth i st 0));
        try lia; try assumption. }
  split.
  - unfold TieCostAtResidue.
    exists chosen, costs, (Znth i st 0 - 2000000000).
    split; [exact Htarget |].
    split; [unfold ChosenBloggers; repeat split; assumption |].
    split; [exact Hlcosts |].
    split.
    + intros m Hm. destruct (Hmain m Hm) as [HR _]. exact HR.
    + unfold ZSum in Hsumcosts. symmetry. exact Hsumcosts.
  - rewrite <- Hsumcosts.
    assert (Hfc : Forall (fun x => 0 <= x <= 400000004000) costs).
    { apply Forall_Znth__solver_sweep_value. intros m Hm. rewrite Hlcosts in Hm.
      destruct (Hmain m Hm) as [_ HB]. exact HB. }
    destruct (zsum_bounds__solver_sweep_value 0 400000004000 costs Hfc) as [Hlo Hhi].
    rewrite Hlcosts in Hlo, Hhi. lia.
Qed.
Lemma ksmall_sum_unique__solver_best_update :
  forall (l : list Z) (k s1 s2 : Z),
    KSmallSum l k s1 ->
    KSmallSum l k s2 ->
    s1 = s2.
Proof.
  intros l k s1 s2 H1 H2.
  destruct H1 as [m1 [[Hsub1 Hmin1] [Hlen1 Hs1]]].
  destruct H2 as [m2 [[Hsub2 Hmin2] [Hlen2 Hs2]]].
  assert (Hle1 : ZSum m1 <= ZSum m2).
  { apply Hmin1; [ exact Hsub2 | rewrite Hlen1, Hlen2; reflexivity ]. }
  assert (Hle2 : ZSum m2 <= ZSum m1).
  { apply Hmin2; [ exact Hsub1 | rewrite Hlen1, Hlen2; reflexivity ]. }
  lia.
Qed.
Lemma sweep_value_unique__solver_best_update :
  forall (st sb : list Z) (k j W i v1 v2 : Z),
    SweepValue st sb k j W i v1 ->
    SweepValue st sb k j W i v2 ->
    v1 = v2.
Proof.
  intros st sb k j W i v1 v2 [s1 [Hk1 Hv1]] [s2 [Hk2 Hv2]].
  pose proof (ksmall_sum_unique__solver_best_update _ _ _ _ Hk1 Hk2) as Hs.
  lia.
Qed.
Lemma sweep_set_step__solver_best_update :
  forall (values : list Z) (k b c j : Z) (st sb : list Z) (W i total : Z),
    k - 1 <= i ->
    SweepValue st sb k j W i total ->
    forall v,
      SweepSet values k b c j st sb W (i + 1) v <->
      (SweepSet values k b c j st sb W i v \/ v = total).
Proof.
  intros values k b c j st sb W i total Hi Htot v.
  unfold SweepSet.
  split.
  - intros [Hres | [i' [Hlo [Hhi Hsv]]]].
    + left. left. exact Hres.
    + assert (i' < i \/ i' = i) as [Hlt | Heq] by lia.
      * left. right. exists i'. split; [ exact Hlo | split; [ exact Hlt | exact Hsv ] ].
      * right. subst i'.
        apply (sweep_value_unique__solver_best_update _ _ _ _ _ _ _ _ Hsv Htot).
  - intros [[Hres | [i' [Hlo [Hhi Hsv]]]] | Heq].
    + left. exact Hres.
    + right. exists i'. split; [ exact Hlo | split; [ lia | exact Hsv ] ].
    + right. exists i. split; [ lia | split; [ lia | ] ].
      subst v. exact Htot.
Qed.
Lemma sweep_set_stall__solver_best_update :
  forall (values : list Z) (k b c j : Z) (st sb : list Z) (W i : Z),
    i + 1 < k ->
    forall v,
      SweepSet values k b c j st sb W (i + 1) v <->
      SweepSet values k b c j st sb W i v.
Proof.
  intros values k b c j st sb W i Hk v.
  unfold SweepSet.
  split.
  - intros [Hres | [i' [Hlo [Hhi _]]]]; [ left; exact Hres | lia ].
  - intros [Hres | [i' [Hlo [Hhi _]]]]; [ left; exact Hres | lia ].
Qed.
Lemma min_id_intro__solver_best_update :
  forall (X : Z -> Prop) (n : Z),
    X n ->
    (forall b, X b -> n <= b) ->
    min_value_of_subset Z.le X (fun x => x) n.
Proof.
  intros X n Hn Hle.
  exists n.
  split; [ split | reflexivity ].
  - exact Hn.
  - exact Hle.
Qed.
Lemma min_id_elim__solver_best_update :
  forall (X : Z -> Prop) (n : Z),
    min_value_of_subset Z.le X (fun x => x) n ->
    X n /\ (forall b, X b -> n <= b).
Proof.
  intros X n [a [[Ha Hle] Hfa]].
  assert (Hna : n = a) by (rewrite <- Hfa; reflexivity).
  subst n.
  split; [ exact Ha | exact Hle ].
Qed.
Lemma best_state_same__solver_best_update :
  forall (P Q : Z -> Prop) (best : Z),
    (forall v, Q v <-> P v) ->
    BestState P best ->
    BestState Q best.
Proof.
  intros P Q best Hiff HB.
  destruct HB as [[Hm1 Hnone] | [Hpos Hmin]].
  - left. split; [ exact Hm1 | ].
    intros v Hv. apply (Hnone v). apply Hiff. exact Hv.
  - right. split; [ exact Hpos | ].
    apply min_id_elim__solver_best_update in Hmin.
    destruct Hmin as [Hin Hle].
    apply min_id_intro__solver_best_update.
    + apply Hiff. exact Hin.
    + intros b Hb. apply Hle. apply Hiff. exact Hb.
Qed.
Lemma best_state_step__solver_best_update :
  forall (P Q : Z -> Prop) (best total : Z),
    BestState P best ->
    (forall v, Q v <-> (P v \/ v = total)) ->
    0 <= total ->
    (best < 0 \/ total < best) ->
    BestState Q total.
Proof.
  intros P Q best total HB Hiff Hnn Hlt.
  right. split; [ exact Hnn | ].
  apply min_id_intro__solver_best_update.
  - apply Hiff. right. reflexivity.
  - intros b Hb.
    apply Hiff in Hb.
    destruct Hb as [Hb | Hb]; [ | lia ].
    destruct HB as [[Hm1 Hnone] | [Hpos Hmin]].
    + exfalso. apply (Hnone b). exact Hb.
    + apply min_id_elim__solver_best_update in Hmin.
      destruct Hmin as [Hin Hle].
      specialize (Hle b Hb). lia.
Qed.
Lemma best_state_keep__solver_best_update :
  forall (P Q : Z -> Prop) (best total : Z),
    BestState P best ->
    (forall v, Q v <-> (P v \/ v = total)) ->
    0 <= best ->
    best <= total ->
    BestState Q best.
Proof.
  intros P Q best total HB Hiff Hnn Hle.
  right. split; [ exact Hnn | ].
  destruct HB as [[Hm1 Hnone] | [Hpos Hmin]]; [ lia | ].
  apply min_id_elim__solver_best_update in Hmin.
  destruct Hmin as [Hin Hlemin].
  apply min_id_intro__solver_best_update.
  - apply Hiff. left. exact Hin.
  - intros b Hb. apply Hiff in Hb.
    destruct Hb as [Hb | Hb]; [ | lia ].
    apply Hlemin. exact Hb.
Qed.
Lemma zsum_perm__solver_residue_rollup : forall (l1 l2 : list Z),
  Permutation l1 l2 -> ZSum l1 = ZSum l2.
Proof.
  intros l1 l2 H. induction H; unfold ZSum in *; simpl in *; lia.
Qed.
Lemma abssum_app__solver_residue_rollup : forall (l1 l2 : list Z),
  fold_right (fun x a => Z.abs x + a) 0 (l1 ++ l2) =
  fold_right (fun x a => Z.abs x + a) 0 l1 + fold_right (fun x a => Z.abs x + a) 0 l2.
Proof.
  intros l1 l2. induction l1; simpl; lia.
Qed.
Lemma abssum_perm__solver_residue_rollup : forall (l1 l2 : list Z),
  Permutation l1 l2 ->
  fold_right (fun x a => Z.abs x + a) 0 l1 = fold_right (fun x a => Z.abs x + a) 0 l2.
Proof.
  intros l1 l2 H. induction H; simpl in *; lia.
Qed.
Lemma abssum_nonneg__solver_residue_rollup : forall (l : list Z),
  0 <= fold_right (fun x a => Z.abs x + a) 0 l.
Proof.
  intros l. induction l; simpl; [lia |]. pose proof (Z.abs_nonneg a). lia.
Qed.
Lemma zsum_abs_bound__solver_residue_rollup : forall (l : list Z),
  - fold_right (fun x a => Z.abs x + a) 0 l <= ZSum l <= fold_right (fun x a => Z.abs x + a) 0 l.
Proof.
  intros l. induction l; unfold ZSum in *; simpl; [lia |].
  pose proof (Z.abs_nonneg a).
  destruct (Z.abs_spec a) as [[? ?] | [? ?]]; lia.
Qed.
Lemma submultiset_prefix__solver_residue_rollup : forall (l : list Z) (k : Z),
  0 <= k <= Zlength l -> SubMultiset (sublist 0 k l) l.
Proof.
  intros l k H. exists (sublist k (Zlength l) l).
  rewrite <- (sublist_split 0 (Zlength l) k l) by lia.
  rewrite (sublist_self l (Zlength l)) by reflexivity.
  apply Permutation_refl.
Qed.
Lemma submultiset_abs__solver_residue_rollup : forall (m l : list Z),
  SubMultiset m l ->
  fold_right (fun x a => Z.abs x + a) 0 m <= fold_right (fun x a => Z.abs x + a) 0 l.
Proof.
  intros m l [rest Hp].
  rewrite (abssum_perm__solver_residue_rollup _ _ Hp).
  rewrite abssum_app__solver_residue_rollup.
  pose proof (abssum_nonneg__solver_residue_rollup rest). lia.
Qed.
Lemma min_submultiset_exists__solver_residue_rollup : forall (l : list Z) (k : Z),
  0 <= k <= Zlength l ->
  exists m, MinSubMultiset l m /\ Zlength m = k.
Proof.
  intros l k Hk.
  remember (fold_right (fun x a => Z.abs x + a) 0 l) as B eqn:HB.
  assert (HB0 : 0 <= B) by (subst B; apply abssum_nonneg__solver_residue_rollup).
  set (Q := fun z => exists m, SubMultiset m l /\ Zlength m = k /\ z = ZSum m + B).
  assert (Hbound : forall m, SubMultiset m l -> 0 <= ZSum m + B <= 2 * B).
  { intros m Hm.
    pose proof (submultiset_abs__solver_residue_rollup _ _ Hm) as H1.
    pose proof (zsum_abs_bound__solver_residue_rollup m) as H2.
    lia. }
  assert (Hex : exists z, 0 <= z <= 2 * B /\ Q z).
  { pose proof (submultiset_prefix__solver_residue_rollup l k Hk) as Hp.
    exists (ZSum (sublist 0 k l) + B). split; [apply Hbound; auto |].
    exists (sublist 0 k l). split; [auto | split; [| reflexivity]].
    apply Zlength_sublist0; lia. }
  destruct (min_n_in_range Q (2 * B) ltac:(lia) Hex) as [z [HQz [Hzr Hmin]]].
  destruct HQz as [m [Hsm [Hlen Hz]]].
  exists m. split; [| exact Hlen].
  split; [exact Hsm |].
  intros m' Hsm' Hlen'.
  assert (HQ' : Q (ZSum m' + B)).
  { exists m'. split; [auto | split; [lia | reflexivity]]. }
  pose proof (Hmin (ZSum m' + B) (Hbound m' Hsm') HQ'). lia.
Qed.
Lemma ksmallsum_exists__solver_residue_rollup : forall (l : list Z) (k : Z),
  0 <= k <= Zlength l -> exists s, KSmallSum l k s.
Proof.
  intros l k Hk.
  destruct (min_submultiset_exists__solver_residue_rollup l k Hk) as [m [Hm Hlen]].
  exists (ZSum m). exists m. auto.
Qed.
Lemma Znth_app1__solver_residue_rollup : forall (A : Type) (d : A) (l1 l2 : list A) (p : Z),
  0 <= p < Zlength l1 -> Znth p (l1 ++ l2) d = Znth p l1 d.
Proof.
  intros A d l1 l2 p H. unfold Znth. rewrite Zlength_correct in H.
  apply app_nth1. lia.
Qed.
Lemma Znth_app2__solver_residue_rollup : forall (A : Type) (d : A) (l1 l2 : list A) (p : Z),
  Zlength l1 <= p -> Znth p (l1 ++ l2) d = Znth (p - Zlength l1) l2 d.
Proof.
  intros A d l1 l2 p H. unfold Znth. rewrite Zlength_correct in *.
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma NoDup_map_inj__solver_residue_rollup : forall (f : Z -> Z) (l : list Z),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros f l. induction l as [| a l IH]; intros Hinj Hnd; simpl; [constructor |].
  inversion Hnd; subst.
  constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
    apply H1. replace a with y; [auto |]. apply Hinj; simpl; auto.
  - apply IH; auto. intros x y Hx Hy. apply Hinj; simpl; auto.
Qed.
Lemma split_at_index__solver_residue_rollup : forall (A : Type) (d : A) (L : list A) (i : Z),
  0 <= i < Zlength L ->
  exists L1 L2, L = L1 ++ Znth i L d :: L2 /\ Zlength L1 = i.
Proof.
  intros A d L i H. rewrite Zlength_correct in H.
  assert (Hn : (Z.to_nat i < length L)%nat) by lia.
  pose proof (nth_error_nth' L d Hn) as Hne.
  apply nth_error_split in Hne.
  destruct Hne as [L1 [L2 [HL Hlen]]].
  exists L1, L2. split; [exact HL |].
  rewrite Zlength_correct, Hlen. lia.
Qed.
Lemma perm_split_indices__solver_residue_rollup :
  forall (A : Type) (d : A) (m L rest : list A),
  Permutation L (m ++ rest) ->
  exists il, NoDup il /\ Forall (fun i => 0 <= i < Zlength L) il /\
             map (fun i => Znth i L d) il = m.
Proof.
  intros A d m. induction m as [| a m IH]; intros L rest Hp.
  - exists nil. simpl. split; [constructor | split; [constructor | reflexivity]].
  - assert (Ha : In a L).
    { eapply Permutation_in; [apply Permutation_sym; exact Hp |]. simpl; auto. }
    apply in_split in Ha. destruct Ha as [L1 [L2 HL]]. subst L.
    remember (Zlength L1) as i0 eqn:Hi0.
    assert (HZ : Zlength (L1 ++ a :: L2) = i0 + Zlength L2 + 1).
    { rewrite Zlength_app, Zlength_cons. lia. }
    assert (HZ2 : Zlength (L1 ++ L2) = i0 + Zlength L2).
    { rewrite Zlength_app. lia. }
    assert (Hp2 : Permutation (L1 ++ L2) (m ++ rest)).
    { apply (Permutation_cons_inv (a := a)).
      eapply Permutation_trans; [| exact Hp].
      apply Permutation_middle. }
    destruct (IH (L1 ++ L2) rest Hp2) as [il [Hnd [Hrng Hmap]]].
    exists (i0 :: map (fun p => if p <? i0 then p else p + 1) il).
    assert (Hi0nn : 0 <= i0) by (subst i0; apply Zlength_nonneg).
    pose proof (Zlength_nonneg L2) as HL2nn.
    assert (Hshift : forall p, 0 <= p < i0 + Zlength L2 ->
              Znth (if p <? i0 then p else p + 1) (L1 ++ a :: L2) d = Znth p (L1 ++ L2) d).
    { intros p Hpr. destruct (Z.ltb_spec p i0) as [Hlt | Hge].
      - rewrite !Znth_app1__solver_residue_rollup by lia. reflexivity.
      - rewrite !Znth_app2__solver_residue_rollup by lia.
        rewrite <- Hi0. rewrite Znth_cons by lia. f_equal. lia. }
    split; [| split].
    + constructor.
      * intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy _]].
        destruct (Z.ltb_spec y i0); lia.
      * apply NoDup_map_inj__solver_residue_rollup; [| exact Hnd].
        intros x y _ _ Heq. destruct (Z.ltb_spec x i0); destruct (Z.ltb_spec y i0); lia.
    + rewrite HZ. constructor.
      * lia.
      * rewrite Forall_map. rewrite Forall_forall in Hrng |- *.
        intros p Hp'. specialize (Hrng p Hp'). rewrite HZ2 in Hrng.
        destruct (Z.ltb_spec p i0); lia.
    + simpl. rewrite map_map.
      f_equal.
      * rewrite Znth_app2__solver_residue_rollup by lia.
        rewrite <- Hi0. replace (i0 - i0) with 0 by lia. apply Znth0_cons.
      * rewrite <- Hmap. apply map_ext_in.
        intros p Hp'. rewrite Forall_forall in Hrng. specialize (Hrng p Hp').
        rewrite HZ2 in Hrng. apply Hshift. lia.
Qed.
Lemma indices_submultiset_n__solver_residue_rollup :
  forall (A : Type) (d : A) (n : nat) (il : list Z) (L : list A),
  length il = n -> NoDup il -> Forall (fun i => 0 <= i < Zlength L) il ->
  exists rest, Permutation L (map (fun i => Znth i L d) il ++ rest).
Proof.
  intros A d n. induction n as [| n IH]; intros il L Hn Hnd Hrng.
  - destruct il as [| i0 il]; [| simpl in Hn; discriminate].
    exists L. simpl. apply Permutation_refl.
  - destruct il as [| i0 il]; [simpl in Hn; discriminate |].
    simpl in Hn. injection Hn as Hn.
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
    rewrite Forall_cons_iff in Hrng. destruct Hrng as [Hi0 Hrng].
    destruct (split_at_index__solver_residue_rollup A d L i0 Hi0) as [L1 [L2 [HL Hlen]]].
    remember (Znth i0 L d) as a eqn:Ha.
    assert (HZ : Zlength L = i0 + Zlength L2 + 1).
    { rewrite HL at 1. rewrite Zlength_app, Zlength_cons. lia. }
    assert (HZ2 : Zlength (L1 ++ L2) = i0 + Zlength L2).
    { rewrite Zlength_app. lia. }
    assert (Hshift : forall p, 0 <= p < Zlength L -> p <> i0 ->
              Znth (if p <? i0 then p else p - 1) (L1 ++ L2) d = Znth p L d).
    { intros p Hpr Hpne. rewrite HL. destruct (Z.ltb_spec p i0) as [Hlt | Hge].
      - rewrite !Znth_app1__solver_residue_rollup by lia. reflexivity.
      - rewrite !Znth_app2__solver_residue_rollup by lia.
        rewrite Hlen. rewrite Znth_cons by lia. f_equal. lia. }
    assert (Hrng2 : Forall (fun p => 0 <= p < Zlength (L1 ++ L2))
                      (map (fun p => if p <? i0 then p else p - 1) il)).
    { rewrite Forall_map. rewrite Forall_forall in Hrng |- *.
      intros p Hp'. specialize (Hrng p Hp'). rewrite HZ2.
      assert (p <> i0) by (intros Hc; subst; contradiction).
      destruct (Z.ltb_spec p i0); lia. }
    assert (Hnd2 : NoDup (map (fun p => if p <? i0 then p else p - 1) il)).
    { apply NoDup_map_inj__solver_residue_rollup; [| exact Hnd'].
      intros x y Hx Hy Heq.
      assert (x <> i0) by (intros Hc; subst; contradiction).
      assert (y <> i0) by (intros Hc; subst; contradiction).
      destruct (Z.ltb_spec x i0); destruct (Z.ltb_spec y i0); lia. }
    assert (Hn2 : length (map (fun p => if p <? i0 then p else p - 1) il) = n)
      by (rewrite length_map; exact Hn).
    destruct (IH _ (L1 ++ L2) Hn2 Hnd2 Hrng2) as [rest Hperm].
    exists rest.
    assert (Hmapeq : map (fun i => Znth i (L1 ++ L2) d)
                       (map (fun p => if p <? i0 then p else p - 1) il)
                     = map (fun i => Znth i L d) il).
    { rewrite map_map. apply map_ext_in. intros p Hp'.
      rewrite Forall_forall in Hrng. specialize (Hrng p Hp').
      apply Hshift; [lia |]. intros Hc; subst; contradiction. }
    rewrite Hmapeq in Hperm.
    simpl.
    eapply Permutation_trans; [| apply perm_skip; exact Hperm].
    rewrite <- Ha. rewrite HL. apply Permutation_sym, Permutation_middle.
Qed.
Lemma indices_submultiset__solver_residue_rollup :
  forall (A : Type) (d : A) (il : list Z) (L : list A),
  NoDup il -> Forall (fun i => 0 <= i < Zlength L) il ->
  exists rest, Permutation L (map (fun i => Znth i L d) il ++ rest).
Proof.
  intros A d il L. apply (indices_submultiset_n__solver_residue_rollup A d (length il) il L).
  reflexivity.
Qed.
Lemma sweep_set_inhabited__solver_residue_rollup :
  forall (contributions st sb : list Z) (k b c j W n : Z),
  2 <= k -> k <= n -> Zlength sb = n ->
  exists v, SweepSet contributions k b c j st sb W n v.
Proof.
  intros contributions st sb k b c j W n Hk Hkn Hsb.
  assert (Hlen : Zlength (sublist 0 (n - 1 + 1) sb) = n)
    by (rewrite Zlength_sublist0 by lia; lia).
  destruct (ksmallsum_exists__solver_residue_rollup (sublist 0 (n - 1 + 1) sb) k
              ltac:(lia)) as [s Hs].
  exists (s + k * ((Znth (n - 1) st 0 - j) / 5) * W).
  right. exists (n - 1). split; [lia | split; [lia |]].
  exists s. split; [exact Hs | reflexivity].
Qed.
Lemma raisecost_le__solver_residue_rollup : forall b c from target cost,
  RaiseCost b c from target cost -> from <= target.
Proof.
  intros b c from target cost H.
  destruct H as [a [[Ha _] _]]. sets_unfold in Ha.
  destruct Ha as [blogs [comments [Hb [Hc [Ht _]]]]]. lia.
Qed.
Lemma raisecost_closed__solver_residue_rollup : forall b c W from target,
  1 <= b -> 1 <= c -> W = Z.min b (5 * c) -> from <= target ->
  RaiseCost b c from target ((target - from) mod 5 * c + (target - from) / 5 * W).
Proof.
  intros b c W from target Hb Hc HW Hle.
  remember (target - from) as d eqn:Hd.
  assert (Hd0 : 0 <= d) by lia.
  pose proof (Z.mod_pos_bound d 5 ltac:(lia)) as Hr.
  pose proof (Z.div_mod d 5 ltac:(lia)) as Hdm.
  assert (Hq0 : 0 <= d / 5) by (apply Z.div_pos; lia).
  unfold RaiseCost, min_value_of_subset, min_object_of_subset.
  exists (d mod 5 * c + d / 5 * W).
  split; [split |]; [| | reflexivity].
  - sets_unfold.
    destruct (Z.le_ge_cases b (5 * c)) as [Hcase | Hcase].
    + exists (d / 5), (d mod 5).
      rewrite (Z.min_l b (5 * c)) in HW by lia. subst W.
      repeat split; try lia.
    + exists 0, d.
      rewrite (Z.min_r b (5 * c)) in HW by lia. subst W.
      repeat split; try lia.
  - intros v Hv. sets_unfold in Hv.
    destruct Hv as [blogs [comments [Hbl [Hcm [Ht Hveq]]]]].
    assert (HW1 : W <= b) by (subst W; apply Z.le_min_l).
    assert (HW2 : W <= 5 * c) by (subst W; apply Z.le_min_r).
    assert (HW0 : 1 <= W) by (subst W; lia).
    assert (Hbq : blogs <= d / 5) by lia.
    assert (H1 : blogs * W <= blogs * b) by nia.
    assert (H2 : (d / 5 - blogs) * W <= (d / 5 - blogs) * (5 * c)) by nia.
    nia.
Qed.
Lemma raisecost_det__solver_residue_rollup : forall b c W from target cost,
  1 <= b -> 1 <= c -> W = Z.min b (5 * c) ->
  RaiseCost b c from target cost ->
  cost = (target - from) mod 5 * c + (target - from) / 5 * W.
Proof.
  intros b c W from target cost Hb Hc HW H.
  pose proof (raisecost_le__solver_residue_rollup _ _ _ _ _ H) as Hle.
  pose proof (raisecost_closed__solver_residue_rollup b c W from target Hb Hc HW Hle) as H2.
  unfold RaiseCost in *.
  eapply min_unique; [apply Zle_TotalOrder | exact H | exact H2].
Qed.
Lemma targetpoint_mod__solver_residue_rollup : forall s j,
  0 <= j < 5 -> (TargetPoint s j - j) mod 5 = 0.
Proof.
  intros s j Hj. unfold TargetPoint.
  pose proof (Z.div_mod (j - s) 5 ltac:(lia)) as H.
  replace (s + (j - s) mod 5 - j) with (0 + (- ((j - s) / 5)) * 5) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma targetpoint_ge__solver_residue_rollup : forall s j,
  0 <= j < 5 -> s <= TargetPoint s j < s + 5.
Proof.
  intros s j Hj. unfold TargetPoint.
  pose proof (Z.mod_pos_bound (j - s) 5 ltac:(lia)). lia.
Qed.
Lemma targetpoint_le__solver_residue_rollup : forall s j t,
  0 <= j < 5 -> (t - j) mod 5 = 0 -> s <= t -> TargetPoint s j <= t.
Proof.
  intros s j t Hj Ht Hs.
  pose proof (targetpoint_mod__solver_residue_rollup s j Hj) as Hp.
  pose proof (targetpoint_ge__solver_residue_rollup s j Hj) as Hr.
  destruct (Z_le_gt_dec (TargetPoint s j) t) as [| Hgt]; [assumption |].
  exfalso.
  pose proof (Z.div_mod (TargetPoint s j - j) 5 ltac:(lia)) as H1.
  pose proof (Z.div_mod (t - j) 5 ltac:(lia)) as H2.
  rewrite Hp in H1. rewrite Ht in H2.
  remember ((TargetPoint s j - j) / 5) as B.
  remember ((t - j) / 5) as A.
  assert (5 * B - 5 * A = TargetPoint s j - t) by lia.
  assert (0 < TargetPoint s j - t < 5) by lia.
  lia.
Qed.
Lemma cost_decomp__solver_residue_rollup : forall s j t W c,
  0 <= j < 5 -> (t - j) mod 5 = 0 -> s <= t ->
  (t - s) mod 5 * c + (t - s) / 5 * W = NormalizedBase s j W c + (t - j) / 5 * W.
Proof.
  intros s j t W c Hj Ht Hs.
  pose proof (targetpoint_mod__solver_residue_rollup s j Hj) as Hp.
  pose proof (targetpoint_ge__solver_residue_rollup s j Hj) as Hr.
  pose proof (Z.div_mod (TargetPoint s j - j) 5 ltac:(lia)) as H1.
  pose proof (Z.div_mod (t - j) 5 ltac:(lia)) as H2.
  rewrite Hp in H1. rewrite Ht in H2.
  unfold NormalizedBase.
  remember ((TargetPoint s j - j) / 5) as B eqn:HB.
  remember ((t - j) / 5) as A eqn:HA.
  remember ((j - s) mod 5) as r eqn:Hrr.
  assert (Hpr : TargetPoint s j = s + r) by (unfold TargetPoint; lia).
  assert (Hr5 : 0 <= r < 5) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Hts : t - s = r + (A - B) * 5) by lia.
  rewrite Hts.
  rewrite Z.mod_add by lia. rewrite Z.div_add by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia.
  nia.
Qed.
Lemma Zlength_combine__solver_residue_rollup : forall (A B : Type) (l1 : list A) (l2 : list B),
  Zlength l2 = Zlength l1 -> Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros A B l1 l2 H. rewrite !Zlength_correct in *.
  rewrite length_combine. lia.
Qed.
Lemma Znth_combine__solver_residue_rollup :
  forall (A B : Type) (l1 : list A) (l2 : list B) (d1 : A) (d2 : B) (p : Z),
  Zlength l2 = Zlength l1 -> 0 <= p < Zlength l1 ->
  Znth p (combine l1 l2) (d1, d2) = (Znth p l1 d1, Znth p l2 d2).
Proof.
  intros A B l1 l2 d1 d2 p Hlen Hp.
  unfold Znth. rewrite !Zlength_correct in *.
  apply combine_nth. lia.
Qed.
Lemma map_fst_combine__solver_residue_rollup : forall (A B : Type) (l1 : list A) (l2 : list B),
  Zlength l2 = Zlength l1 -> map fst (combine l1 l2) = l1.
Proof.
  intros A B l1. induction l1 as [| a l1 IH]; intros l2 H; simpl; [reflexivity |].
  destruct l2 as [| b l2].
  - rewrite Zlength_nil, Zlength_cons in H. pose proof (Zlength_nonneg l1). lia.
  - simpl. f_equal. apply IH. rewrite !Zlength_cons in H. lia.
Qed.
Lemma map_snd_combine__solver_residue_rollup : forall (A B : Type) (l1 : list A) (l2 : list B),
  Zlength l2 = Zlength l1 -> map snd (combine l1 l2) = l2.
Proof.
  intros A B l1. induction l1 as [| a l1 IH]; intros l2 H; simpl.
  - destruct l2 as [| b l2]; [reflexivity |].
    rewrite Zlength_nil, Zlength_cons in H. pose proof (Zlength_nonneg l2). lia.
  - destruct l2 as [| b l2].
    + rewrite Zlength_nil, Zlength_cons in H. pose proof (Zlength_nonneg l1). lia.
    + simpl. f_equal. apply IH. rewrite !Zlength_cons in H. lia.
Qed.
Lemma zsum_add_const__solver_residue_rollup : forall (A : Type) (f : A -> Z) (K : Z) (l : list A),
  ZSum (map (fun x => f x + K) l) = ZSum (map f l) + Zlength l * K.
Proof.
  intros A f K l. induction l as [| a l IH]; unfold ZSum in *; simpl; [lia |].
  rewrite Zlength_cons. lia.
Qed.
Lemma Zlength_map__solver_residue_rollup : forall (A B : Type) (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__solver_residue_rollup :
  forall (A B : Type) (f : A -> B) (l : list A) (q : Z) (da : A) (db : B),
  0 <= q < Zlength l -> Znth q (map f l) db = f (Znth q l da).
Proof.
  intros A B f l q da db H. unfold Znth. rewrite Zlength_correct in H.
  rewrite (nth_indep (map f l) db (f da)) by (rewrite length_map; lia).
  apply map_nth.
Qed.
Lemma st_mod__solver_residue_rollup :
  forall (sh ct cb st sb : list Z) (n j W c p : Z),
  0 <= j < 5 -> Zlength ct = n -> Zlength cb = n -> Zlength st = n -> Zlength sb = n ->
  CandPrefix sh j W c n ct cb -> ZipPerm ct cb st sb ->
  0 <= p < n ->
  (Znth p st 0 - j) mod 5 = 0.
Proof.
  intros sh ct cb st sb n j W c p Hj Hct Hcb Hst Hsb Hcand Hzip Hp.
  destruct Hzip as [_ [_ [_ Hperm]]].
  assert (Hfst : Permutation ct st).
  { rewrite <- (map_fst_combine__solver_residue_rollup Z Z ct cb) by lia.
    rewrite <- (map_fst_combine__solver_residue_rollup Z Z st sb) by lia.
    apply Permutation_map. exact Hperm. }
  assert (Hin : In (Znth p st 0) st).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Hst. lia. }
  assert (Hin2 : In (Znth p st 0) ct)
    by (eapply Permutation_in; [apply Permutation_sym; exact Hfst | exact Hin]).
  apply In_nth with (d := 0) in Hin2.
  destruct Hin2 as [q [Hq Hnq]].
  assert (Hq' : 0 <= Z.of_nat q < n) by (rewrite Zlength_correct in Hct; lia).
  destruct (Hcand (Z.of_nat q) Hq') as [Hcq _].
  assert (Znth (Z.of_nat q) ct 0 = Znth p st 0)
    by (unfold Znth; rewrite Nat2Z.id; exact Hnq).
  rewrite Hcq in H.
  rewrite <- H. apply targetpoint_mod__solver_residue_rollup. exact Hj.
Qed.
Lemma sweep_value_is_tie__solver_residue_rollup :
  forall (contributions sh ct cb st sb : list Z) (n k b c j W i' v : Z),
  n = Zlength contributions -> 2 <= k -> k <= n ->
  1 <= b -> 1 <= c -> W = WCost b c -> 0 <= j < 5 ->
  Zlength sh = n -> Zlength ct = n -> Zlength cb = n ->
  Zlength st = n -> Zlength sb = n ->
  ShiftedPrefix contributions sh n ->
  CandPrefix sh j W c n ct cb ->
  ZipPerm ct cb st sb ->
  Nondecreasing st ->
  k - 1 <= i' -> i' < n ->
  SweepValue st sb k j W i' v ->
  TieCostAtResidue contributions k b c j v.
Proof.
  intros contributions sh ct cb st sb n k b c j W i' v
         Hn Hk2 Hkn Hb Hc HW Hj Hshl Hctl Hcbl Hstl Hsbl Hshift Hcand Hzip Hnd Hi1 Hi2 Hsv.
  assert (HWm : W = Z.min b (5 * c)) by (subst W; unfold WCost; reflexivity).
  assert (Hi0 : 0 <= i') by lia.
  destruct Hsv as [s [Hks Hv]].
  destruct Hks as [m [[Hsub _] [Hmlen Hs]]].
  destruct Hsub as [rest0 Hperm0].
  assert (Hsl : Zlength (sublist 0 (i' + 1) sb) = i' + 1)
    by (rewrite Zlength_sublist0 by lia; lia).
  destruct (perm_split_indices__solver_residue_rollup Z 0 m (sublist 0 (i' + 1) sb) rest0 Hperm0)
    as [il [Hilnd [Hilrng Hilmap]]].
  rewrite Hsl in Hilrng.
  assert (Hilmap2 : map (fun p => Znth p sb 0) il = m).
  { rewrite <- Hilmap. apply map_ext_in. intros p Hp.
    rewrite Forall_forall in Hilrng. specialize (Hilrng p Hp).
    rewrite Znth_sublist0 by lia. reflexivity. }
  assert (Hillen : Zlength il = k).
  { rewrite <- Hmlen, <- Hilmap2, Zlength_map__solver_residue_rollup. reflexivity. }
  remember (map (fun p => (Znth p st 0, Znth p sb 0)) il) as mp eqn:Hmp.
  assert (HP1len : Zlength (combine st sb) = n)
    by (rewrite Zlength_combine__solver_residue_rollup by lia; lia).
  assert (HP0len : Zlength (combine ct cb) = n)
    by (rewrite Zlength_combine__solver_residue_rollup by lia; lia).
  assert (Hilrng2 : Forall (fun p => 0 <= p < Zlength (combine st sb)) il).
  { rewrite HP1len. rewrite Forall_forall in Hilrng |- *. intros p Hp.
    specialize (Hilrng p Hp). lia. }
  destruct (indices_submultiset__solver_residue_rollup (Z * Z) (0, 0) il (combine st sb)
              Hilnd Hilrng2) as [rest1 Hperm1].
  assert (Hmpeq : map (fun p => Znth p (combine st sb) (0, 0)) il = mp).
  { rewrite Hmp. apply map_ext_in. intros p Hp.
    rewrite Forall_forall in Hilrng2. specialize (Hilrng2 p Hp).
    apply Znth_combine__solver_residue_rollup; lia. }
  rewrite Hmpeq in Hperm1.
  pose proof Hzip as HzipC.
  destruct HzipC as [Hzl1 [Hzl2 [Hzl3 Hzperm]]].
  assert (Hperm2 : Permutation (combine ct cb) (mp ++ rest1))
    by (eapply Permutation_trans; [exact Hzperm | exact Hperm1]).
  destruct (perm_split_indices__solver_residue_rollup (Z * Z) (0, 0) mp (combine ct cb) rest1 Hperm2)
    as [chosen [Hcnd [Hcrng Hcmap]]].
  rewrite HP0len in Hcrng.
  assert (Hmplen : Zlength mp = k) by (rewrite Hmp, Zlength_map__solver_residue_rollup; exact Hillen).
  assert (Hclen : Zlength chosen = k)
    by (rewrite <- Hmplen, <- Hcmap, Zlength_map__solver_residue_rollup; reflexivity).
  remember (Znth i' st 0) as t eqn:Ht.
  assert (Ht5 : (t - j) mod 5 = 0).
  { rewrite Ht.
    apply (st_mod__solver_residue_rollup sh ct cb st sb n j W c i'); auto; lia. }
  remember ((t - j) / 5 * W) as Kw eqn:HKw.
  exists chosen, (map (fun pr => snd pr + Kw) mp), (t - 2000000000).
  assert (Hpair : forall q, 0 <= q < k ->
            (Znth (Znth q chosen 0) ct 0, Znth (Znth q chosen 0) cb 0) = Znth q mp (0, 0)).
  { intros q Hq.
    rewrite <- Hcmap.
    rewrite (Znth_map__solver_residue_rollup Z (Z * Z) _ chosen q 0 (0, 0)) by lia.
    rewrite Forall_forall in Hcrng.
    assert (Hin : In (Znth q chosen 0) chosen).
    { unfold Znth. apply nth_In. rewrite Zlength_correct in Hclen. lia. }
    specialize (Hcrng _ Hin).
    rewrite Znth_combine__solver_residue_rollup by lia. reflexivity. }
  assert (Hilq : forall q, 0 <= q < k -> 0 <= Znth q il 0 <= i').
  { intros q Hq. rewrite Forall_forall in Hilrng.
    assert (Hin : In (Znth q il 0) il).
    { unfold Znth. apply nth_In. rewrite Zlength_correct in Hillen. lia. }
    specialize (Hilrng _ Hin). lia. }
  assert (Hmpq : forall q, 0 <= q < k ->
            Znth q mp (0, 0) = (Znth (Znth q il 0) st 0, Znth (Znth q il 0) sb 0)).
  { intros q Hq. rewrite Hmp.
    apply (Znth_map__solver_residue_rollup Z (Z * Z)
             (fun p => (Znth p st 0, Znth p sb 0)) il q 0 (0, 0)). lia. }
  split; [| split; [| split; [| split]]].
  - pose proof (Z.div_mod (t - j) 5 ltac:(lia)) as Hdm. rewrite Ht5 in Hdm.
    replace (t - 2000000000) with (j + ((t - j) / 5 - 400000000) * 5) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - split; [exact Hclen | split; [exact Hcnd |]].
    rewrite Forall_forall in Hcrng |- *. intros x Hx. specialize (Hcrng x Hx). lia.
  - rewrite Zlength_map__solver_residue_rollup. exact Hmplen.
  - intros q Hq.
    remember (Znth q chosen 0) as idx eqn:Hidx.
    remember (Znth q il 0) as p eqn:Hp.
    specialize (Hpair q Hq). specialize (Hmpq q Hq). specialize (Hilq q Hq).
    rewrite <- Hidx in Hpair. rewrite <- Hp in Hmpq, Hilq.
    rewrite Hmpq in Hpair.
    injection Hpair as Hct_eq Hcb_eq.
    assert (Hidxrng : 0 <= idx < n).
    { rewrite Forall_forall in Hcrng. rewrite Hidx. apply Hcrng.
      unfold Znth. apply nth_In. rewrite Zlength_correct in Hclen. lia. }
    destruct (Hcand idx ltac:(lia)) as [Hctidx Hcbidx].
    assert (Hshidx : Znth idx sh 0 = Znth idx contributions 0 + 2000000000)
      by (apply Hshift; lia).
    assert (Hstp : Znth p st 0 <= t).
    { rewrite Ht. apply Hnd; lia. }
    assert (Hsle : Znth idx sh 0 <= t).
    { pose proof (targetpoint_ge__solver_residue_rollup (Znth idx sh 0) j Hj).
      rewrite <- Hctidx in *. lia. }
    assert (Hcost : Znth q (map (fun pr => snd pr + Kw) mp) 0 = Znth idx cb 0 + Kw).
    { rewrite (Znth_map__solver_residue_rollup (Z * Z) Z _ mp q (0, 0) 0) by lia.
      rewrite Hmpq. simpl. lia. }
    rewrite Hcost.
    assert (Heq : Znth idx cb 0 + Kw =
      (t - 2000000000 - Znth idx contributions 0) mod 5 * c +
      (t - 2000000000 - Znth idx contributions 0) / 5 * W).
    { replace (t - 2000000000 - Znth idx contributions 0) with (t - Znth idx sh 0) by lia.
      rewrite Hcbidx, HKw.
      symmetry. apply cost_decomp__solver_residue_rollup; auto. }
    rewrite Heq.
    apply raisecost_closed__solver_residue_rollup; auto; lia.
  - rewrite Hv, Hs, <- Hilmap2.
    replace (fold_right Z.add 0 (map (fun pr : Z * Z => snd pr + Kw) mp))
      with (ZSum (map (fun pr : Z * Z => snd pr + Kw) mp)) by reflexivity.
    rewrite (zsum_add_const__solver_residue_rollup (Z * Z) snd Kw mp).
    rewrite Hmplen.
    assert (Hsnd : map snd mp = map (fun p => Znth p sb 0) il)
      by (rewrite Hmp, map_map; reflexivity).
    rewrite Hsnd, HKw. ring.
Qed.
Lemma mul3_mono__solver_residue_rollup : forall k X Y W,
  0 <= k -> 0 <= W -> X <= Y -> k * X * W <= k * Y * W.
Proof.
  intros k X Y W Hk HW Hxy.
  assert (H2 : 0 <= k * (Y - X)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (H3 : 0 <= k * (Y - X) * W) by (apply Z.mul_nonneg_nonneg; lia).
  nia.
Qed.
Lemma In_Znth__solver_residue_rollup : forall (l : list Z) (x : Z),
  In x l -> exists q, 0 <= q < Zlength l /\ Znth q l 0 = x.
Proof.
  intros l x H. apply In_nth with (d := 0) in H. destruct H as [q [Hq Hnq]].
  exists (Z.of_nat q). rewrite Zlength_correct. split; [lia |].
  unfold Znth. rewrite Nat2Z.id. exact Hnq.
Qed.
Lemma Znth_In__solver_residue_rollup : forall (l : list Z) (q : Z),
  0 <= q < Zlength l -> In (Znth q l 0) l.
Proof.
  intros l q H. unfold Znth. apply nth_In. rewrite Zlength_correct in H. lia.
Qed.
Lemma nodup_range_length__solver_residue_rollup : forall (il : list Z) (M : Z),
  0 <= M -> NoDup il -> Forall (fun p => 0 <= p < M) il -> Zlength il <= M.
Proof.
  intros il M HM Hnd Hrng.
  assert (Hincl : incl il (map Z.of_nat (seq 0 (Z.to_nat M)))).
  { intros x Hx. rewrite Forall_forall in Hrng. specialize (Hrng x Hx).
    apply in_map_iff. exists (Z.to_nat x). split; [lia |].
    apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite length_map, length_seq in Hle.
  rewrite Zlength_correct. lia.
Qed.
Lemma div5_mono__solver_residue_rollup : forall x y j,
  (x - j) mod 5 = 0 -> (y - j) mod 5 = 0 -> x <= y -> (x - j) / 5 <= (y - j) / 5.
Proof.
  intros x y j Hx Hy Hle.
  pose proof (Z.div_mod (x - j) 5 ltac:(lia)) as H1. rewrite Hx in H1.
  pose proof (Z.div_mod (y - j) 5 ltac:(lia)) as H2. rewrite Hy in H2.
  lia.
Qed.
Lemma list_eq_Znth__solver_residue_rollup : forall (l1 l2 : list Z),
  Zlength l1 = Zlength l2 ->
  (forall q, 0 <= q < Zlength l1 -> Znth q l1 0 = Znth q l2 0) ->
  l1 = l2.
Proof.
  intros l1 l2 Hlen H.
  apply (nth_ext l1 l2 0 0); [rewrite !Zlength_correct in Hlen; lia |].
  intros q Hq. specialize (H (Z.of_nat q)).
  rewrite Zlength_correct in H. unfold Znth in H. rewrite Nat2Z.id in H.
  apply H. lia.
Qed.
Lemma tie_ge_sweep__solver_residue_rollup :
  forall (contributions sh ct cb st sb : list Z) (n k b c j W v : Z),
  n = Zlength contributions -> 2 <= k -> k <= n ->
  1 <= b -> 1 <= c -> W = WCost b c -> 0 <= j < 5 ->
  Zlength sh = n -> Zlength ct = n -> Zlength cb = n ->
  Zlength st = n -> Zlength sb = n ->
  ShiftedPrefix contributions sh n ->
  CandPrefix sh j W c n ct cb ->
  ZipPerm ct cb st sb ->
  Nondecreasing st ->
  TieCostAtResidue contributions k b c j v ->
  exists i' w, k - 1 <= i' /\ i' < n /\ SweepValue st sb k j W i' w /\ w <= v.
Proof.
  intros contributions sh ct cb st sb n k b c j W v
         Hn Hk2 Hkn Hb Hc HW Hj Hshl Hctl Hcbl Hstl Hsbl Hshift Hcand Hzip Hmono Htie.
  assert (HWm : W = Z.min b (5 * c)) by (subst W; unfold WCost; reflexivity).
  assert (HW1 : 1 <= W) by (rewrite HWm; lia).
  destruct Htie as [chosen [costs [tau [Htau [Hcho [Hcostlen [Hcost Hv]]]]]]].
  destruct Hcho as [Hchlen [Hchnd Hchrng]].
  rewrite <- Hn in Hchrng.
  remember (tau + 2000000000) as t eqn:Ht.
  assert (Ht5 : (t - j) mod 5 = 0).
  { pose proof (Z.div_mod tau 5 ltac:(lia)) as Hdm. rewrite Htau in Hdm.
    replace (t - j) with (0 + (tau / 5 + 400000000) * 5) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  remember ((t - j) / 5 * W) as Kw eqn:HKw.
  pose proof Hzip as HzipC.
  destruct HzipC as [Hzl1 [Hzl2 [Hzl3 Hzperm]]].
  assert (HP0len : Zlength (combine ct cb) = n)
    by (rewrite Zlength_combine__solver_residue_rollup by lia; lia).
  assert (HP1len : Zlength (combine st sb) = n)
    by (rewrite Zlength_combine__solver_residue_rollup by lia; lia).
  remember (map (fun q => Znth q (combine ct cb) (0, 0)) chosen) as mp eqn:Hmp.
  assert (Hchrng' : Forall (fun q => 0 <= q < Zlength (combine ct cb)) chosen)
    by (rewrite HP0len; exact Hchrng).
  destruct (indices_submultiset__solver_residue_rollup (Z * Z) (0, 0) chosen (combine ct cb)
              Hchnd Hchrng') as [rest Hperm0].
  rewrite <- Hmp in Hperm0.
  assert (Hperm1 : Permutation (combine st sb) (mp ++ rest))
    by (eapply Permutation_trans; [apply Permutation_sym; exact Hzperm | exact Hperm0]).
  destruct (perm_split_indices__solver_residue_rollup (Z * Z) (0, 0) mp (combine st sb) rest Hperm1)
    as [il [Hilnd [Hilrng Hilmap]]].
  rewrite HP1len in Hilrng.
  assert (Hmplen : Zlength mp = k)
    by (rewrite Hmp, Zlength_map__solver_residue_rollup; exact Hchlen).
  assert (Hillen : Zlength il = k)
    by (rewrite <- Hmplen, <- Hilmap, Zlength_map__solver_residue_rollup; reflexivity).
  (* pointwise descriptions *)
  assert (Hmpch : forall q, 0 <= q < k ->
            Znth q mp (0, 0) = (Znth (Znth q chosen 0) ct 0, Znth (Znth q chosen 0) cb 0)).
  { intros q Hq. rewrite Hmp.
    rewrite (Znth_map__solver_residue_rollup Z (Z * Z)
               (fun q0 => Znth q0 (combine ct cb) (0, 0)) chosen q 0 (0, 0)) by lia.
    rewrite Forall_forall in Hchrng.
    specialize (Hchrng _ (Znth_In__solver_residue_rollup chosen q ltac:(lia))).
    apply Znth_combine__solver_residue_rollup; lia. }
  assert (Hmpil : forall q, 0 <= q < k ->
            Znth q mp (0, 0) = (Znth (Znth q il 0) st 0, Znth (Znth q il 0) sb 0)).
  { intros q Hq. rewrite <- Hilmap.
    rewrite (Znth_map__solver_residue_rollup Z (Z * Z)
               (fun q0 => Znth q0 (combine st sb) (0, 0)) il q 0 (0, 0))
      by (rewrite Hillen; lia).
    rewrite Forall_forall in Hilrng.
    specialize (Hilrng _ (Znth_In__solver_residue_rollup il q ltac:(lia))).
    apply Znth_combine__solver_residue_rollup; lia. }
  (* each chosen blogger's target point is at most t *)
  assert (Hctle : forall q, 0 <= q < k -> Znth (Znth q chosen 0) ct 0 <= t).
  { intros q Hq.
    remember (Znth q chosen 0) as idx eqn:Hidx.
    assert (Hidxr : 0 <= idx < n).
    { rewrite Forall_forall in Hchrng. rewrite Hidx.
      apply Hchrng, Znth_In__solver_residue_rollup. lia. }
    specialize (Hcost q Hq). rewrite <- Hidx in Hcost.
    pose proof (raisecost_le__solver_residue_rollup _ _ _ _ _ Hcost) as Hle.
    destruct (Hcand idx ltac:(lia)) as [Hctidx _].
    assert (Hshidx : Znth idx sh 0 = Znth idx contributions 0 + 2000000000)
      by (apply Hshift; lia).
    rewrite Hctidx. apply targetpoint_le__solver_residue_rollup; auto; lia. }
  assert (Hstle : forall q, 0 <= q < k -> Znth (Znth q il 0) st 0 <= t).
  { intros q Hq. pose proof (Hmpch q Hq) as H1. pose proof (Hmpil q Hq) as H2.
    rewrite H1 in H2. injection H2 as H3 H4. rewrite <- H3. apply Hctle. lia. }
  (* i' is the largest index used *)
  assert (Hexmax : exists p, 0 <= p <= n - 1 /\ In p il).
  { exists (Znth 0 il 0). split.
    - rewrite Forall_forall in Hilrng.
      specialize (Hilrng _ (Znth_In__solver_residue_rollup il 0 ltac:(lia))). lia.
    - apply Znth_In__solver_residue_rollup. lia. }
  destruct (max_n_in_range (fun p => In p il) (n - 1) ltac:(lia) Hexmax)
    as [i' [Hini' [Hi'r Hi'max]]].
  assert (Hallle : forall p, In p il -> p <= i').
  { intros p Hp. rewrite Forall_forall in Hilrng. specialize (Hilrng p Hp).
    apply Hi'max; [lia | exact Hp]. }
  assert (Hi'k : k - 1 <= i').
  { assert (Hsub : Forall (fun p => 0 <= p < i' + 1) il).
    { rewrite Forall_forall. intros p Hp. rewrite Forall_forall in Hilrng.
      specialize (Hilrng p Hp). pose proof (Hallle p Hp). lia. }
    pose proof (nodup_range_length__solver_residue_rollup il (i' + 1) ltac:(lia) Hilnd Hsub).
    lia. }
  assert (Hsti' : Znth i' st 0 <= t).
  { destruct (In_Znth__solver_residue_rollup il i' Hini') as [q [Hq Hqe]].
    rewrite <- Hqe. apply Hstle. lia. }
  (* the sb values at the indices il sit inside the prefix *)
  assert (Hsublen : Zlength (sublist 0 (i' + 1) sb) = i' + 1)
    by (rewrite Zlength_sublist0 by lia; lia).
  assert (Hilrng3 : Forall (fun p => 0 <= p < Zlength (sublist 0 (i' + 1) sb)) il).
  { rewrite Hsublen, Forall_forall. intros p Hp. rewrite Forall_forall in Hilrng.
    specialize (Hilrng p Hp). pose proof (Hallle p Hp). lia. }
  destruct (indices_submultiset__solver_residue_rollup Z 0 il (sublist 0 (i' + 1) sb)
              Hilnd Hilrng3) as [rest2 Hperm2].
  assert (Hmapsb : map (fun p => Znth p (sublist 0 (i' + 1) sb) 0) il
                   = map (fun p => Znth p sb 0) il).
  { apply map_ext_in. intros p Hp. rewrite Forall_forall in Hilrng3.
    specialize (Hilrng3 p Hp). rewrite Hsublen in Hilrng3.
    apply Znth_sublist0. lia. }
  rewrite Hmapsb in Hperm2.
  (* the k smallest sum in the prefix *)
  destruct (min_submultiset_exists__solver_residue_rollup (sublist 0 (i' + 1) sb) k
              ltac:(lia)) as [mm [Hmm Hmmlen]].
  exists i', (ZSum mm + k * ((Znth i' st 0 - j) / 5) * W).
  split; [exact Hi'k | split; [lia | split]].
  - exists (ZSum mm). split; [| reflexivity].
    exists mm. split; [exact Hmm | split; [exact Hmmlen | reflexivity]].
  - (* w <= v *)
    assert (Hsndmp : map snd mp = map (fun p => Znth p sb 0) il).
    { apply (list_eq_Znth__solver_residue_rollup).
      - rewrite !Zlength_map__solver_residue_rollup. lia.
      - intros q Hq. rewrite Zlength_map__solver_residue_rollup in Hq.
        rewrite (Znth_map__solver_residue_rollup (Z * Z) Z snd mp q (0, 0) 0) by lia.
        rewrite (Znth_map__solver_residue_rollup Z Z (fun p => Znth p sb 0) il q 0 0)
          by (rewrite Hillen; lia).
        rewrite Hmpil by lia. reflexivity. }
    assert (Hmin : ZSum mm <= ZSum (map snd mp)).
    { destruct Hmm as [_ Hminp]. rewrite Hsndmp.
      apply Hminp.
      - exists rest2. exact Hperm2.
      - rewrite Zlength_map__solver_residue_rollup, Hillen, Hmmlen. reflexivity. }
    assert (Hcostseq : costs = map (fun pr : Z * Z => snd pr + Kw) mp).
    { apply list_eq_Znth__solver_residue_rollup.
      - rewrite Zlength_map__solver_residue_rollup. lia.
      - intros q Hq. rewrite Hcostlen in Hq.
        rewrite (Znth_map__solver_residue_rollup (Z * Z) Z
                   (fun pr : Z * Z => snd pr + Kw) mp q (0, 0) 0) by lia.
        rewrite Hmpch by lia. simpl.
        remember (Znth q chosen 0) as idx eqn:Hidx.
        assert (Hidxr : 0 <= idx < n).
        { rewrite Forall_forall in Hchrng. rewrite Hidx.
          apply Hchrng, Znth_In__solver_residue_rollup. lia. }
        specialize (Hcost q ltac:(lia)). rewrite <- Hidx in Hcost.
        pose proof (raisecost_det__solver_residue_rollup b c W
                      (Znth idx contributions 0) tau (Znth q costs 0) Hb Hc HWm Hcost) as Hdet.
        destruct (Hcand idx ltac:(lia)) as [Hctidx Hcbidx].
        assert (Hshidx : Znth idx sh 0 = Znth idx contributions 0 + 2000000000)
          by (apply Hshift; lia).
        assert (Hsle : Znth idx sh 0 <= t).
        { pose proof (Hctle q ltac:(lia)) as Hq2. rewrite <- Hidx in Hq2.
          rewrite Hctidx in Hq2.
          pose proof (targetpoint_ge__solver_residue_rollup (Znth idx sh 0) j Hj). lia. }
        rewrite Hdet.
        replace (tau - Znth idx contributions 0) with (t - Znth idx sh 0) by lia.
        rewrite (cost_decomp__solver_residue_rollup (Znth idx sh 0) j t W c Hj Ht5 Hsle).
        rewrite Hcbidx, HKw. reflexivity. }
    rewrite Hv, Hcostseq.
    replace (fold_right Z.add 0 (map (fun pr : Z * Z => snd pr + Kw) mp))
      with (ZSum (map (fun pr : Z * Z => snd pr + Kw) mp)) by reflexivity.
    rewrite (zsum_add_const__solver_residue_rollup (Z * Z) snd Kw mp), Hmplen.
    assert (Hdiv : (Znth i' st 0 - j) / 5 <= (t - j) / 5).
    { apply div5_mono__solver_residue_rollup with (j := j); auto.
      apply (st_mod__solver_residue_rollup sh ct cb st sb n j W c i'); auto; lia. }
    rewrite HKw.
    pose proof (mul3_mono__solver_residue_rollup k ((Znth i' st 0 - j) / 5)
                  ((t - j) / 5) W ltac:(lia) ltac:(lia) Hdiv) as Hmul.
    nia.
Qed.
Lemma residue_best_of_sweep_best__solver_residue_rollup :
  forall (contributions sh ct cb st sb : list Z) (n k b c j W best : Z),
  n = Zlength contributions -> 2 <= k -> k <= n ->
  1 <= b -> 1 <= c -> W = WCost b c -> 0 <= j < 5 -> 0 <= best ->
  Zlength sh = n -> Zlength ct = n -> Zlength cb = n ->
  Zlength st = n -> Zlength sb = n ->
  ShiftedPrefix contributions sh n ->
  CandPrefix sh j W c n ct cb ->
  ZipPerm ct cb st sb ->
  Nondecreasing st ->
  SweepBest contributions k b c j st sb W n best ->
  ResidueBest contributions k b c (j + 1) best.
Proof.
  intros contributions sh ct cb st sb n k b c j W best
         Hn Hk2 Hkn Hb Hc HW Hj Hbest Hshl Hctl Hcbl Hstl Hsbl Hshift Hcand Hzip Hmono Hsb0.
  assert (KEY1 : forall w, (exists i', k - 1 <= i' /\ i' < n /\ SweepValue st sb k j W i' w) ->
                   TieCostAtResidue contributions k b c j w).
  { intros w [i' [H1 [H2 H3]]].
    apply (sweep_value_is_tie__solver_residue_rollup contributions sh ct cb st sb
             n k b c j W i' w); auto. }
  assert (KEY2 : forall w, TieCostAtResidue contributions k b c j w ->
                   exists u, (exists i', k - 1 <= i' /\ i' < n /\ SweepValue st sb k j W i' u)
                             /\ u <= w).
  { intros w Hw.
    destruct (tie_ge_sweep__solver_residue_rollup contributions sh ct cb st sb
                n k b c j W w Hn Hk2 Hkn Hb Hc HW Hj Hshl Hctl Hcbl Hstl Hsbl
                Hshift Hcand Hzip Hmono Hw) as [i' [u [H1 [H2 [H3 H4]]]]].
    exists u. split; [| exact H4]. exists i'. auto. }
  unfold SweepBest, BestState in Hsb0.
  destruct Hsb0 as [[Hm1 _] | [_ Hmin]]; [lia |].
  destruct Hmin as [a [[Hain Halb] Haeq]].
  sets_unfold in Hain. subst a.
  unfold ResidueBest, BestState.
  right. split; [exact Hbest |].
  exists best. split; [split |]; [| | reflexivity].
  - sets_unfold.
    destruct Hain as [[j' [Hj' Htie]] | Hsw].
    + exists j'. split; [lia | exact Htie].
    + exists j. split; [lia |]. apply KEY1. exact Hsw.
  - intros w Hw. sets_unfold in Hw.
    destruct Hw as [j' [Hj' Htie]].
    destruct (Z_lt_ge_dec j' j) as [Hlt | Hge].
    + apply Halb. sets_unfold. left. exists j'. split; [lia | exact Htie].
    + assert (j' = j) by lia. subst j'.
      destruct (KEY2 w Htie) as [u [Hu Hule]].
      assert (best <= u) by (apply Halb; sets_unfold; right; exact Hu).
      lia.
Qed.
Lemma min_value_of_subset_ext__solver_final_spec :
  forall (X Y : Z -> Prop) (n : Z),
    (forall v, X v <-> Y v) ->
    min_value_of_subset Z.le X (fun x => x) n ->
    min_value_of_subset Z.le Y (fun x => x) n.
Proof.
  intros X Y n Hiff Hmin.
  unfold min_value_of_subset, min_object_of_subset in *.
  destruct Hmin as [a [[Ha Hle] Hfa]].
  exists a.
  split; [split |].
  - apply Hiff. exact Ha.
  - intros b Hb. apply Hle. apply Hiff. exact Hb.
  - exact Hfa.
Qed.
Lemma tie_cost_residue_cover__solver_final_spec :
  forall (values : list Z) (k b c v : Z),
    (exists j', 0 <= j' < 5 /\ TieCostAtResidue values k b c j' v) <->
    TieCost values k b c v.
Proof.
  intros values k b c v.
  split.
  - intros [j' [Hj' Hres]].
    unfold TieCostAtResidue in Hres.
    destruct Hres as [chosen [costs [target [Hmod [Hch [Hlen [Hcost Hsum]]]]]]].
    unfold TieCost.
    exists chosen, costs, target.
    tauto.
  - intros Hty.
    unfold TieCost in Hty.
    destruct Hty as [chosen [costs [target [Hch [Hlen [Hcost Hsum]]]]]].
    exists (target mod 5).
    split.
    + apply Z.mod_pos_bound. lia.
    + unfold TieCostAtResidue.
      exists chosen, costs, target.
      split; [reflexivity |].
      split; [exact Hch |].
      split; [exact Hlen |].
      split; [exact Hcost | exact Hsum].
Qed.
Lemma fold_max_nonneg__solver_final_spec :
  forall (l : list Z), 0 <= fold_right Z.max 0 l.
Proof.
  induction l as [| a l IH]; simpl; [lia |].
  pose proof (Z.le_max_r a (fold_right Z.max 0 l)). lia.
Qed.
Lemma nth_le_fold_max__solver_final_spec :
  forall (l : list Z) (n : nat), nth n l 0 <= fold_right Z.max 0 l.
Proof.
  induction l as [| a l IH]; intros n.
  - destruct n; simpl; lia.
  - destruct n as [| m]; simpl.
    + apply Z.le_max_l.
    + pose proof (IH m).
      pose proof (Z.le_max_r a (fold_right Z.max 0 l)).
      lia.
Qed.
Lemma Znth_le_fold_max__solver_final_spec :
  forall (l : list Z) (i : Z), Znth i l 0 <= fold_right Z.max 0 l.
Proof.
  intros l i. unfold Znth. apply nth_le_fold_max__solver_final_spec.
Qed.
Lemma z_min_exists_nonneg__solver_final_spec :
  forall (X : Z -> Prop),
    (exists v, X v) ->
    (forall v, X v -> 0 <= v) ->
    exists n, min_value_of_subset Z.le X (fun x => x) n.
Proof.
  intros X Hne Hnn.
  pose proof (min_nonempty_exists Z.to_nat X Hne) as [m Hm].
  unfold min_value_of_subset, min_object_of_subset in Hm.
  destruct Hm as [a [[Ha Hle] Hfa]].
  exists a.
  unfold min_value_of_subset, min_object_of_subset.
  exists a.
  split; [split |]; auto.
  intros b Hb.
  simpl.
  apply (proj2 (Z2Nat.inj_le a b (Hnn a Ha) (Hnn b Hb))).
  apply Hle. exact Hb.
Qed.
Lemma raise_cost_exists__solver_final_spec :
  forall (b c from target : Z),
    1 <= b -> 1 <= c -> from <= target ->
    exists cost, RaiseCost b c from target cost.
Proof.
  intros b c from target Hb Hc Hft.
  unfold RaiseCost.
  apply z_min_exists_nonneg__solver_final_spec.
  - exists (0 * b + (target - from) * c).
    exists 0, (target - from).
    repeat split; lia.
  - intros v [blogs [comments [Hbl [Hcm [Heq Hv]]]]].
    subst v. nia.
Qed.
Lemma Znth_map__solver_final_spec :
  forall (f : Z -> Z) (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    Znth i (map f l) 0 = f (Znth i l 0).
Proof.
  intros f l i Hi.
  rewrite Zlength_correct in Hi.
  unfold Znth.
  rewrite (nth_indep (map f l) 0 (f 0)).
  - apply map_nth.
  - rewrite length_map. lia.
Qed.
Lemma nodup_map_of_nat_seq__solver_final_spec :
  forall (n s : nat), NoDup (map Z.of_nat (seq s n)).
Proof.
  induction n as [| n IH]; intros s; simpl.
  - constructor.
  - constructor.
    + intros Hin.
      apply in_map_iff in Hin.
      destruct Hin as [x [Hx Hinx]].
      apply Nat2Z.inj in Hx.
      apply in_seq in Hinx. lia.
    + apply IH.
Qed.
Lemma Zlength_map_of_nat_seq__solver_final_spec :
  forall (n s : nat), Zlength (map Z.of_nat (seq s n)) = Z.of_nat n.
Proof.
  intros n s.
  rewrite Zlength_correct, length_map, length_seq.
  reflexivity.
Qed.
Lemma tie_cost_inhabited__solver_final_spec :
  forall (values : list Z) (k b c : Z),
    1 <= b -> 1 <= c -> 0 <= k -> k <= Zlength values ->
    exists v, TieCost values k b c v.
Proof.
  intros values k b c Hb Hc Hk Hkv.
  pose (target := fold_right Z.max 0 values).
  pose (chosen := map Z.of_nat (seq 0 (Z.to_nat k))).
  pose (g := fun idx : Z =>
               epsilon (inhabits 0)
                 (fun cost => RaiseCost b c (Znth idx values 0) target cost)).
  assert (Hg : forall idx, RaiseCost b c (Znth idx values 0) target (g idx)).
  { intros idx. unfold g. apply epsilon_spec.
    apply raise_cost_exists__solver_final_spec; auto.
    apply Znth_le_fold_max__solver_final_spec. }
  assert (Hlenc : Zlength chosen = k).
  { unfold chosen. rewrite Zlength_map_of_nat_seq__solver_final_spec. lia. }
  exists (fold_right Z.add 0 (map g chosen)).
  unfold TieCost.
  exists chosen, (map g chosen), target.
  split; [| split; [| split]].
  - unfold ChosenBloggers.
    split; [exact Hlenc | split].
    + unfold chosen. apply nodup_map_of_nat_seq__solver_final_spec.
    + apply Forall_forall. intros x Hx.
      unfold chosen in Hx.
      apply in_map_iff in Hx.
      destruct Hx as [m [Hm Hinm]].
      apply in_seq in Hinm.
      subst x. lia.
  - rewrite Zlength_correct, length_map, <- Zlength_correct. exact Hlenc.
  - intros i Hi.
    rewrite Znth_map__solver_final_spec by lia.
    apply Hg.
  - reflexivity.
Qed.
Lemma zsum_cons__solver_hpop_call_pre : forall (a : Z) (l : list Z),
  ZSum (a :: l) = a + ZSum l.
Proof.
  intros a l. unfold ZSum. simpl. reflexivity.
Qed.
Lemma zsum_permutation__solver_hpop_call_pre : forall (l1 l2 : list Z),
  Permutation l1 l2 -> ZSum l1 = ZSum l2.
Proof.
  intros l1 l2 H. unfold ZSum in *.
  induction H; simpl in *; lia.
Qed.
Lemma zsum_range_from_bounds__solver_hpop_call_pre :
  forall (l : list Z) (lo hi : Z),
    Forall (fun x => lo <= x <= hi) l ->
    Zlength l * lo <= ZSum l <= Zlength l * hi.
Proof.
  intros l lo hi H. induction H as [| x l Hx Hl IH].
  - rewrite Zlength_nil. unfold ZSum. simpl. lia.
  - rewrite Zlength_cons, !Z.mul_succ_l.
    rewrite zsum_cons__solver_hpop_call_pre.
    lia.
Qed.
Lemma zsum_range_from_znth__solver_hpop_call_pre :
  forall (l : list Z) (n lo hi : Z),
    0 <= n <= Zlength l ->
    (forall q, 0 <= q < n -> lo <= Znth q l 0 <= hi) ->
    n * lo <= ZSum (sublist 0 n l) <= n * hi.
Proof.
  intros l n lo hi Hn H.
  assert (HF : Forall (fun x : Z => lo <= x <= hi) (sublist 0 n l)).
  { apply (proj2 (Forall_Znth (fun x : Z => lo <= x <= hi) 0 (sublist 0 n l))).
    intros q Hq. cbv beta.
    rewrite (Zlength_sublist0 n l) in Hq by lia.
    rewrite (Znth_sublist0 0 q n l) by lia.
    apply H; lia. }
  pose proof (zsum_range_from_bounds__solver_hpop_call_pre _ _ _ HF) as [Hlo Hhi].
  rewrite (Zlength_sublist0 n l) in Hlo, Hhi by lia.
  lia.
Qed.
