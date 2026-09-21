Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
Require Import MaxMinLib.MaxMin.

Import ListNotations.
Local Open Scope Z_scope.

(** Mathematical area of the container whose endpoints are [i] and [j]. *)
Definition LinearContainerHeight (l : list Z) (i j : Z) : Z :=
  Z.min (Znth i l 0) (Znth j l 0).

Definition LinearContainerArea (l : list Z) (i j : Z) : Z :=
  (j - i) * LinearContainerHeight l i j.

Definition LinearContainerPair (l : list Z) (i j : Z) : Prop :=
  0 <= i /\ i < j /\ j < Zlength l.

(** The exact, implementation-independent optimization problem: [ans] is
    attained by a valid pair and dominates every valid pair. *)
Definition MaximumContainerArea (l : list Z) (ans : Z) : Prop :=
  max_value_of_subset Z.le
    (fun ij : Z * Z => LinearContainerPair l (fst ij) (snd ij))
    (fun ij => LinearContainerArea l (fst ij) (snd ij)) ans.

Lemma MaximumContainerArea_unfold l ans :
  MaximumContainerArea l ans <->
  (exists i j, LinearContainerPair l i j /\ ans = LinearContainerArea l i j) /\
  forall i j, LinearContainerPair l i j -> LinearContainerArea l i j <= ans.
Proof.
  unfold MaximumContainerArea, max_value_of_subset, max_object_of_subset.
  cbn. split.
  - intros [[i j] [[Hp Hmax] Heq]]. cbn in *. split.
    + exists i, j. auto.
    + intros x y Hxy. specialize (Hmax (x,y) Hxy). cbn in Hmax. lia.
  - intros [[i [j [Hp Heq]]] Hmax]. exists (i,j). cbn.
    split; [split; [exact Hp | intros [x y] Hxy; cbn in *; specialize (Hmax x y Hxy); lia] | lia].
Qed.


(** [best] is either the initial zero or the area of an inspected pair. *)
Definition LinearContainerBest (l : list Z) (best : Z) : Prop :=
  best = 0 \/
  exists i j,
    LinearContainerPair l i j /\ best = LinearContainerArea l i j.

Definition LinearContainerRemaining
    (l : list Z) (left right i j : Z) : Prop :=
  LinearContainerPair l i j /\ left <= i /\ j <= right.

(** Every pair discarded by the two-pointer search is already dominated by
    [best], or by a pair that remains in the current closed interval.  This is
    a semantic frontier property, independent of the program's control flow. *)
Definition LinearContainerTwoPointerInvariant
    (l : list Z) (left right best : Z) : Prop :=
  LinearContainerBest l best /\
  forall i j,
    LinearContainerPair l i j ->
    LinearContainerArea l i j <= best \/
    exists p q,
      LinearContainerRemaining l left right p q /\
      LinearContainerArea l i j <= LinearContainerArea l p q.

Lemma linear_container_invariant_update_best__best_update
    (l : list Z) (left right old_best : Z) :
  LinearContainerTwoPointerInvariant l left right old_best ->
  LinearContainerPair l left right ->
  old_best < LinearContainerArea l left right ->
  LinearContainerTwoPointerInvariant
    l left right (LinearContainerArea l left right).
Proof.
  intros [Hold_best Hold_frontier] Hpair Hlarger.
  split.
  - right.
    exists left, right.
    split; [exact Hpair | reflexivity].
  - intros i j Hij.
    specialize (Hold_frontier i j Hij).
    destruct Hold_frontier as
        [Hdominated | [p [q [Hremaining Hdominated]]]].
    + left.
      lia.
    + right.
      exists p, q.
      split; assumption.
Qed.
Lemma linear_container_invariant_advance_left__pointer_transitions
    (l : list Z) (left right best : Z) :
  (forall k, 0 <= k < Zlength l -> 0 <= Znth k l 0) ->
  LinearContainerPair l left right ->
  Znth left l 0 < Znth right l 0 ->
  LinearContainerArea l left right <= best ->
  LinearContainerTwoPointerInvariant l left right best ->
  LinearContainerTwoPointerInvariant l (left + 1) right best.
Proof.
  intros Hnonneg Hcurrent Hheight Hcurrent_best Hinv.
  unfold LinearContainerPair in Hcurrent.
  destruct Hcurrent as [Hleft [Hleft_right Hright]].
  unfold LinearContainerTwoPointerInvariant in Hinv |- *.
  destruct Hinv as [Hbest Hdominated].
  split; [exact Hbest |].
  intros i j Hij.
  destruct (Hdominated i j Hij) as
      [Hij_best | [p [q [Hremaining Hij_pq]]]].
  - left; exact Hij_best.
  - unfold LinearContainerRemaining in Hremaining.
    destruct Hremaining as [Hpq [Hleft_p Hq_right]].
    unfold LinearContainerPair in Hpq.
    destruct Hpq as [Hp [Hp_q Hq]].
    destruct (Z_le_gt_dec (left + 1) p) as [Hleft1_p | Hp_left1].
    + right.
      exists p, q.
      split; [| exact Hij_pq].
      unfold LinearContainerRemaining, LinearContainerPair.
      repeat split; lia.
    + left.
      assert (Hp_eq : p = left) by lia.
      subst p.
      eapply Z.le_trans; [exact Hij_pq |].
      eapply Z.le_trans; [| exact Hcurrent_best].
      unfold LinearContainerArea, LinearContainerHeight.
      assert (Hcurrent_min :
          Z.min (Znth left l 0) (Znth right l 0) = Znth left l 0).
      { apply Z.min_l; lia. }
      rewrite Hcurrent_min.
      assert (Hleft_height : 0 <= Znth left l 0).
      { apply Hnonneg; lia. }
      assert (Hmin : Z.min (Znth left l 0) (Znth q l 0) <=
                     Znth left l 0) by apply Z.le_min_l.
      nia.
Qed.
Lemma linear_container_invariant_retreat_right__pointer_transitions
    (l : list Z) (left right best : Z) :
  (forall k, 0 <= k < Zlength l -> 0 <= Znth k l 0) ->
  LinearContainerPair l left right ->
  Znth left l 0 >= Znth right l 0 ->
  LinearContainerArea l left right <= best ->
  LinearContainerTwoPointerInvariant l left right best ->
  LinearContainerTwoPointerInvariant l left (right - 1) best.
Proof.
  intros Hnonneg Hcurrent Hheight Hcurrent_best Hinv.
  unfold LinearContainerPair in Hcurrent.
  destruct Hcurrent as [Hleft [Hleft_right Hright]].
  unfold LinearContainerTwoPointerInvariant in Hinv |- *.
  destruct Hinv as [Hbest Hdominated].
  split; [exact Hbest |].
  intros i j Hij.
  destruct (Hdominated i j Hij) as
      [Hij_best | [p [q [Hremaining Hij_pq]]]].
  - left; exact Hij_best.
  - unfold LinearContainerRemaining in Hremaining.
    destruct Hremaining as [Hpq [Hleft_p Hq_right]].
    unfold LinearContainerPair in Hpq.
    destruct Hpq as [Hp [Hp_q Hq]].
    destruct (Z_le_gt_dec q (right - 1)) as [Hq_right1 | Hright1_q].
    + right.
      exists p, q.
      split; [| exact Hij_pq].
      unfold LinearContainerRemaining, LinearContainerPair.
      repeat split; lia.
    + left.
      assert (Hq_eq : q = right) by lia.
      subst q.
      eapply Z.le_trans; [exact Hij_pq |].
      eapply Z.le_trans; [| exact Hcurrent_best].
      unfold LinearContainerArea, LinearContainerHeight.
      assert (Hcurrent_min :
          Z.min (Znth left l 0) (Znth right l 0) = Znth right l 0).
      { apply Z.min_r; lia. }
      rewrite Hcurrent_min.
      assert (Hright_height : 0 <= Znth right l 0).
      { apply Hnonneg; lia. }
      assert (Hmin : Z.min (Znth p l 0) (Znth right l 0) <=
                     Znth right l 0) by apply Z.le_min_r.
      nia.
Qed.
Lemma linear_container_closed_invariant_maximum__final_result :
  forall l left right best,
    left = right ->
    2 <= Zlength l ->
    (forall k, 0 <= k < Zlength l -> 0 <= Znth k l 0) ->
    LinearContainerTwoPointerInvariant l left right best ->
    MaximumContainerArea l best.
Proof.
  intros l left right best Hclosed Hlength Hnonnegative Hinv.
  unfold LinearContainerTwoPointerInvariant in Hinv.
  destruct Hinv as [Hbest Hfrontier].
  assert (Hdominates :
    forall i j,
      LinearContainerPair l i j ->
      LinearContainerArea l i j <= best).
  {
    intros i j Hpair.
    specialize (Hfrontier i j Hpair).
    destruct Hfrontier as [Hle | [p [q [Hremaining Hle]]]].
    - exact Hle.
    - unfold LinearContainerRemaining in Hremaining.
      destruct Hremaining as [Hpq [Hleft Hright]].
      unfold LinearContainerPair in Hpq.
      destruct Hpq as [_ [Hpq _]].
      lia.
  }
  apply MaximumContainerArea_unfold.
  split.
  - destruct Hbest as [Hzero | [i [j [Hpair Hattained]]]].
    + exists 0, 1.
      assert (Hpair : LinearContainerPair l 0 1).
      {
        unfold LinearContainerPair.
        lia.
      }
      split.
      * exact Hpair.
      * specialize (Hdominates 0 1 Hpair).
        assert (Harea_nonnegative : 0 <= LinearContainerArea l 0 1).
        {
          unfold LinearContainerArea, LinearContainerHeight.
          replace (1 - 0) with 1 by lia.
          rewrite Z.mul_1_l.
          apply Z.min_glb.
          -- apply Hnonnegative; lia.
          -- apply Hnonnegative; lia.
        }
        lia.
    + exists i, j.
      split; assumption.
  - exact Hdominates.
Qed.
