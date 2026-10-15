Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(stock:list Z)->Z. Output is the maximum total of a
   feasible purchase vector satisfying the statement's ordered condition. *)
Definition FeasiblePurchase (a x : list Z) : Prop :=
  Zlength x = Zlength a /\
  (forall i, 0 <= i < Zlength a -> 0 <= Znth i x 0 <= Znth i a 0) /\
  (forall j i, 0 <= j < i /\ i < Zlength a -> Znth j x 0 = 0 \/ Znth j x 0 < Znth i x 0).
Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 200000 /\ Forall (fun x => 1 <= x <= 1000000000) a.
Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (fun v=>exists x, FeasiblePurchase a x /\ v=(fold_right Z.add 0) x) (fun x => x) out.

(* A dominant purchase is a mathematical upper envelope of all legal purchase
   vectors for the same ordered stock list.  It is independent of the C loop:
   any implementation producing such a vector attains the optimum. *)
Definition DominantPurchase (a x : list Z) : Prop :=
  FeasiblePurchase a x /\
  forall y,
    FeasiblePurchase a y ->
    forall k, 0 <= k < Zlength a -> Znth k y 0 <= Znth k x 0.

(* The loop has already fixed the suffix beginning at [lo].  [total] is its
   sum and [prev] is its leftmost chosen amount (or zero for the empty suffix),
   which is exactly the boundary that constrains the next item to the left. *)
Definition SuffixDominantState
    (a : list Z) (lo total prev : Z) : Prop :=
  exists x,
    DominantPurchase (sublist lo (Zlength a) a) x /\
    total = fold_right Z.add 0 x /\
    (lo = Zlength a -> prev = 0) /\
    (lo < Zlength a -> prev = Znth 0 x 0).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma dominant_purchase_empty__initialization :
  forall a : list Z,
    DominantPurchase (sublist (Zlength a) (Zlength a) a) [].
Proof.
  intros a.
  unfold DominantPurchase, FeasiblePurchase.
  rewrite (Zsublist_nil a (Zlength a) (Zlength a)) by lia.
  split.
  - split.
    + reflexivity.
    + split.
      * intros i Hi. rewrite Zlength_nil in Hi. lia.
      * intros j i Hi. rewrite Zlength_nil in Hi. lia.
  - intros y Hy k Hk. rewrite Zlength_nil in Hk. lia.
Qed.
Lemma sublist_step__backward_transitions :
  forall (a : list Z) i,
    0 <= i < Zlength a ->
    sublist i (Zlength a) a =
      Znth i a 0 :: sublist (i + 1) (Zlength a) a.
Proof.
  intros a i Hi.
  rewrite (sublist_split i (Zlength a) (i + 1) a) by lia.
  assert (Hsingle : sublist i (i + 1) a = [Znth i a 0]).
  { apply sublist_single; lia. }
  rewrite Hsingle.
  reflexivity.
Qed.
Lemma feasible_purchase_cons__backward_transitions :
  forall (cur p : Z) (s x : list Z),
    FeasiblePurchase s x ->
    0 <= p <= cur ->
    (forall k, 0 <= k < Zlength x -> p = 0 \/ p < Znth k x 0) ->
    FeasiblePurchase (cur :: s) (p :: x).
Proof.
  intros cur p s x [Hlen [Hbound Horder]] Hp Htop.
  unfold FeasiblePurchase.
  refine (conj _ (conj _ _));
    [ rewrite !Zlength_cons; lia
    | intros k Hk;
      destruct (Z.eq_dec k 0) as [-> | Hk0];
      [ rewrite Znth0_cons; exact Hp
      | rewrite !Znth_cons by lia;
        specialize (Hbound (k - 1));
        assert (Hk' : 0 <= k - 1 < Zlength x) by
          (rewrite Hlen; rewrite Zlength_cons in Hk; lia);
        specialize (Hbound ltac:(rewrite <- Hlen; exact Hk'));
        exact Hbound ]
    | intros j k [Hj Hklen];
      destruct (Z.eq_dec j 0) as [-> | Hj0];
      [ rewrite Znth0_cons;
        rewrite Znth_cons by lia;
        apply Htop;
        rewrite Hlen;
        rewrite Zlength_cons in Hklen;
        lia
      | rewrite Znth_cons by lia;
        rewrite Znth_cons by lia;
        specialize (Horder (j - 1) (k - 1));
        assert (Hjk : 0 <= j - 1 < k - 1 /\ k - 1 < Zlength s) by
          (rewrite Zlength_cons in Hklen; lia);
        specialize (Horder Hjk);
        exact Horder ]
    ].
Qed.
Lemma feasible_purchase_tail__backward_transitions :
  forall (cur : Z) (s y : list Z),
    FeasiblePurchase (cur :: s) y -> FeasiblePurchase s (tl y).
Proof.
  intros cur s y [Hlen [Hbound Horder]].
  destruct y as [| q y].
  - rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg s). lia.
  - simpl.
    unfold FeasiblePurchase.
    refine (conj _ (conj _ _));
      [ replace (Zlength (cur :: s)) with (Z.succ (Zlength s)) in Hlen
          by (symmetry; apply Zlength_cons);
        replace (Zlength (q :: y)) with (Z.succ (Zlength y)) in Hlen
          by (symmetry; apply Zlength_cons);
        change (Z.succ (Zlength y) = Z.succ (Zlength s)) in Hlen;
        pose proof (f_equal Z.pred Hlen) as Hlen';
        rewrite !Z.pred_succ in Hlen';
        exact Hlen'
      | intros k Hk;
        specialize (Hbound (k + 1));
        assert (Hk' : 0 <= k + 1 < Zlength (cur :: s)) by
          (rewrite Zlength_cons; lia);
        specialize (Hbound Hk');
        rewrite Znth_cons in Hbound by lia;
        rewrite Znth_cons in Hbound by lia;
        replace (k + 1 - 1) with k in Hbound by lia;
        exact Hbound
      | intros j k [Hj Hklen];
        specialize (Horder (j + 1) (k + 1));
        assert (Hjk : 0 <= j + 1 < k + 1 /\ k + 1 < Zlength (cur :: s)) by
          (rewrite Zlength_cons; lia);
        specialize (Horder Hjk);
        rewrite Znth_cons in Horder by lia;
        rewrite Znth_cons in Horder by lia;
        replace (j + 1 - 1) with j in Horder by lia;
        replace (k + 1 - 1) with k in Horder by lia;
        exact Horder
      ].
Qed.
Lemma dominant_purchase_cons__backward_transitions :
  forall (cur p : Z) (s x : list Z),
    DominantPurchase s x ->
    0 <= p <= cur ->
    (forall k, 0 <= k < Zlength x -> p = 0 \/ p < Znth k x 0) ->
    (forall y, FeasiblePurchase (cur :: s) y -> Znth 0 y 0 <= p) ->
    DominantPurchase (cur :: s) (p :: x).
Proof.
  intros cur p s x [Hfeasible Hdominant] Hp Htop Hhead.
  unfold DominantPurchase.
  split.
  - apply feasible_purchase_cons__backward_transitions; assumption.
  - intros y Hy k Hk.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + rewrite Znth0_cons. apply Hhead. exact Hy.
    + destruct y as [| q y].
      * unfold FeasiblePurchase in Hy.
        destruct Hy as [Hlen _].
        rewrite Zlength_nil in Hlen.
        rewrite <- Hlen in Hk.
        lia.
      * rewrite Znth_cons by lia.
        rewrite Znth_cons by lia.
        pose proof
          (feasible_purchase_tail__backward_transitions cur s (q :: y) Hy)
          as Htail.
        simpl in Htail.
        apply (Hdominant y Htail (k - 1)).
        rewrite Zlength_cons in Hk.
        lia.
Qed.
Lemma suffix_dominant_prepend__backward_transitions :
  forall (values : list Z) (i total prev p : Z),
    0 <= i < Zlength values ->
    SuffixDominantState values (i + 1) total prev ->
    0 <= p <= Znth i values 0 ->
    (forall x,
        DominantPurchase (sublist (i + 1) (Zlength values) values) x ->
        forall k, 0 <= k < Zlength x -> p = 0 \/ p < Znth k x 0) ->
    (forall x,
        DominantPurchase (sublist (i + 1) (Zlength values) values) x ->
        forall y, FeasiblePurchase
          (Znth i values 0 :: sublist (i + 1) (Zlength values) values) y ->
          Znth 0 y 0 <= p) ->
    SuffixDominantState values i (total + p) p.
Proof.
  intros values i total prev p Hi Hstate Hp Htop Hhead.
  unfold SuffixDominantState in Hstate |- *.
  destruct Hstate as [x [Hdom [Htotal [Hem Hprev]]]].
  exists (p :: x).
  refine (conj _ (conj _ (conj _ _))).
  - rewrite sublist_step__backward_transitions by exact Hi.
    apply dominant_purchase_cons__backward_transitions with
      (cur := Znth i values 0) (p := p).
    + exact Hdom.
    + exact Hp.
    + exact (Htop x Hdom).
    + exact (Hhead x Hdom).
  - simpl. rewrite <- Htotal. lia.
  - intro Hieq. exfalso. lia.
  - intros _. rewrite Znth0_cons. reflexivity.
Qed.
Lemma fold_right_Z_add_le__final_result :
  forall xs ys : list Z,
    Zlength xs = Zlength ys ->
    (forall k, 0 <= k < Zlength xs -> Znth k xs 0 <= Znth k ys 0) ->
    fold_right Z.add 0 xs <= fold_right Z.add 0 ys.
Proof.
  intros xs.
  induction xs as [|x xs IH]; intros ys Hlength Hpointwise.
  - destruct ys as [|y ys].
    + simpl. lia.
    + rewrite !Zlength_correct in Hlength.
      simpl in Hlength. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlength.
      simpl in Hlength. lia.
    + rewrite !Zlength_cons in Hlength.
      pose proof (Zlength_nonneg xs) as Hxs_nonneg.
      assert (Hhead : x <= y).
      { specialize (Hpointwise 0 ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth0_cons in Hpointwise.
        exact Hpointwise. }
      assert (Htail : forall k, 0 <= k < Zlength xs ->
          Znth k xs 0 <= Znth k ys 0).
      { intros k Hk.
        specialize (Hpointwise (k + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hpointwise by lia.
        replace (k + 1 - 1) with k in Hpointwise by lia.
        exact Hpointwise. }
      specialize (IH ys ltac:(lia) Htail).
      simpl. lia.
Qed.
Lemma suffix_dominant_state_to_spec__final_result :
  forall a total prev,
    SuffixDominantState a 0 total prev -> Spec a total.
Proof.
  intros a total prev Hstate.
  unfold SuffixDominantState in Hstate.
  destruct Hstate as [x [Hdominant [Htotal _]]].
  unfold DominantPurchase in Hdominant.
  rewrite (sublist_self a (Zlength a) eq_refl) in Hdominant.
  destruct Hdominant as [Hx Hdominates].
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists (fold_right Z.add 0 x).
  split.
  - split.
    + exists x. split; [exact Hx | reflexivity].
    + intros v Hv.
      destruct Hv as [y [Hy Hv]].
      subst v.
      pose proof Hy as Hy_feasible.
      unfold FeasiblePurchase in Hx, Hy.
      destruct Hx as [Hx_length _].
      destruct Hy as [Hy_length _].
      apply fold_right_Z_add_le__final_result.
      * lia.
      * intros k Hk.
        apply (Hdominates y Hy_feasible k).
        rewrite Hy_length in Hk. exact Hk.
  - symmetry. exact Htotal.
Qed.
