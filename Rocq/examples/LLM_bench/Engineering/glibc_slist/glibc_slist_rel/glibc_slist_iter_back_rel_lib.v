Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From FP Require Import PartialOrder_Setoid BourbakiWitt.
From MonadLib.MonadErr Require Import StateRelMonadErr.
Import MonadNotation.
Local Open Scope monad.


Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).

Definition range (l : list Z) : Prop :=
  Zlength l <= 100 /\ Forall (fun x => -100 <= x <= 100) l.

Lemma glibc_slist_clean_iter_back_sum_step_int_range :
  forall sum v,
    -10000 <= sum <= 10000 ->
    -100 <= v <= 100 ->
    -2147483648 <= sum + v /\ sum + v <= 2147483647.
Proof.
  intros; lia.
Qed.

(* ---- Abstract program declaration for glibc_slist_clean_iter_back ---- *)

Definition glibc_slist_clean_iter_back_M : list Z -> MONAD ((list Z * Z)) :=
  fix glibc_slist_clean_iter_back_M (l1 : list Z) : MONAD (list Z * Z) :=
    match l1 with
    | [] => return ([], 0)
    | v :: l1' =>
        r <- glibc_slist_clean_iter_back_M l1';;
        let '(l2, sum) := r in
        assert (-2147483648 <= sum + v /\ sum + v <= 2147483647);;
        return (v :: l2, sum + v)
    end.

Definition residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v : Z) : list Z * Z -> MONAD (list Z * Z) :=
  fun r =>
    let '(l2, sum) := r in
    assert (-2147483648 <= sum + v /\ sum + v <= 2147483647);;
    return (v :: l2, sum + v).

(* ---- Functional-correctness extension ---- *)

From AUXLib Require Import ListLib.

Fixpoint list_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + list_sum xs
  end.

Lemma list_sum_range_bound :
  forall l,
    Zlength l <= 100 ->
    Forall (fun x => -100 <= x <= 100) l ->
    -100 * Zlength l <= list_sum l <= 100 * Zlength l.
Proof.
  induction l as [| x xs IH]; intros Hlen Hall.
  - rewrite Zlength_correct. simpl. lia.
  - inversion Hall as [| ? ? Hx Hxs_forall]; subst.
    rewrite Zlength_cons in Hlen.
    assert (Hxs_len : Zlength xs <= 100) by lia.
    pose proof (IH Hxs_len Hxs_forall) as Hxs.
    rewrite Zlength_cons.
    unfold Z.succ.
    cbn [list_sum].
    destruct Hx as [Hx_low Hx_high].
    destruct Hxs as [Hxs_low Hxs_high].
    nia.
Qed.

Lemma range_cons_inv :
  forall v xs,
    range (v :: xs) ->
    range xs /\ -100 <= v <= 100.
Proof.
  intros v xs [Hlen Hall].
  inversion Hall as [| ? ? Hv Hxs]; subst.
  rewrite Zlength_cons in Hlen.
  split.
  - split; auto; lia.
  - exact Hv.
Qed.

Lemma glibc_slist_clean_iter_back_M_Hoare :
  forall l1,
    Hoare
      (fun _ : unit => range l1)
      (glibc_slist_clean_iter_back_M l1)
      (fun r _ => r = (l1, list_sum l1)).
Proof.
  induction l1 as [| v xs IH]; simpl.
  - apply Hoare_ret.
    intros _ _.
    reflexivity.
  - eapply Hoare_bind with
      (Q := fun r _ => r = (xs, list_sum xs) /\ range (v :: xs)).
    + apply Hoare_unit_pre.
      intro Hrange.
      eapply Hoare_cons_post.
      * intros r sigma Hr.
        split.
        -- exact Hr.
        -- exact Hrange.
      * eapply Hoare_cons_pre.
        -- intros sigma _.
           apply range_cons_inv in Hrange as [Hrange_xs _].
           exact Hrange_xs.
        -- apply IH.
    + intros (l2, sum).
      apply Hoare_assert_bind.
      * intros _ [Hr Hrange].
        inversion Hr; subst l2 sum.
        apply range_cons_inv in Hrange as [Hrange_xs Hv].
        destruct Hrange_xs as [Hxs_len Hxs_forall].
        pose proof (list_sum_range_bound xs Hxs_len Hxs_forall) as Hsum.
        assert (-10000 <= list_sum xs <= 10000) by lia.
        pose proof (glibc_slist_clean_iter_back_sum_step_int_range
          (list_sum xs) v ltac:(lia) Hv) as Hstep.
        lia.
      * intros _.
        apply Hoare_ret.
        intros _ [Hr _].
        inversion Hr; subst l2 sum.
        cbn [list_sum].
        f_equal; lia.
Qed.
