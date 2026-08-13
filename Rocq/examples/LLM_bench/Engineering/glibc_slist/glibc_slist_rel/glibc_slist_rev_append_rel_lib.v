Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
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


Definition MretTy : Type := list Z.

(* ---- Abstract program segments for glibc_slist_clean_rev_append ---- *)

Definition glibc_slist_clean_rev_append_M_loop_M1 : (list Z * list Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, l2) := a in
    return l2.
Definition glibc_slist_clean_rev_append_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=
  fun a =>
    let '(l1, l2) := a in
    match l1 with
    | nil => return (l1, l2)
    | x :: xs => return (xs, x :: l2)
    end.

Definition glibc_slist_clean_rev_append_guardP : (list Z * list Z) -> Prop :=
  fun a =>
    let '(l1, l2) := a in
    l1 <> [].

Definition glibc_slist_clean_rev_append_M_loop_end : MretTy -> MONAD (list Z) :=
  fun r => return r.

Definition glibc_slist_clean_rev_append_M_loop_body : (list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_rev_append_guardP a));; r <- glibc_slist_clean_rev_append_M_loop_M1 a ;; break r)
           (assume!! ((glibc_slist_clean_rev_append_guardP a));; a' <- glibc_slist_clean_rev_append_M_loop_M2 a ;; continue a').

Definition glibc_slist_clean_rev_append_M_loop_aux :=
  repeat_break glibc_slist_clean_rev_append_M_loop_body.

Definition glibc_slist_clean_rev_append_M_loop : list Z -> list Z -> program unit MretTy :=
  fun l1 l2 => glibc_slist_clean_rev_append_M_loop_aux (l1, l2).

Definition glibc_slist_clean_rev_append_M_loop_before : list Z -> list Z -> MONAD (list Z * list Z) :=
  fun l1 l2 => return (l1, l2).

Definition glibc_slist_clean_rev_append_M : list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 =>
    s0 <- glibc_slist_clean_rev_append_M_loop_before l1 l2;;
    re <- glibc_slist_clean_rev_append_M_loop_aux s0;;
    glibc_slist_clean_rev_append_M_loop_end re.

(* ---- Functional-correctness extension ---- *)

Lemma glibc_slist_clean_rev_append_M_loop_aux_Hoare :
  forall (rest acc target : list Z),
    Hoare (fun _ : unit => rev rest ++ acc = target)
      (glibc_slist_clean_rev_append_M_loop_aux (rest, acc))
      (fun r _ => r = target).
Proof.
  intros rest acc target.
  pose proof (Hoare_repeat_break glibc_slist_clean_rev_append_M_loop_body
       (fun a _ =>
          let '(rest0, acc0) := a in
          rev rest0 ++ acc0 = target)
       (fun r _ => r = target)) as Hloop.
  assert (Hbody:
    forall a : list Z * list Z,
      Hoare
        ((fun a _ =>
          let '(rest0, acc0) := a in
          rev rest0 ++ acc0 = target) a)
        (glibc_slist_clean_rev_append_M_loop_body a)
        (fun x _ =>
          match x with
          | by_continue a0 =>
              (let '(rest0, acc0) := a0 in
               rev rest0 ++ acc0 = target)
          | by_break b => b = target
          end)).
  {
    intros (rest0, acc0).
    unfold glibc_slist_clean_rev_append_M_loop_body,
      glibc_slist_clean_rev_append_guardP.
    apply Hoare_choice.
    + apply Hoare_assume_bind.
      intro Hnot_guard.
      unfold glibc_slist_clean_rev_append_M_loop_M1, break.
      destruct rest0 as [| h t].
      * prog_nf.
        apply Hoare_ret.
        intros _ Hpre.
        simpl in Hpre.
        exact Hpre.
      * prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hnot_guard. discriminate.
    + apply Hoare_assume_bind.
      intro Hguard.
      unfold glibc_slist_clean_rev_append_M_loop_M2, continue.
      destruct rest0 as [| h t].
      * prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hguard. reflexivity.
      * prog_nf.
        apply Hoare_ret.
        intros _ Hpre.
        simpl in Hpre.
        rewrite <- app_assoc in Hpre.
        simpl in Hpre.
        exact Hpre.
  }
  exact (Hloop Hbody (rest, acc)).
Qed.

Lemma glibc_slist_clean_rev_append_M_Hoare :
  forall l1 l2,
    Hoare ATrue
      (glibc_slist_clean_rev_append_M l1 l2)
      (fun r _ => r = rev l1 ++ l2).
Proof.
  intros l1 l2.
  unfold glibc_slist_clean_rev_append_M,
    glibc_slist_clean_rev_append_M_loop_before.
  eapply Hoare_bind with
    (Q := fun s _ =>
      let '(rest, acc) := s in rev rest ++ acc = rev l1 ++ l2).
  - apply Hoare_ret.
    intros _ _.
    reflexivity.
  - intros s.
    destruct s as [rest acc].
    simpl.
    eapply Hoare_bind.
    + apply glibc_slist_clean_rev_append_M_loop_aux_Hoare.
    + intros r.
      unfold glibc_slist_clean_rev_append_M_loop_end.
      apply Hoare_ret.
      intros _ Hr.
      exact Hr.
Qed.
