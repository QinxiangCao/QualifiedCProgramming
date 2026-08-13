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


Definition MretTy : Type := unit.

(* ---- Abstract program segments for glibc_slist_clean_free ---- *)

Definition glibc_slist_clean_free_M_loop_M1 : list Z -> MONAD MretTy :=
  fun l1 => return tt.
Definition glibc_slist_clean_free_M_loop_M2 : list Z -> MONAD (list Z) :=
  fun l1 =>
    match l1 with
    | [] => return []
    | _ :: l1' => return l1'
    end.

Definition glibc_slist_clean_free_guardP : list Z -> Prop :=
  fun l1 =>
    l1 <> [].

Definition glibc_slist_clean_free_M_loop_end : MretTy -> MONAD (unit) :=
  fun r => return r.

Definition glibc_slist_clean_free_M_loop_body : list Z -> MONAD (CntOrBrk (list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_free_guardP a));; r <- glibc_slist_clean_free_M_loop_M1 a ;; break r)
           (assume!! ((glibc_slist_clean_free_guardP a));; a' <- glibc_slist_clean_free_M_loop_M2 a ;; continue a').

Definition glibc_slist_clean_free_M_loop_aux :=
  repeat_break glibc_slist_clean_free_M_loop_body.

Definition glibc_slist_clean_free_M_loop : list Z -> program unit MretTy :=
  fun l1 => glibc_slist_clean_free_M_loop_aux l1.

Definition glibc_slist_clean_free_M_loop_before : list Z -> MONAD (list Z) :=
  fun l1 => return l1.

Definition glibc_slist_clean_free_M : list Z -> MONAD (unit) :=
  fun l1 =>
    s0 <- glibc_slist_clean_free_M_loop_before l1;;
    re <- glibc_slist_clean_free_M_loop_aux s0;;
    glibc_slist_clean_free_M_loop_end re.

(* ---- Functional-correctness extension ---- *)

Lemma glibc_slist_clean_free_M_loop_aux_Hoare :
  forall l1,
    Hoare ATrue
      (glibc_slist_clean_free_M_loop_aux l1)
      (fun r _ => r = tt).
Proof.
  intro l1.
  pose proof (Hoare_repeat_break glibc_slist_clean_free_M_loop_body
       (fun _ _ => True)
       (fun r _ => r = tt)) as Hloop.
  assert (Hbody:
    forall a : list Z,
      Hoare
        ((fun _ _ => True) a)
        (glibc_slist_clean_free_M_loop_body a)
        (fun x _ =>
          match x with
          | by_continue a0 => (fun _ _ => True) a0 tt
          | by_break b => b = tt
          end)).
  {
    intro a.
    unfold glibc_slist_clean_free_M_loop_body, glibc_slist_clean_free_guardP.
    apply Hoare_choice.
    + apply Hoare_assume_bind.
      intro Hnot_guard.
      unfold glibc_slist_clean_free_M_loop_M1, break.
      prog_nf.
      apply Hoare_ret.
      intros _ _.
      reflexivity.
    + apply Hoare_assume_bind.
      intro Hguard.
      unfold glibc_slist_clean_free_M_loop_M2, continue.
      destruct a as [| h t].
      * prog_nf.
        apply Hoare_ret.
        intros _ _.
        exact I.
      * prog_nf.
        apply Hoare_ret.
        intros _ _.
        exact I.
  }
  exact (Hloop Hbody l1).
Qed.

Lemma glibc_slist_clean_free_M_Hoare :
  forall l1,
    Hoare ATrue
      (glibc_slist_clean_free_M l1)
      (fun r _ => r = tt).
Proof.
  intro l1.
  unfold glibc_slist_clean_free_M, glibc_slist_clean_free_M_loop_before.
  eapply Hoare_bind with (Q := fun _ _ => True).
  - apply Hoare_ret.
    intros _ _.
    exact I.
  - intro s.
    eapply Hoare_bind.
    + apply glibc_slist_clean_free_M_loop_aux_Hoare.
    + intro r.
      unfold glibc_slist_clean_free_M_loop_end.
      apply Hoare_ret.
      intros _ Hr.
      exact Hr.
Qed.
