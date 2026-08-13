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


Require Import list_append_raw_rel_lib.

(* ---- Abstract program declaration for glibc_slist_clean_multi_append ---- *)

Definition glibc_slist_clean_multi_append_M : list Z -> list Z -> list Z -> MONAD (list Z) :=
  fun x y z =>
    x <- list_append_raw_M x y;;
    x <- list_append_raw_M x z;;
    return x.

Definition residual_prog_in_glibc_slist_clean_multi_append_M_call_1 (z : list Z) : list Z -> MONAD (list Z) :=
  fun x =>
    x <- list_append_raw_M x z;;
return x.

Definition residual_prog_in_glibc_slist_clean_multi_append_M_call_2 : list Z -> MONAD (list Z) :=
  fun x =>
    return x.

Lemma glibc_slist_clean_multi_append_M_Hoare :
  forall l1 l2 l3,
    Hoare ATrue
      (glibc_slist_clean_multi_append_M l1 l2 l3)
      (fun r _ => r = app (app l1 l2) l3).
Proof.
  intros l1 l2 l3.
  unfold glibc_slist_clean_multi_append_M.
  eapply Hoare_bind with
    (Q := fun r _ => r = app l1 l2).
  - apply list_append_raw_M_Hoare.
  - intros xy.
    eapply Hoare_bind with
      (Q := fun r _ => xy = app l1 l2 /\ r = app xy l3).
    + apply Hoare_unit_pre.
      intro Hxy.
      eapply Hoare_conseq.
      * intros sigma _.
        exact I.
      * intros r sigma Hr.
        split.
        -- exact Hxy.
        -- exact Hr.
      * apply list_append_raw_M_Hoare.
    + intros r.
      apply Hoare_ret.
      intros _ [Hxy Hr].
      subst xy r.
      reflexivity.
Qed.
