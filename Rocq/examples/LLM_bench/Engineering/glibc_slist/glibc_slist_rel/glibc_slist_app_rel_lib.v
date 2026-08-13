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

(* ---- Abstract program declaration for glibc_slist_clean_app ---- *)

Definition glibc_slist_clean_app_M : list Z -> list Z -> MONAD (list Z) :=
  fun x y =>
    list_append_raw_M x y.

Definition residual_prog_in_glibc_slist_clean_app_M_call_1 : list Z -> MONAD (list Z) :=
  fun r =>
    return r.

(* ---- Functional-correctness extension ---- *)

Lemma glibc_slist_clean_app_M_Hoare :
  forall l1 l2,
    Hoare ATrue
      (glibc_slist_clean_app_M l1 l2)
      (fun r _ => r = app l1 l2).
Proof.
  intros l1 l2.
  unfold glibc_slist_clean_app_M.
  apply list_append_raw_M_Hoare.
Qed.
