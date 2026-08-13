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


Require Import list_tail_rel_lib.

Definition MretTy : Type := (list Z * list Z).

Inductive early_result (S Ret : Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
Arguments Continue {S Ret} _.
Arguments ReturnNow {S Ret} _.

(* ---- Abstract program segments for list_append_raw ---- *)

Definition list_append_raw_M_before : list Z -> list Z -> MONAD (early_result MretTy (list Z)) :=
  fun l1 l2 =>
    match l1 with
    | [] => return (ReturnNow l2)
    | _ :: _ => return (Continue (l1, l2))
    end.
Definition list_append_raw_M_normal : MretTy -> MONAD (list Z) :=
  fun s =>
    let '(l1, l2) := s in
    r <- list_tail_M l1;;
    let '(l3, v) := r in
    return (l3 ++ (v :: l2)).

Definition list_append_raw_M : list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 =>
    e <- list_append_raw_M_before l1 l2;;
    match e with
    | Continue s => list_append_raw_M_normal s
    | ReturnNow r => return r
    end.

Definition residual_prog_in_list_append_raw_M_call_1 (l2 : list Z) : list Z * Z -> MONAD (list Z) :=
  fun r =>
    let '(l3, v) := r in
    return (l3 ++ (v :: l2)).

Definition app : list Z -> list Z -> list Z := @List.app Z.

Lemma list_append_raw_M_Hoare :
  forall (l1 l2 : list Z),
    Hoare ATrue (list_append_raw_M l1 l2) (fun r _ => r = app l1 l2).
Proof.
  intros l1 l2.
  unfold list_append_raw_M, list_append_raw_M_before.
  destruct l1 as [| h t].
  - prog_nf.
    apply Hoare_ret.
    intros _ _. reflexivity.
  - prog_nf.
    unfold list_append_raw_M_normal.
    eapply Hoare_bind.
    + apply list_tail_M_Hoare. discriminate.
    + intros [prefix last].
      unfold app.
      prog_nf.
      apply Hoare_ret.
      intros _ Htail.
      rewrite Htail.
      rewrite <- List.app_assoc.
      reflexivity.
Qed.
