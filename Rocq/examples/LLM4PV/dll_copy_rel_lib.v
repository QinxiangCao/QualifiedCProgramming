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

From MonadLib Require Import MonadLib.
Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.


Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).

Definition MretTy : Type := (list Z * list Z * list Z * Z).

Inductive early_result (S Ret : Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
Arguments Continue {S Ret} _.
Arguments ReturnNow {S Ret} _.

(* ---- Abstract program segments for dll_copy ---- *)

Definition dll_copy_M_loop_M1 : (list Z * list Z * list Z * Z) -> MONAD MretTy :=
  fun r => return r.
Definition dll_copy_M_loop_M2 : (list Z * list Z * list Z * Z) -> MONAD (list Z * list Z * list Z * Z) :=
  fun '(l1, l2, l3, v) =>
    x <- any Z;;
    l2' <- any (list Z);;
    assume!! (l2 = x :: l2');;
    return (l1 ++ (x :: nil), l2', l3 ++ (v :: nil), x).

(* Guard could not be generated — declare as Parameter *)
Parameter dll_copy_guardP : (list Z * list Z * list Z * Z) -> Prop.

Definition dll_copy_M_loop_end : MretTy -> MONAD ((list Z * list Z)) :=
  fun '(l1, l2, l3, v) =>
    assume!! (l2 = nil);;
    return (l3 ++ (v :: nil), l1 ++ nil).

Definition dll_copy_M_loop_body : (list Z * list Z * list Z * Z) -> MONAD (CntOrBrk (list Z * list Z * list Z * Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (dll_copy_guardP a));; r <- dll_copy_M_loop_M1 a ;; break r)
           (assume!! ((dll_copy_guardP a));; a' <- dll_copy_M_loop_M2 a ;; continue a').

Definition dll_copy_M_loop_aux :=
  repeat_break dll_copy_M_loop_body.

Definition dll_copy_M_loop : list Z -> list Z -> list Z -> Z -> program unit MretTy :=
  fun l1 l2 l3 l4 => dll_copy_M_loop_aux (l1, l2, l3, l4).

Definition dll_copy_M_loop_before : list Z -> MONAD (early_result (list Z * list Z * list Z * Z) (list Z * list Z)) :=
  fun l1 =>
    choice
      ( x <- any Z;;
        l1' <- any (list Z);;
        assume!! (l1 = x :: l1');;
        return Continue ((nil ++ (x :: nil), l1', nil, x)) )
      ( assume!! (l1 = nil);;
        return ReturnNow ((nil, nil)) ).

Definition dll_copy_M : list Z -> MONAD ((list Z * list Z)) :=
  fun l1 =>
    e <- dll_copy_M_loop_before l1;;
    match e with
    | Continue s =>
        re <- dll_copy_M_loop_aux s;;
        dll_copy_M_loop_end re
    | ReturnNow r =>
        return r
    end.
