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


Definition MretTy : Type := (list Z * list Z).

(* ---- Abstract program segments for reverse ---- *)

Definition reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy :=
  fun r => return r.
Definition reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=
  fun '(l1, l2) =>
    x <- any Z;;
    l2' <- any (list Z);;
    assume!! (l2 = x :: l2');;
    return (x :: l1, l2').

(* Guard could not be generated — declare as Parameter *)
Parameter reverse_guardP : (list Z * list Z) -> Prop.

Definition reverse_M_loop_end : MretTy -> MONAD (list Z) :=
  fun '(l1, l2) =>
    assume!! (l2 = nil);;
    return l1.

Definition reverse_M_loop_body : (list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (reverse_guardP a));; r <- reverse_M_loop_M1 a ;; break r)
           (assume!! ((reverse_guardP a));; a' <- reverse_M_loop_M2 a ;; continue a').

Definition reverse_M_loop_aux :=
  repeat_break reverse_M_loop_body.

Definition reverse_M_loop : list Z -> list Z -> program unit MretTy :=
  fun l1 l2 => reverse_M_loop_aux (l1, l2).

Definition reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=
  fun l1 =>
    return (nil, l1).

Definition reverse_M : list Z -> MONAD (list Z) :=
  fun l1 =>
    s0 <- reverse_M_loop_before l1;;
    re <- reverse_M_loop_aux s0;;
    reverse_M_loop_end re.
