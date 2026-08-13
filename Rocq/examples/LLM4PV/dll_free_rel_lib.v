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


Definition MretTy : Type := list Z.

(* ---- Abstract program segments for dll_free ---- *)

Definition dll_free_M_loop_M1 : list Z -> MONAD MretTy :=
  fun r => return r.
Definition dll_free_M_loop_M2 : list Z -> MONAD (list Z) :=
  fun l1 =>
    x <- any Z;;
    l1' <- any (list Z);;
    assume!! (l1 = x :: l1');;
    return l1'.

(* Guard could not be generated — declare as Parameter *)
Parameter dll_free_guardP : list Z -> Prop.

Definition dll_free_M_loop_end : MretTy -> MONAD (unit) :=
  fun l1 =>
    return tt.

Definition dll_free_M_loop_body : list Z -> MONAD (CntOrBrk (list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (dll_free_guardP a));; r <- dll_free_M_loop_M1 a ;; break r)
           (assume!! ((dll_free_guardP a));; a' <- dll_free_M_loop_M2 a ;; continue a').

Definition dll_free_M_loop_aux :=
  repeat_break dll_free_M_loop_body.

Definition dll_free_M_loop : list Z -> program unit MretTy :=
  fun l1 => dll_free_M_loop_aux l1.

Definition dll_free_M_loop_before : list Z -> MONAD (list Z) :=
  fun l1 =>
    return l1.

Definition dll_free_M : list Z -> MONAD (unit) :=
  fun l1 =>
    s0 <- dll_free_M_loop_before l1;;
    re <- dll_free_M_loop_aux s0;;
    dll_free_M_loop_end re.
