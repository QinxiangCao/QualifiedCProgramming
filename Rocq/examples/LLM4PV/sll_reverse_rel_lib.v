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

(* ---- Abstract program segments for sll_reverse ---- *)

Definition sll_reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy:=
  fun '(l1,l2) => return l1.
Definition sll_reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=
  fun '(l1,l2) =>
    match l2 with
    | nil => return (l1,l2)
    | v :: l2' => return (v :: l1, l2')
    end.

(*@ guard-struct: (atom l2 ne) @*)
Definition sll_reverse_guardP : (list Z * list Z) -> Prop :=
  fun a =>
    let '(l1, l2) := a in
    l2 <> [].

Definition sll_reverse_M_loop_end : MretTy -> MONAD (list Z):=
  fun l => return l.

Definition sll_reverse_M_loop_body : (list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (sll_reverse_guardP a));; r <- sll_reverse_M_loop_M1 a ;; break r)
           (assume!! ((sll_reverse_guardP a));; a' <- sll_reverse_M_loop_M2 a ;; continue a').

Definition sll_reverse_M_loop_aux :=
  repeat_break sll_reverse_M_loop_body.

Definition sll_reverse_M_loop : list Z -> list Z -> program unit MretTy :=
  fun l1 l2 => sll_reverse_M_loop_aux (l1, l2).

Definition sll_reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=
  fun l => return (nil, l).

Definition sll_reverse_M : list Z -> MONAD (list Z) :=
  fun l1 =>
    s0 <- sll_reverse_M_loop_before l1;;
    re <- sll_reverse_M_loop_aux s0;;
    sll_reverse_M_loop_end re.
