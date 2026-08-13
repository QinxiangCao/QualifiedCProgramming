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


Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).

Definition MretTy : Type := (list Z * Z).

Inductive early_result (S Ret : Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
Arguments Continue {S Ret} _.
Arguments ReturnNow {S Ret} _.

(* ---- Abstract program segments for list_tail ---- *)

Definition list_tail_M_loop_M1 : (list Z * list Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, l2) := a in
    match l2 with
    | [] => v <- any Z;; return (l1, v)
    | v :: _ => return (l1, v)
    end.
Definition list_tail_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=
  fun a =>
    let '(l1, l2) := a in
    match l2 with
    | [] => return (l1, [])
    | v :: l2' => return (l1 ++ [v], l2')
    end.

Definition list_tail_guardP : (list Z * list Z) -> Prop :=
  fun a =>
    let '(l1, l2) := a in
    tl l2 <> [].

Definition list_tail_M_loop_end : MretTy -> MONAD ((list Z * Z)) :=
  fun r => return r.

Definition list_tail_M_loop_body : (list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (list_tail_guardP a));; r <- list_tail_M_loop_M1 a ;; break r)
           (assume!! ((list_tail_guardP a));; a' <- list_tail_M_loop_M2 a ;; continue a').

Definition list_tail_M_loop_aux :=
  repeat_break list_tail_M_loop_body.

Definition list_tail_M_loop : list Z -> list Z -> program unit MretTy :=
  fun l1 l2 => list_tail_M_loop_aux (l1, l2).

Definition list_tail_M_loop_before : list Z -> MONAD (early_result (list Z * list Z) (list Z * Z)) :=
  fun l1 =>
    assume!! (l1 <> []);;
    return (Continue ([], l1)).

Definition list_tail_M : list Z -> MONAD ((list Z * Z)) :=
  fun l1 =>
    e <- list_tail_M_loop_before l1;;
    match e with
    | Continue s =>
        re <- list_tail_M_loop_aux s;;
        list_tail_M_loop_end re
    | ReturnNow r =>
        return r
    end.

(* ---- Functional-correctness extension ---- *)

Lemma list_tail_M_loop_aux_Hoare :
  forall (prefix rest target : list Z),
    Hoare (fun _ : unit => prefix ++ rest = target /\ rest <> [])
      (list_tail_M_loop_aux (prefix, rest))
      (fun r _ => let '(prefix', last) := r in target = prefix' ++ [last]).
Proof.
  intros prefix rest target.
  pose proof (Hoare_repeat_break list_tail_M_loop_body
       (fun a _ =>
          let '(prefix0, rest0) := a in
          prefix0 ++ rest0 = target /\ rest0 <> [])
       (fun r _ =>
          let '(prefix', last) := r in target = prefix' ++ [last])) as Hloop.
  assert (Hbody:
    forall a : list Z * list Z,
      Hoare
        ((fun a _ =>
          let '(prefix0, rest0) := a in
          prefix0 ++ rest0 = target /\ rest0 <> []) a)
        (list_tail_M_loop_body a)
        (fun x _ =>
          match x with
          | by_continue a0 =>
              (let '(prefix0, rest0) := a0 in
               prefix0 ++ rest0 = target /\ rest0 <> [])
          | by_break b =>
              let '(prefix', last) := b in target = prefix' ++ [last]
          end)).
  {
    intros (prefix0, rest0).
    unfold list_tail_M_loop_body, list_tail_guardP.
    apply Hoare_choice.
    + apply Hoare_assume_bind.
      intro Hnot_guard.
      unfold list_tail_M_loop_M1, break.
      destruct rest0 as [| last rest_tail].
      * eapply Hoare_conseq with
          (P2 := fun _ : unit => False)
          (Q2 := fun _ _ => False).
        -- intros _ [_ Hnonempty].
           apply Hnonempty. reflexivity.
        -- intros b _ Hfalse. destruct Hfalse.
        -- unfold Hoare. firstorder.
      * destruct rest_tail as [| h t].
        -- prog_nf.
           apply Hoare_ret.
           intros _ [Hpre _].
           symmetry.
           exact Hpre.
        -- prog_nf.
           apply Hoare_ret.
           intros _ _.
           exfalso. apply Hnot_guard. discriminate.
    + apply Hoare_assume_bind.
      intro Hguard.
      unfold list_tail_M_loop_M2, continue.
      destruct rest0 as [| h t].
      * eapply Hoare_conseq with
          (P2 := fun _ : unit => False)
          (Q2 := fun _ _ => False).
        -- intros _ [_ Hnonempty].
           apply Hnonempty. reflexivity.
        -- intros b _ Hfalse. destruct Hfalse.
        -- unfold Hoare. firstorder.
      * prog_nf.
        apply Hoare_ret.
        intros _ [Hpre _].
        split.
        -- rewrite <- app_assoc.
           simpl.
           exact Hpre.
        -- destruct t as [| h' t'].
           ++ exfalso. apply Hguard. reflexivity.
           ++ discriminate.
  }
  exact (Hloop Hbody (prefix, rest)).
Qed.

Lemma list_tail_M_Hoare :
  forall (l1 : list Z),
    l1 <> [] ->
    Hoare ATrue
      (list_tail_M l1)
      (fun r _ => let '(prefix, last) := r in l1 = prefix ++ [last]).
Proof.
  intros l1 Hnonempty.
  unfold list_tail_M, list_tail_M_loop_before.
  eapply Hoare_bind with
    (Q := fun e _ =>
      match e with
      | Continue s =>
          let '(prefix, rest) := s in prefix ++ rest = l1 /\ rest <> []
      | ReturnNow r =>
          let '(prefix, last) := r in l1 = prefix ++ [last]
      end).
  - apply Hoare_assume_bind.
    intro Hassume.
    apply Hoare_ret.
    intros _ _.
    simpl.
    split; [reflexivity | exact Hnonempty].
  - intros r.
    destruct r as [[prefix rest] | [prefix last]].
    + simpl.
      eapply Hoare_bind.
      * apply list_tail_M_loop_aux_Hoare.
      * intros r.
        unfold list_tail_M_loop_end.
        apply Hoare_ret.
        intros _ Hr.
        exact Hr.
    + apply Hoare_ret.
      intros _ Hr.
      exact Hr.
Qed.
