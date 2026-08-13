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

Inductive early_result (S Ret : Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
Arguments Continue {S Ret} _.
Arguments ReturnNow {S Ret} _.

(* ---- Abstract program segments for glibc_slist_clean_merge ---- *)

Definition glibc_slist_clean_merge_M_loop_M1 : (list Z * list Z * list Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, l2, l3) := a in
    return (l1 ++ l2).
Definition glibc_slist_clean_merge_M_loop_M2 : (list Z * list Z * list Z) -> MONAD (early_result (list Z * list Z * list Z) (list Z)) :=
  fun a =>
    let '(l1, l2, l3) := a in
    match l3 with
    | nil => return (Continue (l1, l2, l3))
    | yv :: l3' =>
        match l2 with
        | nil => return (ReturnNow (l1 ++ (yv :: l3')))
        | cv :: l2' =>
            match l2' with
            | nil => return (ReturnNow (l1 ++ (cv :: yv :: nil) ++ l3'))
            | _ => return (Continue (l1 ++ (cv :: yv :: nil), l2', l3'))
            end
        end
    end.

Definition glibc_slist_clean_merge_guardP : (list Z * list Z * list Z) -> Prop :=
  fun a =>
    let '(l1, l2, l3) := a in
    l3 <> [].

Definition glibc_slist_clean_merge_M_loop_end : MretTy -> MONAD (list Z) :=
  fun r => return r.

Definition glibc_slist_clean_merge_M_after_loop : (early_result MretTy (list Z)) -> MONAD (list Z) :=
  fun re =>
    match re with
    | Continue r => glibc_slist_clean_merge_M_loop_end r
    | ReturnNow r => return r
    end.

Definition glibc_slist_clean_merge_M_loop_body : (list Z * list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z * list Z) (early_result MretTy (list Z))) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_merge_guardP a));; r <- glibc_slist_clean_merge_M_loop_M1 a ;; break (Continue r))
           (assume!! ((glibc_slist_clean_merge_guardP a));;
            a' <- glibc_slist_clean_merge_M_loop_M2 a ;;
            match a' with
            | Continue a'' => continue a''
            | ReturnNow r' => break (ReturnNow r')
            end).

Definition glibc_slist_clean_merge_M_loop_aux :=
  repeat_break glibc_slist_clean_merge_M_loop_body.

Definition glibc_slist_clean_merge_M_loop : list Z -> list Z -> list Z -> program unit (early_result MretTy (list Z)) :=
  fun l1 l2 l3 => glibc_slist_clean_merge_M_loop_aux (l1, l2, l3).

Definition glibc_slist_clean_merge_M_loop_before : list Z -> list Z -> MONAD (early_result (list Z * list Z * list Z) (list Z)) :=
  fun l1 l2 =>
    match l1 with
    | nil => return (ReturnNow l2)
    | _ => return (Continue (nil, l1, l2))
    end.

Definition glibc_slist_clean_merge_M : list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 =>
    e <- glibc_slist_clean_merge_M_loop_before l1 l2;;
    match e with
    | Continue s =>
        re <- glibc_slist_clean_merge_M_loop_aux s;;
        glibc_slist_clean_merge_M_after_loop re
    | ReturnNow r =>
        return r
    end.

(* ---- Functional-correctness extension ---- *)

Require Import Coq.Sorting.Permutation.

Lemma glibc_slist_clean_merge_insert_perm :
  forall (prefix cursor_tail y_tail target : list Z) (cursor node : Z),
    Permutation
      (prefix ++ cursor :: cursor_tail ++ node :: y_tail)
      target ->
    Permutation
      ((prefix ++ [cursor; node]) ++ cursor_tail ++ y_tail)
      target.
Proof.
  intros prefix cursor_tail y_tail target cursor node Hperm.
  eapply Permutation_trans; [| exact Hperm].
  repeat rewrite <- app_assoc.
  simpl.
  apply Permutation_app_head.
  apply perm_skip.
  replace (node :: cursor_tail ++ y_tail)
    with (node :: cursor_tail ++ y_tail) by reflexivity.
  replace (cursor_tail ++ node :: y_tail)
    with (cursor_tail ++ node :: y_tail) by reflexivity.
  apply Permutation_middle.
Qed.

Lemma glibc_slist_clean_merge_M_loop_aux_Hoare :
  forall (prefix cursor y target : list Z),
    Hoare
      (fun _ : unit =>
         Permutation (prefix ++ cursor ++ y) target)
      (glibc_slist_clean_merge_M_loop_aux (prefix, cursor, y))
      (fun r _ =>
         match r with
         | Continue ret => Permutation ret target
         | ReturnNow ret => Permutation ret target
         end).
Proof.
  intros prefix cursor y target.
  pose proof (Hoare_repeat_break
    glibc_slist_clean_merge_M_loop_body
    (fun a _ =>
       let '(prefix0, cursor0, y0) := a in
       Permutation (prefix0 ++ cursor0 ++ y0) target)
    (fun r _ =>
       match r with
       | Continue ret => Permutation ret target
       | ReturnNow ret => Permutation ret target
       end)) as Hloop.
  assert (Hbody:
    forall a : list Z * list Z * list Z,
      Hoare
        ((fun a _ =>
           let '(prefix0, cursor0, y0) := a in
           Permutation (prefix0 ++ cursor0 ++ y0) target) a)
        (glibc_slist_clean_merge_M_loop_body a)
        (fun x _ =>
           match x with
           | by_continue a0 =>
               let '(prefix0, cursor0, y0) := a0 in
               Permutation (prefix0 ++ cursor0 ++ y0) target
           | by_break r =>
               match r with
               | Continue ret => Permutation ret target
               | ReturnNow ret => Permutation ret target
               end
           end)).
  {
    intros ((prefix0, cursor0), y0).
    unfold glibc_slist_clean_merge_M_loop_body,
      glibc_slist_clean_merge_guardP.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      intro Hnot_guard.
      unfold glibc_slist_clean_merge_M_loop_M1, break.
      destruct y0 as [| yh yt].
      + prog_nf.
        apply Hoare_ret.
        intros _ Hpre.
        rewrite app_nil_r in Hpre.
        exact Hpre.
      + prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hnot_guard. discriminate.
    - apply Hoare_assume_bind.
      intro Hguard.
      unfold glibc_slist_clean_merge_M_loop_M2, continue, break.
      destruct y0 as [| node y_tail].
      + prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hguard. reflexivity.
      + destruct cursor0 as [| cur cursor_tail].
        * prog_nf.
          apply Hoare_ret.
          intros _ Hpre.
          exact Hpre.
        * destruct cursor_tail as [| next cursor_tail].
          -- prog_nf.
             apply Hoare_ret.
             intros _ Hpre.
             repeat rewrite <- app_assoc.
             simpl in *.
             exact Hpre.
          -- prog_nf.
             apply Hoare_ret.
             intros _ Hpre.
             eapply (glibc_slist_clean_merge_insert_perm
               prefix0 (next :: cursor_tail) y_tail target cur node).
             exact Hpre.
  }
  exact (Hloop Hbody (prefix, cursor, y)).
Qed.

Lemma glibc_slist_clean_merge_M_Hoare :
  forall l1 l2,
    Hoare ATrue
      (glibc_slist_clean_merge_M l1 l2)
      (fun r _ => Permutation r (l1 ++ l2)).
Proof.
  intros l1 l2.
  unfold glibc_slist_clean_merge_M,
    glibc_slist_clean_merge_M_loop_before.
  destruct l1 as [| x xs].
  - prog_nf.
    apply Hoare_ret.
    intros _ _.
    reflexivity.
  - prog_nf.
    eapply Hoare_bind.
    + eapply (@Hoare_cons_pre (early_result MretTy (list Z)) unit
        (fun _ =>
          Permutation (nil ++ (x :: xs) ++ l2) ((x :: xs) ++ l2))
        ATrue
        (glibc_slist_clean_merge_M_loop_aux (nil, x :: xs, l2))
        (fun r _ =>
          match r with
          | Continue ret => Permutation ret ((x :: xs) ++ l2)
          | ReturnNow ret => Permutation ret ((x :: xs) ++ l2)
          end)).
      * intros sigma _.
        simpl.
        reflexivity.
      * apply (glibc_slist_clean_merge_M_loop_aux_Hoare
          nil (x :: xs) l2 ((x :: xs) ++ l2)).
    + intros r.
      destruct r as [ret | ret].
      * unfold glibc_slist_clean_merge_M_after_loop,
          glibc_slist_clean_merge_M_loop_end.
        apply Hoare_ret.
        intros _ Hperm.
        exact Hperm.
      * unfold glibc_slist_clean_merge_M_after_loop.
        apply Hoare_ret.
        intros _ Hperm.
        exact Hperm.
Qed.
