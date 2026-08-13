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

(* ---- Abstract program segments for glibc_slist_clean_multi_merge ---- *)

Definition glibc_slist_clean_multi_merge_M_loop_M1 : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, l2, l3, l4) := a in
    return (l1 ++ l2).
Definition glibc_slist_clean_multi_merge_M_loop_M2 : (list Z * list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z * list Z) :=
  fun a =>
    let '(l1, l2, l3, l4) := a in
    match l2 with
    | nil => return (l1, l2, l3, l4)
    | cv :: l2' =>
        let insert_after_cursor :=
          fun node l3' l4' =>
            match l2' with
            | nil => return (l1 ++ (cv :: nil), node :: nil, l3', l4')
            | _ => return (l1 ++ (cv :: node :: nil), l2', l3', l4')
            end in
        choice
          (assume!! (l3 <> nil);;
           match l3 with
           | nil => return (l1, l2, l3, l4)
           | node :: l3' => insert_after_cursor node l3' l4
           end)
          (assume!! (l4 <> nil);;
           match l4 with
           | nil => return (l1, l2, l3, l4)
           | node :: l4' => insert_after_cursor node l3 l4'
           end)
    end.

Definition glibc_slist_clean_multi_merge_guardP : (list Z * list Z * list Z * list Z) -> Prop :=
  fun a =>
    let '(l1, l2, l3, l4) := a in
    (l3 <> [] \/ l4 <> []).

Definition glibc_slist_clean_multi_merge_M_loop_end : MretTy -> MONAD (list Z) :=
  fun r => return r.

Definition glibc_slist_clean_multi_merge_M_loop_body : (list Z * list Z * list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z * list Z * list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_multi_merge_guardP a));; r <- glibc_slist_clean_multi_merge_M_loop_M1 a ;; break r)
           (assume!! ((glibc_slist_clean_multi_merge_guardP a));; a' <- glibc_slist_clean_multi_merge_M_loop_M2 a ;; continue a').

Definition glibc_slist_clean_multi_merge_M_loop_aux :=
  repeat_break glibc_slist_clean_multi_merge_M_loop_body.

Definition glibc_slist_clean_multi_merge_M_loop : list Z -> list Z -> list Z -> list Z -> program unit MretTy :=
  fun l1 l2 l3 l4 => glibc_slist_clean_multi_merge_M_loop_aux (l1, l2, l3, l4).

Definition glibc_slist_clean_multi_merge_M_loop_before : list Z -> list Z -> list Z -> MONAD (early_result (list Z * list Z * list Z * list Z) (list Z)) :=
  fun l1 l2 l3 =>
    match l1 with
    | nil =>
        match l2 with
        | nil => return (ReturnNow l3)
        | _ => return (Continue (nil, l2, nil, l3))
        end
    | _ => return (Continue (nil, l1, l2, l3))
    end.

Definition glibc_slist_clean_multi_merge_M : list Z -> list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 l3 =>
    e <- glibc_slist_clean_multi_merge_M_loop_before l1 l2 l3;;
    match e with
    | Continue s =>
        re <- glibc_slist_clean_multi_merge_M_loop_aux s;;
        glibc_slist_clean_multi_merge_M_loop_end re
    | ReturnNow r =>
        return r
    end.

(* ---- Functional-correctness extension ---- *)

Require Import Coq.Sorting.Permutation.

Ltac glibc_slist_clean_multi_merge_perm :=
  repeat rewrite app_assoc;
  simpl;
  try reflexivity;
  repeat constructor.

Lemma glibc_slist_clean_multi_merge_insert_y_perm :
  forall (prefix cursor_tail y_tail z_tail target : list Z) (cursor node : Z),
    Permutation
      (prefix ++ cursor :: cursor_tail ++ node :: y_tail ++ z_tail)
      target ->
    Permutation
      ((match cursor_tail with
        | [] => prefix ++ [cursor]
        | _ => prefix ++ [cursor; node]
        end) ++
       (match cursor_tail with
        | [] => [node]
        | _ => cursor_tail
        end) ++ y_tail ++ z_tail)
      target.
Proof.
  intros prefix cursor_tail y_tail z_tail target cursor node Hperm.
  destruct cursor_tail as [| next cursor_tail].
  - simpl in *.
    eapply Permutation_trans; [| exact Hperm].
    repeat rewrite <- app_assoc.
    reflexivity.
  - eapply Permutation_trans; [| exact Hperm].
    repeat rewrite <- app_assoc.
    simpl.
    apply Permutation_app_head.
    apply perm_skip.
    replace (node :: next :: cursor_tail ++ y_tail ++ z_tail)
      with (node :: (next :: cursor_tail) ++ (y_tail ++ z_tail))
      by reflexivity.
    replace (next :: cursor_tail ++ node :: y_tail ++ z_tail)
      with ((next :: cursor_tail) ++ node :: (y_tail ++ z_tail))
      by (repeat rewrite <- app_assoc; reflexivity).
    apply Permutation_middle.
Qed.

Lemma glibc_slist_clean_multi_merge_insert_z_perm :
  forall (prefix cursor_tail y_tail z_tail target : list Z) (cursor node : Z),
    Permutation
      (prefix ++ cursor :: cursor_tail ++ y_tail ++ node :: z_tail)
      target ->
    Permutation
      ((match cursor_tail with
        | [] => prefix ++ [cursor]
        | _ => prefix ++ [cursor; node]
        end) ++
       (match cursor_tail with
        | [] => [node]
        | _ => cursor_tail
        end) ++ y_tail ++ z_tail)
      target.
Proof.
  intros prefix cursor_tail y_tail z_tail target cursor node Hperm.
  destruct cursor_tail as [| next cursor_tail].
  - simpl in *.
    eapply Permutation_trans; [| exact Hperm].
    repeat rewrite <- app_assoc.
    simpl.
    apply Permutation_app_head.
    apply perm_skip.
    apply Permutation_middle.
  - eapply Permutation_trans; [| exact Hperm].
    repeat rewrite <- app_assoc.
    simpl.
    apply Permutation_app_head.
    apply perm_skip.
    replace (node :: next :: cursor_tail ++ y_tail ++ z_tail)
      with (node :: ((next :: cursor_tail) ++ y_tail) ++ z_tail)
      by (repeat rewrite <- app_assoc; reflexivity).
    replace (next :: cursor_tail ++ y_tail ++ node :: z_tail)
      with (((next :: cursor_tail) ++ y_tail) ++ node :: z_tail)
      by (repeat rewrite <- app_assoc; reflexivity).
    apply Permutation_middle.
Qed.

Lemma glibc_slist_clean_multi_merge_M_loop_aux_Hoare :
  forall (prefix cursor y z target : list Z),
    Hoare
      (fun _ : unit =>
         Permutation (prefix ++ cursor ++ y ++ z) target)
      (glibc_slist_clean_multi_merge_M_loop_aux
         (prefix, cursor, y, z))
      (fun r _ => Permutation r target).
Proof.
  intros prefix cursor y z target.
  pose proof (Hoare_repeat_break
    glibc_slist_clean_multi_merge_M_loop_body
    (fun a _ =>
       let '(prefix0, cursor0, y0, z0) := a in
       Permutation (prefix0 ++ cursor0 ++ y0 ++ z0) target)
    (fun r _ => Permutation r target)) as Hloop.
  assert (Hbody:
    forall a : list Z * list Z * list Z * list Z,
      Hoare
        ((fun a _ =>
           let '(prefix0, cursor0, y0, z0) := a in
           Permutation (prefix0 ++ cursor0 ++ y0 ++ z0) target) a)
        (glibc_slist_clean_multi_merge_M_loop_body a)
        (fun x _ =>
           match x with
           | by_continue a0 =>
               let '(prefix0, cursor0, y0, z0) := a0 in
               Permutation (prefix0 ++ cursor0 ++ y0 ++ z0) target
           | by_break r => Permutation r target
           end)).
  {
    intros (((prefix0, cursor0), y0), z0).
    unfold glibc_slist_clean_multi_merge_M_loop_body,
      glibc_slist_clean_multi_merge_guardP.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      intro Hnot_guard.
      unfold glibc_slist_clean_multi_merge_M_loop_M1, break.
      prog_nf.
      apply Hoare_ret.
      intros _ Hpre.
      destruct y0 as [| yh yt]; [| exfalso; apply Hnot_guard; left; discriminate].
      destruct z0 as [| zh zt]; [| exfalso; apply Hnot_guard; right; discriminate].
      simpl in Hpre.
      repeat rewrite app_nil_r in Hpre.
      exact Hpre.
    - apply Hoare_assume_bind.
      intro Hguard.
      unfold glibc_slist_clean_multi_merge_M_loop_M2, continue.
      destruct cursor0 as [| cur cursor_tail].
      + prog_nf.
        apply Hoare_ret.
        intros _ Hpre.
        exact Hpre.
      + prog_nf.
        apply Hoare_choice.
        * apply Hoare_assume_bind.
          intro Hy.
          destruct y0 as [| node y_tail].
          -- exfalso. apply Hy. reflexivity.
          -- destruct cursor_tail as [| next cursor_tail].
             ++ prog_nf.
                apply Hoare_ret.
                intros _ Hpre.
                eapply (glibc_slist_clean_multi_merge_insert_y_perm
                  prefix0 nil y_tail z0 target cur node).
                exact Hpre.
             ++ prog_nf.
                apply Hoare_ret.
                intros _ Hpre.
                eapply (glibc_slist_clean_multi_merge_insert_y_perm
                  prefix0 (next :: cursor_tail) y_tail z0 target cur node).
                exact Hpre.
        * apply Hoare_assume_bind.
          intro Hz.
          destruct z0 as [| node z_tail].
          -- exfalso. apply Hz. reflexivity.
          -- destruct cursor_tail as [| next cursor_tail].
             ++ prog_nf.
                apply Hoare_ret.
                intros _ Hpre.
                eapply (glibc_slist_clean_multi_merge_insert_z_perm
                  prefix0 nil y0 z_tail target cur node).
                exact Hpre.
             ++ prog_nf.
                apply Hoare_ret.
                intros _ Hpre.
                eapply (glibc_slist_clean_multi_merge_insert_z_perm
                  prefix0 (next :: cursor_tail) y0 z_tail target cur node).
                exact Hpre.
  }
  exact (Hloop Hbody (prefix, cursor, y, z)).
Qed.

Lemma glibc_slist_clean_multi_merge_M_Hoare :
  forall l1 l2 l3,
    Hoare ATrue
      (glibc_slist_clean_multi_merge_M l1 l2 l3)
      (fun r _ => Permutation r ((l1 ++ l2) ++ l3)).
Proof.
  intros l1 l2 l3.
  unfold glibc_slist_clean_multi_merge_M,
    glibc_slist_clean_multi_merge_M_loop_before.
  destruct l1 as [| x xs].
  - destruct l2 as [| y ys].
    + prog_nf.
      apply Hoare_ret.
      intros _ _.
      reflexivity.
    + prog_nf.
      eapply (@Hoare_cons_pre MretTy unit
        (fun _ =>
          Permutation (nil ++ (y :: ys) ++ nil ++ l3)
            ((y :: ys) ++ l3))
        ATrue
        (glibc_slist_clean_multi_merge_M_loop_aux
          (nil, y :: ys, nil, l3))
        (fun r _ => Permutation r ((y :: ys) ++ l3))).
      * intros sigma _.
        simpl.
        apply Permutation_refl.
      * apply (glibc_slist_clean_multi_merge_M_loop_aux_Hoare
          nil (y :: ys) nil l3 ((y :: ys) ++ l3)).
  - prog_nf.
    eapply (@Hoare_cons_pre MretTy unit
      (fun _ =>
        Permutation (nil ++ (x :: xs) ++ l2 ++ l3)
          (((x :: xs) ++ l2) ++ l3))
      ATrue
      (glibc_slist_clean_multi_merge_M_loop_aux
        (nil, x :: xs, l2, l3))
      (fun r _ => Permutation r (((x :: xs) ++ l2) ++ l3))).
    + intros sigma _.
      simpl.
      rewrite <- app_assoc.
      apply Permutation_refl.
    + apply (glibc_slist_clean_multi_merge_M_loop_aux_Hoare
        nil (x :: xs) l2 l3 (((x :: xs) ++ l2) ++ l3)).
Qed.
