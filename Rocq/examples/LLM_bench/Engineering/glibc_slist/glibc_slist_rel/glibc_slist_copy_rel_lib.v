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

Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).

Definition MretTy : Type := (list Z * list Z)%type.

Inductive early_result (S Ret : Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
Arguments Continue {S Ret} _.
Arguments ReturnNow {S Ret} _.

(* ---- Abstract program segments for glibc_slist_clean_copy ---- *)

Definition glibc_slist_clean_copy_M_loop_M1 : (list Z * list Z * list Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, l2, l3) := a in
    return (l1 ++ l2, l3).
Definition glibc_slist_clean_copy_M_loop_M2 : (list Z * list Z * list Z) -> MONAD (early_result (list Z * list Z * list Z) (list Z * list Z)) :=
  fun a =>
    let '(l1, l2, l3) := a in
    match l2 with
    | nil => return (Continue (l1, l2, l3))
    | v :: l2' =>
        choice (return (ReturnNow (l1 ++ l2, nil)))
               (r <- list_append_raw_M l3 (v :: nil);;
                return (Continue (l1 ++ (v :: nil), l2', r)))
    end.

Definition glibc_slist_clean_copy_guardP : (list Z * list Z * list Z) -> Prop :=
  fun a =>
    let '(l1, l2, l3) := a in
    l2 <> [].

Definition glibc_slist_clean_copy_M_loop_end : MretTy -> MONAD ((list Z * list Z)) :=
  fun r => return r.

Definition glibc_slist_clean_copy_M_after_loop : (early_result MretTy (list Z * list Z)) -> MONAD ((list Z * list Z)) :=
  fun re =>
    match re with
    | Continue r => glibc_slist_clean_copy_M_loop_end r
    | ReturnNow r => return r
    end.

Definition glibc_slist_clean_copy_M_loop_body : (list Z * list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z * list Z) (early_result MretTy (list Z * list Z))) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_copy_guardP a));; r <- glibc_slist_clean_copy_M_loop_M1 a ;; break (Continue r))
           (assume!! ((glibc_slist_clean_copy_guardP a));;
            a' <- glibc_slist_clean_copy_M_loop_M2 a ;;
            match a' with
            | Continue a'' => continue a''
            | ReturnNow r' => break (ReturnNow r')
            end).

Definition glibc_slist_clean_copy_M_loop_aux :=
  repeat_break glibc_slist_clean_copy_M_loop_body.

Definition glibc_slist_clean_copy_M_loop : list Z -> list Z -> list Z -> program unit (early_result MretTy (list Z * list Z)) :=
  fun l1 l2 l3 => glibc_slist_clean_copy_M_loop_aux (l1, l2, l3).

Definition glibc_slist_clean_copy_M_loop_before : list Z -> MONAD (list Z * list Z * list Z) :=
  fun l1 => return (nil, l1, nil).

Definition glibc_slist_clean_copy_M : list Z -> MONAD ((list Z * list Z)) :=
  fun l1 =>
    s0 <- glibc_slist_clean_copy_M_loop_before l1;;
    re <- glibc_slist_clean_copy_M_loop_aux s0;;
    glibc_slist_clean_copy_M_after_loop re.

Definition residual_prog_in_glibc_slist_clean_copy_M_call_1 (l1 : list Z) (v : Z) (l2' : list Z) : list Z -> MONAD (list Z * list Z) :=
  fun r =>
    step <- match (Continue (l1 ++ (v :: nil), l2', r)) with
| Continue a'' => continue a''
| ReturnNow r' => break (ReturnNow r')
end;;
re <- match step with
| by_continue a' => repeat_break glibc_slist_clean_copy_M_loop_body a'
| by_break b => ret b
end;;
glibc_slist_clean_copy_M_after_loop re.

(* ---- Functional-correctness extension ---- *)

Definition glibc_slist_clean_copy_result (src copied : list Z) : Prop :=
  copied = src \/ copied = nil.

Lemma glibc_slist_clean_copy_M_loop_aux_Hoare :
  forall (prefix rest copied src : list Z),
    Hoare
      (fun _ : unit => prefix ++ rest = src /\ copied = prefix)
      (glibc_slist_clean_copy_M_loop_aux (prefix, rest, copied))
      (fun r _ =>
        match r with
        | Continue (src_ret, copied_ret)
        | ReturnNow (src_ret, copied_ret) =>
            src_ret = src /\
            glibc_slist_clean_copy_result src copied_ret
        end).
Proof.
  intros prefix rest copied src.
  pose proof (Hoare_repeat_break
    glibc_slist_clean_copy_M_loop_body
    (fun a _ =>
       let '(prefix0, rest0, copied0) := a in
       prefix0 ++ rest0 = src /\ copied0 = prefix0)
    (fun r _ =>
       match r with
       | Continue (src_ret, copied_ret)
       | ReturnNow (src_ret, copied_ret) =>
           src_ret = src /\
           glibc_slist_clean_copy_result src copied_ret
       end)) as Hloop.
  assert (Hbody:
    forall a : list Z * list Z * list Z,
      Hoare
        ((fun a _ =>
           let '(prefix0, rest0, copied0) := a in
           prefix0 ++ rest0 = src /\ copied0 = prefix0) a)
        (glibc_slist_clean_copy_M_loop_body a)
        (fun x _ =>
           match x with
           | by_continue a0 =>
               let '(prefix0, rest0, copied0) := a0 in
               prefix0 ++ rest0 = src /\ copied0 = prefix0
           | by_break r =>
               match r with
               | Continue (src_ret, copied_ret)
               | ReturnNow (src_ret, copied_ret) =>
                   src_ret = src /\
                   glibc_slist_clean_copy_result src copied_ret
               end
           end)).
  {
    intros ((prefix0, rest0), copied0).
    unfold glibc_slist_clean_copy_M_loop_body,
      glibc_slist_clean_copy_guardP.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      intro Hnot_guard.
      unfold glibc_slist_clean_copy_M_loop_M1, break.
      destruct rest0 as [| v rest_tail].
      + prog_nf.
        apply Hoare_ret.
        intros _ [Hsrc Hcopied].
        split.
        * exact Hsrc.
        * unfold glibc_slist_clean_copy_result.
          left.
          rewrite app_nil_r in Hsrc.
          rewrite Hcopied.
          exact Hsrc.
      + prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hnot_guard. discriminate.
    - apply Hoare_assume_bind.
      intro Hguard.
      unfold glibc_slist_clean_copy_M_loop_M2, continue, break.
      destruct rest0 as [| v rest_tail].
      + prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hguard. reflexivity.
      + eapply Hoare_bind with
          (Q := fun a' _ =>
            match a' with
            | Continue (prefix1, rest1, copied1) =>
                prefix1 ++ rest1 = src /\ copied1 = prefix1
            | ReturnNow (src_ret, copied_ret) =>
                src_ret = src /\
                glibc_slist_clean_copy_result src copied_ret
            end).
        * apply Hoare_choice.
          -- prog_nf.
             apply Hoare_ret.
             intros _ [Hsrc _].
             split.
             ++ exact Hsrc.
             ++ unfold glibc_slist_clean_copy_result.
                right.
                reflexivity.
          -- eapply Hoare_bind with
              (Q := fun r _ =>
                r = copied0 ++ v :: nil /\
                prefix0 ++ v :: rest_tail = src /\
                copied0 = prefix0).
             ++ apply Hoare_unit_pre.
                intro Hpre.
                eapply Hoare_cons_post.
                ** intros r sigma Hr.
                   split; [exact Hr | exact Hpre].
                ** apply list_append_raw_M_Hoare.
             ++ intro r.
                apply Hoare_ret.
                intros _ [Happend [Hsrc Hcopied]].
                subst r copied0.
                split.
                ** rewrite <- app_assoc.
                   simpl.
                   exact Hsrc.
                ** reflexivity.
        * intro a'.
          destruct a' as [((prefix1, rest1), copied1)
                         | (src_ret, copied_ret)];
            unfold continue, break; prog_nf; apply Hoare_ret;
            intros _ Hpost; exact Hpost.
  }
  exact (Hloop Hbody (prefix, rest, copied)).
Qed.

Lemma glibc_slist_clean_copy_M_Hoare :
  forall src,
    Hoare ATrue
      (glibc_slist_clean_copy_M src)
      (fun r _ =>
        let '(src_ret, copied_ret) := r in
        src_ret = src /\ glibc_slist_clean_copy_result src copied_ret).
Proof.
  intro src.
  unfold glibc_slist_clean_copy_M,
    glibc_slist_clean_copy_M_loop_before.
  eapply Hoare_bind with
    (Q := fun s _ =>
      let '(prefix, rest, copied) := s in
      prefix ++ rest = src /\ copied = prefix).
  - apply Hoare_ret.
    intros _ _.
    simpl.
    split; reflexivity.
  - intros s.
    destruct s as ((prefix, rest), copied).
    simpl.
    eapply Hoare_bind.
    + apply glibc_slist_clean_copy_M_loop_aux_Hoare.
    + intros r.
      destruct r as [[src_ret copied_ret] | [src_ret copied_ret]];
        unfold glibc_slist_clean_copy_M_after_loop,
          glibc_slist_clean_copy_M_loop_end.
      * apply Hoare_ret.
        intros _ Hret.
        exact Hret.
      * apply Hoare_ret.
        intros _ Hret.
        exact Hret.
Qed.
