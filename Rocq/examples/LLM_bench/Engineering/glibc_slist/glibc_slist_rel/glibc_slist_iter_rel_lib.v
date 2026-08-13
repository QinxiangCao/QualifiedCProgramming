Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
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

Definition range (l : list Z) : Prop :=
  Zlength l <= 100 /\ Forall (fun x => -100 <= x <= 100) l.

Lemma glibc_slist_clean_iter_sum_step_int_range :
  forall s v,
    -10000 <= s <= 10000 ->
    -100 <= v <= 100 ->
    -2147483648 <= s + v /\ s + v <= 2147483647.
Proof.
  intros; lia.
Qed.

Definition MretTy : Type := (list Z * Z).

(* ---- Abstract program segments for glibc_slist_clean_iter ---- *)

Definition glibc_slist_clean_iter_M_loop_M1 : (list Z * list Z * Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, l2, s) := a in
    return (l1 ++ l2, s).
Definition glibc_slist_clean_iter_M_loop_M2 : (list Z * list Z * Z) -> MONAD (list Z * list Z * Z) :=
  fun a =>
    let '(l1, l2, s) := a in
    match l2 with
    | [] => return (l1, l2, s)
    | v :: l2' =>
        assert (-2147483648 <= s + v /\ s + v <= 2147483647);;
        return (l1 ++ [v], l2', s + v)
    end.

Definition glibc_slist_clean_iter_guardP : (list Z * list Z * Z) -> Prop :=
  fun a =>
    let '(l1, l2, s) := a in
    l2 <> [].

Definition glibc_slist_clean_iter_M_loop_end : MretTy -> MONAD ((list Z * Z)) :=
  fun r => return r.

Definition glibc_slist_clean_iter_M_loop_body : (list Z * list Z * Z) -> MONAD (CntOrBrk (list Z * list Z * Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_iter_guardP a));; r <- glibc_slist_clean_iter_M_loop_M1 a ;; break r)
           (assume!! ((glibc_slist_clean_iter_guardP a));; a' <- glibc_slist_clean_iter_M_loop_M2 a ;; continue a').

Definition glibc_slist_clean_iter_M_loop_aux :=
  repeat_break glibc_slist_clean_iter_M_loop_body.

Definition glibc_slist_clean_iter_M_loop : list Z -> list Z -> Z -> program unit MretTy :=
  fun l1 l2 l3 => glibc_slist_clean_iter_M_loop_aux (l1, l2, l3).

Definition glibc_slist_clean_iter_M_loop_before : list Z -> MONAD (list Z * list Z * Z) :=
  fun l1 => return ([], l1, 0).

Definition glibc_slist_clean_iter_M : list Z -> MONAD ((list Z * Z)) :=
  fun l1 =>
    s0 <- glibc_slist_clean_iter_M_loop_before l1;;
    re <- glibc_slist_clean_iter_M_loop_aux s0;;
    glibc_slist_clean_iter_M_loop_end re.

(* ---- Functional-correctness extension ---- *)

From AUXLib Require Import ListLib.

Fixpoint list_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + list_sum xs
  end.

Lemma list_sum_app :
  forall l1 l2,
    list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma list_sum_singleton :
  forall x,
    list_sum [x] = x.
Proof.
  intros; simpl; lia.
Qed.

Lemma list_sum_range_bound :
  forall l,
    Zlength l <= 100 ->
    Forall (fun x => -100 <= x <= 100) l ->
    -100 * Zlength l <= list_sum l <= 100 * Zlength l.
Proof.
  induction l as [| x xs IH]; intros Hlen Hall.
  - rewrite Zlength_correct. simpl. lia.
  - inversion Hall as [| ? ? Hx Hxs_forall]; subst.
    rewrite Zlength_cons in Hlen.
    assert (Hxs_len : Zlength xs <= 100) by lia.
    assert (Hxs_nonneg : 0 <= Zlength xs) by (rewrite Zlength_correct; lia).
    pose proof (IH Hxs_len Hxs_forall) as Hxs.
    rewrite Zlength_cons.
    unfold Z.succ.
    cbn [list_sum].
    destruct Hx as [Hx_low Hx_high].
    destruct Hxs as [Hxs_low Hxs_high].
    nia.
Qed.

Lemma range_app_prefix_bound :
  forall prefix rest target,
    prefix ++ rest = target ->
    range target ->
    -100 * Zlength prefix <= list_sum prefix <= 100 * Zlength prefix /\
    Zlength prefix <= 100.
Proof.
  intros prefix rest target Htarget [Hlen Hall].
  subst target.
  rewrite Zlength_app in Hlen.
  rewrite Forall_app in Hall.
  destruct Hall as [Hall_prefix _].
  assert (0 <= Zlength rest) by (rewrite Zlength_correct; lia).
  split.
  - apply list_sum_range_bound; auto; lia.
  - lia.
Qed.

Lemma glibc_slist_clean_iter_M_loop_aux_Hoare :
  forall prefix rest s target,
    Hoare
      (fun _ : unit =>
        prefix ++ rest = target /\
        s = list_sum prefix /\
        range target)
      (glibc_slist_clean_iter_M_loop_aux (prefix, rest, s))
      (fun r _ => r = (target, list_sum target)).
Proof.
  intros prefix rest s target.
  pose proof (Hoare_repeat_break glibc_slist_clean_iter_M_loop_body
       (fun a _ =>
          let '(prefix0, rest0, s0) := a in
          prefix0 ++ rest0 = target /\
          s0 = list_sum prefix0 /\
          range target)
       (fun r _ => r = (target, list_sum target))) as Hloop.
  assert (Hbody:
    forall a : list Z * list Z * Z,
      Hoare
        ((fun a _ =>
          let '(prefix0, rest0, s0) := a in
          prefix0 ++ rest0 = target /\
          s0 = list_sum prefix0 /\
          range target) a)
        (glibc_slist_clean_iter_M_loop_body a)
        (fun x _ =>
          match x with
          | by_continue a0 =>
              (let '(prefix0, rest0, s0) := a0 in
               prefix0 ++ rest0 = target /\
               s0 = list_sum prefix0 /\
               range target)
          | by_break b => b = (target, list_sum target)
          end)).
  {
    intros ((prefix0, rest0), s0).
    unfold glibc_slist_clean_iter_M_loop_body,
      glibc_slist_clean_iter_guardP.
    apply Hoare_choice.
    + apply Hoare_assume_bind.
      intros Hnot_guard.
      unfold glibc_slist_clean_iter_M_loop_M1, break.
      destruct rest0 as [| v rest0'].
      * prog_nf.
        apply Hoare_ret.
        intros _ [Hcat [Hs0 Hrange]].
        rewrite app_nil_r in Hcat.
        subst target s0.
        rewrite app_nil_r.
        reflexivity.
      * prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hnot_guard. discriminate.
    + apply Hoare_assume_bind.
      intros Hguard.
      unfold glibc_slist_clean_iter_M_loop_M2, continue.
      destruct rest0 as [| v rest0'].
      * prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hguard. reflexivity.
      * prog_nf.
        apply Hoare_assert_bind.
        -- intros _ [Hcat [Hs0 Hrange]].
           subst s0.
           pose proof (range_app_prefix_bound prefix0 (v :: rest0') target Hcat Hrange)
             as [Hprefix_sum Hprefix_len].
           destruct Hrange as [_ Hall].
           rewrite <- Hcat in Hall.
           rewrite Forall_app in Hall.
           destruct Hall as [_ Hall_tail].
           inversion Hall_tail; subst.
           rename H1 into Hv_bound.
           split.
           ++ pose proof (glibc_slist_clean_iter_sum_step_int_range
                (list_sum prefix0) v ltac:(lia) Hv_bound) as Hstep.
              lia.
           ++ pose proof (glibc_slist_clean_iter_sum_step_int_range
                (list_sum prefix0) v ltac:(lia) Hv_bound) as Hstep.
              lia.
        -- intros _.
           apply Hoare_ret.
           intros _ [Hcat [Hs0 Hrange]].
           split.
           ++ rewrite <- Hcat.
              rewrite <- app_assoc.
              reflexivity.
           ++ split.
              ** subst s0.
                 rewrite list_sum_app.
                 simpl.
                 lia.
              ** exact Hrange.
  }
  exact (Hloop Hbody (prefix, rest, s)).
Qed.

Lemma glibc_slist_clean_iter_M_Hoare :
  forall l1,
    Hoare
      (fun _ : unit => range l1)
      (glibc_slist_clean_iter_M l1)
      (fun r _ => r = (l1, list_sum l1)).
Proof.
  intros l1.
  unfold glibc_slist_clean_iter_M,
    glibc_slist_clean_iter_M_loop_before.
  eapply Hoare_bind with
    (Q := fun st _ =>
      let '(prefix, rest, s) := st in
      prefix ++ rest = l1 /\ s = list_sum prefix /\ range l1).
  - apply Hoare_ret.
    intros sigma Hrange.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * exact Hrange.
  - intros ((prefix, rest), s).
    eapply Hoare_bind.
    + apply glibc_slist_clean_iter_M_loop_aux_Hoare.
    + intros r.
      unfold glibc_slist_clean_iter_M_loop_end.
      apply Hoare_ret.
      intros _ Hr.
      exact Hr.
Qed.
