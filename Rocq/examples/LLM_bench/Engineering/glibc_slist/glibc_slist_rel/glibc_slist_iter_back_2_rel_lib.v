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

Definition glibc_slist_clean_iter_back_2_prev_case
  (p : Z) (lpre : list Z) (node x : Z) : Prop :=
  p = 0 -> lpre = nil /\ node = x.

Lemma glibc_slist_clean_iter_back_2_sum_step_int_range :
  forall s v,
    -10000 <= s <= 10000 ->
    -100 <= v <= 100 ->
    -2147483648 <= s + v /\ s + v <= 2147483647.
Proof.
  intros; lia.
Qed.

Definition MretTy : Type := (list Z * Z)%type.

(* ---- Abstract program segments for glibc_slist_clean_iter_back_2 (loop forest: 2 loops, 1 top-level) ---- *)

Definition glibc_slist_clean_iter_back_2_M_loop2_M1 : (list Z * Z) -> MONAD MretTy :=
  fun a =>
    let '(l1, s) := a in
    match l1 with
    | [] => return a
    | v :: _ =>
        assert (-2147483648 <= s + v /\ s + v <= 2147483647);;
        return a
    end.
Definition glibc_slist_clean_iter_back_2_M_loop2_M2 : (list Z * Z) -> MONAD (list Z * Z) :=
  fun a =>
    let '(l1, s) := a in
    match l1 with
    | [] => return ([], s)
    | _ :: l1' => return (l1', s)
    end.
(* Guard could not be generated — declare as Parameter *)
Definition glibc_slist_clean_iter_back_2_loop2_guardP : (list Z * Z) -> Prop :=
  fun a =>
    let '(l1, _) := a in
    match l1 with
    | _ :: _ :: _ => True
    | _ => False
    end.
Definition glibc_slist_clean_iter_back_2_M_loop2_body : (list Z * Z) -> MONAD (CntOrBrk (list Z * Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_iter_back_2_loop2_guardP a));; r <- glibc_slist_clean_iter_back_2_M_loop2_M1 a ;; break r)
           (assume!! ((glibc_slist_clean_iter_back_2_loop2_guardP a));; a' <- glibc_slist_clean_iter_back_2_M_loop2_M2 a ;; continue a').
Definition glibc_slist_clean_iter_back_2_M_loop2_aux := repeat_break glibc_slist_clean_iter_back_2_M_loop2_body.
Definition glibc_slist_clean_iter_back_2_M_loop2 : list Z -> Z -> program unit MretTy :=
  fun l1 l2 => glibc_slist_clean_iter_back_2_M_loop2_aux (l1, l2).

Definition glibc_slist_clean_iter_back_2_M_loop1_M1 : (list Z * Z) -> MONAD MretTy :=
  fun a => return a.
Definition glibc_slist_clean_iter_back_2_M_loop1_to_inner_2 : (list Z * Z) -> MONAD (list Z * Z) :=
  fun a => return a.
Definition glibc_slist_clean_iter_back_2_M_loop1_after_inner_2 : (list Z * Z) -> MretTy -> MONAD (list Z * Z) :=
  fun a r =>
    let '(l1, s) := a in
    let '(node_l, _) := r in
    let fix front_and_last (l : list Z) : list Z * Z :=
        match l with
        | [] => ([], 0)
        | v :: [] => ([], v)
        | v :: l' =>
            let '(front, last) := front_and_last l' in
            (v :: front, last)
        end in
    let '(front, last_from_state) := front_and_last l1 in
    match node_l with
    | v :: _ =>
        assert (-2147483648 <= s + v /\ s + v <= 2147483647);;
        return (front, s + v)
    | [] =>
        assert (-2147483648 <= s + last_from_state /\ s + last_from_state <= 2147483647);;
        return (front, s + last_from_state)
    end.
Definition glibc_slist_clean_iter_back_2_M_loop1_M2 : (list Z * Z) -> MONAD (list Z * Z) :=
  fun a =>
    s' <- glibc_slist_clean_iter_back_2_M_loop1_to_inner_2 a;;
    r  <- glibc_slist_clean_iter_back_2_M_loop2_aux s';;
    glibc_slist_clean_iter_back_2_M_loop1_after_inner_2 a r.
(* Guard could not be generated — declare as Parameter *)
Definition glibc_slist_clean_iter_back_2_loop1_guardP : (list Z * Z) -> Prop :=
  fun a =>
    let '(l1, _) := a in
    l1 <> [].
Definition glibc_slist_clean_iter_back_2_M_loop1_body : (list Z * Z) -> MONAD (CntOrBrk (list Z * Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (glibc_slist_clean_iter_back_2_loop1_guardP a));; r <- glibc_slist_clean_iter_back_2_M_loop1_M1 a ;; break r)
           (assume!! ((glibc_slist_clean_iter_back_2_loop1_guardP a));; a' <- glibc_slist_clean_iter_back_2_M_loop1_M2 a ;; continue a').
Definition glibc_slist_clean_iter_back_2_M_loop1_aux := repeat_break glibc_slist_clean_iter_back_2_M_loop1_body.
Definition glibc_slist_clean_iter_back_2_M_loop1 : list Z -> Z -> program unit MretTy :=
  fun l1 l2 => glibc_slist_clean_iter_back_2_M_loop1_aux (l1, l2).

Definition glibc_slist_clean_iter_back_2_M_loop1_before : list Z -> MONAD (list Z * Z) :=
  fun l1 => return (l1, 0).
Definition glibc_slist_clean_iter_back_2_M_loop1_end : list Z -> MretTy -> MONAD ((list Z * Z)) :=
  fun lorig r =>
    let '(_, s) := r in
    return (lorig, s).

Definition glibc_slist_clean_iter_back_2_M_loop2_cont : list Z -> list Z -> Z -> MretTy -> MONAD ((list Z * Z)) :=
  fun lorig l1 s r =>
    a' <- glibc_slist_clean_iter_back_2_M_loop1_after_inner_2 (l1, s) r;;
    r1 <- glibc_slist_clean_iter_back_2_M_loop1_aux a';;
    glibc_slist_clean_iter_back_2_M_loop1_end lorig r1.

Definition glibc_slist_clean_iter_back_2_M : list Z -> MONAD ((list Z * Z)) :=
  fun l1 =>
    s1 <- glibc_slist_clean_iter_back_2_M_loop1_before l1;;
    r1 <- glibc_slist_clean_iter_back_2_M_loop1_aux s1;;
    glibc_slist_clean_iter_back_2_M_loop1_end l1 r1.

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
    pose proof (IH Hxs_len Hxs_forall) as Hxs.
    rewrite Zlength_cons.
    unfold Z.succ.
    cbn [list_sum].
    destruct Hx as [Hx_low Hx_high].
    destruct Hxs as [Hxs_low Hxs_high].
    nia.
Qed.

Lemma range_app_right :
  forall prefix rest target,
    prefix ++ rest = target ->
    range target ->
    range rest.
Proof.
  intros prefix rest target Htarget [Hlen Hall].
  subst target.
  rewrite Zlength_app in Hlen.
  rewrite Forall_app in Hall.
  destruct Hall as [_ Hall_rest].
  split.
  - pose proof (Zlength_nonneg prefix). lia.
  - exact Hall_rest.
Qed.

Lemma range_app_last :
  forall prefix last suffix target,
    (prefix ++ last :: suffix)%list = target ->
    range target ->
    -100 <= last <= 100.
Proof.
  intros prefix last suffix target Htarget Hrange.
  pose proof (range_app_right prefix (last :: suffix) target Htarget Hrange)
    as [_ Hall].
  inversion Hall; subst; auto.
Qed.

Lemma sum_suffix_bound :
  forall prefix suffix target,
    prefix ++ suffix = target ->
    range target ->
    -10000 <= list_sum suffix <= 10000.
Proof.
  intros prefix suffix target Htarget Hrange.
  pose proof (range_app_right prefix suffix target Htarget Hrange)
    as [Hlen Hall].
  pose proof (list_sum_range_bound suffix Hlen Hall).
  pose proof (Zlength_nonneg suffix).
  lia.
Qed.

Lemma nonempty_last_decomp :
  forall (l : list Z),
    l <> [] ->
    exists prefix last, l = prefix ++ [last].
Proof.
  induction l as [| x xs IH]; intros Hnonempty.
  - contradiction.
  - destruct xs as [| y ys].
    + exists [], x. reflexivity.
    + assert (Htail : y :: ys <> []) by discriminate.
      destruct (IH Htail) as [prefix [last Hdecomp]].
      exists (x :: prefix), last.
      simpl. f_equal. exact Hdecomp.
Qed.

Lemma app_singleton_cons :
  forall (prefix suffix : list Z) (last : Z),
    prefix ++ last :: suffix = (prefix ++ [last]) ++ suffix.
Proof.
  induction prefix as [| x xs IH]; intros suffix last; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma front_and_last_app_singleton :
  forall (prefix : list Z) (last : Z),
    (fix front_and_last (l : list Z) : list Z * Z :=
       match l with
       | [] => ([], 0)
       | v :: [] => ([], v)
       | v :: l' =>
           let '(front, last0) := front_and_last l' in
           (v :: front, last0)
       end) (prefix ++ [last]) = (prefix, last).
Proof.
  induction prefix as [| x xs IH]; intros last; simpl.
  - reflexivity.
  - destruct xs as [| y ys].
    + reflexivity.
    + rewrite (IH last). reflexivity.
Qed.

Lemma glibc_slist_clean_iter_back_2_M_loop2_aux_last_Hoare :
  forall prefix last s,
    -10000 <= s <= 10000 ->
    -100 <= last <= 100 ->
    Hoare ATrue
      (glibc_slist_clean_iter_back_2_M_loop2_aux (prefix ++ [last], s))
      (fun r _ => r = ([last], s)).
Proof.
  intros prefix last s Hs Hlast.
  pose proof (Hoare_repeat_break glibc_slist_clean_iter_back_2_M_loop2_body
       (fun a _ =>
          let '(cur, s0) := a in
          s0 = s /\ exists prefix0, cur = prefix0 ++ [last])
       (fun r _ => r = ([last], s))) as Hloop.
  assert (Hbody:
    forall a : list Z * Z,
      Hoare
        ((fun a _ =>
          let '(cur, s0) := a in
          s0 = s /\ exists prefix0, cur = prefix0 ++ [last]) a)
        (glibc_slist_clean_iter_back_2_M_loop2_body a)
        (fun x _ =>
          match x with
          | by_continue a0 =>
              let '(cur, s0) := a0 in
              s0 = s /\ exists prefix0, cur = prefix0 ++ [last]
          | by_break b => b = ([last], s)
          end)).
  {
    intros (cur, s0).
    unfold glibc_slist_clean_iter_back_2_M_loop2_body,
      glibc_slist_clean_iter_back_2_loop2_guardP.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      intros Hnot_guard.
      unfold glibc_slist_clean_iter_back_2_M_loop2_M1, break.
      destruct cur as [| v rest].
      + prog_nf.
        apply Hoare_ret.
        intros _ [_ [prefix0 Hcur]].
        destruct prefix0; discriminate.
      + destruct rest as [| w rest'].
        * prog_nf.
          apply Hoare_assert_bind.
          -- intros _ [Hs0 [prefix0 Hcur]].
             subst s0.
             destruct prefix0 as [| p ps].
             ++ simpl in Hcur. inversion Hcur; subst v.
                pose proof (glibc_slist_clean_iter_back_2_sum_step_int_range
                  s last Hs Hlast) as Hstep.
                exact Hstep.
             ++ simpl in Hcur.
                destruct ps; discriminate.
          -- intros _.
             apply Hoare_ret.
             intros _ [Hs0 [prefix0 Hcur]].
             subst s0.
             destruct prefix0 as [| p ps].
             ++ simpl in Hcur. inversion Hcur; reflexivity.
             ++ simpl in Hcur.
                destruct ps; discriminate.
        * prog_nf.
          apply Hoare_assert_bind.
          -- intros _ _.
             exfalso. apply Hnot_guard. simpl. exact I.
          -- intros _.
             apply Hoare_ret.
             intros _ _.
             exfalso. apply Hnot_guard. simpl. exact I.
    - apply Hoare_assume_bind.
      intros Hguard.
      unfold glibc_slist_clean_iter_back_2_M_loop2_M2, continue.
      destruct cur as [| v rest].
      + prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. exact Hguard.
      + destruct rest as [| w rest'].
        * prog_nf.
          apply Hoare_ret.
          intros _ _.
          exfalso. exact Hguard.
        * prog_nf.
          apply Hoare_ret.
          intros _ [Hs0 [prefix0 Hcur]].
          subst s0.
          split; [reflexivity |].
          destruct prefix0 as [| p ps].
          -- simpl in Hcur. discriminate.
          -- simpl in Hcur. inversion Hcur; subst.
             exists ps. exact H1.
  }
  eapply (@Hoare_cons_pre MretTy unit
    (fun _ : unit =>
      s = s /\ exists prefix0 : list Z, prefix ++ [last] = prefix0 ++ [last])
    ATrue).
  - intros sigma Htrue. split; [reflexivity | exists prefix; reflexivity].
  - exact (Hloop Hbody (prefix ++ [last], s)).
Qed.

Lemma glibc_slist_clean_iter_back_2_M_loop1_M2_Hoare :
  forall rest s target done,
    rest <> [] ->
    rest ++ done = target ->
    s = list_sum done ->
    range target ->
    Hoare ATrue
      (glibc_slist_clean_iter_back_2_M_loop1_M2 (rest, s))
      (fun a _ =>
         let '(rest', s') := a in
         exists done',
           rest' ++ done' = target /\
           s' = list_sum done' /\
           range target).
Proof.
  intros rest s target done Hnonempty Htarget Hs Hrange.
  destruct (nonempty_last_decomp rest Hnonempty) as [front [last Hrest]].
  subst rest.
  unfold glibc_slist_clean_iter_back_2_M_loop1_M2,
    glibc_slist_clean_iter_back_2_M_loop1_to_inner_2.
  prog_nf.
  eapply Hoare_bind with (Q := fun r _ => r = ([last], s)).
	  - apply glibc_slist_clean_iter_back_2_M_loop2_aux_last_Hoare.
	    + subst s.
	      eapply sum_suffix_bound with (prefix := front ++ [last]) (target := target).
	      * exact Htarget.
      * exact Hrange.
	    + eapply range_app_last with
	        (prefix := front) (suffix := done) (target := target).
	      * replace (front ++ last :: done) with ((front ++ [last]) ++ done).
	        -- exact Htarget.
	        -- symmetry. apply app_singleton_cons.
      * exact Hrange.
  - intros (node_l, sum0).
    unfold glibc_slist_clean_iter_back_2_M_loop1_after_inner_2.
    destruct node_l as [| rv rtail].
    + rewrite front_and_last_app_singleton.
      apply Hoare_assert_bind.
      * intros _ Hr. inversion Hr.
      * intros _.
        apply Hoare_ret.
        intros _ Hr. inversion Hr.
    + rewrite front_and_last_app_singleton.
      apply Hoare_assert_bind.
      * intros _ Hr.
        inversion Hr; subst rv rtail sum0.
        subst s.
        pose proof (sum_suffix_bound (front ++ [last]) done target
          Htarget Hrange) as Hsum.
        pose proof (range_app_last front last done target
          ltac:(replace (front ++ last :: done) with ((front ++ [last]) ++ done);
                [exact Htarget | symmetry; apply app_singleton_cons]) Hrange) as Hlast.
        pose proof (glibc_slist_clean_iter_back_2_sum_step_int_range
          (list_sum done) last Hsum Hlast) as Hstep.
        exact Hstep.
      * intros _.
        apply Hoare_ret.
        intros _ Hr.
        inversion Hr; subst rv rtail sum0.
        exists (last :: done).
        split.
        -- replace (front ++ last :: done) with ((front ++ [last]) ++ done).
           ++ exact Htarget.
           ++ symmetry. apply app_singleton_cons.
        -- split.
           ++ subst s. simpl. lia.
           ++ exact Hrange.
Qed.

Lemma glibc_slist_clean_iter_back_2_M_loop1_aux_Hoare :
  forall rest s target,
    Hoare
      (fun _ : unit =>
        exists done,
          rest ++ done = target /\
          s = list_sum done /\
          range target)
      (glibc_slist_clean_iter_back_2_M_loop1_aux (rest, s))
      (fun r _ => r = ([], list_sum target)).
Proof.
  intros rest s target.
  pose proof (Hoare_repeat_break glibc_slist_clean_iter_back_2_M_loop1_body
       (fun a _ =>
          let '(rest0, s0) := a in
          exists done,
            rest0 ++ done = target /\
            s0 = list_sum done /\
            range target)
       (fun r _ => r = ([], list_sum target))) as Hloop.
  assert (Hbody:
    forall a : list Z * Z,
      Hoare
        ((fun a _ =>
          let '(rest0, s0) := a in
          exists done,
            rest0 ++ done = target /\
            s0 = list_sum done /\
            range target) a)
        (glibc_slist_clean_iter_back_2_M_loop1_body a)
        (fun x _ =>
          match x with
          | by_continue a0 =>
              let '(rest0, s0) := a0 in
              exists done,
                rest0 ++ done = target /\
                s0 = list_sum done /\
                range target
          | by_break b => b = ([], list_sum target)
          end)).
  {
    intros (rest0, s0).
    unfold glibc_slist_clean_iter_back_2_M_loop1_body,
      glibc_slist_clean_iter_back_2_loop1_guardP.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      intros Hnot_guard.
      unfold glibc_slist_clean_iter_back_2_M_loop1_M1, break.
      destruct rest0 as [| v rest0'].
      + prog_nf.
        apply Hoare_ret.
        intros _ [done [Htarget [Hs0 _]]].
        simpl in Htarget.
        subst done s0.
        reflexivity.
      + prog_nf.
        apply Hoare_ret.
        intros _ _.
        exfalso. apply Hnot_guard. discriminate.
    - apply Hoare_assume_bind.
      intros Hguard.
      unfold continue.
      destruct rest0 as [| v rest0'].
      + exfalso. apply Hguard. reflexivity.
      + apply Hoare_unit_pre.
        intros [done [Htarget [Hs0 Hrange]]].
        eapply Hoare_bind with
          (Q := fun a _ =>
             let '(rest1, s1) := a in
             exists done',
               rest1 ++ done' = target /\
               s1 = list_sum done' /\
               range target).
        * eapply glibc_slist_clean_iter_back_2_M_loop1_M2_Hoare.
          -- discriminate.
          -- exact Htarget.
          -- exact Hs0.
          -- exact Hrange.
        * intros a. apply Hoare_ret.
          intros _ Ha. exact Ha.
  }
  exact (Hloop Hbody (rest, s)).
Qed.

Lemma glibc_slist_clean_iter_back_2_M_Hoare :
  forall l1,
    Hoare
      (fun _ : unit => range l1)
      (glibc_slist_clean_iter_back_2_M l1)
      (fun r _ => r = (l1, list_sum l1)).
Proof.
  intros l1.
  unfold glibc_slist_clean_iter_back_2_M,
    glibc_slist_clean_iter_back_2_M_loop1_before.
  eapply Hoare_bind with
    (Q := fun st _ =>
      let '(rest, s) := st in
      exists done,
        rest ++ done = l1 /\
        s = list_sum done /\
        range l1).
  - apply Hoare_ret.
    intros _ Hrange.
    exists [].
    split.
    + rewrite app_nil_r. reflexivity.
    + split; [reflexivity | exact Hrange].
  - intros (rest, s).
    eapply Hoare_bind.
    + apply glibc_slist_clean_iter_back_2_M_loop1_aux_Hoare.
    + intros (rest', s').
      unfold glibc_slist_clean_iter_back_2_M_loop1_end.
      apply Hoare_ret.
      intros _ Hr.
      inversion Hr; subst.
      reflexivity.
Qed.
