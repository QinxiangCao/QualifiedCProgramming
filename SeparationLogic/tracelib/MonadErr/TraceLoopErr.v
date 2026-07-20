Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import TraceLib.MonadErr.TraceBasicErr.
Require Import TraceLib.TraceLogic.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrHoarePartial MonadErrLoop.
From FP Require Import BourbakiWitt.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope list.
Local Open Scope monad.

Inductive Tag {X: Type}: Type :=
| Entry: X -> Tag
| Exit: X -> Tag.

Section TraceLoopErr.

Context {A Σ: Type}.

Notation programT := (programT Σ (@Tag A)) (only parsing).
Notation TR := (TR (@Tag A) Σ) (only parsing).

Definition forset_f'
    (body: A -> programT unit)
    (W: (A -> Prop) -> programT unit) (universe: A -> Prop):
    programT unit :=
    choice (a <- get (fun _ a => a ∈ universe);;
            track (Entry a);;
            body a;;
            track (Exit a);;
            W (fun x => x ∈ universe /\ x <> a))
           (assume!! ((universe == ∅)%sets);;
            ret tt).

Definition forset'
    (universe: A -> Prop)
    (body: A -> programT unit): programT unit :=
    BW_fix (forset_f' body) universe.

End TraceLoopErr.

Section SnapshotLoopErr.

Context {Σ: Type} (default: Σ).

Definition snapshot_loop (cond: Σ -> Prop) (body: program Σ unit): programTS Σ unit :=
  trackS;;
  whileP (fun '(s, _) => cond s)
    (liftG body;; trackS).

Lemma Gequiv_snapshot_loop (cond: Σ -> Prop) (body: program Σ unit):
  Gequiv (whileP cond body) (snapshot_loop cond body).
Proof.
  unfold snapshot_loop.
  apply Gequiv_Gupdate_l.
  - apply trackS_live.
  - apply Gequiv_whileP.
    apply Gequiv_Gupdate_r.
    + apply trackS_live.
    + apply Gequiv_liftG.
Qed.

Definition snapshot_inv (cond P0: Σ -> Prop) (s: Σ) (tr: list Σ) : Prop :=
  tr <> nil /\
  P0 (hd default tr) /\
  last tr default = s /\
  forall i, i < length tr -> cond (nth i tr default) \/ i = length tr - 1.

Class SnapshotBodySafe (body: program Σ unit) : Prop :=
{
  snapshot_body_safe: Hoare ATrue body (fun _ _ => True);
}.

Ltac prove_snapshot_body_safe :=
  constructor; first [assumption | hoare_auto].

Tactic Notation "prove_snapshot_body_safe" "by" uconstr(H) :=
  constructor; exact H.

Definition TraceShape (cond P0: Σ -> Prop) (s: Σ) (tr: list Σ) : Prop :=
  P0 (hd default tr) /\
  last tr default = s /\
  ~ cond s /\
  forall i, i < length tr - 1 -> cond (nth i tr default).

Definition TraceHave (P: Σ -> Prop) (tr: list Σ) : Prop :=
  last_satisfyS (haveS (sLift P)) tr.

Definition TraceImplies (P Q: list Σ -> nat -> Prop) (tr: list Σ) : Prop :=
  last_satisfyS (impliesS P Q) tr.

Definition AbsRel {L St: Type}
    (P: nat -> L -> St -> Prop)
    (Q: nat -> L -> St -> Prop)
    (n: nat) (s1 s2: St) : Prop :=
  forall l, P n l s1 -> Q n l s2.

Definition TraceAbsRel {L: Type}
    (P Q: nat -> L -> Σ -> Prop)
    (tr: list Σ): Prop :=
  forall i j, i < j -> j < length tr ->
    AbsRel P Q (j - i) (nth i tr default) (nth j tr default).

Theorem snapshot_loop_trace_shape
  (cond P0: Σ -> Prop) (body: program Σ unit)
  `{SnapshotBodySafe body}:
    Hoare
      (fun '(s1, tr) => P0 s1 /\ tr = nil)
      (snapshot_loop cond body)
      (fun _ '(s2, tr) => TraceShape cond P0 s2 tr).
Proof.
  unfold snapshot_loop.
  eapply Hoare_bind with
    (Q := fun _ '(s, tr) => snapshot_inv cond P0 s tr).
  - eapply Hoare_cons_post.
    2: apply (@Hoare_trackS Σ (fun '(s, tr) => P0 s /\ tr = nil)).
    intros _ (s, tr) H.
    destruct H as [tr' [Htr' [HP0 Hnil]]].
    subst tr'.
    simpl in Htr'.
    subst tr.
    unfold snapshot_inv.
    split.
    + discriminate.
    + split.
      * simpl. exact HP0.
      * split.
        -- simpl. reflexivity.
        -- intros i Hi.
           right.
           simpl in Hi |- *.
           destruct i; [reflexivity | lia].
  - intros x.
    eapply Hoare_cons_post.
    2: {
      eapply Hoare_whileP with
        (P := fun '(s, tr) => snapshot_inv cond P0 s tr)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_bind with
        (Q := fun _ '(s', tr0) => exists sold, cond sold /\ snapshot_inv cond P0 sold tr0).
      + eapply Hoare_liftG'.
        intros tr.
        unfold Hoare; split.
        * intros a s1 s2 Hpre _.
          exists s1.
          destruct Hpre as [Hinv Hcond].
          split; auto.
        * intros s1 _ Herr.
          destruct snapshot_body_safe as [_ Herr_safe].
          eapply Herr_safe; eauto.
          unfold ATrue; auto.
      + intros y.
        eapply Hoare_cons_post.
        2: apply (@Hoare_trackS Σ (fun '(s', tr0) => exists sold, cond sold /\ snapshot_inv cond P0 sold tr0)).
        intros _ (s', tr1) H.
        destruct H as [tr0 [Htr1 Hex]].
        destruct Hex as [sold [Hcond_sold HInv0]].
        subst tr1.
        unfold snapshot_inv in *.
        destruct HInv0 as [Hnn [HP0_hd [Hlast Hall]]].
        repeat split.
        * destruct tr0; simpl; discriminate.
        * destruct tr0 as [|x0 xs].
          { exfalso; apply Hnn; reflexivity. }
          simpl in *.
          exact HP0_hd.
        * assert (Hlast_app_single: forall (l: list Σ) d x0, last (l ++ x0 :: nil) d = x0).
          {
            intros l d x0.
            revert d.
            induction l as [|a l IH]; intros d; simpl.
            - reflexivity.
            - destruct (l ++ x0 :: nil) as [|b tl] eqn:Hl.
              + apply app_eq_nil in Hl.
                destruct Hl as [_ Hnil].
                discriminate.
              + apply IH.
          }
          exact (Hlast_app_single tr0 default s').
        * intros i Hi.
          assert (Hnth_app_left: forall (l1 l2: list Σ) i d,
                i < length l1 -> nth i (l1 ++ l2) d = nth i l1 d).
          {
            intros l1.
            induction l1 as [|a l1 IH]; intros l2 j d Hi0.
            - simpl in Hi0. lia.
            - destruct j as [|j].
              + reflexivity.
              + simpl.
                apply IH.
                simpl in Hi0.
                lia.
          }
          assert (Hnth_last: forall (l: list Σ) dn dl,
                l <> nil -> nth (length l - 1) l dn = last l dl).
          {
            intros l.
            induction l as [|a l IH]; intros dn dl Hnn0.
            - contradiction.
            - destruct l as [|b l'].
              + simpl. reflexivity.
              + destruct l' as [|c l''].
                * simpl. reflexivity.
                * simpl.
                  apply IH.
                  discriminate.
          }
          destruct (classic (i < length tr0)) as [Hlt | Hnlt].
          { specialize (Hall i Hlt).
            destruct Hall as [Hcond_i | Hi_last].
            - left.
              rewrite (Hnth_app_left tr0 (s' :: nil) i default); [exact Hcond_i | lia].
            - left.
              rewrite (Hnth_app_left tr0 (s' :: nil) i default); [|lia].
              subst i.
              rewrite (Hnth_last tr0 default default Hnn).
              rewrite Hlast.
              exact Hcond_sold.
          }
          { right.
            rewrite length_app in *.
            simpl in *.
            lia.
          }
    }
    intros _ (s2, tr) Hpost.
    destruct Hpost as [HInv Hncond].
    unfold snapshot_inv in HInv.
    destruct HInv as [_ [HP0_hd [Hlast Hall]]].
    repeat split; auto.
    intros i Hi.
    assert (Hi_len: i < length tr) by lia.
    specialize (Hall i Hi_len).
    destruct Hall as [Hc | Hi_last]; auto.
    lia.
Qed.

Lemma trace_shape_have_exit
  (cond Q: Σ -> Prop) (s: Σ) (tr: list Σ):
  (forall s, Q s -> ~ cond s) ->
  TraceShape cond (fun _ => True) s tr ->
  TraceHave Q tr ->
  Q s.
Proof.
  intros HQ Hshape Hhave.
  unfold TraceHave in Hhave.
  destruct Hshape as [_ [Hlast [Hncond Hprefix]]].
  destruct (haveS_exists_nth tr Q default Hhave) as [i [Hi HQi]].
  assert (Htr_nonempty: tr <> nil).
  {
    intro Hnil.
    subst tr.
    simpl in Hi.
    lia.
  }
  destruct (Nat.lt_ge_cases i (length tr - 1)) as [Hi_prefix | Hi_final].
  - specialize (Hprefix i Hi_prefix).
    specialize (HQ _ HQi).
    tauto.
  - assert (Hi_eq: i = length tr - 1) by lia.
    subst i.
    rewrite nth_lastS_nonempty with (d := default) in HQi by exact Htr_nonempty.
    rewrite Hlast in HQi.
    exact HQi.
Qed.

Lemma trace_shape_have_exit_trace
  (cond Q: Σ -> Prop) (s: Σ) (tr: list Σ):
  (forall s, Q s -> ~ cond s) ->
  TraceShape cond (fun _ => True) s tr ->
  TraceImplies (haveS (sLift Q)) (sLift Q) tr.
Proof.
  intros HQ Hshape.
  unfold TraceImplies, impliesS, trace_implies, last_satisfyS.
  intro Hhave.
  pose proof (trace_shape_have_exit cond Q s tr HQ Hshape Hhave) as HQs.
  destruct Hshape as [_ [Hlast _]].
  assert (Htr_nonempty: tr <> nil).
  {
    intro Hnil.
    subst tr.
    eapply not_nil_haveS.
    exact Hhave.
  }
  unfold sLift.
  rewrite nth_error_last_nonempty with (d := default) by exact Htr_nonempty.
  rewrite Hlast.
  exact HQs.
Qed.

Theorem snapshot_loop_have_exit
  (cond Q: Σ -> Prop) (body: program Σ unit)
  `{SnapshotBodySafe body}:
  (forall s, Q s -> ~ cond s) ->
  Hoare
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) => TraceImplies (haveS (sLift Q)) (sLift Q) tr).
Proof.
  intros HQ.
  eapply Hoare_cons_post with
    (Q := fun _ '(s, tr) => TraceShape cond (fun _ => True) s tr).
  - intros _ (s, tr) Hshape.
    eapply trace_shape_have_exit_trace; eauto.
  - eapply Hoare_cons_pre with
      (P := fun '(s, tr) => (fun _ => True) s /\ tr = nil).
    + intros [s tr] Hnil.
      split; [exact I | exact Hnil].
    + eapply snapshot_loop_trace_shape.
      exact H0.
Qed.

Theorem snapshot_loop_have_final
  (cond Q: Σ -> Prop) (body: program Σ unit)
  `{SnapshotBodySafe body}:
  (forall s, Q s -> ~ cond s) ->
  Hoare
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(s, tr) => TraceHave Q tr -> Q s).
Proof.
  intros HQ.
  eapply Hoare_cons_post with
    (Q := fun _ '(s, tr) => TraceShape cond (fun _ => True) s tr).
  - intros _ (s, tr) Hshape Hhave.
    eapply trace_shape_have_exit; eauto.
  - eapply Hoare_cons_pre with
      (P := fun '(s, tr) => (fun _ => True) s /\ tr = nil).
    + intros [s tr] Hnil.
      split; [exact I | exact Hnil].
    + eapply snapshot_loop_trace_shape.
      assumption.
Qed.

Theorem snapshot_loop_initial_have
  (cond P Q: Σ -> Prop) (body: program Σ unit)
  `{SnapshotBodySafe body}:
  (forall s, P s -> Q s) ->
  Hoare
    (fun '(s, tr) => P s /\ tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) => TraceHave Q tr).
Proof.
  intros HPQ.
  unfold snapshot_loop.
  eapply Hoare_bind with
    (Q := fun _ '(_, tr) => TraceHave Q tr).
  - eapply Hoare_cons_post.
    2: apply (@Hoare_trackS Σ (fun '(s, tr) => P s /\ tr = nil)).
    intros _ (s, tr) [tr' [Htr [HP Hnil]]].
    subst tr'.
    simpl in Htr.
    subst tr.
    unfold TraceHave.
    apply singleton_haveS_atom.
    apply HPQ.
    exact HP.
  - intros [].
    eapply Hoare_cons_post.
    2:{
      eapply Hoare_whileP with
        (P := fun '(_, tr) => TraceHave Q tr)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_bind with
        (Q := fun _ '(_, tr) => TraceHave Q tr).
      + eapply Hoare_liftG'.
        intros tr.
        unfold Hoare; split.
        * intros [] s1 s2 Hpre _.
          destruct Hpre as [_ Hhave].
          exact Hhave.
        * intros s1 _ Herr.
          destruct snapshot_body_safe as [_ Herr_safe].
          eapply Herr_safe; eauto.
          exact Logic.I.
      + intros [].
        eapply Hoare_cons_post.
        2: apply (@Hoare_trackS Σ).
        intros _ (s2, tr2) [tr0 [Htr2 Hhave]].
        subst tr2.
        unfold TraceHave in *.
        eapply haveS_app_l.
        exact Hhave.
    }
    intros _ (s, tr) [Hhave _].
    exact Hhave.
Qed.

Theorem snapshot_loop_inner_have
  (cond inner_cond inner_inv: Σ -> Prop) (body: program Σ unit)
  `{SnapshotBodySafe body}:
  (forall s, inner_cond s -> cond s) ->
  Hoare
    (fun s => inner_inv s /\ inner_cond s)
    body
    (fun _ s => inner_inv s) ->
  Hoare
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) =>
      let I := inner_inv in
      let INC := fun s => inner_inv s /\ ~ inner_cond s in
      TraceImplies (haveS (sLift I)) (haveS (sLift INC)) tr).
Proof.
  intros Hinner_cond Hbody.
  set (I := inner_inv).
  set (INC := fun s => inner_inv s /\ ~ inner_cond s).
  set (PhaseInv := fun '(s, tr) =>
    tr <> nil /\
    (TraceHave INC tr \/ ~ TraceHave I tr \/ (I s /\ inner_cond s))).
  unfold snapshot_loop.
  eapply Hoare_bind with (Q := fun _ st => PhaseInv st).
  - eapply Hoare_cons_post.
    2: apply (@Hoare_trackS Σ (fun '(_, tr) => tr = nil)).
    intros _ (s, tr) [tr' [Htr Hnil]].
    subst tr'.
    simpl in Htr.
    subst tr.
    unfold PhaseInv.
    split; [discriminate |].
    destruct (classic (I s)) as [HI | HnotI].
    + destruct (classic (inner_cond s)) as [HC | HnotC].
      * right. right. split; assumption.
      * left.
        unfold TraceHave.
        apply singleton_haveS_atom.
        unfold INC. split; assumption.
    + right. left.
      intro Hhave.
      unfold TraceHave in Hhave.
      pose proof (proj1 (singleton_haveS_atom I s) Hhave) as HI.
      apply HnotI.
      exact HI.
  - intros [].
    eapply Hoare_cons_post.
    2:{
      eapply Hoare_whileP with
        (P := PhaseInv)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_bind with
        (Q := fun _ '(s', tr0) =>
          tr0 <> nil /\
          (TraceHave INC tr0 \/ ~ TraceHave I tr0 \/ inner_inv s')).
      + eapply Hoare_liftG'.
        intros tr.
        unfold Hoare; split.
        * intros [] s1 s2 Hpre Hrun.
          destruct Hpre as [Hcond [Hnn Hphase]].
          split; [exact Hnn |].
          destruct Hphase as [Hinc | [Hnoi | Hic]].
          -- left. exact Hinc.
          -- destruct (classic (I s2)) as [HI2 | HnotI2].
             ++ right. right. exact HI2.
             ++ right. left. exact Hnoi.
          -- right. right.
             destruct Hbody as [Hbody_nrm _].
             eapply Hbody_nrm.
             ++ exact Hic.
             ++ exact Hrun.
        * intros s1 _ Herr.
          destruct snapshot_body_safe as [_ Herr_safe].
          eapply Herr_safe; eauto.
          unfold ATrue.
          exact Logic.I.
      + intros [].
        eapply Hoare_cons_post.
        2: apply (@Hoare_trackS Σ).
        intros _ (s2, tr2) [tr0 [Htr2 [Hnn Hphase]]].
        subst tr2.
        unfold PhaseInv.
        split.
        * destruct tr0; simpl; discriminate.
        * destruct Hphase as [Hinc | [Hnoi | Hinv]].
          -- left.
             unfold TraceHave in *.
             eapply haveS_app_l.
             exact Hinc.
          -- destruct (classic (I s2)) as [HI2 | HnotI2].
             ++ destruct (classic (inner_cond s2)) as [HC2 | HnotC2].
                ** right. right. split; assumption.
                ** left.
                   unfold TraceHave.
                   apply app_last_haveS_atom.
                   unfold INC. split; assumption.
             ++ right. left.
                intro Hhave.
                unfold TraceHave in *.
                apply haveS_app_single_inv in Hhave.
                destruct Hhave as [Hhave_old | Hlast].
                ** apply Hnoi. exact Hhave_old.
                ** contradiction.
          -- destruct (classic (inner_cond s2)) as [HC2 | HnotC2].
             ++ right. right.
                split; assumption.
             ++ left.
                unfold TraceHave.
                apply app_last_haveS_atom.
                unfold INC.
                split; assumption.
    }
    intros _ (s, tr) [Hphase Hnotcond].
    unfold TraceImplies, impliesS, trace_implies, last_satisfyS.
    intro HhaveI.
    change (TraceHave I tr) in HhaveI.
    unfold PhaseInv in Hphase.
    destruct Hphase as [_ [Hinc | [Hnoi | Hic]]].
    + unfold TraceHave in Hinc.
      exact Hinc.
    + contradiction.
    + exfalso.
      destruct Hic as [_ HC].
      apply Hnotcond.
      apply Hinner_cond.
      exact HC.
Qed.

Lemma snapshot_loop_AbsRel {L: Type}
  (cond: Σ -> Prop)
  (P Q: nat -> L -> Σ -> Prop)
  (body: program Σ unit)
  `{SnapshotBodySafe body}
  (h: forall l, Hoare (P 1 l) body (fun _ => Q 1 l)):
    Hoare
      (fun '(_, tr) => tr = nil)
      (snapshot_loop cond body)
      (fun _ '(_, tr) =>
          forall i, i < length tr - 1 ->
          AbsRel P Q 1 (nth i tr default) (nth (S i) tr default)).
Proof.
  unfold snapshot_loop.
  eapply Hoare_bind with
    (Q := fun _ '(s, tr) =>
      tr <> nil /\
      last tr default = s /\
      forall i, i >= 0 -> i < length tr - 1 ->
      AbsRel P Q 1 (nth i tr default) (nth (S i) tr default)).
  - eapply Hoare_cons_post.
    2: apply (@Hoare_trackS Σ (fun '(_, tr) => tr = nil)).
    intros _ (s, tr) [tr' [Htr' Hnil]].
    subst tr'. simpl in Htr'. subst tr.
    split; [discriminate | ].
    split; [reflexivity | ].
    intros i Hi0 Hi. simpl in *; lia.
  - intros x.
    eapply Hoare_cons_post.
    2: {
      eapply Hoare_whileP with
        (P := fun '(s, tr) =>
          tr <> nil /\
          last tr default = s /\
          forall i, i >= 0 -> i < length tr - 1 ->
          AbsRel P Q 1 (nth i tr default) (nth (S i) tr default))
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      + eapply Hoare_bind with
          (Q := fun _ '(s', tr0) => exists sold, AbsRel P Q 1 sold s' /\
            tr0 <> nil /\ last tr0 default = sold /\
            forall i, i >= 0 -> i < length tr0 - 1 ->
            AbsRel P Q 1 (nth i tr0 default) (nth (S i) tr0 default)).
        * eapply Hoare_liftG'.
          intros tr. unfold Hoare; split.
          -- intros a s1 s2 Hpre Heval.
             destruct Hpre as [Hcond [Hnn [Hlast Hforall]]].
             exists s1. split; [ | repeat split; auto ].
             intros l Hl. specialize (h l) as [Hnrm _].
             eapply Hnrm; eauto.
          -- intros s1 Hpre Herr.
             destruct snapshot_body_safe as [_ Herr_safe].
             eapply Herr_safe; eauto.
             unfold ATrue; auto.
        * intros y.
          eapply Hoare_cons_post.
          2: apply (@Hoare_trackS Σ).
          intros _ (s''', tr2) [tr0' [Htr2 [sold [Hrel [Hnn [Hlast Hforall]]]]]].
          subst tr2.
          repeat split.
          -- destruct tr0'; simpl; discriminate.
          -- apply last_last.
          -- intros i Hi0 Hi.
             rewrite length_app in Hi; simpl in Hi.
             destruct (Nat.lt_ge_cases i (length tr0' - 1)) as [Hlt | Hnle].
             ++ rewrite (app_nth1 _ (s''' :: nil) default); [|lia].
                rewrite (app_nth1 _ (s''' :: nil) default); [|lia].
                apply Hforall; auto.
             ++ assert (Heq: i = length tr0' - 1).
                { clear - Hi Hnle Hnn. destruct tr0'; [contradiction | simpl in *; lia]. }
                subst i.
                rewrite (app_nth1 _ (s''' :: nil) default); [|lia].
                replace (S (length tr0' - 1)) with (length tr0') by lia.
                rewrite (app_nth2 _ _ default); [|lia].
                replace (length tr0' - length tr0') with 0 by lia.
                simpl.
                assert (H_nth_last_gen: forall (l: list Σ) dn dl, l <> nil -> nth (length l - 1) l dn = last l dl).
                { intros lst. induction lst as [| a l IH].
                  - intros; contradiction.
                  - destruct l as [| b l'].
                    + intros; reflexivity.
                    + intros dn' dl' Hnn_l.
                      simpl in *.
                      assert (Heq0: forall n, n - 0 = n) by (intros; lia).
                      rewrite Heq0 in IH.
                      apply IH. discriminate.
                }
                rewrite (H_nth_last_gen tr0' default default); [|exact Hnn].
                rewrite Hlast. exact Hrel.
    }
    intros _ (s2, tr) [HInv Hncond].
    destruct HInv as [Hnn [Hlast Hforall]].
    intros i Hi.
    apply Hforall; lia.
Qed.

Theorem snapshot_loop_AbsRel_trace {L: Type}
  (cond: Σ -> Prop) 
  (P Q: nat -> L -> Σ -> Prop) 
  (body: program Σ unit)
  `{SnapshotBodySafe body}
  (h: forall l, Hoare (P 1 l) body (fun _ => Q 1 l))
  (hassoc: forall s1 s2 s3 m n, AbsRel P Q m s1 s2 -> AbsRel P Q n s2 s3 -> AbsRel P Q (m+n) s1 s3):
    Hoare
      (fun '(_, tr) => tr = nil)
      (snapshot_loop cond body)
      (fun _ '(_, tr) => TraceAbsRel P Q tr).
Proof.
  eapply Hoare_cons_post.
  2: { apply (snapshot_loop_AbsRel cond P Q body); exact h. }
  intros _ (st, tr) Hforall i j Hij Hj.
  remember (j - i) as n.
  revert i j Hij Hj Heqn.
  induction n as [| n IH].
  + intros i j Hij Hj Heqn.
    lia.
  + intros i j Hij Hj Heqn.
    destruct n as [| n'].
    * assert (Heqj: j = S i) by lia.
      subst j.
      replace (S i - i) with 1 by lia.
      apply Hforall. lia.
    * assert (Hij': i < j - 1) by lia.
      assert (Hj': j - 1 < length tr - 1) by lia.
      specialize (IH i (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Htemp: AbsRel P Q (S n' + 1) (nth i tr default) (nth j tr default)).
      { apply (hassoc _ (nth (j - 1) tr default) _ (S n') 1); [exact IH | ].
        specialize (Hforall (j - 1) Hj').
        replace (S (j - 1)) with j in Hforall by lia.
        exact Hforall.
      }
      replace (j - i) with (S n' + 1) by lia.
      replace (S (S n')) with (S n' + 1) by lia.
      exact Htemp.
Qed.

Lemma last_app_single (l: list Σ) d x:
  last (l ++ x :: nil) d = x.
Proof.
  revert d.
  induction l as [|a l IH]; intros d; simpl.
  - reflexivity.
  - destruct (l ++ x :: nil) as [|b tl] eqn:Hl.
    + apply app_eq_nil in Hl.
      destruct Hl as [_ Hnil].
      discriminate.
    + apply IH.
Qed.

Lemma nth_last_nonempty (l: list Σ) dn dl:
  l <> nil -> nth (length l - 1) l dn = last l dl.
Proof.
  induction l as [|a l IH]; intros Hnn.
  - contradiction.
  - destruct l as [|b l'].
    + simpl. reflexivity.
    + destruct l' as [|c l''].
      * simpl. reflexivity.
      * simpl.
        apply IH.
        discriminate.
Qed.

Lemma nth_app_single_last (l: list Σ) d x:
  nth (length l) (l ++ x :: nil) d = x.
Proof.
  induction l as [|a l IH]; simpl; auto.
Qed.

Lemma trace_absrel_extend {L: Type}
  (P Q: nat -> L -> Σ -> Prop)
  (hassoc: forall s1 s2 s3 m n,
      AbsRel P Q m s1 s2 ->
      AbsRel P Q n s2 s3 ->
      AbsRel P Q (m+n) s1 s3)
  (tr: list Σ) (sold s': Σ):
  tr <> nil ->
  last tr default = sold ->
  TraceAbsRel P Q tr ->
  AbsRel P Q 1 sold s' ->
  TraceAbsRel P Q (tr ++ s' :: nil).
Proof.
  intros Hnn Hlast Habs Hstep i j Hij Hj.
  rewrite length_app in Hj; simpl in Hj.
  destruct (Nat.lt_ge_cases j (length tr)) as [Hj_tr | Hj_last].
  - rewrite app_nth1 by lia.
    rewrite app_nth1 by lia.
    apply Habs; lia.
  - assert (Hj_eq: j = length tr) by lia.
    subst j.
    rewrite nth_app_single_last.
    rewrite app_nth1 by lia.
    destruct (Nat.eq_dec i (length tr - 1)) as [Hi_last | Hi_not_last].
    + subst i.
      replace (length tr - (length tr - 1)) with 1 by lia.
      rewrite nth_last_nonempty with (dl:= default) by exact Hnn.
      rewrite Hlast.
      exact Hstep.
    + assert (Hi_mid: i < length tr - 1) by lia.
      assert (Hmid: AbsRel P Q (length tr - 1 - i)
                    (nth i tr default) sold).
      {
        rewrite <- Hlast.
        rewrite <- nth_last_nonempty with (dn:= default) (dl:= default) by exact Hnn.
        apply Habs; lia.
      }
      replace (length tr - i) with ((length tr - 1 - i) + 1) by lia.
      eapply hassoc; [exact Hmid | exact Hstep].
Qed.

Theorem snapshot_loop_step_have
  (cond P Q: Σ -> Prop) (body: program Σ unit)
  `{SnapshotBodySafe body}:
  Hoare
    (fun s => P s /\ cond s)
    body
    (fun _ s => Q s) ->
  Hoare
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) =>
      let PC := fun s => P s /\ cond s in
      TraceImplies (haveS (sLift PC)) (haveS (sLift Q)) tr).
Proof.
  intros Hbody.
  set (PC := fun s => P s /\ cond s).
  set (StepInv := fun '(s, tr) =>
    tr <> nil /\
    last tr default = s /\
    (TraceHave Q tr \/
      forall i, i < length tr - 1 -> ~ PC (nth i tr default))).
  unfold snapshot_loop.
  eapply Hoare_bind with (Q := fun _ st => StepInv st).
  - eapply Hoare_cons_post.
    2: apply (@Hoare_trackS Σ (fun '(_, tr) => tr = nil)).
    intros _ (s, tr) [tr' [Htr Hnil]].
    subst tr'. simpl in Htr. subst tr.
    unfold StepInv.
    split; [discriminate |].
    split; [reflexivity |].
    right. intros i Hi. simpl in Hi. lia.
  - intros [].
    eapply Hoare_cons_post.
    2:{
      eapply Hoare_whileP with
        (P := StepInv)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      + eapply Hoare_bind with
          (Q := fun _ '(s', tr0) =>
            tr0 <> nil /\
            (TraceHave Q tr0 \/
              (forall i, i < length tr0 - 1 -> ~ PC (nth i tr0 default)) /\
              (PC (last tr0 default) -> Q s'))).
        * eapply Hoare_liftG'.
          intros tr. unfold Hoare; split.
          -- intros [] s1 s2 Hpre Heval.
             destruct Hpre as [Hcond [Hnn [Hlast Hphase]]].
             split; [exact Hnn |].
             destruct Hphase as [HhaveQ | HnoPC].
             ++ left. exact HhaveQ.
             ++ right.
                split.
                ** exact HnoPC.
                ** intros HPC.
                   destruct Hbody as [Hbody_nrm _].
                   eapply Hbody_nrm.
                   --- rewrite <- Hlast. exact HPC.
                   --- rewrite Hlast. exact Heval.
          -- intros s1 _ Herr.
             destruct snapshot_body_safe as [_ Herr_safe].
             eapply Herr_safe; eauto.
             exact I.
        * intros [].
          eapply Hoare_cons_post.
          2: apply (@Hoare_trackS Σ).
          intros _ (s2, tr2) [tr0 [Htr2 [Hnn Hstep]]].
          subst tr2.
          unfold StepInv.
          split.
          -- destruct tr0; simpl; discriminate.
          -- split.
             ++ rewrite last_app_single.
                reflexivity.
             ++ destruct Hstep as [HhaveQ | [HnoPC Hcommit]].
                ** left.
                   unfold TraceHave in *.
                   eapply haveS_app_l.
                   exact HhaveQ.
                ** destruct (classic (PC (last tr0 default))) as [HPC | HnotPC].
                   --- left.
                       unfold TraceHave.
                       apply app_last_haveS_atom.
                       apply Hcommit.
                       exact HPC.
                   --- right.
                       intros i Hi.
                       rewrite length_app in Hi.
                       simpl in Hi.
                       destruct (Nat.lt_ge_cases i (length tr0 - 1)) as [Hlt | Hge].
                       +++ rewrite app_nth1 by lia.
                           apply HnoPC. exact Hlt.
                       +++ assert (Hi_eq: i = length tr0 - 1).
                           { clear - Hi Hge Hnn. destruct tr0; [contradiction | simpl in *; lia]. }
                           subst i.
                           rewrite app_nth1 by lia.
                           rewrite nth_lastS_nonempty with (d := default) by exact Hnn.
                           exact HnotPC.
    }
    intros _ (s, tr) [Hstep Hnotcond].
    unfold TraceImplies, impliesS, trace_implies, last_satisfyS.
    intro HhavePC.
    change (TraceHave PC tr) in HhavePC.
    unfold StepInv in Hstep.
    destruct Hstep as [Hnn [Hlast [HhaveQ | HnoPC]]].
    + unfold TraceHave in HhaveQ.
      exact HhaveQ.
    + exfalso.
      destruct (haveS_exists_nth tr PC default HhavePC) as [i [Hi HPC]].
      destruct (Nat.lt_ge_cases i (length tr - 1)) as [Hlt | Hge].
      * exact (HnoPC i Hlt HPC).
      * assert (Hi_eq: i = length tr - 1) by lia.
        subst i.
        rewrite nth_lastS_nonempty with (d := default) in HPC by exact Hnn.
        rewrite Hlast in HPC.
        destruct HPC as [_ Hcond].
        exact (Hnotcond Hcond).
Qed.

Theorem snapshot_loop_trace_shape_nrm
  (cond P0: Σ -> Prop) (body: program Σ unit):
    Hoare_nrm
      (fun '(s1, tr) => P0 s1 /\ tr = nil)
      (snapshot_loop cond body)
      (fun _ '(s2, tr) => TraceShape cond P0 s2 tr).
Proof.
  unfold snapshot_loop.
  eapply Hoare_nrm_bind with
    (Q := fun _ '(s, tr) => snapshot_inv cond P0 s tr).
  - eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_trackS. }
    intros _ (s, tr) H.
    destruct H as [tr' [Htr' [HP0 Hnil]]].
    subst tr'.
    simpl in Htr'.
    subst tr.
    unfold snapshot_inv.
    split.
    + discriminate.
    + split.
      * simpl. exact HP0.
      * split.
        -- simpl. reflexivity.
        -- intros i Hi.
           right.
           simpl in Hi |- *.
           destruct i; [reflexivity | lia].
  - intros [].
    eapply Hoare_nrm_cons_post.
    2:{
      eapply Hoare_nrm_whileP with
        (P := fun '(s, tr) => snapshot_inv cond P0 s tr)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_nrm_bind with
        (Q := fun _ '(s', tr0) => exists sold, cond sold /\ snapshot_inv cond P0 sold tr0).
      + eapply Hoare_nrm_liftG'.
        intros tr.
        unfold Hoare_nrm.
        intros [] s1 s2 [Hinv Hcond] _.
        exists s1.
        split; auto.
      + intros [].
        eapply Hoare_nrm_cons_post.
        2:{ apply Hoare_implies_nrm, Hoare_trackS. }
        intros _ (s', tr1) H.
        destruct H as [tr0 [Htr1 Hex]].
        destruct Hex as [sold [Hcond_sold HInv0]].
        subst tr1.
        unfold snapshot_inv in *.
        destruct HInv0 as [Hnn [HP0_hd [Hlast Hall]]].
        repeat split.
        * destruct tr0; simpl; discriminate.
        * destruct tr0 as [|x0 xs].
          { exfalso; apply Hnn; reflexivity. }
          simpl in *.
          exact HP0_hd.
        * apply last_app_single.
        * intros i Hi.
          destruct (classic (i < length tr0)) as [Hlt | Hnlt].
          { specialize (Hall i Hlt).
            destruct Hall as [Hcond_i | Hi_last].
            - left.
              rewrite app_nth1 by lia.
              exact Hcond_i.
            - left.
              rewrite app_nth1 by lia.
              subst i.
              rewrite nth_last_nonempty with (dl:=default) by exact Hnn.
              rewrite Hlast.
              exact Hcond_sold.
          }
          { right.
            rewrite length_app in *.
            simpl in *.
            lia.
          }
    }
    intros _ (s2, tr) [HInv Hncond].
    destruct HInv as [_ [HP0_hd [Hlast Hall]]].
    unfold TraceShape.
    repeat split; auto.
    intros i Hi.
    specialize (Hall i ltac:(lia)).
    destruct Hall as [Hc | Hi_last]; [exact Hc | lia].
Qed.

Theorem snapshot_loop_have_exit_nrm
  (cond Q: Σ -> Prop) (body: program Σ unit):
  (forall s, Q s -> ~ cond s) ->
  Hoare_nrm
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) => TraceImplies (haveS (sLift Q)) (sLift Q) tr).
Proof.
  intros HQ.
  eapply Hoare_nrm_cons_post with
    (Q := fun _ '(s, tr) => TraceShape cond (fun _ => True) s tr).
  - intros _ (s, tr) Hshape.
    eapply trace_shape_have_exit_trace; eauto.
  - eapply Hoare_nrm_cons_pre with
      (P := fun '(s, tr) => (fun _ => True) s /\ tr = nil).
    + intros [s tr] Hnil.
      split; [exact I | exact Hnil].
    + eapply snapshot_loop_trace_shape_nrm.
Qed.

Theorem snapshot_loop_have_final_nrm
  (cond Q: Σ -> Prop) (body: program Σ unit):
  (forall s, Q s -> ~ cond s) ->
  Hoare_nrm
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(s, tr) => TraceHave Q tr -> Q s).
Proof.
  intros HQ.
  eapply Hoare_nrm_cons_post with
    (Q := fun _ '(s, tr) => TraceShape cond (fun _ => True) s tr).
  - intros _ (s, tr) Hshape Hhave.
    eapply trace_shape_have_exit; eauto.
  - eapply Hoare_nrm_cons_pre with
      (P := fun '(s, tr) => (fun _ => True) s /\ tr = nil).
    + intros [s tr] Hnil.
      split; [exact I | exact Hnil].
    + eapply snapshot_loop_trace_shape_nrm.
Qed.

Theorem snapshot_loop_initial_have_nrm
  (cond P Q: Σ -> Prop) (body: program Σ unit):
  (forall s, P s -> Q s) ->
  Hoare_nrm
    (fun '(s, tr) => P s /\ tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) => TraceHave Q tr).
Proof.
  intros HPQ.
  unfold snapshot_loop.
  eapply Hoare_nrm_bind with
    (Q := fun _ '(_, tr) => TraceHave Q tr).
  - eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_trackS. }
    intros _ (s, tr) [tr' [Htr [HP Hnil]]].
    subst tr'.
    simpl in Htr.
    subst tr.
    unfold TraceHave.
    apply singleton_haveS_atom.
    apply HPQ.
    exact HP.
  - intros [].
    eapply Hoare_nrm_cons_post.
    2:{
      eapply Hoare_nrm_whileP with
        (P := fun '(_, tr) => TraceHave Q tr)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_nrm_bind with
        (Q := fun _ '(_, tr) => TraceHave Q tr).
      + eapply Hoare_nrm_liftG'.
        intros tr.
        unfold Hoare_nrm.
        intros [] s1 s2 [Hhave _] _.
        exact Hhave.
      + intros [].
        eapply Hoare_nrm_cons_post.
        2:{ apply Hoare_implies_nrm, Hoare_trackS. }
        intros _ (s2, tr2) [tr0 [Htr2 Hhave]].
        subst tr2.
        unfold TraceHave in *.
        eapply haveS_app_l.
        exact Hhave.
    }
    intros _ (s, tr) [Hhave _].
    exact Hhave.
Qed.

Theorem snapshot_loop_inner_have_nrm
  (cond inner_cond inner_inv: Σ -> Prop) (body: program Σ unit):
  (forall s, inner_cond s -> cond s) ->
  Hoare_nrm
    (fun s => inner_inv s /\ inner_cond s)
    body
    (fun _ s => inner_inv s) ->
  Hoare_nrm
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) =>
      let I := inner_inv in
      let INC := fun s => inner_inv s /\ ~ inner_cond s in
      TraceImplies (haveS (sLift I)) (haveS (sLift INC)) tr).
Proof.
  intros Hinner_cond Hbody.
  set (I := inner_inv).
  set (INC := fun s => inner_inv s /\ ~ inner_cond s).
  set (PhaseInv := fun '(s, tr) =>
    tr <> nil /\
    (TraceHave INC tr \/ ~ TraceHave I tr \/ (I s /\ inner_cond s))).
  unfold snapshot_loop.
  eapply Hoare_nrm_bind with (Q := fun _ st => PhaseInv st).
  - eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_trackS. }
    intros _ (s, tr) [tr' [Htr Hnil]].
    subst tr'.
    simpl in Htr.
    subst tr.
    unfold PhaseInv.
    split; [discriminate |].
    destruct (classic (I s)) as [HI | HnotI].
    + destruct (classic (inner_cond s)) as [HC | HnotC].
      * right. right. split; assumption.
      * left.
        unfold TraceHave.
        apply singleton_haveS_atom.
        unfold INC. split; assumption.
    + right. left.
      intro Hhave.
      unfold TraceHave in Hhave.
      pose proof (proj1 (singleton_haveS_atom I s) Hhave) as HI.
      apply HnotI.
      exact HI.
  - intros [].
    eapply Hoare_nrm_cons_post.
    2:{
      eapply Hoare_nrm_whileP with
        (P := PhaseInv)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_nrm_bind with
        (Q := fun _ '(s', tr0) =>
          tr0 <> nil /\
          (TraceHave INC tr0 \/ ~ TraceHave I tr0 \/ inner_inv s')).
      + eapply Hoare_nrm_liftG'.
        intros tr.
        unfold Hoare_nrm.
        intros [] s1 s2 [[Hnn Hphase] Hcond] Hrun.
        split; [exact Hnn |].
        destruct Hphase as [Hinc | [Hnoi | Hic]].
        * left. exact Hinc.
        * destruct (classic (I s2)) as [HI2 | HnotI2].
          -- right. right. exact HI2.
          -- right. left. exact Hnoi.
        * right. right.
          eapply Hbody.
          -- exact Hic.
          -- exact Hrun.
      + intros [].
        eapply Hoare_nrm_cons_post.
        2:{ apply Hoare_implies_nrm, Hoare_trackS. }
        intros _ (s2, tr2) [tr0 [Htr2 [Hnn Hphase]]].
        subst tr2.
        unfold PhaseInv.
        split.
        * destruct tr0; simpl; discriminate.
        * destruct Hphase as [Hinc | [Hnoi | Hinv]].
          -- left.
             unfold TraceHave in *.
             eapply haveS_app_l.
             exact Hinc.
          -- destruct (classic (I s2)) as [HI2 | HnotI2].
             ++ destruct (classic (inner_cond s2)) as [HC2 | HnotC2].
                ** right. right. split; assumption.
                ** left.
                   unfold TraceHave.
                   apply app_last_haveS_atom.
                   unfold INC. split; assumption.
             ++ right. left.
                intro Hhave.
                unfold TraceHave in *.
                apply haveS_app_single_inv in Hhave.
                destruct Hhave as [Hhave_old | Hlast].
                ** apply Hnoi. exact Hhave_old.
                ** contradiction.
          -- destruct (classic (inner_cond s2)) as [HC2 | HnotC2].
             ++ right. right.
                split; assumption.
             ++ left.
                unfold TraceHave.
                apply app_last_haveS_atom.
                unfold INC.
                split; assumption.
    }
    intros _ (s, tr) [Hphase Hnotcond].
    unfold TraceImplies, impliesS, trace_implies, last_satisfyS.
    intro HhaveI.
    change (TraceHave I tr) in HhaveI.
    unfold PhaseInv in Hphase.
    destruct Hphase as [_ [Hinc | [Hnoi | Hic]]].
    + unfold TraceHave in Hinc.
      exact Hinc.
    + contradiction.
    + exfalso.
      destruct Hic as [_ HC].
      apply Hnotcond.
      apply Hinner_cond.
      exact HC.
Qed.

Theorem snapshot_loop_step_have_nrm
  (cond P Q: Σ -> Prop) (body: program Σ unit):
  Hoare_nrm
    (fun s => P s /\ cond s)
    body
    (fun _ s => Q s) ->
  Hoare_nrm
    (fun '(_, tr) => tr = nil)
    (snapshot_loop cond body)
    (fun _ '(_, tr) =>
      let PC := fun s => P s /\ cond s in
      TraceImplies (haveS (sLift PC)) (haveS (sLift Q)) tr).
Proof.
  intros Hbody.
  set (PC := fun s => P s /\ cond s).
  set (StepInv := fun '(s, tr) =>
    tr <> nil /\
    last tr default = s /\
    (TraceHave Q tr \/
      forall i, i < length tr - 1 -> ~ PC (nth i tr default))).
  unfold snapshot_loop.
  eapply Hoare_nrm_bind with (Q := fun _ st => StepInv st).
  - eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_trackS. }
    intros _ (s, tr) [tr' [Htr Hnil]].
    subst tr'. simpl in Htr. subst tr.
    unfold StepInv.
    split; [discriminate |].
    split; [reflexivity |].
    right. intros i Hi. simpl in Hi. lia.
  - intros [].
    eapply Hoare_nrm_cons_post.
    2:{
      eapply Hoare_nrm_whileP with
        (P := StepInv)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_nrm_bind with
        (Q := fun _ '(s', tr0) =>
          tr0 <> nil /\
          (TraceHave Q tr0 \/
            (forall i, i < length tr0 - 1 -> ~ PC (nth i tr0 default)) /\
            (PC (last tr0 default) -> Q s'))).
      + eapply Hoare_nrm_liftG'.
        intros tr.
        unfold Hoare_nrm.
        intros [] s1 s2 [[Hnn [Hlast Hphase]] Hcond] Hrun.
        split; [exact Hnn |].
        destruct Hphase as [HhaveQ | HnoPC].
        * left. exact HhaveQ.
        * right.
          split.
          -- exact HnoPC.
          -- intros HPC.
             eapply Hbody.
             ++ rewrite <- Hlast. exact HPC.
             ++ rewrite Hlast. exact Hrun.
      + intros [].
        eapply Hoare_nrm_cons_post.
        2:{ apply Hoare_implies_nrm, Hoare_trackS. }
        intros _ (s2, tr2) [tr0 [Htr2 [Hnn Hstep]]].
        subst tr2.
        unfold StepInv.
        split.
        * destruct tr0; simpl; discriminate.
        * split.
          -- rewrite last_app_single.
             reflexivity.
          -- destruct Hstep as [HhaveQ | [HnoPC Hcommit]].
             ++ left.
                unfold TraceHave in *.
                eapply haveS_app_l.
                exact HhaveQ.
             ++ destruct (classic (PC (last tr0 default))) as [HPC | HnotPC].
                ** left.
                   unfold TraceHave.
                   apply app_last_haveS_atom.
                   apply Hcommit.
                   exact HPC.
                ** right.
                   intros i Hi.
                   rewrite length_app in Hi.
                   simpl in Hi.
                   destruct (Nat.lt_ge_cases i (length tr0 - 1)) as [Hlt | Hge].
                   --- rewrite app_nth1 by lia.
                       apply HnoPC. exact Hlt.
                   --- assert (Hi_eq: i = length tr0 - 1).
                       { clear - Hi Hge Hnn. destruct tr0; [contradiction | simpl in *; lia]. }
                       subst i.
                       rewrite app_nth1 by lia.
                       rewrite nth_lastS_nonempty with (d := default) by exact Hnn.
                       exact HnotPC.
    }
    intros _ (s, tr) [Hstep Hnotcond].
    unfold TraceImplies, impliesS, trace_implies, last_satisfyS.
    intro HhavePC.
    change (TraceHave PC tr) in HhavePC.
    unfold StepInv in Hstep.
    destruct Hstep as [Hnn [Hlast [HhaveQ | HnoPC]]].
    + unfold TraceHave in HhaveQ.
      exact HhaveQ.
    + exfalso.
      destruct (haveS_exists_nth tr PC default HhavePC) as [i [Hi HPC]].
      destruct (Nat.lt_ge_cases i (length tr - 1)) as [Hlt | Hge].
      * exact (HnoPC i Hlt HPC).
      * assert (Hi_eq: i = length tr - 1) by lia.
        subst i.
        rewrite nth_lastS_nonempty with (d := default) in HPC by exact Hnn.
        rewrite Hlast in HPC.
        destruct HPC as [_ Hcond].
        exact (Hnotcond Hcond).
Qed.

Theorem snapshot_loop_AbsRel_trace_nrm {L: Type}
  (cond: Σ -> Prop)
  (P Q: nat -> L -> Σ -> Prop)
  (body: program Σ unit)
  (h: forall l, Hoare_nrm (P 1 l) body (fun _ => Q 1 l))
  (hassoc: forall s1 s2 s3 m n,
      AbsRel P Q m s1 s2 ->
      AbsRel P Q n s2 s3 ->
      AbsRel P Q (m+n) s1 s3):
    Hoare_nrm
      (fun '(_, tr) => tr = nil)
      (snapshot_loop cond body)
      (fun _ '(_, tr) => TraceAbsRel P Q tr).
Proof.
  unfold snapshot_loop.
  eapply Hoare_nrm_bind with
    (Q := fun _ '(s, tr) =>
      tr <> nil /\
      last tr default = s /\
      TraceAbsRel P Q tr).
  - eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_trackS. }
    intros _ (s, tr) [tr' [Htr' Hnil]].
    subst tr'. simpl in Htr'. subst tr.
    split; [discriminate |].
    split; [reflexivity |].
    intros i j Hij Hj.
    destruct j; simpl in Hj; lia.
  - intros [].
    eapply Hoare_nrm_cons_post.
    2:{
      eapply Hoare_nrm_whileP with
        (P := fun '(s, tr) =>
          tr <> nil /\
          last tr default = s /\
          TraceAbsRel P Q tr)
        (cond := fun '(s, _) => cond s)
        (body := liftG body;; trackS).
      eapply Hoare_nrm_bind with
        (Q := fun _ '(s', tr0) => exists sold,
          tr0 <> nil /\
          last tr0 default = sold /\
          TraceAbsRel P Q tr0 /\
          AbsRel P Q 1 sold s').
      + eapply Hoare_nrm_liftG'.
        intros tr.
        unfold Hoare_nrm.
        intros [] sold s' [[Hnn [Hlast Habs]] _] Hrun.
        exists sold.
        repeat split; auto.
        intros l HP.
        specialize (h l).
        eapply h; eauto.
      + intros [].
        eapply Hoare_nrm_cons_post.
        2:{ apply Hoare_implies_nrm, Hoare_trackS. }
        intros _ (s'', tr2) [tr0 [Htr2 [sold [Hnn [Hlast [Habs Hstep]]]]]].
        subst tr2.
        split.
        * destruct tr0; simpl; discriminate.
        * split.
          -- apply last_app_single.
          -- eapply trace_absrel_extend; eauto.
    }
    intros _ (s, tr) [[_ [_ Habs]] _].
    exact Habs.
Qed.

End SnapshotLoopErr.
