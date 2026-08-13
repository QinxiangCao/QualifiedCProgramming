Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import TraceLib.TraceLogic.
Require Import TraceLib.MonadErr.TraceBasicErr.
Require Import TraceLib.MonadErr.CommonTacticsErr.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrLoop.
From FP Require Import BourbakiWitt.

Import MonadNotation.
Local Open Scope list.
Local Open Scope monad.

Inductive Tag {X: Type}: Type :=
| In: X -> Tag
| Out: X -> Tag.

Section TraceRecurErr.

Context {A Σ: Type}.

Notation programT := (programT Σ (@Tag A)) (only parsing).
Notation TR := (TR (@Tag A) Σ) (only parsing).

Context (f: (A -> programT unit) -> A -> programT unit).

Definition keep_trace_inv :=
  forall (W: A -> programT unit) (P: TR -> Prop),
    (forall a, keepG P (W a)) -> forall a, keepG P (f W a).

Definition trace_call_f (W: A -> programT unit) (a: A) :=
  track (In a);;
  f W a;;
  track (Out a).

Definition trace_call :=
  BW_fix trace_call_f.

Ltac unfold_call :=
  unfold trace_call, trace_call_f.

Class TraceCall :=
{
  trace_inv_f: keep_trace_inv;
  origin_prog: A -> program Σ unit;
  call_Gequiv: forall a, Gequiv (origin_prog a) (trace_call a);
}.

Context `{TraceCall}.

Local Open Scope trace.

Context
  (P Q: A -> Σ -> Prop)
  (Hp: forall a, Hoare (P a) (origin_prog a) (fun _ => Q a)).

Lemma trace_call_Hp (a: A):
  Hoare (fun '(s, _) => P a s)
        (trace_call a)
        (fun _ '(s, _) => Q a s).
Proof.
  eapply Hoare_toG.
  apply call_Gequiv.
  apply Hp.
  simpl; tauto.
Qed.

Lemma trace_call_local_out (a: A):
  Hoare (fun '(s, _) => P a s)
        (trace_call a)
        (fun _ '(s, tr) => tr |= (tsAtom (Out a) (fun s' => s' = s))).
Proof.
  unfold Hoare.
  split.
  - intros [] [s1 tr1] [s2 tr2] _ Hrun.
    unfold trace_call in Hrun.
    unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
      omega_lub, oLub_program, ProgramPO.indexed_union in Hrun; simpl in Hrun.
    sets_unfold in Hrun.
    destruct Hrun as [i Hi].
    destruct i as [|i]; simpl in Hi; [tauto|].
    unfold trace_call_f in Hi.
    unfold_monad in Hi.
    destruct Hi as [u [[sm trm] [Hin Hrest]]].
    destruct Hrest as [v [[sn trn] [_ Hout]]].
    unfold track, Gupdate, track_f in Hout; simpl in Hout.
    destruct Hout as [Hs Htr]; subst.
    apply app_last_atom.
    unfold tsAtom; auto.
  - intros [s tr] HP Herr.
    destruct (trace_call_Hp a) as [_ Herr_safe].
    eapply Herr_safe; eauto.
    exact HP.
Qed.

Lemma trace_call_local_prop (a: A):
  Hoare (fun '(s, _) => P a s)
        (trace_call a)
        (fun _ '(s, tr) => tr |= have (ts↑ (Out a) (Q a))).
Proof.
  eapply Hoare_cons_post.
  2:{
    eapply Hoare_conj.
    - eapply Hoare_cons_pre; [| apply trace_call_Hp].
      simpl; tauto.
    - eapply Hoare_cons_pre; [| apply trace_call_local_out].
      unfold ATrue; tauto.
  }
  simpl.
  intros _ (s, tr).
  intros [HQ Ht].
  apply last_have_atom.
  revert Ht; apply last_atom_implies.
  intros (t, s0).
  unfold tsAtom, sAtom.
  intros [? ?]; subst; auto.
Qed.

Definition trace_in_implies (a: A) (tr: TR): Prop :=
  tr |= have (tsAtom (In a) (P a)) -> tr |= have (ts↑ (Out a) (Q a)).

Lemma trace_in_implies_track_neq (a b: A) (s: Σ) (tr: TR):
  b <> a ->
  trace_in_implies a tr ->
  trace_in_implies a (tr ++ (In b, s)::nil).
Proof.
  intros.
  intros con; rewrite app_have_atom in con; destruct con.
  - rewrite app_have_atom; left; apply H1; auto.
  - rewrite singleton_have_atom in H2; destruct H2; inversion H2; congruence.
Qed.

Lemma trace_in_implies_track_notP (a: A) (s: Σ) (tr: TR):
  ~ P a s ->
  trace_in_implies a tr ->
  trace_in_implies a (tr ++ (In a, s)::nil).
Proof.
  intros; intros con.
  rewrite app_have_atom in con; destruct con.
  - rewrite app_have_atom; left; apply H1; auto.
  - rewrite singleton_have_atom in H2; destruct H2; inversion H2; congruence.
Qed.

Lemma trace_in_implies_track_out (a b: A) (s: Σ) (tr: TR):
  trace_in_implies a tr ->
  trace_in_implies a (tr ++ (Out b, s)::nil).
Proof.
  intros; intros con.
  rewrite app_have_atom in con; destruct con.
  - rewrite app_have_atom; left; apply H; auto.
  - rewrite singleton_have_atom in H1; destruct H1; inversion H1; congruence.
Qed.

Theorem Hoare_trace_in_implies (u v: A):
  Hoare (fun '(_, tr) => tr = nil)
        (trace_call u)
        (fun _ '(_, tr) => trace_in_implies v tr).
Proof.
  eapply Hoare_cons_pre with
    (P := fun '(s, tr) => trace_in_implies v tr).
  {
    intros (s, tr) H.
    subst; intros con.
    exfalso; eapply not_nil_have; eauto.
  }
  unfold_call.
  hoare_fix_lv_auto_conj' A unit tt.
  intros; eapply trace_call_local_prop.
  instantiate (1 := unit).
  clear u; simpl; intros W _ IH1 IH2 u _.
  assert (HW: (forall a, keepG (trace_in_implies v) (W a))).
  {
    intros; apply IH1. exact tt.
  }
  apply trace_inv_f in HW.
  destruct (classic (u = v)).
  subst.
  eapply Hoare_cons_pre with
  (P := fun x =>
    (trace_in_implies v (snd x) /\ P v (fst x)) \/
    (trace_in_implies v (snd x) /\ ~ P v (fst x))).
  {
    intros (s, tr) H.
    destruct (classic (P v s)).
    left; tauto.
    right; tauto.
  }
  apply Hoare_disj.
  {
    hoare_cons IH2.
    intros (s, tr); simpl; tauto.
    intros _ (s, tr); unfold trace_in_implies; auto.
  }
  {
    eapply Hoare_bind.
    - apply Hoare_track.
    - intros x.
      eapply Hoare_cons_pre with
        (P := fun '(_ ,tr) => trace_in_implies v tr).
      {
        intros (s, tr) [tr' (Htr & Him & Hnp)].
        subst; simpl in Hnp.
        apply trace_in_implies_track_notP; auto.
      }
      eapply Hoare_bind.
      + apply HW.
      + simpl; intros y.
        apply Hoare_track_inv.
        intros s tr Hti.
        apply trace_in_implies_track_out.
        exact Hti.
  }
  eapply Hoare_bind.
  - apply Hoare_track_inv.
    intros s tr Hti.
    apply trace_in_implies_track_neq; auto.
  - simpl; intros x.
    eapply Hoare_bind.
    + apply HW.
    + simpl; intros y.
      apply Hoare_track_inv.
      intros s tr Hti.
      apply trace_in_implies_track_out.
      exact Hti.
Qed.

Lemma trace_in_inversion (a b: A) (tr: TR):
  tr |= have_both (t↑(In a)) (t↑(In b)) -> a = b.
Proof.
  intros.
  destruct H as [n [?[]]].
  unfold lift in H1, H2.
  destruct (nth_error tr (n - 1)).
  * destruct p. unfold tAtom in H1, H2; subst.
    inversion H2; auto.
  * exfalso; auto.
Qed.

Lemma trace_in_out_inversion (a b: A) (tr: TR):
  ~ (tr |= have_both (t↑(In a)) (t↑(Out b))).
Proof.
  unfold not; intros.
  destruct H as [n [?[]]].
  unfold lift in H1, H2.
  destruct (nth_error tr (n - 1)).
  * destruct p. unfold tAtom in H1, H2; subst.
    inversion H2.
  * exfalso; auto.
Qed.

End TraceRecurErr.

Ltac unfold_call :=
  unfold trace_call, trace_call_f.
