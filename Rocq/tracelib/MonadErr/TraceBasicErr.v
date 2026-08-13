Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
Require Export TraceLib.MonadErr.GhostCodeErr.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section TraceErr.

Context {T: Type}
        {Σ: Type}.

Notation TR := (list (T * Σ)) (only parsing).
Notation programT := (@programG Σ TR) (only parsing).

Definition track_f (t: T) (s: Σ) (g1 g2: TR) : Prop :=
  g2 = g1 ++ (t, s) :: nil.

Definition track (t: T) : programT unit :=
  Gupdate (track_f t).

Lemma track_live (t: T):
  Gupdate_live (track_f t).
Proof.
  unfold Gupdate_live, track_f.
  intros.
  eexists; eauto.
Qed.

Lemma Hoare_track (P: Σ * TR -> Prop) (t: T):
  Hoare P (track t)
    (fun _ '(s, tr) =>
      exists tr', tr = tr' ++ (t, s) :: nil /\ P (s, tr')).
Proof.
  unfold Hoare, track, Gupdate; simpl.
  split; intros.
  - destruct σ1 as [s0 tr], σ2 as [s1 tr1].
    destruct H0 as [Hs Htr].
    subst.
    exists tr; auto.
  - tauto.
Qed.

Lemma Hoare_track_s (s: Σ) (tr: TR) (t: T):
  Hoare (fun x => x = (s, tr)) (track t)
    (fun _ x => x = (s, tr ++ (t, s) :: nil)).
Proof.
  unfold Hoare, track, Gupdate, track_f; simpl.
  split; intros.
  - destruct σ1 as [s0 tr0], σ2 as [s1 tr1].
    inversion H; destruct H0; subst; auto.
  - tauto.
Qed.

Lemma Hoare_track_inv (P: Σ * TR -> Prop) (t: T):
  (forall s tr, P (s, tr) -> P (s, tr ++ (t, s) :: nil)) ->
  Hoare P (track t) (fun _ => P).
Proof.
  intros.
  eapply Hoare_cons_post.
  2: apply Hoare_track.
  intros [] [s tr] [tr' [Htr HP]].
  subst.
  auto.
Qed.

End TraceErr.

Section StateTraceErr.

Context {Σ: Type}.

Notation STR := (list Σ) (only parsing).
Notation programTS := (@programG Σ STR) (only parsing).

Definition trackS_f (s: Σ) (tr1 tr2: STR) : Prop :=
  tr2 = tr1 ++ s :: nil.

Definition trackS : programTS unit :=
  Gupdate trackS_f.

Lemma trackS_live:
  Gupdate_live trackS_f.
Proof.
  unfold Gupdate_live, trackS_f.
  intros.
  eexists; eauto.
Qed.

Lemma Hoare_trackS (P: Σ * STR -> Prop):
  Hoare P trackS
    (fun _ '(s, tr) =>
      exists tr', tr = tr' ++ s :: nil /\ P (s, tr')).
Proof.
  unfold Hoare, trackS, Gupdate; simpl.
  split; intros.
  - destruct σ1 as [s0 tr], σ2 as [s1 tr1].
    destruct H0 as [Hs Htr].
    subst.
    exists tr; auto.
  - tauto.
Qed.

Lemma Hoare_trackS_s (s: Σ) (tr: STR):
  Hoare (fun x => x = (s, tr)) trackS
    (fun _ x => x = (s, tr ++ s :: nil)).
Proof.
  unfold Hoare, trackS, Gupdate, trackS_f; simpl.
  split; intros.
  - destruct σ1 as [s0 tr0], σ2 as [s1 tr1].
    inversion H; destruct H0; subst; auto.
  - tauto.
Qed.

Lemma Hoare_trackS_inv (P: Σ * STR -> Prop):
  (forall s tr, P (s, tr) -> P (s, tr ++ s :: nil)) ->
  Hoare P trackS (fun _ => P).
Proof.
  intros.
  eapply Hoare_cons_post.
  2: apply Hoare_trackS.
  intros [] [s tr] [tr' [Htr HP]].
  subst.
  auto.
Qed.

End StateTraceErr.

Notation TR A Σ := (list (A * Σ)) (only parsing).
Notation programT Σ T := (@programG Σ (TR T Σ)).
Notation STR Σ := (list Σ) (only parsing).
Notation programTS Σ := (@programG Σ (STR Σ)).
