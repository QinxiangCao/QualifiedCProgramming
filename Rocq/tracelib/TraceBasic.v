Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.
Require Export GhostCode.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section Trace.

Context {T: Type} (* tag type *)
        {Σ: Type} (* program state type *).

(* trace type *)
Notation TR := (list (T * Σ)) (only parsing).
(* program with trace *)
Notation programT := (@programG Σ TR) (only parsing).

(* track the current state *)
Definition track_f (t:T) (s: Σ) (g1 g2: TR) : Prop :=
  g2 = g1 ++ (t, s)::nil.

Definition track (t: T) : programT unit :=
  Gupdate (track_f t).

Lemma track_live (t:T):
  Gupdate_live (track_f t).
Proof.
  unfold Gupdate_live, track_f.
  intros.
  eexists; eauto.
Qed.

(** Trace Hoare *)
Lemma Hoare_track (P: Σ * TR -> Prop) (t: T):
  Hoare P (track t) 
  (fun _ '(s, tr) => 
    exists tr', tr = tr' ++ (t, s)::nil /\ P (s, tr')).
Proof.
  unfold Hoare, track; sets_unfold.
  intros (s0, tr) a (s1, tr1) HP (Hs & Htr).
  subst.
  exists tr; auto.
Qed.

Lemma Hoare_track_s (s: Σ) (tr: TR) (t: T):
  Hoare (fun x => x = (s, tr)) (track t) (fun _ x => x = (s, tr ++ (t, s)::nil)).
Proof.
  unfold Hoare, track, Gupdate, track_f; sets_unfold.
  intros (s0, tr0) a (s1, tr1) HP Hs.
  inversion HP; destruct Hs; subst.
  auto.
Qed.

Lemma Hoare_track_inv (P: Σ * TR -> Prop) (t: T):
  (forall s tr, P (s, tr) -> P (s, tr ++ (t, s)::nil)) ->
  Hoare P (track t) (fun _ => P).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:apply Hoare_track.
  intros a (s, tr) H1; clear a.
  destruct H1 as [tr' [Htr HP]].
  subst.
  auto.
Qed.


(** We may need trace monotone lemmas *)

End Trace.

Section StateTrace.

Context {Σ: Type}.

(* Specialized trace: store only states, no tags. *)
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
  unfold Hoare, trackS; sets_unfold.
  intros (s0, tr) a (s1, tr1) HP (Hs & Htr).
  subst.
  exists tr; auto.
Qed.

Lemma Hoare_trackS_s (s: Σ) (tr: STR):
  Hoare (fun x => x = (s, tr)) trackS
    (fun _ x => x = (s, tr ++ s :: nil)).
Proof.
  unfold Hoare, trackS, Gupdate, trackS_f; sets_unfold.
  intros (s0, tr0) a (s1, tr1) HP Hs.
  inversion HP; destruct Hs; subst.
  auto.
Qed.

Lemma Hoare_trackS_inv (P: Σ * STR -> Prop):
  (forall s tr, P (s, tr) -> P (s, tr ++ s :: nil)) ->
  Hoare P trackS (fun _ => P).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2: apply Hoare_trackS.
  intros a (s, tr) H1; clear a.
  destruct H1 as [tr' [Htr HP]].
  subst.
  auto.
Qed.

End StateTrace.

Notation TR A Σ := (list (A * Σ)) (only parsing).
Notation programT Σ T:= (@programG Σ (TR T Σ)).
Notation STR Σ := (list Σ) (only parsing).
Notation programTS Σ := (@programG Σ (STR Σ)).

(* Auto tactics for trace equivalence *)
Ltac Gequiv_autoT :=
  unfold track;
  Gequiv_auto;
  try apply track_live.

Ltac Gequiv_autoTS :=
  unfold trackS;
  Gequiv_auto;
  try apply trackS_live.
