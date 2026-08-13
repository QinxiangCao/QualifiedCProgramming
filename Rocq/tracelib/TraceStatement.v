Require Import TraceBasic TraceLogic.
Require Import Coq.Logic.Classical_Prop Lia.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope trace_scope.

Class StatementTrace (Stmt Tag: Type) := {
  statement_before: Stmt -> Tag;
  statement_after: Stmt -> Tag;
  statement_before_injective:
    forall stmt1 stmt2, statement_before stmt1 = statement_before stmt2 -> stmt1 = stmt2;
  statement_after_injective:
    forall stmt1 stmt2, statement_after stmt1 = statement_after stmt2 -> stmt1 = stmt2;
  statement_before_after_disjoint:
    forall stmt1 stmt2, statement_before stmt1 <> statement_after stmt2;
}.

Section TraceStatement.

Context {Stmt Tag Σ: Type}
        `{StatementTrace Stmt Tag}.

Notation TR := (TR Tag Σ) (only parsing).
Notation programT := (programT Σ Tag) (only parsing).

Definition trace_statement {A: Type} (stmt: Stmt) (body: programT A):
  programT A :=
  track (statement_before stmt);;
  x <- body;;
  track (statement_after stmt);;
  ret x.

Definition trace_statement_unit (stmt: Stmt) (body: programT unit):
  programT unit :=
  track (statement_before stmt);;
  body;;
  track (statement_after stmt).

Definition statement_snapshot
  (stmt: Stmt) (P: Σ -> Prop) (tr: TR): Prop :=
  tr |= have (tsAtom (statement_after stmt) P).

Definition statement_before_snapshot
  (stmt: Stmt) (P: Σ -> Prop) (tr: TR): Prop :=
  tr |= have (tsAtom (statement_before stmt) P).

Definition statement_trace_implies
  (stmt: Stmt) (P Q: Σ -> Prop) (tr: TR): Prop :=
  statement_before_snapshot stmt P tr -> statement_snapshot stmt Q tr.

Definition statement_snapshot_current
  (stmt: Stmt) (P: Σ -> Prop) (s: Σ) (tr: TR): Prop :=
  statement_snapshot stmt P tr /\ P s.

Lemma statement_snapshot_app:
  forall stmt P tr t s,
    statement_snapshot stmt P tr ->
    statement_snapshot stmt P (tr ++ (t, s) :: nil).
Proof.
  unfold statement_snapshot.
  intros.
  apply app_have_atom.
  left; auto.
Qed.

Lemma statement_before_snapshot_app:
  forall stmt P tr t s,
    statement_before_snapshot stmt P tr ->
    statement_before_snapshot stmt P (tr ++ (t, s) :: nil).
Proof.
  unfold statement_before_snapshot.
  intros.
  apply app_have_atom.
  left; auto.
Qed.

Lemma statement_snapshot_app_two:
  forall stmt P tr t1 s1 t2 s2,
    statement_snapshot stmt P tr ->
    statement_snapshot stmt P
      ((tr ++ (t1, s1) :: nil) ++ (t2, s2) :: nil).
Proof.
  intros.
  apply statement_snapshot_app.
  apply statement_snapshot_app.
  auto.
Qed.

Lemma statement_after_records_snapshot:
  forall stmt P s tr,
    P s ->
    Hoare (fun x => x = (s, tr))
          (track (statement_after stmt))
          (fun _ '(s', tr') => statement_snapshot_current stmt P s' tr').
Proof.
  intros.
  hoare_cons_post Hoare_track_s.
  intros _ [s' tr'] Hst.
  inversion Hst; subst; clear Hst.
  unfold statement_snapshot_current, statement_snapshot.
  split; auto.
  apply app_last_have_atom.
  unfold tsAtom; split; auto.
Qed.

Lemma trace_statement_records_snapshots:
  forall (stmt: Stmt) (P Q: Σ -> Prop) (body: program Σ unit),
    Hoare P body (fun _ => Q) ->
    Hoare (fun '(s, _) => P s)
          (trace_statement_unit stmt (liftG body))
          (fun _ '(s, tr) =>
            statement_before_snapshot stmt P tr /\
            statement_snapshot_current stmt Q s tr).
Proof.
  intros stmt P Q body Hbody.
  unfold trace_statement_unit.
  intro_state_pair.
  hoare_bind' Hoare_track_s.
  eapply Hoare_bind.
  {
    eapply Hoare_liftG_s.
    hoare_cons_pre Hbody.
    intros s0 Hstate; subst; auto.
  }
  intros body_result.
  eapply Hoare_conseq_pre with
    (P2 := fun '(s, tr) =>
      Q s /\ tr = (l ++ (statement_before stmt, σ) :: nil)%list).
  {
    intros [s tr] Hpost.
    destruct Hpost as [s' [Hstate HQ]].
    inversion Hstate; subst; auto.
  }
  hoare_cons_post Hoare_track.
  intros _ [s tr] [tr0 [Htr [HQ Htr0]]].
  subst tr tr0.
  split.
  - unfold statement_before_snapshot.
    apply app_have_atom; left.
    apply app_last_have_atom.
    unfold tsAtom; split; auto.
  - unfold statement_snapshot_current, statement_snapshot.
    split; auto.
    apply app_last_have_atom.
    unfold tsAtom; split; auto.
Qed.

Lemma Gequiv_trace_statement_unit:
  forall (stmt: Stmt) (body: program Σ unit),
    Gequiv body (trace_statement_unit stmt (liftG body)).
Proof.
  intros; unfold trace_statement_unit.
  Gequiv_autoT.
Qed.

Theorem Hoare_trace_statement_implies:
  forall (stmt: Stmt) (P Q: Σ -> Prop) (body: program Σ unit),
    Hoare P body (fun _ => Q) ->
    Hoare (fun '(s, _) => P s)
          (trace_statement_unit stmt (liftG body))
          (fun _ '(_, tr) => statement_trace_implies stmt P Q tr).
Proof.
  intros stmt P Q body Hbody.
  eapply Hoare_conseq_post.
  2: { eapply trace_statement_records_snapshots; exact Hbody. }
  intros _ [s tr] [Hbefore [Hafter Hcurrent]].
  unfold statement_trace_implies; intros _.
  exact Hafter.
Qed.

Lemma trace_statement_no_matching_before:
  forall (stmt: Stmt) (P: Σ -> Prop) (body: program Σ unit),
    Hoare (fun '(s, tr) => ~ P s /\ tr = nil)
          (trace_statement_unit stmt (liftG body))
          (fun _ '(_, tr) => ~ statement_before_snapshot stmt P tr).
Proof.
  intros stmt P body.
  unfold trace_statement_unit.
  intro_state_pair; destruct H0 as [Hnot Hnil]; subst l.
  hoare_bind' Hoare_track_s.
  eapply Hoare_bind.
  { eapply Hoare_liftG_s; apply Hoare_post_true. }
  intros body_result.
  eapply Hoare_conseq_pre with
    (P2 := fun '(s, tr) => tr = ((statement_before stmt, σ) :: nil)%list).
  {
    intros [s tr] Hpost.
    destruct Hpost as [s' [Hstate _]].
    inversion Hstate; subst; auto.
  }
  hoare_cons_post Hoare_track.
  intros _ [s tr] [tr0 [Htr Htr0]].
  subst tr tr0.
  unfold statement_before_snapshot, last_satisfy, have, lift.
  intros [j [[Hj1 Hj2] Hatom]].
  simpl in Hj2.
  destruct j as [|[|[|j]]]; simpl in Hatom; try lia.
  - unfold tsAtom in Hatom; destruct Hatom; auto.
  - unfold tsAtom in Hatom; destruct Hatom as [Htag _].
    exfalso; eapply statement_before_after_disjoint; eauto.
Qed.

Theorem Hoare_trace_statement_implies_empty:
  forall (stmt: Stmt) (P Q: Σ -> Prop) (body: program Σ unit),
    Hoare P body (fun _ => Q) ->
    Hoare (fun '(_, tr) => tr = nil)
          (trace_statement_unit stmt (liftG body))
          (fun _ '(_, tr) => statement_trace_implies stmt P Q tr).
Proof.
  intros stmt P Q body Hbody.
  eapply Hoare_conseq_pre with
    (P2 := fun st =>
      (P (fst st) /\ snd st = nil) \/ (~ P (fst st) /\ snd st = nil)).
  {
    intros [s tr] Hnil.
    destruct (classic (P s)); tauto.
  }
  eapply (@Hoare_disj (Σ * TR) unit
    (fun st => P (fst st) /\ snd st = nil)
    (fun st => ~ P (fst st) /\ snd st = nil)
    (trace_statement_unit stmt (liftG body))
    (fun _ '(_, tr) => statement_trace_implies stmt P Q tr)).
  - hoare_cons_pre (Hoare_trace_statement_implies stmt P Q body Hbody).
    intros [s tr] [HP _]; exact HP.
  - eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: { apply (trace_statement_no_matching_before stmt P body). }
      intros [s tr] Hpre; exact Hpre.
    }
    intros _ [s tr] Hnot.
    unfold statement_trace_implies; intros Hbefore; contradiction.
Qed.

End TraceStatement.
