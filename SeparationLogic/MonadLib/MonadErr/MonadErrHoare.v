Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrLoop.

Import SetsNotation.
Local Open Scope sets.

Export MonadNotation.
Local Open Scope monad.
Local Open Scope order_scope.
Local Open Scope Z_scope.

Section HoareBasic.
Import MonadErr.

Definition Hoare {Σ A: Type}
(P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop): Prop :=
  ((forall (a: A)(σ1 σ2: Σ), 
    P σ1 -> c.(nrm) σ1 a σ2 -> Q a σ2)
  /\ (forall (σ1: Σ), P σ1 -> c.(err) σ1 -> False)).


Lemma Hoare_proequiv:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare P c1 Q -> Hoare P c2 Q.
Proof.
  intros.
  unfold Hoare in *.
  destruct H0 as [H0 H1].
  unfold Sets.equiv in H; destruct H as [Hn He].
  split; intros.
  + specialize (H0 a σ1 σ2 H).
    apply H0; clear H0.    
    sets_unfold in Hn.
    apply Hn; auto.
  + specialize (H1 σ1 H).
    apply H1; clear H1.
    sets_unfold in He.
    apply He; auto.
Qed.

#[export] Instance Hoare_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (equiv ==> eq ==> iff) (@Hoare Σ A P).
Proof.
  unfold Proper, respectful; intros.
  subst x0; split; intros.
  - apply Hoare_proequiv with x; easy.
  - apply Hoare_proequiv with y; easy.
Qed.

#[export] Instance Hoare_setsequiv_iff_Proper {Σ: Type} {A: Type} :
  Proper (Sets.equiv ==> eq ==> Sets.equiv ==> iff) (@Hoare Σ A).
Proof.
  unfold Proper, respectful; intros P1 P2 HP c c' <- Q1 Q2 HQ.
  unfold Hoare.
  match goal with
  | |- (?A /\ ?B) <-> (?C /\ ?D) =>
    enough ((A <-> C) /\ (B <-> D)) by firstorder
  end.
  split.
  - split; intros; apply HQ; firstorder.
  - split; intros ? ? HPσ ?; apply HP in HPσ; firstorder.
Qed.

Lemma Hoare_bind {A B Σ: Type}: 
  forall (P: Σ -> Prop) (Q : A -> Σ -> Prop) (R: B -> Σ -> Prop)
  (c1: program Σ A) (c2: A -> program Σ B) ,
    Hoare P c1 Q -> (forall a, Hoare (Q a) (c2 a) R) -> Hoare P (bind c1 c2) R.
Proof.
  unfold Hoare.
  intros.
  split; simpl.
  + unfold nrm_nrm; intros.
    destruct H2 as [? [? [? ?]]].
    destruct H.
    specialize (H0 x).
    destruct H0.
    eapply H0; eauto.
  + sets_unfold.
    unfold nrm_err; intros.
    destruct H2.
    - destruct H.
      apply (H3 σ1 H1 H2).
    - destruct H2 as [? [? [? ?]]].
      specialize (H0 x).
      destruct H; destruct H0.
      eapply H5; eauto.
Qed.

Lemma Hoare_assert {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Q ->
    Hoare P (assert Q) (fun _ => P).
Proof.
  firstorder. congruence.
Qed. 

Lemma Hoare_assertS {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Prop),
    (forall s, P s -> Q s) ->
    Hoare P (assertS Q) (fun _ => P).
Proof.
  firstorder. congruence. 
Qed.

Theorem Hoare_any {Σ A: Type}:
  forall (P: Σ -> Prop),
    Hoare P (any A) (fun _ => P).
Proof.
  unfold any.
  firstorder. 
  simpl in H0.
  congruence. 
Qed.

Theorem Hoare_any_bind {Σ A B: Type}:
  forall (P: Σ -> Prop) (f: A -> program Σ B) (Q: B -> Σ -> Prop),
    (forall a, Hoare P (f a) Q) ->
    Hoare P (a <- any A;; f a) Q.
Proof.
  intros.
  eapply Hoare_bind.
  apply Hoare_any.
  simpl; auto.
Qed.

Theorem Hoare_get {A Σ: Type}:
  forall (P: Σ -> Prop) (Pa: Σ -> A -> Prop),
    Hoare P (get Pa) (fun a s2 => Pa s2 a /\ P s2).
Proof.
  unfold get.
  simpl. 
  firstorder;try congruence. 
Qed.

Theorem Hoare_update {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Σ -> Prop),
    Hoare P (update Q) (fun a s2 => exists s1, Q s1 s2 /\ P s1).
Proof. firstorder. Qed.


Theorem Hoare_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P2 f Q2 ->
    Hoare P1 f Q1.
Proof. firstorder. Qed.

Lemma Hoare_spec_derivation {Σ A L: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop)
         (SpecP: L -> Σ -> Prop) (SpecQ: L -> A -> Σ -> Prop),
    (forall l, Hoare (SpecP l) c (SpecQ l)) ->
    (forall s, P s -> exists l, SpecP l s) ->
    (forall s0 a s1,
        P s0 ->
        (forall l, SpecP l s0 -> SpecQ l a s1) ->
        Q a s1) ->
    Hoare P c Q.
Proof.
  unfold Hoare; intros * Hspec Hlive Hderive.
  split.
  - intros a s0 s1 HP Hrun.
    apply Hderive with (s0 := s0); auto.
    intros l Hpre.
    destruct (Hspec l) as [Hnrm _].
    eapply Hnrm; eauto.
  - intros s HP Herr.
    destruct (Hlive s HP) as [l Hpre].
    destruct (Hspec l) as [_ Herr_spec].
    eapply Herr_spec; eauto.
Qed.


Lemma Hoare_implies {A Σ: Type}:
  forall (P P': Σ -> Prop) (P0: Prop)
         (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> P0 /\ P' σ) ->
    (P0 -> Hoare P' c Q) ->
    Hoare P c Q.
Proof. firstorder. Qed.

Lemma Hoare_unit_pre {A: Type} :
  forall (P: Prop) (c: program unit A) (Q: A -> unit -> Prop),
    (P -> Hoare (fun _ => True) c Q) ->
    Hoare (fun _ => P) c Q.
Proof. firstorder. Qed.

Lemma Hoare_cons_pre {B Σ: Type} : 
  forall (P P': Σ -> Prop) (c: program Σ B) (Q: B -> Σ -> Prop),
    (forall σ, P' σ -> P σ) ->
    Hoare P c Q ->
    Hoare P' c Q.
Proof. firstorder. Qed.

Lemma Hoare_cons_post {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q Q': A -> Σ -> Prop),
    (forall a σ, Q a σ -> Q' a σ) ->
    Hoare P c Q ->
    Hoare P c Q'.
Proof. firstorder. Qed.

Lemma Hoare_choice {A Σ: Type}:
  forall (P: Σ -> Prop) (c1 c2: program Σ A) (Q: A -> Σ -> Prop),
    Hoare P c1 Q -> Hoare P c2 Q -> Hoare P (choice c1 c2) Q.
Proof.
  unfold Hoare; intros.
  destruct H as [H1 H2]; destruct H0 as [H3 H4].
  split; intros; unfold choice in H0; simpl in H0.
  - specialize (H1 a σ1); specialize (H3 a σ1).
    destruct H0; [apply H1 | apply H3]; auto.
  - specialize (H2 σ1); specialize (H4 σ1).
    destruct H0; [apply H2 | apply H4]; auto.
Qed.

(* A disjunctive version of choice for Hoare triples. *)
Lemma Hoare_choice_disj {Σ A}
      (P: Σ -> Prop) (c1 c2: program Σ A)
      (Q1 Q2: A -> Σ -> Prop):
  Hoare P c1 Q1 ->
  Hoare P c2 Q2 ->
  Hoare P (choice c1 c2) (fun a s => Q1 a s \/ Q2 a s).
Proof.
  intros H1 H2; unfold Hoare in *.
  destruct H1 as [H1n H1e], H2 as [H2n H2e].
  split; intros.
  - unfold choice in H0; simpl in H0.
    destruct H0; [left; eapply H1n | right; eapply H2n]; eauto.
  - unfold choice in H0; simpl in H0.
    destruct H0; [eapply H1e | eapply H2e]; eauto.
Qed.

Lemma Hoare_assume' {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Hoare P (assume!! Q) (fun _ s => P s /\ Q).
Proof.
  intros P Q.
  unfold Hoare; simpl; split; intros; try tauto.
  destruct H0; subst; tauto.
Qed.

Lemma Hoare_assume_bind {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (P2 -> Hoare P1 c Q) -> Hoare P1 (assume!! P2;; c) Q.
Proof.
  split; intros; unfold test in H1; simpl in H1.
  - unfold nrm_nrm in H1. destruct H1 as [_ [? [[Hs HP] H1]]].
    subst σ1. specialize (H HP). destruct H as [H _].
    specialize (H a x σ2). tauto.
  - destruct H1; [tauto |].
    unfold nrm_err in H1. destruct H1 as [_ [s [[? ?] ?]]].
    subst σ1. specialize (H H2). destruct H as [_ H].
    specialize (H s). tauto.
Qed.

Lemma Hoare_assumeS {Σ: Type}:
  forall (P1 P2: Σ -> Prop),
    Hoare P1 (assume P2) (fun _ s => P1 s /\ P2 s).
Proof.
  intros.
  firstorder; congruence.
Qed.

Lemma Hoare_assumeS_bind {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (Hoare (fun s => P1 s /\ P2 s) c Q) -> Hoare P1 (assume P2;; c) Q.
Proof.
  intros.
  eapply Hoare_bind; [apply Hoare_assumeS|].
  simpl; auto.
Qed.

Lemma Hoare_assert_bind {A Σ: Type}:
  forall (P: Σ -> Prop) (P': Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> P') ->
    (P' -> Hoare P c Q) -> 
    Hoare P (assert P';; c) Q.
Proof.
  unfold Hoare; intros.
  split; intros; unfold assert in H2; simpl in H2.
  - unfold nrm_nrm in H2. destruct H2 as [_ [s [[Hs HP] Hn]]].
    subst σ1. specialize (H0 HP). destruct H0 as [H0 _].
    specialize (H0 a s σ2). tauto.
  - pose proof (H σ1) H1. 
    destruct H2; [tauto |].
    unfold nrm_err in H2. destruct H2 as [_ [s [[? ?] ?]]].
    subst σ1. specialize (H0 H3). destruct H0 as [_ H0].
    specialize (H0 s). tauto.
Qed.

Lemma Hoare_assertS_bind {A Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Prop) (c: program Σ A) (R: A -> Σ -> Prop),
    (forall s, P s -> Q s) ->
    Hoare P (assertS Q ;; c) R <-> Hoare P c R.
Proof.
  intros * Himp; split; intros Hhoare.
  - unfold Hoare in *.
    destruct Hhoare as [Hn Herr].
    split; intros.
    + apply (Hn a σ1 σ2 H).
      unfold bind; simpl.
      unfold MonadErr.bind; simpl.
      exists tt; exists σ1; split; [| assumption].
      split; [reflexivity | apply Himp; assumption].
    + apply (Herr σ1 H).
      unfold bind; simpl.
      unfold MonadErr.bind; simpl.
      right.
      exists tt; exists σ1; split; [| assumption].
      split; [reflexivity | apply Himp; assumption].
  - eapply Hoare_bind; [apply Hoare_assertS; exact Himp|].
    intros []; simpl; assumption.
Qed.

(* Additional basic lemmas mirrored from StateRelMonad/StateRelHoare.v *)
Lemma Hoare_step {Σ A: Type}:
  forall (P: Σ -> Prop) (f: program Σ A),
    (forall s, P s -> ~ err f s) ->
    Hoare P f (fun a s2 => exists s1, f.(nrm) s1 a s2 /\ P s1).
Proof. firstorder. Qed.


Lemma Hoare_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) (f: program Σ A) (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) ->
    Hoare P f (fun a s => forall x, Q x a s).
Proof.
  unfold Hoare; intros X P f Q  Hforall.
  split.
  - intros a σ1 σ2 HP Hrun x.
    destruct (Hforall x) as [Hn _].
    eapply Hn; eauto.
  - intros σ1 HP.
Abort.

Lemma Hoare_state_intro {A Σ}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s0, P s0 -> Hoare (fun s => s = s0) c Q)->
    Hoare P c Q.
Proof. firstorder. Qed.

Lemma Hoare_ret {A Σ: Type}:
  forall (P: Σ -> Prop) (a: A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> Q a σ) ->
    Hoare P (return a) Q.
Proof. firstorder. subst. auto. Qed.

Lemma Hoare_post_true:
  forall {A Σ} (P: Σ -> Prop) (c: program Σ A),
    (forall s, P s -> ~ err c s) ->
    Hoare P c (fun _ _ => True).
Proof. firstorder. Qed.


Lemma Hoare_progrefine:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    (nrm c2 ⊆ nrm c1) ->
    (err c2 ⊆ err c1) ->
    Hoare P c1 Q -> Hoare P c2 Q.
Proof.
  intros * Hn HerrInc [Hnrm Herr].
  unfold Hoare.
  split; intros.
  - apply (Hnrm a σ1 σ2 H); eapply Hn; eauto.
  - apply (Herr σ1 H); eapply HerrInc; eauto.
Qed.


Lemma Hoare_equiv_iff {Σ A: Type}:
  forall (P: Σ -> Prop) (c1 c2: program Σ A) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare P c1 Q <-> Hoare P c2 Q.
Proof.
  intros; split; intro Hhoare;
    eapply Hoare_proequiv; eauto; try rewrite H; reflexivity.
Qed.

Lemma Hoare_step_s {A Σ: Type}:
  forall (s0: Σ) (c: program Σ A),
    (~ err c s0) ->
    Hoare (fun s => s = s0) c (fun a s1 => c.(nrm) s0 a s1).
Proof.
  intros s0 c Herr.
  unfold Hoare; split; intros; subst; auto.
Qed.


Lemma Hoare_assume_s {Σ}:
  forall (s0: Σ) (Q: Σ -> Prop),
    Q s0 ->
    Hoare (fun s => s = s0) (assume Q) (fun _ s1 => s1 = s0 /\ Q s0).
Proof.
  intros s0 Q HQ.
  eapply Hoare_cons_post.
  2: apply Hoare_assumeS.
  simpl; intros [] σ [HP HQ'].
  subst; tauto.
Qed.

Definition continue_case {A B Σ: Type} (ab: CntOrBrk A B): (program Σ A) := 
  {|
    nrm := fun s1 r s2 => match ab with
                          | by_continue a => s1 = s2 /\ r = a
                          | by_break _ => ∅
                          end;
    err := ∅;
  |}.

Definition break_case {A B Σ: Type} (ab: CntOrBrk A B): (program Σ B) := 
  {|
    nrm := fun s1 r s2 => match ab with
                          | by_continue _ => ∅
                          | by_break b => s1 = s2 /\ r = b
                          end;
    err := ∅;
  |}.

Lemma Hoare_cnt_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a: A),
    (forall s, P s -> Q a s) ->
    Hoare P (@continue_case A B Σ (by_continue a)) Q.
Proof.
  intros.
  unfold Hoare, continue_case; simpl.
  split; intros.
  - destruct H1; subst.
    apply H; auto.
  - tauto.
Qed.

Lemma Hoare_brk_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (b: B),
    (forall s, P s -> Q b s) ->
    Hoare P (@break_case A B Σ (by_break b)) Q.
Proof.
  intros.
  unfold Hoare, break_case; simpl.
  split; intros.
  - destruct H1; subst.
    apply H; auto.
  - tauto.
Qed.

Lemma Hoare_brk_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (a: A),
    Hoare P (@break_case A B Σ (by_continue a)) Q.
Proof.
  intros.
  unfold Hoare, break_case; simpl.
  split; intros; tauto.
Qed.

Lemma Hoare_cnt_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (b: B),
    Hoare P (@continue_case A B Σ (by_break b)) Q.
Proof.
  intros.
  unfold Hoare, continue_case; simpl.
  split; intros; tauto.
Qed.

Lemma Hoare_sum {A B Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ (CntOrBrk A B)) (Q: A -> Σ -> Prop) (R: B -> Σ -> Prop),
    Hoare P (x <- c;; continue_case x) Q ->
    Hoare P (x <- c;; break_case x) R ->
    Hoare P c (fun x σ => match x with
                          | by_continue a => Q a σ
                          | by_break b => R b σ
                          end).
Proof.
  intros.
  unfold Hoare in *.
  split; intros.
  2:{ 
    destruct H as [_ H], H0 as [_ H0].
    specialize (H σ1 H1).
    unfold bind in H.
    simpl in H.
    sets_unfold in H.
    tauto.
  }
  destruct H as [H _], H0 as [H0 _].
  destruct a.
  - specialize (H a σ1 σ2 H1).
    apply H; clear H.
    unfold bind; simpl.
    unfold nrm_nrm.
    exists (by_continue a); exists σ2.
    simpl; tauto.
  - specialize (H0 b σ1 σ2 H1).
    apply H0; clear H0.
    unfold bind; simpl.
    unfold nrm_nrm.
    exists (by_break b); exists σ2.
    simpl; tauto.
Qed.

Lemma Hoare_conj {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop) (R: A -> Σ -> Prop),
    Hoare P c Q ->
    Hoare P c R ->
    Hoare P c (fun a σ => Q a σ /\ R a σ).
Proof. firstorder. Qed.

Theorem Hoare_disj {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q: A -> Σ -> Prop),
    Hoare P1 f Q ->
    Hoare P2 f Q ->
    Hoare (fun s => P1 s \/ P2 s) f Q.
Proof. firstorder. Qed.

Lemma Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof. firstorder. Qed.

Lemma Hoare_stateless:
  forall {A Σ} (P: Prop) (c: program Σ A) Q,
    (P -> Hoare (fun _ => True) c Q) ->
    Hoare (fun _ => P) c Q.
Proof.
  unfold Hoare; intros.
  sets_unfold; intros.
  split.
  - intros.
    apply H in H0.
    destruct H0.
    apply (H0 a σ1 σ2); auto.
  - intros.
    apply H in H0.
    destruct H0.
    apply (H2 σ1); auto.
Qed.

Lemma Hoare_stateless':
  forall {A Σ} (P: Prop) (P': Σ -> Prop) (c: program Σ A) Q,
    (P -> Hoare P' c Q) ->
    Hoare (fun s => P' s /\ P) c Q.
Proof.
  unfold Hoare; intros.
  sets_unfold; intros.
  split.
  - intros.
    specialize (H ltac:(tauto)).
    destruct H.
    apply (H a σ1 σ2); tauto.
  - intros.
    specialize (H ltac:(tauto)).
    destruct H.
    apply (H2 σ1); tauto.
Qed.

Lemma Hoare_bot {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    Hoare P bot Q.
Proof. firstorder. Qed.

Lemma Hoare_update_bind {Σ A: Type}:
  forall (P: Σ -> Prop) (f: Σ -> Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s1,  P s1 -> Hoare (fun s2 => f s1 s2) c Q) ->
    Hoare P (update f;; c) Q.
Proof. firstorder. Qed.


Lemma Hoare_update_s {Σ}:
  forall (s0: Σ) (f: Σ -> Σ -> Prop),
    Hoare (fun s => s = s0) (update f) (fun _ s1 => f s0 s1).
Proof.
  firstorder.
  unfold update in H0. simpl in H0. subst. auto.
Qed.

Lemma Hoare_update' {Σ}:
  forall (s0: Σ) (f: Σ -> Σ),
    Hoare (fun s => s = s0) (update' f) (fun _ s1 => s1 = f s0).
Proof.
  intros.
  eapply Hoare_update_s.
Qed.

Lemma Hoare_get_s {Σ A}:
  forall (s0: Σ) (Pa: Σ -> A -> Prop),
    Hoare (fun s => s = s0) (get Pa) (fun a s1 => s1 = s0 /\ Pa s0 a).
Proof.
  firstorder; congruence. 
Qed.

Lemma Hoare_get' {Σ A}:
  forall (s0: Σ) (fa: Σ -> A),
    Hoare (fun s => s = s0) (get' fa) (fun a s1 => s1 = s0 /\ a = fa s0).
Proof.
  intros.
  eapply Hoare_get_s.
Qed.

End HoareBasic.

(** Tactics *)
Tactic Notation "hoare_bind" uconstr(H) :=
  eapply Hoare_bind; [apply H |]; intros.

(* for unit type *)
Tactic Notation "hoare_bind'" uconstr(H) :=
  eapply Hoare_bind; [apply H |]; simpl; intros _.

Ltac hoare_conj :=
  match goal with
    | |- Hoare _  _ (fun _ _ => _ /\ _) => apply Hoare_conj; [try hoare_conj | try hoare_conj]
    | |- Hoare _ _ _ => eapply Hoare_cons_pre
  end.

Ltac hoare_intros :=
  apply Hoare_pre_ex; intros.

Ltac stateless_intros :=
  repeat (apply Hoare_stateless || apply Hoare_stateless'); intros.

Ltac hoare_step :=
  unfold continue, break;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_step
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_step
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_l
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind; intros
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assumeS_bind
    | |- Hoare _ (assert _;; _) _ => apply Hoare_assert_bind; [ |intros]
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice
    | |- Hoare _ (ret _) _ => apply Hoare_ret; intros
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (match ?a with _ => _ end) _ => destruct a; hoare_step
  end; auto.

Ltac hoare_auto :=
  unfold continue, break;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_l; try hoare_auto
    | |- Hoare _ (bind (assert _) _) _ => hoare_bind' Hoare_assert; try hoare_auto
    | |- Hoare _ (bind (assertS _) _) _ => hoare_bind' Hoare_assertS; try hoare_auto
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind; intros; try hoare_auto
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assumeS_bind; try hoare_auto
    | |- Hoare _ (assert _;; _) _ => apply Hoare_assert_bind; [auto |intros; try hoare_auto]
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto
    | |- Hoare _ (bind _ _) _ => apply Hoare_bind; intros; try hoare_auto
    | |- Hoare _ (ret _) _ => apply Hoare_ret; intros
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (match ?a with _ => _ end) _ => destruct a; try hoare_auto
  end; auto.

Ltac hoare_auto_s :=
  unfold continue, break;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto_s
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto_s
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_l; try hoare_auto_s
    | |- Hoare _ (bind (assert _) _) _ => hoare_bind' Hoare_assert; try hoare_auto_s
    | |- Hoare _ (bind (assertS _) _) _ => hoare_bind' Hoare_assertS; try hoare_auto_s
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind; intros; try hoare_auto_s
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assumeS_bind; try hoare_auto_s
    | |- Hoare _ (assert _;; _) _ => apply Hoare_assert_bind; [auto | intros; try hoare_auto_s]
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto_s
    | |- Hoare _ (bind _ _) _ => apply Hoare_bind; intros; try hoare_auto_s
    | |- Hoare _ (ret _) _ => apply Hoare_ret; intros
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (match ?a with _ => _ end) _ => destruct a; try hoare_auto_s
  end; auto.

Ltac monad_law :=
  repeat (rewrite bind_assoc ||
          rewrite bind_ret_l ||
          rewrite bind_ret_r).

Ltac intro_bound :=
  unfold Sets.equiv; simpl; unfold Sets.lift_equiv; intros.

Ltac monad_equiv :=
  unfold continue_case, break_case;
  repeat (prog_nf; try easy;
          apply bind_equiv; try easy;
          intro_bound).

Tactic Notation "hoare_apply" uconstr(H) :=
  eapply Hoare_proequiv;
  [ | apply H; try tauto];
  monad_equiv.

Tactic Notation "hoare_cons_pre" uconstr(H) :=
  eapply Hoare_cons_pre; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_cons_post" uconstr(H) :=
  eapply Hoare_cons_post; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_cons" uconstr(H) :=
  eapply Hoare_cons_pre; [|eapply Hoare_cons_post; [| apply H] ]; simpl; try tauto.


(** Hoare Logic For Recursions and Loops *)
Lemma Hoare_BW_fix {Σ A B: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop) (a: A),
    (forall W: A -> program Σ B,
        (forall a, Hoare (P a) (W a) (fun b s => Q a b s)) ->
        forall a, Hoare (P a) (f W a) (fun b s => Q a b s)) ->
    Hoare (P a) (BW_fix f a) (fun b s => Q a b s).
Proof.
  intros.
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (forall i, Hoare (P a) (Init.Nat.iter i f bot a) (Q a)).
  2:{
    unfold Hoare in H0.
    split. 
    - intros b s1 s2 H1 H2.
      destruct H2 as [i H2].
      eapply H0; eauto.
    - intros s1 H1 H2.
      destruct H2 as [i H2].
      eapply H0; eauto.
  }
  intros i; revert a.
  induction i.
  split; simpl; easy.
  simpl.
  apply H; auto.
Qed.

Lemma Hoare_BW_fix_logicv {Σ A B C: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> C -> Σ -> Prop) (Q: A -> C -> B -> Σ -> Prop) (a: A) c,
    (forall W: A -> program Σ B,
        (forall a c, Hoare (P a c) (W a) (fun b s => Q a c b s)) ->
        forall a c, Hoare (P a c) (f W a) (fun b s => Q a c b s)) ->
    Hoare (P a c) (BW_fix f a) (fun b s => Q a c b s).
Proof.
  intros.
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i a c,
             Hoare (P a c) (Init.Nat.iter i f bot a) (fun b s => Q a c b s)).
  { intro i; induction i; intros a0 c0; simpl.
    - split; simpl; easy.
    - apply H; auto. }
  split.
  - intros b s1 s2 HP Hrun.
    destruct Hrun as [i Hi].
    specialize (Hiter i a c) as [Hnrm _].
    eapply Hnrm; eauto.
  - intros s1 HP Herr.
    destruct Herr as [i Hi].
    specialize (Hiter i a c) as [_ Herr'].
    eapply Herr'; eauto.
Qed.

Lemma Hoare_BW_fix_prog {Σ A: Type}:
  forall (f: program Σ A -> program Σ A)
         (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    (forall W, Hoare P W Q -> Hoare P (f W) Q) ->
    Hoare P (BW_fix f) Q.
Proof.
  intros f * Hmono.
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i, Hoare P (Init.Nat.iter i f bot) Q).
  { intro i; induction i; simpl.
    - split; simpl; easy.
    - apply Hmono; auto. }
  split.
  - intros a σ1 σ2 HP Hrun.
    destruct Hrun as [i Hi].
    specialize (Hiter i) as [Hnrm _].
    eapply Hnrm; eauto.
  - intros σ1 HP Herr.
    destruct Herr as [i Hi].
    specialize (Hiter i) as [_ Herr'].
    eapply Herr'; eauto.
Qed.

Theorem Hoare_BW_fix_logicv_conj' {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P1 : A -> C -> Σ -> Prop)
       (Q1 : A -> C -> B -> Σ -> Prop) 
       a c,
forall {D: Type}
       (P2 : A -> D -> Σ -> Prop) (Q2 : A -> D -> B -> Σ -> Prop),
  (forall a d, Hoare (P2 a d) (BW_fix F a) (Q2 a d)) ->
  (forall W: A -> program Σ B, 
    (forall a d, Hoare (P2 a d) (W a) (Q2 a d)) ->
    (forall a c, Hoare (P1 a c) (W a) (Q1 a c)) ->
    (forall a c, Hoare (P2 a c) (F W a) (Q2 a c)) ->
    (forall a c, Hoare (P1 a c) (F W a) (Q1 a c))) ->  
  (Hoare (P1 a c) (BW_fix F a) (Q1 a c)).
Proof.
  intros *  HT1; intros.
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i a c,
             Hoare (P1 a c) (Init.Nat.iter i F bot a) (fun b s => Q1 a c b s)).
  { assert (forall n a d, Hoare (P2 a d) (Nat.iter n F bot a) (Q2 a d)).
  { intros.
    specialize (HT1 a0 d).
    unfold Hoare.
    unfold Hoare, BW_fix in HT1.
    destruct HT1 as [HT1nrm HT1err].
    split.
    - 
    intros.
    eapply (HT1nrm _ _ σ2 H0).
    exists n.
    auto.
    - 
    intros.
    eapply (HT1err _ H0).
    exists n.
    auto.
  }
    intro i; induction i; intros a0 c0; simpl.
    - split; simpl; easy.
    - apply H.
      apply H0.
      apply IHi.
      specialize (H0 (S i)).
      simpl in H0.
      apply H0. }
  split.
  - intros b s1 s2 HP Hrun.
    destruct Hrun as [i Hi].
    specialize (Hiter i a c) as [Hnrm _].
    eapply Hnrm; eauto.
  - intros s1 HP Herr.
    destruct Herr as [i Hi].
    specialize (Hiter i a c) as [_ Herr'].
    eapply Herr'; eauto.
Qed.

Lemma Hoare_whileP {Σ: Type} (cond: Σ -> Prop)
  (body : program Σ unit) (P: Σ -> Prop):
  Hoare (fun s => cond s /\ P s) body (fun _ s => P s) ->
  Hoare P (whileP cond body) (fun _ s => P s /\ ~ cond s).
Proof.
  intros.
  unfold whileP.
  apply Hoare_BW_fix_prog.
  intros W HW.
  unfold whileP_f.
  eapply Hoare_choice.
  - apply Hoare_assumeS_bind.
    eapply Hoare_bind.
    + eapply Hoare_cons_pre; [| eapply H]. intros; tauto.
    + intros []. apply HW.
  - apply Hoare_assumeS_bind.
    apply Hoare_ret.
    tauto.
Qed.

Lemma Hoare_while {Σ: Type}
  (cond: program Σ bool) (body : program Σ unit) (P: Σ -> Prop):
  Hoare P cond (fun _ s => P s) ->
  Hoare P body (fun _ s => P s) ->
  Hoare P (while cond body) (fun _ s => P s).
Proof.
  intros.
  unfold while.
  apply Hoare_BW_fix_prog.
  intros W HW.
  unfold while_f.
  eapply Hoare_bind; [eapply H |].
  intros x.
  destruct x.
  - eapply Hoare_bind; [eapply H0 |].
    intros [].
    apply HW.
  - apply Hoare_ret.
    auto.
Qed.

Lemma Hoare_whileret {Σ A: Type}
  (cond: A -> program Σ bool)
  (body : A -> program Σ A)
  (P: A -> Σ -> Prop) (a: A):
  (forall a, Hoare (P a) (cond a) (fun _ s => P a s)) ->
  (forall a, Hoare (P a) (body a) P) ->
  Hoare (P a) (whileret cond body a) P.
Proof.
  intros.
  unfold whileret.
  apply Hoare_BW_fix with (P:= P) (Q:= fun _ => P).
  intros W HW a0.
  unfold whileret_f.
  eapply Hoare_bind; [eapply H |].
  intros x.
  destruct x.
  - eapply Hoare_bind; [eapply H0 |].
    intros a1.
    apply HW.
  - apply Hoare_ret.
    auto.
Qed.

Lemma Hoare_whileretP {Σ A: Type}
  (cond: A -> Σ -> Prop) (body : A -> program Σ A)
  (P: A -> Σ -> Prop) (a: A):
  (forall a, Hoare (fun s => cond a s /\ P a s) (body a) P) ->
  Hoare (P a) (whileretP cond body a) (fun a s => P a s /\ ~ cond a s).
Proof.
  intros.
  unfold whileretP.
  apply Hoare_BW_fix with (P:= P) (Q:= fun (_:A) (b:A) s => P b s /\ ~ cond b s).
  intros W HW a0.
  unfold whileretP_f.
  eapply Hoare_choice.
  - apply Hoare_assumeS_bind.
    eapply Hoare_bind.
    + eapply Hoare_cons_pre; [| eapply H]. intros; tauto.
    + intros a1. apply HW.
  - apply Hoare_assumeS_bind.
    apply Hoare_ret. tauto.
Qed.

(* we consider a recursive monadic program (A -> program Σ R) may have multiple specifications *)
Record monad_funcspec {Σ A R: Type}: Type := mk_mfs { 
  mFS_lv : Type;
  mFS_pre : A -> mFS_lv -> Σ -> Prop;
  mFS_Post : A -> mFS_lv -> R -> Σ -> Prop;
  }.

Definition monad_funcspecs {Σ A R: Type} : Type := list (@monad_funcspec Σ A R).
Definition monad_sat_funcspec  {Σ A R: Type} 
  (m: (A -> program Σ R)) (fs: monad_funcspec) : Prop :=
  forall (a: A) (lv: mFS_lv fs),
    Hoare ((mFS_pre fs) a lv) (m a) ((mFS_Post fs) a lv).

Theorem Hoare_fix_logicv_fspecs {Σ A R: Type}:
forall (F: (A -> program Σ R) -> (A -> program Σ R)) Fspecs fs,
  Forall (fun fs => monad_sat_funcspec (fun a => BW_fix F a) fs) Fspecs ->
  (forall W: A -> program Σ R, 
    (Forall (fun fs => monad_sat_funcspec W fs) Fspecs) ->
    (forall a lv, Hoare ((mFS_pre fs) a lv) (W a) ((mFS_Post fs) a lv)) ->
    (forall a lv, Hoare ((mFS_pre fs) a lv) (F W a) ((mFS_Post fs) a lv))) ->  
  (forall (a: A) (lv: mFS_lv fs),
    Hoare ((mFS_pre fs) a lv) (BW_fix F a) ((mFS_Post fs) a lv)).
Proof.
  intros F Fspecs fs Hsat Hstep a lv.
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  (* Every finite iterate of F satisfies all specs in Fspecs. *)
  assert (Hforall: forall n,
            Forall (fun fs0 =>
              monad_sat_funcspec (fun a => Init.Nat.iter n F bot a) fs0) Fspecs).
  { intros n.
    apply Forall_forall.
    rewrite Forall_forall in Hsat.
    intros fs0 Hmem a0 lv0.
    specialize (Hsat fs0 Hmem a0 lv0).
    (* refine BW_fix spec to the n-th iterate *)
    eapply Hoare_progrefine; [ | | exact Hsat].
    - intros s1' r' s2' Hnrm; exists n; exact Hnrm.
    - intros s1' Herr; exists n; exact Herr.
  }
  assert (Hiter: forall i a c,
             Hoare ((mFS_pre fs)  a c) (Init.Nat.iter i F bot a) (fun b s => (mFS_Post fs) a c b s)).
  { intro i; induction i; intros a0 c0; simpl.
    - split; simpl; easy.
    - apply Hstep.
      apply Hforall.
      apply IHi.
  }
  split.
  - intros b s1 s2 HP Hrun.
    destruct Hrun as [i Hi].
    specialize (Hiter i a lv) as [Hnrm _].
    eapply Hnrm; eauto.
  - intros s1 HP Herr.
    destruct Herr as [i Hi].
    specialize (Hiter i a lv) as [_ Herr'].
    eapply Herr'; eauto.
Qed.

(** Backend-independent recursion rules. *)
Theorem Hoare_Rec {Σ A B: Type}:
  forall (F: (A -> program Σ B) -> A -> program Σ B)
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop) (a: A),
    (forall W: A -> program Σ B,
      (forall a, Hoare (P a) (W a) (Q a)) ->
      forall a, Hoare (P a) (F W a) (Q a)) ->
    Hoare (P a) (Rec F a) (Q a).
Proof.
  intros. unfold Rec. apply Hoare_BW_fix. assumption.
Qed.

Theorem Hoare_Rec_prog {Σ A: Type}:
  forall (F: program Σ A -> program Σ A)
         (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    (forall W, Hoare P W Q -> Hoare P (F W) Q) ->
    Hoare P (Rec F) Q.
Proof.
  intros. unfold Rec. apply Hoare_BW_fix_prog. assumption.
Qed.

Theorem Hoare_Rec_logicv {Σ A B C: Type}:
  forall (F: (A -> program Σ B) -> A -> program Σ B)
         (P: A -> C -> Σ -> Prop)
         (Q: A -> C -> B -> Σ -> Prop) a c,
    (forall W: A -> program Σ B,
      (forall a c, Hoare (P a c) (W a) (Q a c)) ->
      forall a c, Hoare (P a c) (F W a) (Q a c)) ->
    Hoare (P a c) (Rec F a) (Q a c).
Proof.
  intros. unfold Rec. apply Hoare_BW_fix_logicv. assumption.
Qed.

Theorem Hoare_Rec_logicv_conj' {Σ A B C: Type}:
  forall (F: (A -> program Σ B) -> A -> program Σ B)
         (P1: A -> C -> Σ -> Prop)
         (Q1: A -> C -> B -> Σ -> Prop) a c,
  forall {D: Type}
         (P2: A -> D -> Σ -> Prop)
         (Q2: A -> D -> B -> Σ -> Prop),
    (forall a d, Hoare (P2 a d) (Rec F a) (Q2 a d)) ->
    (forall W: A -> program Σ B,
      (forall a d, Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall a c, Hoare (P1 a c) (W a) (Q1 a c)) ->
      (forall a c, Hoare (P2 a c) (F W a) (Q2 a c)) ->
      forall a c, Hoare (P1 a c) (F W a) (Q1 a c)) ->
    Hoare (P1 a c) (Rec F a) (Q1 a c).
Proof.
  intros. unfold Rec in *. eapply Hoare_BW_fix_logicv_conj'; eauto.
Qed.

Theorem Hoare_Rec_fspecs {Σ A R: Type}:
  forall (F: (A -> program Σ R) -> A -> program Σ R) Fspecs fs,
    Forall (fun fs => monad_sat_funcspec (fun a => Rec F a) fs) Fspecs ->
    (forall W: A -> program Σ R,
      Forall (fun fs => monad_sat_funcspec W fs) Fspecs ->
      (forall a lv, Hoare ((mFS_pre fs) a lv) (W a) ((mFS_Post fs) a lv)) ->
      forall a lv, Hoare ((mFS_pre fs) a lv) (F W a) ((mFS_Post fs) a lv)) ->
    forall (a: A) (lv: mFS_lv fs),
      Hoare ((mFS_pre fs) a lv) (Rec F a) ((mFS_Post fs) a lv).
Proof.
  intros. unfold Rec in *. eapply Hoare_fix_logicv_fspecs; eauto.
Qed.

Tactic Notation "hoare_rec" uconstr(P) uconstr(Q) :=
  lazymatch goal with
  | |- Hoare _ (Rec ?F ?a) _ => eapply (@Hoare_Rec _ _ _ F P Q a)
  | |- ?G => fail 1 "hoare_rec: expected a Hoare goal headed by Rec" G
  end.

Ltac hoare_fix_nolv_auto A :=
   lazymatch goal with
  | |- @Hoare ?Sigma ?R ?P1 (Rec ?F ?a) ?P2 =>
    unfold Rec; hoare_fix_nolv_auto A
  | |- @Hoare ?Σ ?R ?P1 (BW_fix ?F ?a) ?P2 =>
    let P := fresh "P" in evar (P: A -> Σ  -> Prop);
    let Q := fresh "Q" in evar (Q: A -> R -> Σ  -> Prop);
     let h := fresh "h" in assert (P = P) as h;[ 
       let P' := eval pattern (a) in P1 in
      match P' with  
      | ?P''  _ => exact (Logic.eq_refl P'') end | ];
    clear h;
    let h := fresh "h" in assert (Q = Q) as h;[
     let Q' := eval pattern (a) in P2 in
      match Q' with  
      | ?Q''  _ => exact (Logic.eq_refl Q'') end |];
    clear h;
    eapply Hoare_BW_fix with (P:= P) (Q := Q);
    subst P Q
  end.

Ltac hoare_fix_lv_auto A C c:=
   lazymatch goal with
  | |- @Hoare ?Sigma ?R ?P1 (Rec ?F ?a) ?Q1 =>
    unfold Rec; hoare_fix_lv_auto A C c
  | |- @Hoare ?Σ ?R ?P1 (BW_fix ?F ?a) ?Q1 =>
     let P := fresh "P" in evar (P: A -> C -> Σ  -> Prop);
     let Q := fresh "Q" in evar (Q: A -> C -> R -> Σ -> Prop);
     let h := fresh "h" in assert (P = P) as h;[ 
      let P0 := eval pattern (c) in P1 in
      match P0 with 
      | ?P0' _ => 
      let P' := eval pattern (a) in P0' in
      match P' with  
      | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
     clear h;
     let h := fresh "h" in assert (Q = Q) as h;[ 
      let Q0 := eval pattern (c) in Q1 in
      match Q0 with 
      | ?Q0' _ => 
      let Q' := eval pattern (a) in Q0' in
      match Q' with  
      | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
    clear h;
    eapply Hoare_BW_fix_logicv with  (P:= P) (Q := Q); subst P Q
  end.

Ltac hoare_fix_lv_auto_conj A C c:=
  lazymatch goal with
| |- @Hoare ?Sigma ?R ?P (Rec ?F ?a) ?Q =>
    unfold Rec; hoare_fix_lv_auto_conj A C c
| |- @Hoare ?Σ ?R ?P (BW_fix ?F ?a) ?Q =>
    let P1 := fresh "P" in evar (P1: A -> C -> Σ  -> Prop);
    let Q1 := fresh "Q" in evar (Q1: A -> C -> R -> Σ -> Prop);
    let h := fresh "h" in assert (P1 = P1) as h;[ 
    let P0 := eval pattern (c) in P in
    match P0 with 
    | ?P0' _ => 
    let P' := eval pattern (a) in P0' in
    match P' with  
    | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
    clear h;
    let h := fresh "h" in assert (Q1 = Q1) as h;[ 
    let Q0 := eval pattern (c) in Q in
    match Q0 with 
    | ?Q0' _ => 
    let Q' := eval pattern (a) in Q0' in
    match Q' with  
    | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
  clear h;
  eapply (Hoare_BW_fix_logicv_conj' _ P1 Q1 a c);
  subst P1 Q1
end.

Ltac hoare_fix_lv_auto_conj' A C c:=
  lazymatch goal with
| |- @Hoare ?Sigma ?R ?P (Rec ?F ?a) ?Q =>
    unfold Rec; hoare_fix_lv_auto_conj' A C c
| |- @Hoare ?Σ ?R ?P (BW_fix ?F ?a) ?Q =>
    let P1 := fresh "P" in evar (P1: A -> C -> Σ  -> Prop);
    let Q1 := fresh "Q" in evar (Q1: A -> C -> R -> Σ -> Prop);
    let h := fresh "h" in assert (P1 = P1) as h;[ 
    let P0 := eval pattern (c) in P in
    match P0 with 
    | ?P0' _ => 
    let P' := eval pattern (a) in P0' in
    match P' with  
    | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
    clear h;
    let h := fresh "h" in assert (Q1 = Q1) as h;[ 
    let Q0 := eval pattern (c) in Q in
    match Q0 with 
    | ?Q0' _ => 
    let Q' := eval pattern (a) in Q0' in
    match Q' with  
    | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
  clear h;
  eapply (Hoare_BW_fix_logicv_conj' _ P1 Q1 a c);
  subst P1 Q1
end.

Ltac hoare_rec_nolv_auto A :=
  hoare_fix_nolv_auto A.

Ltac hoare_rec_lv_auto A C c :=
  hoare_fix_lv_auto A C c.

Ltac hoare_rec_lv_auto_conj' A C c :=
  hoare_fix_lv_auto_conj' A C c.

Lemma Hoare_repeat_break {Σ A B: Type}:
forall (f: A -> program Σ (CntOrBrk A B)) (P: A -> Σ -> Prop) (Q: B -> Σ -> Prop),
  (forall a, Hoare (P a) (f a) (fun ab σ =>
  match ab with
  | by_continue a => P a σ
  | by_break b => Q b σ
  end)) -> (forall a, Hoare (P a) (repeat_break f a) Q).
Proof.
  intros.
  unfold repeat_break.
  apply Hoare_BW_fix with (Q:= fun _ => Q).
  intros.
  unfold repeat_break_f.
  hoare_bind H.
  hoare_auto.
Qed.

Lemma Hoare_repeat_break' {Σ A B: Type}:
  forall (body: A -> program Σ (CntOrBrk A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare (P a) (x <- body a;; continue_case x) P) ->
    (forall a, Hoare (P a) (x <- body a;; break_case x) Q) -> 
    (forall a, Hoare (P a) (repeat_break body a) Q).
Proof.
  intros.
  apply Hoare_repeat_break.
  intros; apply Hoare_sum; auto.
Qed.

Lemma Hoare_repeat_break_noin {Σ B: Type}:
  forall (body: program Σ (CntOrBrk unit B)) (P: Σ -> Prop) (Q: B -> Σ -> Prop),
    Hoare P body (fun ab σ =>
  match ab with
  | by_continue _ => P σ
  | by_break b => Q b σ
  end) -> Hoare P (repeat_break_noin body) Q.
Proof.
  intros.
  eapply Hoare_BW_fix_prog.
  intros W HW.
  unfold repeat_break_noin, repeat_break_f_noinput in *.
  hoare_bind H.
  hoare_auto.
Qed.

Lemma range_plus_1_aux: forall (P: Z -> Prop) lo hi,
  (forall i, lo <= i < hi -> P i) ->
  (forall i, lo + 1 <= i < hi -> P i).
Proof.
  intros.
  apply H.
  lia.
Qed.

Lemma Hoare_range_iter' {A Σ: Type} : 
forall (f: Z -> A -> program Σ A) (P: Z -> A -> Σ -> Prop) (lo hi: Z),
  lo <= hi ->
  (forall i, lo <= i < hi -> forall a, Hoare (P i a) (f i a) (fun b => P (i+1) b)) -> 
  (forall a, Hoare (P lo a) (range_iter lo hi f a) (fun b => P hi b)).
Proof.
  intros.
  unfold range_iter.
  apply Hoare_cons_pre with (P:= fun s => P lo a s /\ lo <= lo <= hi). 
  intros; split; [auto| lia].
  unfold range_iter.
  apply Hoare_BW_fix with
    (P:= fun '(i, a) s => P i a s /\ lo <= i <= hi)
    (a:= (lo, a))
    (Q:= fun '(_, a) a' s => P hi a' s).
  clear a.
  intros; destruct a as [i a].
  unfold range_iter_f.
  hoare_auto.
  2:{ 
    assert (i = hi) by lia.
    subst; tauto. 
  }
  stateless_intros.
  specialize (H0 i (ltac:(lia)) a).
  hoare_bind H0.
  specialize (H1 (i+1, a0)); simpl in H1.
  eapply Hoare_cons_pre.
  2:apply H1.
  intros; simpl.
  split; [auto | lia].
Qed.


Lemma Hoare_range_iter_break' {A B Σ: Type} : 
forall (f: Z -> A -> program Σ (CntOrBrk A B)) (P: Z -> A -> Σ -> Prop) (Q: B -> Σ -> Prop) (lo hi: Z),
  lo <= hi ->
  (forall i, lo <= i < hi -> forall a,
     Hoare (P i a) (f i a) (fun res => match res with
                                       | by_continue a => P (i+1) a
                                       | by_break b => Q b
                                       end)) -> 
  (forall a, Hoare (P lo a) (range_iter_break lo hi f a)
               (fun res σ => match res with
                             | by_continue a => P hi a σ
                             | by_break b => Q b σ
                             end)).
Proof.
  intros.
  unfold range_iter.
  apply Hoare_cons_pre with (P:= fun s => P lo a s /\ lo <= lo <= hi). 
  intros; split; [auto| lia].
  unfold range_iter_break.
  apply Hoare_BW_fix with
    (P:= fun '(i, a) s => P i a s /\ lo <= i <= hi)
    (a:= (lo, a))
    (Q:= fun '_ res s =>
      match res with
      | by_continue a0 => P hi a0 s
      | by_break b => Q b s
      end).
  clear a.
  intros; destruct a as [i a].
  unfold range_iter_break_f.
  hoare_auto.
  2:{
    assert (i = hi) by lia.
    subst; tauto.
  }
  stateless_intros.
  specialize (H0 i (ltac:(lia)) a).
  hoare_bind H0.
  simpl.
  hoare_auto.
  specialize (H1 (i+1, a0)); simpl in H1.
  eapply Hoare_cons_pre.
  2:apply H1.
  intros; simpl.
  split; [auto | lia].
Qed.

Lemma Hoare_range_iter {A Σ: Type}:
  forall (f: Z -> A -> program Σ A)
         (Q: Σ -> Prop) (P: Z -> A -> Σ -> Prop) (lo hi: Z),
    lo <= hi ->
    forall a, 
      (forall σ, Q σ -> P lo a σ) ->
      (forall i, lo <= i < hi -> forall a, Hoare (P i a) (f i a) (P (i+1))) -> 
      Hoare Q (range_iter lo hi f a) (P hi).
Proof.
  intros.
  eapply Hoare_cons_pre; [ | apply (Hoare_range_iter' f P lo hi H H1)].
  auto.
Qed.

Lemma Hoare_range_iter_break {A B Σ: Type}:
  forall (f: Z -> A -> program Σ (CntOrBrk A B))
         (P: Z -> A -> Σ -> Prop)
         (Q1: Σ -> Prop)
         (Q2: B -> Σ -> Prop) (lo hi: Z),
    lo <= hi ->
    forall a,
      (forall σ, Q1 σ -> P lo a σ) ->
      (forall i, lo <= i < hi -> forall a,
         Hoare (P i a) (f i a) (fun res => match res with
                                           | by_continue a => P (i+1) a
                                           | by_break b => Q2 b
                                           end)) -> 
      Hoare Q1
            (range_iter_break lo hi f a)
            (fun res σ => match res with
                          | by_continue a => P hi a σ
                          | by_break b => Q2 b σ
                          end).
Proof.
  intros.
  eapply Hoare_cons_pre; [ | apply (Hoare_range_iter_break' f P Q2 lo hi H H1)].
  auto.
Qed.

Lemma app_singleton_tail {A} (prefix: list A) (a: A) (l: list A):
  ((prefix ++ a :: nil) ++ l) = prefix ++ a :: l.
Proof.
  induction prefix as [| x prefix IHprefix]; simpl.
  - reflexivity.
  - rewrite IHprefix.
    reflexivity.
Qed.

Lemma Hoare_list_iter_aux {Σ A B}
  (P: list A -> B -> Σ -> Prop)
  (body: A -> B -> program Σ B)
  (prefix: list A):
  (forall pfx x b,
    Hoare (fun s => P pfx b s) (body x b) (fun b' s => P (pfx ++ x :: nil) b' s)) ->
  forall l b,
    Hoare (fun s => P prefix b s) (list_iter body l b) (fun b' s => P (prefix ++ l) b' s).
Proof.
  intros H l.
  revert prefix.
  induction l; intros prefix b.
  - simpl.
    rewrite app_nil_r.
    apply Hoare_ret.
    auto.
  - simpl.
    eapply Hoare_bind.
    + apply H.
    + intros b'.
      specialize (IHl (prefix ++ a :: nil) b').
      eapply (@Hoare_cons_post B Σ
        (fun s => P (prefix ++ a :: nil) b' s)
        (list_iter body l b')
        (fun b'' s => P ((prefix ++ a :: nil) ++ l) b'' s)
        (fun b'' s => P (prefix ++ a :: l) b'' s)).
      * intros b'' s HP.
        rewrite app_singleton_tail in HP.
        exact HP.
      * exact IHl.
Qed.

Theorem Hoare_list_iter {Σ A B}
  (P: list A -> B -> Σ -> Prop)
  (body: A -> B -> program Σ B):
  (forall prefix x b,
    Hoare (fun s => P prefix b s) (body x b) (fun b' s => P (prefix ++ x :: nil) b' s)) ->
  forall l b,
    Hoare (fun s => P nil b s) (list_iter body l b) (fun b' s => P l b' s).
Proof.
  intros H l b.
  eapply (@Hoare_cons_post B Σ
    (fun s => P nil b s)
    (list_iter body l b)
    (fun b' s => P (nil ++ l) b' s)
    (fun b' s => P l b' s)).
  - intros b' s HP. simpl in HP. exact HP.
  - apply Hoare_list_iter_aux; auto.
Qed.

Lemma range_iter_no_iter {A Σ: Type} : 
  forall (f: Z -> A -> program Σ A) (P: A -> Σ -> Prop) (lo hi: Z),
  hi < lo ->
  (forall a, Hoare (P a) (range_iter lo hi f a) P).
Proof.
  intros.
  rewrite range_iter_unfold.
  hoare_auto.
  lia.
Qed.

Lemma Hoare_forset {Σ A}
  (P: (A -> Prop) -> Σ -> Prop)
  (universe: A -> Prop)
  (body: A -> program Σ unit)
  (ProperP: Proper (Sets.equiv ==> eq ==> iff) P):
  (forall done a,
    done ⊆ universe ->
    Hoare (fun s => P done s /\ a ∈ universe /\ ~ a ∈ done)
      (body a)
      (fun _ s => P (done ∪ [a]) s)) ->
  Hoare (fun s => P ∅ s) (forset universe body) (fun _ s => P universe s).
Proof.
  intros.
  change (Hoare (fun s => P (fun _ : A => False) s)
            (forset universe body) (fun _ s => P universe s)).
  assert (Hfix: Hoare
    (fun s => P (fun a => a ∈ universe /\ ~ a ∈ universe) s /\ universe ⊆ universe)
    (forset universe body)
    (fun _ s => P universe s)).
  2:{
    eapply Hoare_cons_pre; [| exact Hfix].
    simpl; intros σ HP.
    assert (Heq: ((fun a : A => a ∈ universe /\ ~ a ∈ universe) == (fun _ : A => False))%sets)
      by (sets_unfold; tauto).
    split.
    + pose proof (ProperP _ _ Heq σ σ eq_refl) as Hiff.
      destruct Hiff as [_ Hiff].
      exact (Hiff HP).
    + sets_unfold; tauto.
  }
  unfold forset.
  apply Hoare_BW_fix with
      (P:= fun todo s => P (fun a => a ∈ universe /\ ~ a ∈ todo) s /\ todo ⊆ universe)
      (Q:= fun _ _ s => P universe s).
    intros W IH todo.
    unfold forset_f.
    eapply Hoare_choice.
    - apply Hoare_state_intro; intros s0 Hpre.
      eapply Hoare_bind.
      + apply Hoare_get.
      + intros a.
        simpl.
        apply Hoare_state_intro; intros s1 [HaTodo Hs]; subst.
        eapply Hoare_bind.
        * eapply Hoare_cons_pre.
          2:{
            eapply (H (fun a0 => a0 ∈ universe /\ ~ a0 ∈ todo) a).
            sets_unfold; tauto.
          }
          intros σ Hσ; subst.
          destruct Hpre as [HP Hsub].
          split; [exact HP|].
          split; [apply Hsub; auto| sets_unfold; tauto].
        * intros [].
          eapply Hoare_cons_pre.
          2: apply IH.
          intros σ HPbody; split.
          -- assert (Heq:
                ((fun a0 : A => a0 ∈ universe /\ ~ a0 ∈ (fun x : A => x ∈ todo /\ x <> a)) ==
                 ((fun a0 : A => a0 ∈ universe /\ ~ a0 ∈ todo) ∪ [a]))%sets).
             {
               destruct Hpre as [_ Hsub].
               sets_unfold; intros a0; split; intros.
               - destruct H0.
                 assert (~ todo a0 \/ a0 = a) by tauto.
                 destruct H2; auto.
               - destruct H0.
                 + split; tauto.
                 + subst; split; try tauto.
                   apply Hsub; auto.
             }
             pose proof (ProperP _ _ Heq σ σ eq_refl) as Hiff.
             destruct Hiff as [_ Hiff].
             exact (Hiff HPbody).
          -- destruct Hpre as [_ Hsub].
             sets_unfold.
             intros; apply Hsub; tauto.
    - apply Hoare_assume_bind.
      intros Hempty.
      eapply Hoare_cons_pre.
      2: apply Hoare_ret.
      intros σ [HP _]; simpl.
      assert (Heq: ((fun a : A => a ∈ universe /\ ~ a ∈ todo) == universe)%sets).
      {
        sets_unfold; intros; split; try tauto.
        intros; split; auto.
        change (~ a ∈ todo).
        rewrite Hempty; tauto.
      }
      pose proof (ProperP _ _ Heq σ σ eq_refl) as Hiff.
      destruct Hiff as [Hiff _].
      exact (Hiff HP).
      auto.
Qed.




(********************************************************************************)
(************************     Other Hoare premitives     ************************)
(************************       1. weakest precondition  ************************)
(************************       1. angelic Hoare         ************************)
(********************************************************************************)
Section Hoare_defs.
Import MonadErr.
(* Weakest liberal precondition  *)
Definition weakestpre {Σ A: Type}
  (c: program Σ A)
  (Q: A -> Σ -> Prop): Σ -> Prop := 
    fun σ =>  ~ c.(err) σ /\ forall r σ', (σ, r, σ') ∈ c.(nrm) -> Q r σ'.

Definition valid_angelic_triple {Σ A: Type}
  (P: Σ -> Prop)
  (c: program Σ A)
  (Q: A -> Σ -> Prop): Prop := 
    forall s1, P s1 -> exists a s2, (s1, a, s2) ∈ c.(nrm) /\ Q a s2.

End Hoare_defs.
Section WLPrules.
Import MonadErr.
  Context {Σ A B: Type}.

  Theorem wp_spec (c: program Σ A) (s1 s2:Σ) a:
    c.(nrm) s1 a s2 -> 
    forall Q,
    s1 ∈ (weakestpre c Q) ->
    s2 ∈ (Q a).
  Proof.
    unfold weakestpre; intros H0 Q H1.
    sets_unfold in H1. destruct H1.
    apply H1;auto.
  Qed.

  Theorem wp_spec_err (c: program Σ A) (s1:Σ) Q:
    s1 ∈ (weakestpre c Q) ->
    ~ err c s1.
  Proof.
    unfold weakestpre; intros. 
    sets_unfold in H. tauto.
  Qed.

  Theorem wp_self (c: program Σ A) (s: Σ):
    ~ err c s ->
    s ∈ (weakestpre c (fun a s' => c.(nrm) s a s')).
  Proof.
    intros. unfold weakestpre. sets_unfold. split;auto. 
  Qed.
 
  Theorem wp_Hoare (c: program Σ A) (Q: A -> Σ -> Prop):
    Hoare (weakestpre c Q) c Q.
  Proof.
    unfold weakestpre, Hoare.
    split. 
    intros s1 a s2 [? H0]. auto.
    intros ? [? ?]. auto.
  Qed.

  Theorem wp_Hoare_iff (P: Σ -> Prop) (Q: A -> Σ -> Prop) (c: program Σ A):
    P ⊆ (weakestpre c Q) <->
    Hoare P c Q.
  Proof.
    split;intros.
    - 
    eapply Hoare_cons_pre;[ | apply wp_Hoare].
    sets_unfold in H.
    auto.
    - unfold weakestpre, Hoare in *.
      destruct H.
      sets_unfold. 
      intros.
      split. unfold not. apply H0;auto.
      intros. 
      eapply H;eauto.
  Qed.

  Lemma wp_progequiv (c1 c2: program Σ A) (Q: A -> Σ -> Prop):
    c2 == c1 ->
    (weakestpre c1 Q == weakestpre c2 Q)%sets.
  Proof.
    intros.
    destruct H. 
    unfold weakestpre. intros s1. 
    split;intros [? ?].
    - split. unfold not in *. intros. apply H. apply errequiv;auto. 
      intros. apply H0. apply nrmequiv. auto.
    - split. unfold not in *. intros. apply H. apply errequiv;auto. 
      intros. apply H0. apply nrmequiv. auto.
  Qed.

  Lemma wp_progrefine (c1 c2: program Σ A) (Q: A -> Σ -> Prop):
    (nrm c2 ⊆ nrm c1) ->
    (err c2 ⊆ err c1) ->
    weakestpre c1 Q ⊆ weakestpre c2 Q.
  Proof.
    unfold weakestpre; intros Hn Herr s1 [Hnoerr Hpost].
    split.
    - intros Herr2; apply Hnoerr; apply Herr; auto.
    - intros a s2 Hin.
      apply Hpost. apply Hn; auto.
  Qed.

  Lemma wp_conseq (c: program Σ A) (Q1 Q2: A -> Σ -> Prop):
    Q1 ⊆ Q2 ->
    weakestpre c Q1 ⊆ weakestpre c Q2.
  Proof.
    unfold weakestpre; intros H s1 [? ?].
    split;auto.
    intros.
    apply H. 
    auto.
  Qed.

  Lemma wp_bind (f: program Σ A) (g: A -> program Σ B) (Q: B -> Σ -> Prop):
  (weakestpre (x <- f;; g x) Q ==  weakestpre f (fun a => weakestpre (g a) Q))%sets.
  Proof.
    intros s1. 
    unfold weakestpre. unfold_monad.
    split. 
    - intros [? ?].
      split.
      + sets_unfold in H.
        tauto.
      + split.
        { sets_unfold in H. unfold not in *. intros. apply H.
          right. do 2 eexists. split;eauto. apply H1. }  
        intros.
        apply H0.
        exists r , σ'.
        split;auto.
    - intros [? ?].
      split.
      + sets_unfold. unfold not. intros [ | ];[tauto | ].
        destruct H1 as [a [s2' [? ?]]].
        apply H0 in H1 as [? _].
        tauto.
      + intros.
        destruct H1 as [a [s2' [? ?]]].
        apply H0 in H1 as [_ ?].
        apply H1;auto.
  Qed.

  Lemma wp_ret (a: A) (Q: A -> Σ -> Prop):
    (weakestpre (return a) Q == (Q a))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H as [_ ?].
      apply H.
      unfold_monad. sets_unfold.
      auto.
    - unfold weakestpre.
      unfold_monad.
      split;[auto | ].
      intros ? ? [? ?].
      subst.
      auto.
  Qed.

  Lemma wp_choice (c1 c2: program Σ A) (Q: A -> Σ -> Prop):
    (weakestpre (choice c1 c2) Q == (weakestpre c1 Q) ∩ (weakestpre c2 Q))%sets.
  Proof.
    intros s1.
    unfold weakestpre, choice. 
    cbn [err nrm].
    sets_unfold. 
    split;intros [? ?].
    - split.
      + split;auto.
      + split;auto. 
    - destruct H. destruct H0.
      split;[tauto | ].
      intros.
      destruct H3 as [H3 | H3].
      apply H1;auto.
      apply H2;auto.
  Qed.

  Lemma wp_assume_coqprop (P: Prop) (Q: unit -> Σ -> Prop):
    P ->
    (weakestpre (assume!! P) Q == (Q tt))%sets.
  Proof.
    intros H s1.
    split;intros.
    - unfold weakestpre in H0.
      destruct H0 as [_ ?].
      apply H0.
      unfold testPure in *. cbn [nrm] in *.
      sets_unfold.
      auto.
    - unfold weakestpre, testPure.
      simpl. split;[auto | ].
      intros ? ? [? ?].
      subst. destruct r.
      auto.
  Qed.

  Lemma wp_assume (P: Σ -> Prop) (Q: unit -> Σ -> Prop):
    (weakestpre (assume P) Q == (fun s => P s -> Q tt s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      apply H.
      unfold test.
      split;auto.
    - unfold weakestpre, test.
      simpl. split;[auto | ].
      intros ? ? [? ?].
      subst. destruct r.
      auto.
  Qed.

  Lemma wp_any (P: Type) (Q: P -> Σ -> Prop):
    (weakestpre (any P) Q == (fun s => forall a, Q a s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H as [_ H].
      apply H.
      unfold any. sets_unfold. simpl.
      auto.
    - unfold weakestpre.
      unfold any. simpl.
      split;[auto | ].
      intros. sets_unfold in H0.  
      subst.
      apply H.
  Qed.

  Lemma wp_assert (P: Prop) (Q: unit -> Σ -> Prop):
    (weakestpre (assert P) Q == (fun s => P /\ Q tt s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H.
      unfold assert in *. 
      cbn in *.
      split;[tauto | ].
      apply H0.
      sets_unfold.
      tauto.
    - unfold weakestpre, assert.
      simpl. split;[tauto | ].
      intros ? ? [? ?].
      subst. destruct r.
      tauto.
  Qed.

  Lemma wp_assertS (P: Σ -> Prop) (Q: unit -> Σ -> Prop):
    (weakestpre (assertS P) Q == (fun s => P s /\ Q tt s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H.
      unfold assertS in *. 
      cbn in *.
      split;[tauto | ].
      apply H0.
      sets_unfold.
      tauto.
    - unfold weakestpre, assertS.
      simpl. split;[tauto | ].
      intros ? ? [? ?].
      subst. destruct r.
      tauto.
  Qed.

  Lemma wp_get (Pa: Σ -> A -> Prop)  (Q: A -> Σ -> Prop):
    (weakestpre (get Pa) Q == (fun s => forall a, Pa s a -> Q a s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      apply H.
      unfold get. simpl.
      sets_unfold.
      auto.
    - unfold weakestpre.
      unfold get.
      simpl. split;auto.
      intros ? ? [? ?].
      subst.
      apply H;auto.
  Qed.

  Lemma wp_get' (f: Σ -> A)  (Q: A -> Σ -> Prop):
    (weakestpre (get' f) Q == (fun s => forall a,  a = f s -> Q a s))%sets.
  Proof.
    intros.
    unfold get'.
    rewrite wp_get.
    reflexivity.
  Qed.

  Lemma wp_update (P: Σ -> Σ -> Prop)  (Q: unit -> Σ -> Prop):
    (weakestpre (update P) Q == (fun s =>  forall s', P s s' -> Q tt s'))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      unfold update in H.
      apply H. simpl. 
      auto.
    - unfold weakestpre.
      unfold update.
      simpl. split;auto.
      intros.
      destruct r.
      apply H;auto.
  Qed.

  Lemma wp_update' (f: Σ -> Σ)  (Q: unit -> Σ -> Prop):
    (weakestpre (update' f) Q == (fun s => forall s',  s' = f s -> Q tt s'))%sets.
  Proof.
    intros.
    unfold update'.
    rewrite wp_update.
    reflexivity.
  Qed.

End WLPrules.
