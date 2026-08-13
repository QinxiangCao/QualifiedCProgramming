Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrLoop MonadErrHoare.

Import SetsNotation.
Local Open Scope sets.

Export MonadNotation.
Local Open Scope monad.
Local Open Scope order_scope.
Local Open Scope Z_scope.

Section HoarePartialBasic.
Import MonadErr.

Definition Hoare_nrm {Σ A: Type}
(P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop): Prop :=
  (forall (a: A)(σ1 σ2: Σ), 
    P σ1 -> c.(nrm) σ1 a σ2 -> Q a σ2).

Lemma Hoare_implies_nrm {Σ A: Type}: 
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
  Hoare P c Q -> Hoare_nrm P c Q.
Proof.
  unfold Hoare, Hoare_nrm. tauto. 
Qed.

Lemma Hoare_nrm_skip:
  forall {A Σ B} P (c: program Σ A) (f: A -> program Σ B) Q,
    (forall a, Hoare_nrm (fun _ => True) (f a) Q) ->
    Hoare_nrm P (bind c f) Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_proequiv:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare_nrm P c1 Q -> Hoare_nrm P c2 Q.
Proof.
  unfold Hoare_nrm; intros * Hequiv Hhoare.
  unfold Sets.equiv in Hequiv; destruct Hequiv as [Hn _].
  sets_unfold in Hn.
  intros; eapply Hhoare; eauto. apply Hn. auto.
Qed.

#[export] Instance Hoare_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (equiv ==> eq ==> iff) (@Hoare_nrm Σ A P).
Proof.
  unfold Proper, respectful; intros.
  subst x0; split; intros.
  - apply Hoare_nrm_proequiv with x; easy.
  - apply Hoare_nrm_proequiv with y; easy.
Qed.

Lemma Hoare_nrm_bind {A B Σ: Type}: 
  forall (P: Σ -> Prop) (Q : A -> Σ -> Prop) (R: B -> Σ -> Prop)
         (c1: program Σ A) (c2: A -> program Σ B),
    Hoare_nrm P c1 Q ->
    (forall a, Hoare_nrm (Q a) (c2 a) R) ->
    Hoare_nrm P (bind c1 c2) R.
Proof.
  unfold Hoare_nrm; intros * Hc1 Hc2 a σ1 σ2 HP Hrun.
  unfold nrm_nrm in Hrun.
  destruct Hrun as [a0 [σmid [Hc1run Hc2run]]].
  specialize (Hc2 a0).
  eapply Hc2; eauto.
Qed.

Lemma Hoare_nrm_assert {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Q -> Hoare_nrm P (assert Q) (fun _ => P).
Proof.
  firstorder congruence.
Qed. 

Lemma Hoare_nrm_assertS {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Prop),
    (forall s, P s -> Q s) ->
    Hoare_nrm P (assertS Q) (fun _ => P).
Proof.
  firstorder congruence.
Qed.

Theorem Hoare_nrm_any {Σ A: Type}:
  forall (P: Σ -> Prop),
    Hoare_nrm P (any A) (fun _ => P).
Proof. firstorder congruence. Qed.

Theorem Hoare_nrm_any_bind {Σ A B: Type}:
  forall (P: Σ -> Prop) (f: A -> program Σ B) (Q: B -> Σ -> Prop),
    (forall a, Hoare_nrm P (f a) Q) ->
    Hoare_nrm P (a <- any A;; f a) Q.
Proof.
  intros; eapply Hoare_nrm_bind; [apply Hoare_nrm_any|].
  simpl; auto.
Qed.

Theorem Hoare_nrm_get {A Σ: Type}:
  forall (P: Σ -> Prop) (Pa: Σ -> A -> Prop),
    Hoare_nrm P (get Pa) (fun a s2 => Pa s2 a /\ P s2).
Proof.
  unfold get; simpl; firstorder congruence.
Qed.

Theorem Hoare_nrm_update {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Σ -> Prop),
    Hoare_nrm P (update Q) (fun _ s2 => exists s1, Q s1 s2 /\ P s1).
Proof. firstorder. Qed.

Theorem Hoare_nrm_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare_nrm P2 f Q2 ->
    Hoare_nrm P1 f Q1.
Proof. firstorder. Qed.

Lemma Hoare_nrm_spec_derivation {Σ A L: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop)
         (SpecP: L -> Σ -> Prop) (SpecQ: L -> A -> Σ -> Prop),
    (forall l, Hoare_nrm (SpecP l) c (SpecQ l)) ->
    (forall s0 a s1,
        P s0 ->
        (forall l, SpecP l s0 -> SpecQ l a s1) ->
        Q a s1) ->
    Hoare_nrm P c Q.
Proof.
  unfold Hoare_nrm; intros * Hspec Hderive a s0 s1 HP Hrun.
  apply Hderive with (s0 := s0); auto.
  intros l Hpre.
  eapply Hspec; eauto.
Qed.

Lemma Hoare_nrm_cons_pre {B Σ: Type} : 
  forall (P P': Σ -> Prop) (c: program Σ B) (Q: B -> Σ -> Prop),
    (forall σ, P' σ -> P σ) ->
    Hoare_nrm P c Q ->
    Hoare_nrm P' c Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_cons_post {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q Q': A -> Σ -> Prop),
    (forall a σ, Q a σ -> Q' a σ) ->
    Hoare_nrm P c Q ->
    Hoare_nrm P c Q'.
Proof. firstorder. Qed.

Lemma Hoare_nrm_choice {A Σ: Type}:
  forall (P: Σ -> Prop) (c1 c2: program Σ A) (Q: A -> Σ -> Prop),
    Hoare_nrm P c1 Q ->
    Hoare_nrm P c2 Q ->
    Hoare_nrm P (choice c1 c2) Q.
Proof.
  unfold Hoare_nrm, choice; intros; sets_unfold in H1.
  simpl in H2.
  destruct H2; [eapply H; eauto | eapply H0; eauto].
Qed.

Lemma Hoare_nrm_ret {A Σ: Type}:
  forall (P: Σ -> Prop) (a: A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> Q a σ) ->
    Hoare_nrm P (return a) Q.
Proof. firstorder subst; auto. Qed.

Lemma Hoare_nrm_post_true {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A),
    Hoare_nrm P c (fun _ _ => True).
Proof. firstorder. Qed.

Lemma Hoare_nrm_progrefine:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    (nrm c2 ⊆ nrm c1) ->
    Hoare_nrm P c1 Q -> Hoare_nrm P c2 Q.
Proof.
  unfold Hoare_nrm; intros * Hn Hhoare a σ1 σ2 HP Hrun.
  eapply Hhoare; eauto.
  eapply Hn; eauto.
Qed.

Lemma Hoare_BW_fix_nerr {Σ A B: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop) (a: A),
    (forall W: A -> program Σ B,
        (forall a, Hoare_nrm (P a) (W a) (fun b s => Q a b s)) ->
        forall a, Hoare_nrm (P a) (f W a) (fun b s => Q a b s)) ->
    Hoare (fun s => P a s /\ ~ (BW_fix f a).(err) s) (BW_fix f a) (fun b s => Q a b s).
Proof.
  intros.
  unfold Hoare.
  split;[ | tauto].
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (forall i, Hoare_nrm (P a) (Init.Nat.iter i f bot a) (Q a)).
  2:{
    unfold Hoare in H0.
    intros b s1 s2 H1 H2.
    destruct H2 as [i H2].
    eapply H0; eauto.
    tauto.
  }
  intros i; revert a.
  induction i.
  simpl; easy.
  simpl.
  apply H; auto.
Qed.

Theorem Hoare_BW_fix_logicv_conj_nerr {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P1 : A -> C -> Σ -> Prop)
       (Q1 : A -> C -> B -> Σ -> Prop) 
       a c,
forall {D: Type}
       (P2 : A -> D -> Σ -> Prop) (Q2 : A -> D -> B -> Σ -> Prop),
  (forall a d, Hoare (P2 a d) (BW_fix F a) (Q2 a d)) ->
  (forall W: A -> program Σ B, 
    (forall a d, Hoare_nrm (P2 a d) (W a) (Q2 a d)) ->
    (forall a c, Hoare_nrm (P1 a c) (W a) (Q1 a c)) ->
    (forall a c, Hoare_nrm (P2 a c) (F W a) (Q2 a c)) ->
    (forall a c, Hoare_nrm (P1 a c) (F W a) (Q1 a c))) ->  
  (Hoare (fun s => P1 a c s /\ ~ (BW_fix F a).(err) s) (BW_fix F a) (fun b s => Q1 a c b s)).
Proof.
  intros *  HT1; intros.
  unfold Hoare.
  split;[ | tauto].
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i a c,
             Hoare_nrm (P1 a c) (Init.Nat.iter i F bot a) (fun b s => Q1 a c b s)).
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
    - simpl; easy.
    - apply H.
      intros a1 d.
      specialize (H0 i a1 d). apply Hoare_implies_nrm in H0.
      exact H0.
      apply IHi.
      specialize (H0 (S i)).
      simpl in H0.
      intros a1 c1.
      specialize (H0 a1 c1). apply Hoare_implies_nrm in H0.
      apply H0. }
  intros b s1 s2 HP Hrun.
  destruct Hrun as [i Hi].
  specialize (Hiter i a c).
  eapply Hiter; eauto.
  tauto.
Qed.

Theorem Hoare_nrm_disj {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q: A -> Σ -> Prop),
    Hoare_nrm P1 f Q ->
    Hoare_nrm P2 f Q ->
    Hoare_nrm (fun s => P1 s \/ P2 s) f Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_choice_disj {Σ A}
      (P: Σ -> Prop) (c1 c2: program Σ A)
      (Q1 Q2: A -> Σ -> Prop):
  Hoare_nrm P c1 Q1 ->
  Hoare_nrm P c2 Q2 ->
  Hoare_nrm P (choice c1 c2) (fun a s => Q1 a s \/ Q2 a s).
Proof.
  unfold Hoare_nrm, choice; intros H1 H2 a σ1 σ2 HP Hrun.
  simpl in Hrun.
  destruct Hrun as [Hrun|Hrun]; [left; eapply H1 | right; eapply H2]; eauto.
Qed.

Lemma Hoare_nrm_assume' {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Q ->
    Hoare_nrm P (assume!! Q) (fun _ s => P s /\ Q).
Proof.
  unfold Hoare_nrm; intros * HQ a σ1 σ2 HP Hrun.
  simpl in Hrun.
  destruct Hrun as [Hσ HQ']; subst; tauto.
Qed.

Lemma Hoare_nrm_assume_bind {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (P2 -> Hoare_nrm P1 c Q) ->
    Hoare_nrm P1 (assume!! P2;; c) Q.
Proof.
  unfold Hoare_nrm; intros P1 P2 c Q Hc a σ1 σ2 HP Hrun.
  unfold bind, MonadErr.bind in Hrun; simpl in Hrun.
  unfold nrm_nrm in Hrun.
  destruct Hrun as [u [σmid [[Hσ HP2] Hc']]].
  subst σmid.
  specialize (Hc HP2).
  eapply Hc; eauto.
Qed.

Lemma Hoare_nrm_assumeS {Σ: Type}:
  forall (P1 P2: Σ -> Prop),
    Hoare_nrm P1 (assume P2) (fun _ s => P1 s /\ P2 s).
Proof. firstorder congruence. Qed.

Lemma Hoare_nrm_assumeS_bind {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    Hoare_nrm (fun s => P1 s /\ P2 s) c Q ->
    Hoare_nrm P1 (assume P2;; c) Q.
Proof.
  unfold Hoare_nrm; intros P1 P2 c Q Hc a σ1 σ2 HP Hrun.
  unfold bind, MonadErr.bind in Hrun; simpl in Hrun.
  unfold nrm_nrm in Hrun.
  destruct Hrun as [u [σmid [[Hσ HP2] Hc']]].
  subst σmid.
  eapply Hc; eauto.
Qed.

Lemma Hoare_nrm_assert_bind {A Σ: Type}:
  forall (P: Σ -> Prop) (P': Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (P' -> Hoare_nrm P c Q) ->
    Hoare_nrm P (assert P';; c) Q.
Proof.
  unfold Hoare_nrm; intros P P' c Q Hc a σ1 σ2 HP Hrun.
  unfold bind, MonadErr.bind in Hrun; simpl in Hrun.
  unfold nrm_nrm in Hrun.
  destruct Hrun as [u [σmid [[Hσ HP'] Hc']]].
  subst σmid.
  specialize (Hc HP').
  eapply Hc; eauto.
Qed.

Lemma Hoare_nrm_assertS_bind_intro {A Σ: Type}:
  forall (P: Σ -> Prop) (P': Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    Hoare_nrm P c Q ->
    Hoare_nrm P (assertS P';; c) Q.
Proof.
  unfold Hoare_nrm; intros P P' c Q Hc a σ1 σ2 HP Hrun.
  unfold bind, MonadErr.bind in Hrun; simpl in Hrun.
  unfold nrm_nrm in Hrun.
  destruct Hrun as [u [σmid [[Hσ _] Hc']]].
  subst σmid.
  eapply Hc; eauto.
Qed.

Lemma Hoare_nrm_assertS_bind {A Σ: Type}:
  forall (P: Σ -> Prop) (Q: Σ -> Prop) (c: program Σ A) (R: A -> Σ -> Prop),
    (forall s, P s -> Q s) ->
    Hoare_nrm P (assertS Q ;; c) R <-> Hoare_nrm P c R.
Proof.
  intros P Q c R Himp; split; intros Hhoare.
  - unfold Hoare_nrm in *.
    intros a σ1 σ2 HP Hrun.
    apply (Hhoare a σ1 σ2 HP).
    unfold bind, MonadErr.bind; simpl.
    unfold nrm_nrm.
    exists tt; exists σ1; split; [|assumption].
    split; [reflexivity| apply Himp; assumption].
  - eapply Hoare_nrm_bind; [apply Hoare_nrm_assertS; exact Himp|].
    intros []; simpl; assumption.
Qed.

Lemma Hoare_nrm_step {Σ A: Type}:
  forall (P: Σ -> Prop) (f: program Σ A),
    Hoare_nrm P f (fun a s2 => exists s1, f.(nrm) s1 a s2 /\ P s1).
Proof. firstorder. Qed.

Lemma Hoare_nrm_state_intro {A Σ}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s0, P s0 -> Hoare_nrm (fun s => s = s0) c Q) ->
    Hoare_nrm P c Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_conj {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop) (R: A -> Σ -> Prop),
    Hoare_nrm P c Q ->
    Hoare_nrm P c R ->
    Hoare_nrm P c (fun a σ => Q a σ /\ R a σ).
Proof. firstorder. Qed.

Lemma Hoare_nrm_Hoare_conj {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop) (R: A -> Σ -> Prop),
    Hoare_nrm P c Q ->
    Hoare P c R ->
    Hoare P c (fun a σ => Q a σ /\ R a σ).
Proof.
  unfold Hoare_nrm, Hoare; firstorder.
Qed.

Lemma Hoare_nrm_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall x, Hoare_nrm (P x) f Q) ->
    Hoare_nrm (fun s => exists x, P x s) f Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_stateless:
  forall {A Σ} (P: Prop) (c: program Σ A) Q,
    (P -> Hoare_nrm (fun _ => True) c Q) ->
    Hoare_nrm (fun _ => P) c Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_stateless':
  forall {A Σ} (P: Prop) (P': Σ -> Prop) (c: program Σ A) Q,
    (P -> Hoare_nrm P' c Q) ->
    Hoare_nrm (fun s => P' s /\ P) c Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_bot {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    Hoare_nrm P bot Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_update_bind {Σ A: Type}:
  forall (P: Σ -> Prop) (f: Σ -> Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s1,  P s1 -> Hoare_nrm (fun s2 => f s1 s2) c Q) ->
    Hoare_nrm P (update f;; c) Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_update_s {Σ}:
  forall (s0: Σ) (f: Σ -> Σ -> Prop),
    Hoare_nrm (fun s => s = s0) (update f) (fun _ s1 => f s0 s1).
Proof. intros. unfold Hoare_nrm, update. simpl. intros. subst. auto. Qed.

Lemma Hoare_nrm_update' {Σ}:
  forall (s0: Σ) (f: Σ -> Σ),
    Hoare_nrm (fun s => s = s0) (update' f) (fun _ s1 => s1 = f s0).
Proof. intros.  eapply Hoare_nrm_update_s.  Qed.

Lemma Hoare_nrm_get_s {Σ A}:
  forall (s0: Σ) (Pa: Σ -> A -> Prop),
    Hoare_nrm (fun s => s = s0) (get Pa) (fun a s1 => s1 = s0 /\ Pa s0 a).
Proof. firstorder congruence. Qed.

Lemma Hoare_nrm_get' {Σ A}:
  forall (s0: Σ) (fa: Σ -> A),
    Hoare_nrm (fun s => s = s0) (get' fa) (fun a s1 => s1 = s0 /\ a = fa s0).
Proof. intros. eapply Hoare_nrm_get_s. Qed.

Lemma Hoare_nrm_BW_fix {Σ A B: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop) (a: A),
    (forall W: A -> program Σ B,
        (forall a, Hoare_nrm (P a) (W a) (fun b s => Q a b s)) ->
        forall a, Hoare_nrm (P a) (f W a) (fun b s => Q a b s)) ->
    Hoare_nrm (P a) (BW_fix f a) (fun b s => Q a b s).
Proof.
  intros.
  unfold Hoare_nrm.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (forall i a, Hoare_nrm (P a) (Init.Nat.iter i f bot a) (Q a)).
  { intro i; induction i; simpl; [firstorder| apply H; auto]. }
  intros b s1 s2 HP Hrun.
  destruct Hrun as [i Hrun].
  specialize (H0 i).
  eapply H0; eauto.
Qed.

Lemma Hoare_nrm_BW_fix_logicv {Σ A B C: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> C -> Σ -> Prop) (Q: A -> C -> B -> Σ -> Prop) (a: A) c,
    (forall W: A -> program Σ B,
        (forall a c, Hoare_nrm (P a c) (W a) (fun b s => Q a c b s)) ->
        forall a c, Hoare_nrm (P a c) (f W a) (fun b s => Q a c b s)) ->
    Hoare_nrm (P a c) (BW_fix f a) (fun b s => Q a c b s).
Proof.
  intros.
  unfold Hoare_nrm.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i a c,
             Hoare_nrm (P a c) (Init.Nat.iter i f bot a) (fun b s => Q a c b s)).
  { intro i; induction i; simpl; [firstorder| apply H; auto]. }
  intros b s1 s2 HP Hrun.
  destruct Hrun as [i Hi].
  specialize (Hiter i a c).
  eapply Hiter; eauto.
Qed.

Lemma Hoare_nrm_BW_fix_prog {Σ A: Type}:
  forall (f: program Σ A -> program Σ A)
         (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    (forall W, Hoare_nrm P W Q -> Hoare_nrm P (f W) Q) ->
    Hoare_nrm P (BW_fix f) Q.
Proof.
  intros f * Hmono.
  unfold Hoare_nrm.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i, Hoare_nrm P (Init.Nat.iter i f bot) Q).
  { intro i; induction i; simpl; [firstorder| apply Hmono; auto]. }
  intros a σ1 σ2 HP Hrun.
  destruct Hrun as [i Hi].
  specialize (Hiter i).
  eapply Hiter; eauto.
Qed.

Theorem Hoare_nrm_BW_fix_logicv_conj {Σ A B C: Type}:
forall (F: (A -> program Σ B)-> (A -> program Σ B))
       (P1 : A -> C -> Σ -> Prop)
       (Q1 : A -> C -> B -> Σ -> Prop) 
       a c,
forall {D: Type}
       (P2 : A -> D -> Σ -> Prop) (Q2 : A -> D -> B -> Σ -> Prop),
  (forall a d, Hoare_nrm (P2 a d) (BW_fix F a) (Q2 a d)) ->
  (forall W: A -> program Σ B, 
    (forall a d, Hoare_nrm (P2 a d) (W a) (Q2 a d)) ->
    (forall a c, Hoare_nrm (P1 a c) (W a) (Q1 a c)) ->
    (forall a c, Hoare_nrm (P1 a c) (F W a) (Q1 a c))) ->  
  Hoare_nrm (P1 a c) (BW_fix F a) (Q1 a c).
Proof.
  intros * HT1 Hstep.
  unfold Hoare_nrm.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (Hiter: forall i a c,
             Hoare_nrm (P1 a c) (Init.Nat.iter i F bot a) (fun b s => Q1 a c b s)).
  { assert (forall n a d, Hoare_nrm (P2 a d) (Nat.iter n F bot a) (Q2 a d)).
    { intros n a0 d.
      specialize (HT1 a0 d).
      unfold Hoare_nrm in HT1.
      intros b σ1 σ2 HP Hrun.
      apply (HT1 _ _ _ HP).
      exists n; exact Hrun. }
    intro i; induction i; simpl.
    - firstorder.
    - apply Hstep; auto. }
  intros b s1 s2 HP Hrun.
  destruct Hrun as [i Hi].
  specialize (Hiter i a c).
  eapply Hiter; eauto.
Qed.

Lemma Hoare_nrm_cnt_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a: A),
    (forall s, P s -> Q a s) ->
    Hoare_nrm P (@continue_case A B Σ (by_continue a)) Q.
Proof. 
  unfold Hoare_nrm,continue_case. simpl. intros.
  firstorder congruence.
Qed.

Lemma Hoare_nrm_brk_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (b: B),
    (forall s, P s -> Q b s) ->
    Hoare_nrm P (@break_case A B Σ (by_break b)) Q.
Proof. 
  unfold Hoare_nrm,break_case. simpl. intros.
  firstorder congruence.
Qed.

Lemma Hoare_nrm_brk_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (a: A),
    Hoare_nrm P (@break_case A B Σ (by_continue a)) Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_cnt_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (b: B),
    Hoare_nrm P (@continue_case A B Σ (by_break b)) Q.
Proof. firstorder. Qed.

Lemma Hoare_nrm_sum {A B Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ (CntOrBrk A B)) (Q: A -> Σ -> Prop) (R: B -> Σ -> Prop),
    Hoare_nrm P (x <- c;; continue_case x) Q ->
    Hoare_nrm P (x <- c;; break_case x) R ->
    Hoare_nrm P c (fun x σ => match x with
                          | by_continue a => Q a σ
                          | by_break b => R b σ
                          end).
Proof.
  unfold Hoare_nrm; intros.
  destruct a.
  eapply H;eauto. unfold continue_case. simpl. exists (by_continue a). eauto.
  eapply H0;eauto. unfold break_case. simpl. exists (by_break b). eauto.
Qed.


Lemma Hoare_nrm_repeat_break {Σ A B: Type}:
forall (f: A -> program Σ (CntOrBrk A B)) (P: A -> Σ -> Prop) (Q: B -> Σ -> Prop),
  (forall a, Hoare_nrm (P a) (f a) (fun ab σ =>
  match ab with
  | by_continue a => P a σ
  | by_break b => Q b σ
  end)) -> (forall a, Hoare_nrm (P a) (repeat_break f a) Q).
Proof.
  intros f P Q Hbody a.
  unfold repeat_break.
  apply Hoare_nrm_BW_fix with (Q:= fun _ => Q).
  intros W HW a0.
  unfold repeat_break_f.
  eapply Hoare_nrm_bind; [apply Hbody|].
  intros []; simpl; auto.
  apply Hoare_nrm_ret. auto.
Qed.

Lemma Hoare_nrm_repeat_break' {Σ A B: Type}:
  forall (body: A -> program Σ (CntOrBrk A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare_nrm (P a) (x <- body a;; continue_case x) P) ->
    (forall a, Hoare_nrm (P a) (x <- body a;; break_case x) Q) -> 
    (forall a, Hoare_nrm (P a) (repeat_break body a) Q).
Proof.
  intros.
  apply Hoare_nrm_repeat_break.
  intros; apply Hoare_nrm_sum; auto.
Qed.

Lemma Hoare_nrm_repeat_break_noin {Σ B: Type}:
  forall (body: program Σ (CntOrBrk unit B)) (P: Σ -> Prop) (Q: B -> Σ -> Prop),
    Hoare_nrm P body (fun ab σ =>
  match ab with
  | by_continue _ => P σ
  | by_break b => Q b σ
  end) -> Hoare_nrm P (repeat_break_noin body) Q.
Proof.
  intros body P Q Hbody.
  eapply Hoare_nrm_BW_fix_prog.
  intros W HW.
  unfold repeat_break_noin, repeat_break_f_noinput in *.
  eapply Hoare_nrm_bind; [apply Hbody|].
  intros []; simpl; auto.
  apply Hoare_nrm_ret. auto.
Qed.

Lemma Hoare_nrm_repeat_break_noin' {Σ B: Type}:
  forall (body: program Σ (CntOrBrk unit B)) (P: Σ -> Prop) (Q: B -> Σ -> Prop),
    (Hoare_nrm (P) (x <- body;; continue_case x) (fun _ => P)) ->
    (Hoare_nrm (P) (x <- body;; break_case x) Q) -> 
    Hoare_nrm P (repeat_break_noin body) Q.
Proof.
  intros.
  apply Hoare_nrm_repeat_break_noin.
  intros; apply Hoare_nrm_sum; auto.
Qed.

Theorem Hoare_nrm_whileP {Σ: Type} (cond: Σ -> Prop) 
  (body : program Σ unit) (P: Σ -> Prop):
  Hoare_nrm (fun s => P s /\ cond s) body (fun _ s => P s) ->
  Hoare_nrm P (whileP cond body) (fun _ s => P s /\ ~ cond s).
Proof.
  intros Hbody.
  unfold whileP.
  apply Hoare_nrm_BW_fix_prog.
  intros W HW.
  unfold whileP_f.
  eapply Hoare_nrm_choice.
  - eapply Hoare_nrm_assumeS_bind.
    eapply Hoare_nrm_bind; [apply Hbody|].
    intros []; simpl.
    eapply Hoare_nrm_cons_pre; [| apply HW].
    intros; tauto.
  - eapply Hoare_nrm_assumeS_bind.
    apply Hoare_nrm_ret; intros; tauto.
Qed.

Lemma Hoare_nrm_while {Σ: Type}
  (cond: program Σ bool) (body : program Σ unit) (P: Σ -> Prop):
  Hoare_nrm P cond (fun _ s => P s) ->
  Hoare_nrm P body (fun _ s => P s) ->
  Hoare_nrm P (while cond body) (fun _ s => P s).
Proof.
  intros Hcond Hbody.
  unfold while.
  apply Hoare_nrm_BW_fix_prog.
  intros W HW.
  unfold while_f.
  eapply Hoare_nrm_bind; [apply Hcond |].
  intros x; destruct x.
  - eapply Hoare_nrm_bind; [apply Hbody |].
    intros []. apply HW.
  - apply Hoare_nrm_ret; intros; tauto.
Qed.

Lemma Hoare_nrm_whileret {Σ A: Type}
  (cond: A -> program Σ bool) (body : A -> program Σ A)
  (P: A -> Σ -> Prop) (a: A):
  (forall a, Hoare_nrm (P a) (cond a) (fun _ s => P a s)) ->
  (forall a, Hoare_nrm (P a) (body a) P) ->
  Hoare_nrm (P a) (whileret cond body a) P.
Proof.
  intros Hcond Hbody.
  unfold whileret.
  apply Hoare_nrm_BW_fix with (P:= P) (Q:= fun _:A => P).
  intros W HW a0.
  unfold whileret_f.
  eapply Hoare_nrm_bind; [apply Hcond |].
  intros x; destruct x.
  - eapply Hoare_nrm_bind; [apply Hbody |].
    intros a1. apply HW.
  - apply Hoare_nrm_ret; intros; tauto.
Qed.

Lemma Hoare_nrm_whileretP {Σ A: Type}
  (cond: A -> Σ -> Prop) (body : A -> program Σ A)
  (P: A -> Σ -> Prop) (a: A):
  (forall a, Hoare_nrm (fun s => cond a s /\ P a s) (body a) P) ->
  Hoare_nrm (P a) (whileretP cond body a) (fun a s => P a s /\ ~ cond a s).
Proof.
  intros Hbody.
  unfold whileretP.
  apply Hoare_nrm_BW_fix with (P:= P) (Q:= fun (_:A) (b:A) s => P b s /\ ~ cond b s).
  intros W HW a0.
  unfold whileretP_f.
  eapply Hoare_nrm_choice.
  - eapply Hoare_nrm_assumeS_bind.
    eapply Hoare_nrm_bind.
    + eapply Hoare_nrm_cons_pre; [| apply Hbody]. intros; tauto.
    + intros a1. apply HW.
  - eapply Hoare_nrm_assumeS_bind.
    apply Hoare_nrm_ret; intros; tauto.
Qed.

End HoarePartialBasic.

(** Tactics *)
Tactic Notation "hoare_nrm_bind" uconstr(H) :=
  eapply Hoare_nrm_bind; [apply H |]; intros.

(* for unit type *)
Tactic Notation "hoare_nrm_bind'" uconstr(H) :=
  eapply Hoare_nrm_bind; [apply H |]; simpl; intros _.

Ltac hoare_nrm_conj :=
  match goal with
    | |- Hoare_nrm _  _ (fun _ _ => _ /\ _) => apply Hoare_nrm_conj; [try hoare_nrm_conj | try hoare_nrm_conj]
    | |- Hoare_nrm _ _ _ => eapply Hoare_nrm_cons_pre
  end.

Ltac hoare_nrm_intros :=
  apply Hoare_nrm_pre_ex; intros.

Ltac stateless_nrm_intros :=
  repeat (apply Hoare_nrm_stateless || apply Hoare_nrm_stateless'); intros.

Ltac hoare_nrm_step :=
  unfold continue, break;
  match goal with
    | |- Hoare_nrm _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_nrm_step
    | |- Hoare_nrm _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_nrm_step
    | |- Hoare_nrm _ (bind (ret _) _) _ => rewrite bind_ret_l
    | |- Hoare_nrm _ (assume!! _;; _) _ => apply Hoare_nrm_assume_bind; intros
    | |- Hoare_nrm _ (assume _ ;; _) _ => apply Hoare_nrm_assumeS_bind
    | |- Hoare_nrm _ (assert _;; _) _ => apply Hoare_nrm_assert_bind; intros
    | |- Hoare_nrm _ (choice _ _) _ => apply Hoare_nrm_choice
    | |- Hoare_nrm _ (ret _) _ => apply Hoare_nrm_ret; intros
    | |- Hoare_nrm _ (continue_case (by_continue _)) _ => apply Hoare_nrm_cnt_cnt; intros
    | |- Hoare_nrm _ (continue_case (by_break _)) _ => apply Hoare_nrm_cnt_brk
    | |- Hoare_nrm _ (break_case (by_continue _)) _ => apply Hoare_nrm_brk_cnt
    | |- Hoare_nrm _ (break_case (by_break _)) _ => apply Hoare_nrm_brk_brk; intros
    | |- Hoare_nrm _ (match ?a with _ => _ end) _ => destruct a; hoare_nrm_step
  end; auto.

Ltac hoare_nrm_auto :=
  unfold continue, break;
  match goal with
    | |- Hoare_nrm _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_nrm_auto
    | |- Hoare_nrm _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_nrm_auto
    | |- Hoare_nrm _ (bind (ret _) _) _ => rewrite bind_ret_l; try hoare_nrm_auto
    | |- Hoare_nrm _ (bind (assert _) _) _ => hoare_nrm_bind' Hoare_nrm_assert; try hoare_nrm_auto
    | |- Hoare_nrm _ (bind (assertS _) _) _ => hoare_nrm_bind' Hoare_nrm_assertS; try hoare_nrm_auto
    | |- Hoare_nrm _ (assume!! _;; _) _ => apply Hoare_nrm_assume_bind; intros; try hoare_nrm_auto
    | |- Hoare_nrm _ (assume _ ;; _) _ => apply Hoare_nrm_assumeS_bind; try hoare_nrm_auto
    | |- Hoare_nrm _ (assert _;; _) _ => apply Hoare_nrm_assert_bind; intros; try hoare_nrm_auto
    | |- Hoare_nrm _ (choice _ _) _ => apply Hoare_nrm_choice; try hoare_nrm_auto
    | |- Hoare_nrm _ (bind _ _) _ => apply Hoare_nrm_bind; intros; try hoare_nrm_auto
    | |- Hoare_nrm _ (ret _) _ => apply Hoare_nrm_ret; intros
    | |- Hoare_nrm _ (continue_case (by_continue _)) _ => apply Hoare_nrm_cnt_cnt; intros
    | |- Hoare_nrm _ (continue_case (by_break _)) _ => apply Hoare_nrm_cnt_brk
    | |- Hoare_nrm _ (break_case (by_continue _)) _ => apply Hoare_nrm_brk_cnt
    | |- Hoare_nrm _ (break_case (by_break _)) _ => apply Hoare_nrm_brk_brk; intros
    | |- Hoare_nrm _ (match ?a with _ => _ end) _ => destruct a; try hoare_nrm_auto
  end; auto.

Ltac hoare_nrm_auto_s :=
  unfold continue, break;
  match goal with
    | |- Hoare_nrm _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (bind (ret _) _) _ => rewrite bind_ret_l; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (bind (assert _) _) _ => hoare_nrm_bind' Hoare_nrm_assert; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (bind (assertS _) _) _ => hoare_nrm_bind' Hoare_nrm_assertS; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (assume!! _;; _) _ => apply Hoare_nrm_assume_bind; intros; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (assume _ ;; _) _ => apply Hoare_nrm_assumeS_bind; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (assert _;; _) _ => apply Hoare_nrm_assert_bind; intros; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (choice _ _) _ => apply Hoare_nrm_choice; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (bind _ _) _ => apply Hoare_nrm_bind; intros; try hoare_nrm_auto_s
    | |- Hoare_nrm _ (ret _) _ => apply Hoare_nrm_ret; intros
    | |- Hoare_nrm _ (continue_case (by_continue _)) _ => apply Hoare_nrm_cnt_cnt; intros
    | |- Hoare_nrm _ (continue_case (by_break _)) _ => apply Hoare_nrm_cnt_brk
    | |- Hoare_nrm _ (break_case (by_continue _)) _ => apply Hoare_nrm_brk_cnt
    | |- Hoare_nrm _ (break_case (by_break _)) _ => apply Hoare_nrm_brk_brk; intros
    | |- Hoare_nrm _ (match ?a with _ => _ end) _ => destruct a; try hoare_nrm_auto_s
  end; auto.

Ltac monad_nrm_equiv :=
  unfold continue_case, break_case;
  repeat (prog_nf; try easy;
          apply bind_equiv; try easy;
          intro_bound).

Tactic Notation "hoare_nrm_apply" uconstr(H) :=
  eapply Hoare_nrm_proequiv;
  [ | apply H; try tauto];
  monad_nrm_equiv.

Tactic Notation "hoare_nrm_cons_pre" uconstr(H) :=
  eapply Hoare_nrm_cons_pre; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_nrm_cons_post" uconstr(H) :=
  eapply Hoare_nrm_cons_post; [| apply H]; simpl; try tauto.

Tactic Notation "hoare_nrm_cons" uconstr(H) :=
  eapply Hoare_nrm_cons_pre; [|eapply Hoare_nrm_cons_post; [| apply H] ]; simpl; try tauto.
