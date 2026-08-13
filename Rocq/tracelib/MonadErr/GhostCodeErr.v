Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrHoarePartial MonadErrLoop.
From FP Require Import BourbakiWitt PartialOrder_Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section GhostErr.

Context {Σ: Type}
        {G: Type}.

Notation programG := (program (Σ * G)).

Definition liftG {A: Type} (p: program Σ A): programG A :=
  {|
    MonadErr.nrm := fun '(s1, g1) a '(s2, g2) =>
      p.(MonadErr.nrm) s1 a s2 /\ g2 = g1;
    MonadErr.err := fun '(s1, _) => p.(MonadErr.err) s1
  |}.

Definition Gupdate (f: Σ -> G -> G -> Prop) : programG unit :=
  {|
    MonadErr.nrm := fun '(s1, g1) _ '(s2, g2) =>
      s1 = s2 /\ f s1 g1 g2;
    MonadErr.err := ∅
  |}.

Definition Gupdate_live (f: Σ -> G -> G -> Prop) : Prop :=
  forall s g1, exists g2, f s g1 g2.

Definition Gequiv {A: Type} (c: program Σ A) (c': programG A) :=
  (forall s1 a s2 g1,
    c.(MonadErr.nrm) s1 a s2 <->
    exists g2, c'.(MonadErr.nrm) (s1, g1) a (s2, g2)) /\
  (forall s g,
    c.(MonadErr.err) s <-> c'.(MonadErr.err) (s, g)).

Lemma Gequiv_proequiv {A: Type} (c0 c1: program Σ A) (c0' c1': programG A):
  @equiv (program Σ A) _ c0 c1 ->
  @equiv (programG A) _ c0' c1' ->
  Gequiv c0 c0' <-> Gequiv c1 c1'.
Proof.
  unfold Gequiv; intros Hc Hc'.
  destruct Hc as [Hn He], Hc' as [Hn' He']; simpl in *.
  sets_unfold in Hn.
  sets_unfold in He.
  sets_unfold in Hn'.
  sets_unfold in He'.
  split; intros [HGn HGe]; split.
  - intros s1 a s2 g1.
    destruct (Hn s1 a s2) as [H01 H10].
    destruct (HGn s1 a s2 g1) as [HG01 HG10].
    split; intros H.
    + apply H10 in H.
      apply HG01 in H as [g2 Hg2].
      exists g2.
      destruct (Hn' (s1, g1) a (s2, g2)) as [H'01 H'10].
      apply H'01; auto.
    + destruct H as [g2 Hg2].
      destruct (Hn' (s1, g1) a (s2, g2)) as [H'01 H'10].
      apply H'10 in Hg2.
      assert (Hex: exists g2 : G, MonadErr.nrm c0' (s1, g1) a (s2, g2)).
      { exists g2; exact Hg2. }
      apply HG10 in Hex.
      apply H01; auto.
  - intros s g.
    destruct (He s) as [He01 He10].
    destruct (HGe s g) as [HG01 HG10].
    destruct (He' (s, g)) as [He'01 He'10].
    split; intros H.
    + apply He10 in H.
      apply HG01 in H.
      apply He'01; auto.
    + apply He'10 in H.
      apply HG10 in H.
      apply He01; auto.
  - intros s1 a s2 g1.
    destruct (Hn s1 a s2) as [H01 H10].
    destruct (HGn s1 a s2 g1) as [HG01 HG10].
    split; intros H.
    + apply H01 in H.
      apply HG01 in H as [g2 Hg2].
      exists g2.
      destruct (Hn' (s1, g1) a (s2, g2)) as [H'01 H'10].
      apply H'10; auto.
    + destruct H as [g2 Hg2].
      destruct (Hn' (s1, g1) a (s2, g2)) as [H'01 H'10].
      apply H'01 in Hg2.
      assert (Hex: exists g2 : G, MonadErr.nrm c1' (s1, g1) a (s2, g2)).
      { exists g2; exact Hg2. }
      apply HG10 in Hex.
      apply H10; auto.
  - intros s g.
    destruct (He s) as [He01 He10].
    destruct (HGe s g) as [HG01 HG10].
    destruct (He' (s, g)) as [He'01 He'10].
    split; intros H.
    + apply He01 in H.
      apply HG01 in H.
      apply He'10; auto.
    + apply He'01 in H.
      apply HG10 in H.
      apply He10; auto.
Qed.

Lemma Gequiv_liftG {A: Type} (c: program Σ A):
  Gequiv c (liftG c).
Proof.
  unfold Gequiv, liftG; simpl; split; intros.
  - split; intros.
    + exists g1; auto.
    + destruct H as [? [? ?]]; auto.
  - tauto.
Qed.

Lemma Gequiv_ret {A: Type} (a: A):
  Gequiv (ret a) (ret a).
Proof.
  unfold Gequiv; unfold_monad; simpl; split.
  - intros s1 b s2 g1; split; intros H.
    + destruct H; subst. exists g1; auto.
    + destruct H as [g2 H]. simpl in H.
      destruct H as [Hb Hst]. inversion Hst; subst; auto.
  - intros s g; split; intros H; tauto.
Qed.

Lemma Gequiv_bind {A B: Type} (c1: program Σ A) (c2: A -> program Σ B)
  (c1': programG A) (c2': A -> programG B):
  Gequiv c1 c1' ->
  (forall a, Gequiv (c2 a) (c2' a)) ->
  Gequiv (bind c1 c2) (bind c1' c2').
Proof.
  unfold Gequiv; unfold_monad; simpl; intros [Hn1 He1] Hc2.
  split.
  - intros s1 b s2 g1; split; intros H.
    + destruct H as [a [sm [Hc1 Hc2n]]].
      apply Hn1 with (g1:=g1) in Hc1 as [gm Hc1'].
      destruct (Hc2 a) as [Hn2 _].
      apply Hn2 with (g1:=gm) in Hc2n as [g2 Hc2'].
      exists g2, a, (sm, gm); auto.
    + destruct H as [g2 [a [[sm gm] [Hc1' Hc2']]]].
      exists a, sm.
      split.
      * apply Hn1 with (g1:=g1). exists gm; auto.
      * destruct (Hc2 a) as [Hn2 _].
        apply Hn2 with (g1:=gm). exists g2; auto.
  - intros s g; split; intros H.
    + destruct H as [H | [a [sm [Hn Herr]]]].
      * left. apply He1; auto.
      * right.
        apply Hn1 with (g1:=g) in Hn as [gm Hn'].
        destruct (Hc2 a) as [_ He2].
        exists a, (sm, gm); split; auto.
        apply He2; auto.
    + destruct H as [H | [a [[sm gm] [Hn Herr]]]].
      * left. apply He1 with (g:=g); auto.
      * right.
        exists a, sm.
        split.
        -- apply Hn1 with (g1:=g). exists gm; auto.
        -- destruct (Hc2 a) as [_ He2].
           apply He2 with (g:=gm); auto.
Qed.

Lemma Gequiv_choice {A: Type} (c1 c2: program Σ A) (c1' c2': programG A):
  Gequiv c1 c1' ->
  Gequiv c2 c2' ->
  Gequiv (choice c1 c2) (choice c1' c2').
Proof.
  unfold Gequiv, choice; simpl; intros [Hn1 He1] [Hn2 He2].
  split.
  - intros s1 a s2 g1; split; intros H.
    + destruct H as [H | H].
      * apply Hn1 with (g1:=g1) in H as [g2 H].
        exists g2; left; auto.
      * apply Hn2 with (g1:=g1) in H as [g2 H].
        exists g2; right; auto.
    + destruct H as [g2 [H | H]].
      * left. apply Hn1 with (g1:=g1). exists g2; auto.
      * right. apply Hn2 with (g1:=g1). exists g2; auto.
  - intros s g; split; intros [H | H].
    + left; apply He1; auto.
    + right; apply He2; auto.
    + left; apply He1 with (g:=g); auto.
    + right; apply He2 with (g:=g); auto.
Qed.

Lemma Gequiv_Gupdate (f: Σ -> G -> G -> Prop):
  Gupdate_live f ->
  Gequiv (ret tt) (Gupdate f).
Proof.
  unfold Gequiv, Gupdate_live, Gupdate; unfold_monad; simpl; intros Hlive.
  split.
  - intros s1 [] s2 g1; split; intros H.
    + destruct H; subst.
      specialize (Hlive s1 g1) as [g2 Hg].
      exists g2; auto.
    + destruct H as [g2 [? ?]]; subst; auto.
  - intros s g; split; intros H; tauto.
Qed.

Lemma Gequiv_Gupdate_l {A: Type} (c: program Σ A) (c': programG A)
  (f: Σ -> G -> G -> Prop):
  Gupdate_live f ->
  Gequiv c c' ->
  Gequiv c (Gupdate f;; c').
Proof.
  intros Hlive HG.
  assert (Htmp: Gequiv (ret tt;; c) (Gupdate f;; c')).
  {
    apply Gequiv_bind.
    - apply Gequiv_Gupdate; auto.
    - intros []; auto.
  }
  pose proof (Gequiv_proequiv (ret tt;; c) c
    (Gupdate f;; c') (Gupdate f;; c')
    (bind_ret_l tt (fun _ => c)) ltac:(reflexivity)) as Hiff.
  exact (proj1 Hiff Htmp).
Qed.

Lemma Gequiv_Gupdate_r (c: program Σ unit) (c': programG unit)
  (f: Σ -> G -> G -> Prop):
  Gupdate_live f ->
  Gequiv c c' ->
  Gequiv c (c';; Gupdate f).
Proof.
  intros Hlive HG.
  assert (Htmp: Gequiv (x <- c;; ret x) (c';; Gupdate f)).
  {
    apply Gequiv_bind; auto.
    intros [].
    apply Gequiv_Gupdate; auto.
  }
  pose proof (Gequiv_proequiv (x <- c;; ret x) c
    (c';; Gupdate f) (c';; Gupdate f)
    (bind_ret_r c) ltac:(reflexivity)) as Hiff.
  exact (proj1 Hiff Htmp).
Qed.

Lemma Gequiv_fix' {A: Type}
  (f: program Σ A -> program Σ A)
  (f': programG A -> programG A):
  (forall W W', Gequiv W W' -> Gequiv (f W) (f' W')) ->
  Gequiv (BW_fix f) (BW_fix f').
Proof.
  intros Hstep.
  unfold BW_fix; sets_unfold.
  assert (forall i, Gequiv (Nat.iter i f bot) (Nat.iter i f' bot)).
  2:{
    revert H; clear Hstep.
    unfold Gequiv; sets_unfold.
    intros Hiter.
    split.
    - intros s1 a s2 g1.
      split.
      + intros [i Hi].
        destruct (Hiter i) as [Hn _].
        apply Hn with (g1:=g1) in Hi.
        destruct Hi as [g2 Hi].
        exists g2, i; auto.
      + intros [g2 [i Hi]].
        exists i.
        destruct (Hiter i) as [Hn _].
        eapply Hn.
        exists g2; eauto.
    - intros s g.
      split.
      + intros [i Hi].
        destruct (Hiter i) as [_ He].
        apply He with (g:=g) in Hi.
        exists i; auto.
      + intros [i Hi].
        exists i.
        destruct (Hiter i) as [_ He].
        apply He with (g:=g); auto.
  }
  induction i.
  - unfold Gequiv; sets_unfold; simpl.
    split.
    + intros s1 a s2 g1; split; intros H; [contradiction |].
      destruct H as [g2 H]; contradiction.
    + intros s g; split; intros H; contradiction.
  - simpl.
    apply Hstep; auto.
Qed.

Lemma Gequiv_assume (P: Σ -> Prop):
  Gequiv (assume P) (assume (fun '(s, _) => P s)).
Proof.
  unfold Gequiv, test; simpl.
  split.
  - intros s1 [] s2 g1; split; intros H.
    + destruct H as [Hs HP].
      subst s2.
      exists g1.
      split; auto.
    + destruct H as [g2 [Hs HP]].
      inversion Hs; subst.
      split; auto.
  - intros s g; split; intros H; tauto.
Qed.

Lemma Gequiv_whileP (c: program Σ unit) (c': programG unit)
  (P: Σ -> Prop):
  Gequiv c c' ->
  Gequiv (whileP P c) (whileP (fun '(s, _) => P s) c').
Proof.
  intros Hc.
  unfold whileP, whileP_f.
  apply Gequiv_fix'.
  intros W W' HW.
  apply Gequiv_choice.
  - apply Gequiv_bind.
    + apply Gequiv_assume.
    + intros [].
      apply Gequiv_bind; auto.
  - apply Gequiv_bind.
    + apply Gequiv_assume.
    + intros [].
      apply Gequiv_ret.
Qed.

Lemma Hoare_toG {A: Type} (c: program Σ A) (c': programG A)
  (P: Σ -> Prop) (P': Σ * G -> Prop) (Q: A -> Σ -> Prop):
  Gequiv c c' ->
  Hoare P c Q ->
  (forall s g, P' (s, g) -> P s) ->
  Hoare P' c' (fun a '(s, _) => Q a s).
Proof.
  unfold Hoare, Gequiv; intros [Hn He] [Hnrm Herr] HP.
  split; intros.
  - destruct σ1 as [s1 g1], σ2 as [s2 g2].
    simpl in *.
    eapply Hnrm; [eapply HP; eauto|].
    apply Hn with (g1:=g1). exists g2; auto.
  - destruct σ1 as [s1 g1].
    eapply Herr; [eapply HP; eauto|].
    apply He with (g:=g1); auto.
Qed.

Lemma Hoare_fromG {A: Type} (c: program Σ A) (c': programG A)
  (P: Σ -> Prop) (P': Σ * G -> Prop) (Q: A -> Σ -> Prop):
  Gequiv c c' ->
  (forall s, P s -> exists g, P' (s, g)) ->
  Hoare P' c' (fun a '(s, _) => Q a s) ->
  Hoare P c Q.
Proof.
  unfold Hoare, Gequiv; intros [Hn He] HP [Hnrm Herr].
  split; intros.
  - destruct (HP σ1 H) as [g Hg].
    specialize (Hn σ1 a σ2) as Hneq.
    destruct (Hneq g) as [Hto _].
    specialize (Hto H0) as [g2 Hrun].
    specialize (Hnrm a (σ1, g) (σ2, g2)).
    simpl in Hnrm.
    eapply Hnrm; eauto.
  - destruct (HP σ1 H) as [g Hg].
    specialize (Herr (σ1, g)).
    simpl in Herr.
    eapply Herr; eauto.
    apply He with (g:=g); auto.
Qed.

Lemma Hoare_nrm_fromG {A: Type} (c: program Σ A) (c': programG A)
  (P: Σ -> Prop) (P': Σ * G -> Prop) (Q: A -> Σ -> Prop):
  Gequiv c c' ->
  (forall s, P s -> exists g, P' (s, g)) ->
  Hoare_nrm P' c' (fun a '(s, _) => Q a s) ->
  Hoare_nrm P c Q.
Proof.
  unfold Hoare_nrm, Gequiv; intros [Hn _] HP Hnrm a s1 s2 HPs Hrun.
  destruct (HP s1 HPs) as [g Hg].
  specialize (Hn s1 a s2 g) as [Hto _].
  destruct (Hto Hrun) as [g2 HrunG].
  specialize (Hnrm a (s1, g) (s2, g2)).
  simpl in Hnrm.
  eapply Hnrm; eauto.
Qed.

Lemma Hoare_liftG {A: Type} (P: G -> Σ -> Prop) (c: program Σ A) (Q: G -> A -> Σ -> Prop):
  (forall g, Hoare (P g) c (Q g)) ->
  Hoare (fun '(s, g) => P g s) (liftG c) (fun a '(s, g) => Q g a s).
Proof.
  unfold Hoare, liftG; simpl; intros H.
  split; intros.
  - destruct σ1 as [s1 g1], σ2 as [s2 g2].
    simpl in *; destruct H1; subst.
    destruct (H g1) as [Hn _].
    eapply Hn; eauto.
  - destruct σ1 as [s1 g1].
    destruct (H g1) as [_ He].
    eapply He; eauto.
Qed.

Lemma Hoare_nrm_liftG' {A: Type} (c: program Σ A)
  (P: Σ * G -> Prop) (Q: A -> Σ * G -> Prop):
  (forall g, Hoare_nrm (fun s => P (s, g)) c (fun a s => Q a (s, g))) ->
  Hoare_nrm P (liftG c) Q.
Proof.
  unfold Hoare_nrm, liftG; simpl; intros H a [s1 g1] [s2 g2] HP Hrun.
  destruct Hrun as [Hrun Hg]; subst g2.
  eapply H; eauto.
Qed.

Lemma Hoare_liftG' {A: Type} (c: program Σ A)
  (P: Σ * G -> Prop) (Q: A -> Σ * G -> Prop):
  (forall g, Hoare (fun s => P (s, g)) c (fun a s => Q a (s, g))) ->
  Hoare P (liftG c) Q.
Proof.
  unfold Hoare, liftG; simpl; intros H.
  split; intros.
  - destruct σ1 as [s1 g1], σ2 as [s2 g2].
    simpl in *; destruct H1; subst.
    destruct (H g1) as [Hn _].
    eapply Hn; eauto.
  - destruct σ1 as [s1 g1].
    destruct (H g1) as [_ He].
    eapply He; eauto.
Qed.

Definition keepG {A: Type} (P: G -> Prop) (c: programG A) :=
  Hoare (fun '(_, g) => P g) c (fun _ '(_, g) => P g).

End GhostErr.

Declare Scope ghost_scope.
Notation programG Σ G := (program (Σ * G)) (only parsing).
Notation "↑ c" := (liftG c) (at level 5): ghost_scope.
