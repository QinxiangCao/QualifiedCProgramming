Require Import Coq.Logic.Classical_Prop.
Require Import Morphisms.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section ContextProperties.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}.

Definition orp_witnessed: context -> Prop :=
  fun Phi => forall x y, Phi (orp x y) -> Phi x \/ Phi y.

Context {GammaP: Provable L} {GammaD: Derivable L}.

Definition context_orp (Phi Psi: context): context :=
  fun z => exists x y, z = x || y /\ Phi |--- x /\ Psi |--- y.

Definition context_orp_captured (P: context -> Prop): Prop :=
  forall Phi Psi, P (context_orp Phi Psi) -> P Phi \/ P Psi.

Context {GammaPD: ProvableFromDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}.

Lemma context_orp_mono: forall Phi Psi Phi' Psi',
  Included _ (derivable Phi) (derivable Phi') ->
  Included _ (derivable Psi) (derivable Psi') ->
  Included _ (context_orp Phi Psi) (context_orp Phi' Psi').
Proof.
  intros.
  hnf; unfold Ensembles.In; intros.
  hnf in H1 |- *.
  destruct H1 as [y [z [? [? ?]]]]; subst.
  exists y, z.
  split; [| split]; auto.
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma context_orp_mono': forall Phi Psi Phi' Psi',
  Included _ Phi Phi' ->
  Included _ Psi Psi' ->
  Included _ (context_orp Phi Psi) (context_orp Phi' Psi').
Proof.
  intros.
  apply context_orp_mono; hnf; intros; eapply deduction_weaken; eauto.
Qed.

Lemma cannot_derive_context_orp_captured: forall (x: expr),
  context_orp_captured (cannot_derive x).
Proof.
  intros.
  unfold cannot_derive.
  hnf; intros.
  apply not_and_or.
  intros [? ?]; apply H; clear H.
  rewrite <- (provable_orp_dup1 x).
  apply derivable_assum.
  exists x, x.
  split; [| split]; auto.
Qed.

Lemma DCS_truep: forall (Phi: context),
  derivable_closed Phi ->
  Phi TT.
Proof.
  intros.
  apply H.
  apply derivable_truep_intros.
Qed.

Lemma DCS_andp_iff: forall (Phi: context),
  derivable_closed Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  pose proof derivable_closed_element_derivable _ H; clear H.
  rewrite !H0; clear H0; split; intros.
  + pose proof derivables_andp_elim1 Phi x y H.
    pose proof derivables_andp_elim2 Phi x y H.
    auto.
  + destruct H.
    pose proof derivables_andp_intros Phi x y H H0.
    auto.
Qed.

Lemma DCS_iffp: forall (Phi: context) (x y: expr),
  derivable_closed Phi ->
  |-- x <--> y ->
  (Phi x <-> Phi y).
Proof.
  intros.
  split; intros.
  + apply H.  
    rewrite <- H0.
    apply derivable_assum; auto.
  + apply H.
    rewrite H0.
    apply derivable_assum; auto.
Qed.

Lemma DCS_multi_and_iff
      {iter_andp_L: IterAndLanguage L}
      {iter_andp_AXL: IterAndAxiomatization_left L GammaP}: forall (Phi: context),
  derivable_closed Phi ->
  (forall xs: list expr, Phi (iter_andp xs) <-> Forall Phi xs).
Proof.
  intros.
  rewrite (DCS_iffp Phi (iter_andp xs) (fold_right andp TT xs)).
  2: auto.
  2: apply provable_iter_andp_sepc_right.

  induction xs.
  + split; intros.
    - constructor.
    - simpl.
      apply DCS_truep; auto.
  + simpl.
    rewrite DCS_andp_iff by auto.
    rewrite IHxs.
    clear.
    split; intros.
    - constructor; tauto.
    - inversion H; auto.
Qed.

Lemma DCS_orp_iff: forall (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  pose proof derivable_closed_element_derivable _ H; clear H.
  split; intros.
  + apply H0; auto.
  + rewrite !H1 in *.
    destruct H.
    - pose proof derivables_orp_intros1 Phi x y H; auto.
    - pose proof derivables_orp_intros2 Phi x y H; auto.
Qed.

Lemma derivable_closed_union_derivable {GammaDP: DerivableFromProvable L GammaP GammaD}: forall (Phi Psi: context) (x: expr),
  derivable_closed Psi ->
  Union _ Phi Psi |--- x ->
  exists y, Psi y /\ Phi |--- y --> x.
Proof.
  intros.
  rewrite __derivable_provable in H0.
  destruct H0 as [xs [? ?]].
  pose proof provable_multi_imp_split _ _ _ _ H0 H1 as [xs1 [xs2 [? [? ?]]]].
  pose proof H4.
  AddConnective_iter_andp.
  rewrite <- iter_andp_multi_imp in H4.
  eapply provables_modus_ponens in H4; [| apply provable_multi_imp_arg_switch1].
  exists (iter_andp xs2).
  split.
  + apply DCS_multi_and_iff; auto.
  + rewrite __derivable_provable.
    exists xs1.
    split; auto.
    eapply provables_modus_ponens.
    - apply provable_multi_imp_weaken.
      rewrite (iter_andp_multi_imp xs2 x).
      apply provable_impp_refl.
    - exact H5.
Qed.

Lemma consistent_spec:
  forall (Phi: context), consistent Phi <-> ~ Phi |--- FF.
Proof.
  intros.
  split; intros.
  + intro.
    destruct H as [x H]; apply H; clear H.
    apply derivables_falsep_elim.
    auto.
  + exists FF; auto.
Qed.

End ContextProperties.
