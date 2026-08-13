Require Import Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Trivial.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.

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
        {truepL: TrueLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {andpSC: AndSequentCalculus L Gamma}
        {orpSC: OrSequentCalculus L Gamma}
        {falsepSC: FalseSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegSequentCalculus L Gamma}
        {cpSC: ClassicalSequentCalculus L Gamma}.

Lemma classical_derivable_spec: forall (Phi: context) (x: expr),
  Phi |--- x <-> ~ consistent (Union _ Phi (Singleton _ (~~ x))).
Proof.
  clear dependent andpL.
  clear dependent falsepL.
  intros.
  unfold consistent.
  AddAxiomatization.
  fold (@consistent L Gamma (Phi;; ~~ x)).
  split; intros.
  + rewrite (provable_double_negp_intros x) in H.
    intro.
    destruct H0 as [y ?].
    apply H0; clear H0.
    apply derivables_contradiction_elim with (~~ x).
    - solve_assum.
    - apply deduction_weaken1; auto.
  + rewrite <- (provable_double_negp_elim x).
    apply NNPP; intro.
    apply H; clear H; exists (~~ (~~ x)).
    intro; apply H0.
    apply derivables_negp_fold2; auto.
Qed.

Lemma MCS_nonelement_inconsistent: forall (Phi: context),
  maximal consistent Phi ->
  (forall x: expr, ~ Phi x <-> Phi |--- x --> FF).
Proof.
  clear dependent andpL.
  intros.
  split; intros.
  + destruct H.
    specialize (H1 (Union _ Phi (Singleton _ x))).
    rewrite consistent_spec in H1.
    rewrite derivables_impp_theorem in H1.
    assert (Included expr Phi (Union expr Phi (Singleton expr x))) by (intros ? ?; left; auto).
    assert (~ Included expr (Union expr Phi (Singleton expr x)) Phi) by (intros HH; specialize (HH x); apply H0, HH; right; constructor).
    tauto.
  + intro.
    pose proof derivable_assum Phi x H1.
    pose proof derivables_modus_ponens _ _ _ H2 H0.
    destruct H as [? _].
    rewrite consistent_spec in H; auto.
Qed.

Lemma maximal_consistent_orp_witnessed: forall (Phi: context),
  maximal consistent Phi -> orp_witnessed Phi.
Proof.
  clear dependent andpL.
  intros.
  hnf; intros.
  rewrite MCS_element_derivable in H0 by auto.
  apply NNPP; intro.
  apply not_or_and in H1.
  destruct H1.
  rewrite MCS_nonelement_inconsistent in H1, H2 by eauto.
  destruct H as [? _]; rewrite consistent_spec in H.
  apply H.
  eapply derivables_modus_ponens; [exact H0 |].
  apply derivables_orp_elim'; auto.
Qed.

Lemma MCS_andp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  apply maximal_consistent_derivable_closed in H.
  apply DCS_andp_iff; auto.
Qed.

Lemma MCS_orp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  apply DCS_orp_iff; auto.
  + apply maximal_consistent_derivable_closed; auto.
  + apply maximal_consistent_orp_witnessed; auto.
Qed.

Lemma MCS_impp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
  intros.
  split; intros.
  + rewrite MCS_element_derivable in H0, H1 |- * by auto.
    apply (derivables_modus_ponens _ x y); auto.
  + pose proof derivable_excluded_middle Phi y.
    rewrite <- MCS_element_derivable in H1 by auto.
    rewrite MCS_orp_iff in H1 by auto.
    pose proof derivable_excluded_middle Phi x.
    rewrite <- MCS_element_derivable in H2 by auto.
    rewrite MCS_orp_iff in H2 by auto.
    destruct H1; [| destruct H2].
    - rewrite MCS_element_derivable in H1 |- * by auto.
      apply derivables_impp_intros_l; auto.
    - exfalso.
      apply H0 in H2.
      rewrite MCS_element_derivable in H1, H2 by auto.
      apply (derivables_negp_unfold Phi y) in H1. rewrite derivables_impp_theorem in H1.
      pose proof derivables_modus_ponens _ _ _ H2 H1.
      destruct H as [? _].
      rewrite consistent_spec in H; auto.
    - rewrite MCS_element_derivable in H2 |- * by auto.
      apply (derivables_negp_unfold Phi x) in H2. rewrite derivables_impp_theorem in H2.
      rewrite <- derivables_impp_theorem in H2 |- *.
      pose proof derivables_falsep_elim _ y H2.
      auto.
Qed.

Lemma MCS_negp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x: expr, Phi (~~ x) <-> ~ Phi x).
Proof.
  clear dependent andpL.
  clear dependent falsepL.
  intros.
  rewrite MCS_element_derivable by auto.
  split.
  + intros ? ?.
    rewrite maximal_consistent_spec in H.
    destruct H as [[y ?] _].
    apply H; clear H.
    apply derivables_contradiction_elim with x; auto.
    apply derivable_assum; auto.
  + intros.
    pose proof proj1 (maximal_consistent_spec _) H as [_ ?].
    specialize (H1 x).
    pose proof fun HH => H0 (H1 HH); clear H0 H1.
    apply derivables_negp_fold2.
    apply NNPP; intro.
    apply H2.
    exists (~~ x).
    auto.
Qed.

Lemma DDCS_MCS: forall (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  consistent Phi ->
  maximal consistent Phi.
Proof.
  intros.
  split; auto.
  intros.
  unfold Included, Ensembles.In; intros.
  pose proof derivable_excluded_middle Phi x.
  apply H in H5.
  apply H0 in H5.
  destruct H5; auto.
  exfalso.
  apply H3 in H5; unfold Ensembles.In in H5.
  rewrite consistent_spec in H2.
  apply H2; clear H2.
  apply derivable_assum in H4.
  apply derivable_assum in H5.
  eapply derivables_modus_ponens.
  - apply H4.
  - apply (derivables_negp_unfold Psi x) in H5.
    rewrite derivables_impp_theorem in H5. apply H5.
Qed.

End ContextProperties.

