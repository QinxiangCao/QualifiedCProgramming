Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Canonical.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaD: Derivable L}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kminSM: KripkeMinimumSemantics L MD M SM}
        {kandpSM: KripkeAndSemantics L MD M SM}
        {korpSM: KripkeOrSemantics L MD M SM}
        {kfalsepSM: KripkeFalseSemantics L MD M SM}
        {ktruepSM: KripkeTrueSemantics L MD M SM}
        {kiffpSM: KripkeIffSemantics L MD M SM}
        {knegpSM: KripkeNegSemantics L MD M SM}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Lemma classical_canonical_ident
      {cpSC: ClassicalSequentCalculus L GammaD}
      (AL_DC: at_least derivable_closed cP)
      (AL_OW: at_least orp_witnessed cP)
      (AL_CONSI: at_least consistent cP):
  IdentityKripkeIntuitionisticModel (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel m) as [Phi ?].
  destruct (im_bij _ _ rel n) as [Psi ?].
  erewrite H_R in H by eauto.
  assert (Phi = Psi); [| subst; eapply (in_bij _ _ rel); eauto].
  clear rel H_R m n H0 H1.

  apply sig_context_ext.
  intros; split; [apply H; auto |].
  intros.
  pose proof derivable_excluded_middle (proj1_sig Phi) x.
  rewrite <- derivable_closed_element_derivable in H1 by (apply AL_DC, (proj2_sig Phi)).
  apply AL_OW in H1; [| apply (proj2_sig Phi)].
  destruct H1; auto.
  exfalso.
  apply H in H1; unfold Ensembles.In in H1.
  rewrite derivable_closed_element_derivable in H0, H1 by (apply AL_DC, (proj2_sig Psi)).
  apply (derivables_negp_unfold (proj1_sig Psi) x) in H1. rewrite derivables_impp_theorem in H1.
  pose proof derivables_modus_ponens _ _ _ H0 H1.
  revert H2; change (~ proj1_sig Psi |--- FF).
  rewrite <- consistent_spec.
  apply AL_CONSI, (proj2_sig Psi).
Qed.

Lemma GodelDummett_canonical_no_branch
      {GammaP: Provable L}
      {GammaPD: ProvableFromDerivable L GammaP GammaD}
      {minAX: MinimumAxiomatization L GammaP}
      {andpAX: AndAxiomatization L GammaP}
      {orpAX: OrAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {inegpAX: IntuitionisticNegAxiomatization L GammaP}
      {iffpAX: IffAxiomatization L GammaP}
      {truepAX: TrueAxiomatization L GammaP}
      {gdpAX: GodelDummettAxiomatization L GammaP}
      (AL_DC: at_least derivable_closed cP)
      (AL_OW: at_least orp_witnessed cP):
  NoBranchKripkeIntuitionisticModel (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  destruct (im_bij _ _ rel m1) as [Psi1 ?].
  destruct (im_bij _ _ rel m2) as [Psi2 ?].
  erewrite !H_R in H, H0 by eauto.
  do 2 erewrite H_R by eauto.
  clear rel H_R m1 m2 n H1 H2 H3.

  apply NNPP; intro.
  apply not_or_and in H1; destruct H1.
  apply not_all_ex_not in H1.
  apply not_all_ex_not in H2.
  destruct H1 as [x1 ?], H2 as [x2 ?].
  pose proof derivables_weaken0 (proj1_sig Phi) _ (impp_choice x1 x2).
  rewrite <- derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Phi)).
  apply AL_OW in H3; [| apply (proj2_sig Phi)].
  destruct H3; pose proof H3; apply H in H3; apply H0 in H4.
  + rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi1)).
    rewrite derivable_closed_element_derivable in H4 by (apply AL_DC, (proj2_sig Psi2)).
    pose proof (fun HH => derivables_modus_ponens _ _ _ HH H3).
    pose proof (fun HH => derivables_modus_ponens _ _ _ HH H4).
    rewrite <- !derivable_closed_element_derivable in H5 by (apply AL_DC, (proj2_sig Psi1)).
    rewrite <- !derivable_closed_element_derivable in H6 by (apply AL_DC, (proj2_sig Psi2)).
    clear - H1 H2 H5 H6.
    tauto.
  + rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi1)).
    rewrite derivable_closed_element_derivable in H4 by (apply AL_DC, (proj2_sig Psi2)).
    pose proof (fun HH => derivables_modus_ponens _ _ _ HH H3).
    pose proof (fun HH => derivables_modus_ponens _ _ _ HH H4).
    rewrite <- !derivable_closed_element_derivable in H5 by (apply AL_DC, (proj2_sig Psi1)).
    rewrite <- !derivable_closed_element_derivable in H6 by (apply AL_DC, (proj2_sig Psi2)).
    clear - H1 H2 H5 H6.
    tauto.
Qed.

Lemma DeMorgan_canonical_branch_join
      {GammaP: Provable L}
      {GammaDP: DerivableFromProvable L GammaP GammaD}
      {GammaPD: ProvableFromDerivable L GammaP GammaD}
      {minAX: MinimumAxiomatization L GammaP}
      {andpAX: AndAxiomatization L GammaP}
      {orpAX: OrAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {inegpAX: IntuitionisticNegAxiomatization L GammaP}
      {iffpAX: IffAxiomatization L GammaP}
      {truepAX: TrueAxiomatization L GammaP}
      {dmpAX: DeMorganAxiomatization L GammaP}
      (AL_DC: at_least derivable_closed cP)
      (AL_OW: at_least orp_witnessed cP)
      (AL_CONSI: at_least consistent cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP):
  BranchJoinKripkeIntuitionisticModel (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  destruct (im_bij _ _ rel m1) as [Psi1 ?].
  destruct (im_bij _ _ rel m2) as [Psi2 ?].
  erewrite !H_R in H, H0 by eauto.
  assert (exists Psi: sig cP, Included _ (proj1_sig Psi1) (proj1_sig Psi) /\
                              Included _ (proj1_sig Psi2) (proj1_sig Psi)).
  2: {
    destruct H4 as [Psi [? ?]].
    destruct (su_bij _ _ rel Psi) as [m ?].
    exists m.
    erewrite !H_R by eauto; auto.
  }
  clear rel H_R m1 m2 n H1 H2 H3.

  assert (~ (Union _ (proj1_sig Psi1) (proj1_sig Psi2)) |--- FF).
  + intro.
    apply derivable_closed_union_derivable in H1; [| apply AL_DC, (proj2_sig Psi2)].
    destruct H1 as [x [? ?]].
    rewrite derivable_closed_element_derivable in H1 by (apply AL_DC, (proj2_sig Psi2)).
    pose proof derivables_weaken0 (proj1_sig Phi) _ (provable_weak_excluded_middle x).
    rewrite <- derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Phi)).
    apply AL_OW in H3; [| apply (proj2_sig Phi)].
    destruct H3.
    - apply H0 in H3; unfold Ensembles.In in H3.
      rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi2)).
      apply (derivables_negp_unfold (proj1_sig Psi2) x) in H3. rewrite derivables_impp_theorem in H3.
      pose proof derivables_modus_ponens _ _ _ H1 H3.
      revert H4; change (~ proj1_sig Psi2 |--- FF).
      rewrite <- consistent_spec.
      apply AL_CONSI, (proj2_sig Psi2).
    - apply H in H3; unfold Ensembles.In in H3.
      rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi1)).
      apply (derivables_negp_unfold (proj1_sig Psi1) (~~ x)) in H3. rewrite derivables_impp_theorem in H3.
      rewrite <- derivables_impp_theorem in H2. apply (derivables_negp_fold (proj1_sig Psi1) x) in H2.
      pose proof derivables_modus_ponens _ _ _ H2 H3.
      revert H4; change (~ proj1_sig Psi1 |--- FF).
      rewrite <- consistent_spec.
      apply AL_CONSI, (proj2_sig Psi1).
  + apply LIN_CD in H1.
    destruct H1 as [Psi [? ?]]; exists Psi.
    split; intros ? ?; apply H1; [left | right]; auto.
Qed.

End Canonical.
