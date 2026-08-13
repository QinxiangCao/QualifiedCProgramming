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
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.
Require Import Morphisms.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section TruthLemma.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaPD: ProvableFromDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {GammaDP: DerivableFromProvable L GammaP GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {J: Join (Kworlds M)}
        {U: Unit (Kworlds M)}
        {SM: Semantics L MD}
        {fsepconSM: SepconSemantics L MD M SM}
        {fwandSM: WandSemantics L MD M SM}
        {empL: EmpLanguage L}
        {empAX: EmpAxiomatization L GammaP}
        {empSM: EmpSemantics L MD M SM}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Hypothesis H_J: forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi -> (join m1 m2 m <-> Included _ (context_sepcon (proj1_sig Phi1) (proj1_sig Phi2)) (proj1_sig Phi)).

Hypothesis H_U: forall m Phi, rel m Phi -> (is_unit m <-> proj1_sig Phi emp).

Lemma truth_lemma_sepcon
      (AL_DC: at_least derivable_closed cP)
      (LIN_SL: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_l Phi (proj1_sig Psi)) cP)
      (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x * y <-> proj1_sig Phi (x * y)).
Proof.
  intros.
  rewrite sat_sepcon.
  split; intros.
  + destruct H0 as [m1 [m2 [? [? ?]]]].
    destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    erewrite IHx in H1 by eauto.
    erewrite IHy in H2 by eauto.
    erewrite H_J in H0 by eauto.
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    apply derivable_assum.
    apply H0.
    exists x, y; split; [| split]; auto; apply derivable_assum; auto.
  + apply derivable_assum in H0.
    assert (Included _ (context_sepcon (Union _ empty_context (Singleton _ x))
             (Union _ empty_context (Singleton _ y))) (proj1_sig Phi)).
    {
      hnf; intros z ?.
      destruct H1 as [x0 [y0 [? [? ?]]]].
      rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
      rewrite derivables_impp_theorem, <- __provable_derivable in H2, H3.
      subst z; rewrite <- H2, <- H3.
      auto.
    }
    apply LIN_SL in H1.
    destruct H1 as [Phi1 [? ?]].
    apply LIN_SR in H2.
    destruct H2 as [Phi2 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    exists m1, m2.
    erewrite H_J, IHx, IHy by eauto.
    split; [| split]; auto.
    - apply H1; right; constructor.
    - apply H2; right; constructor.
Qed.

Lemma truth_lemma_wand
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x -* y <-> proj1_sig Phi (x -* y)).
Proof.
  intros.
  rewrite sat_wand.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)); auto.
    rewrite <- wand_derivables_impp_theorem.
    apply NNPP; intro.
    apply LIN_CD in H1.
    destruct H1 as [Phi2 [? ?]].
    apply H2; clear H2.
    rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi2)); auto.
    apply LIN_SR in H1.
    destruct H1 as [Phi1 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    erewrite <- IHy by eauto.
    unfold context_sepcon_included_r in H2; erewrite <- H_J in H2 by eauto.
    apply (H0 _ _ H2).
    erewrite IHx by eauto.
    apply H1; right; constructor.
  + destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    erewrite IHy by eauto.
    erewrite IHx in H2 by eauto.
    erewrite H_J in H1 by eauto.
    rewrite derivable_closed_element_derivable in H0 by (apply AL_DC, (proj2_sig Phi)).
    rewrite derivable_closed_element_derivable in H2 by (apply AL_DC, (proj2_sig Phi1)).
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi2)).
    rewrite <- provable_wand_elim1 with (x := x).
    apply derivable_assum; apply H1.
    exists (x -* y), x; split; [| split]; auto.
Qed.


Lemma truth_lemma_emp
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= emp <-> proj1_sig Phi emp).
Proof.
  intros.
  rewrite sat_emp.
  split; intros.
  + rewrite (H_U _ _ H) in H0. apply H0.
  + rewrite <- (H_U _ _ H) in H0. apply H0.
Qed.

End TruthLemma.
