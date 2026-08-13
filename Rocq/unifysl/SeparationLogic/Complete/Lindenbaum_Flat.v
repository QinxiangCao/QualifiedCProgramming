Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section Lindenbaum_Flat.

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
        {fwSC: FiniteWitnessedSequentCalculus L GammaD}
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
        {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
        {sepcon_falsep_AX: SepconFalseAxiomatization L GammaP}.

Lemma Lindenbaum_preserves_context_sepcon_included_l: forall Phi2 Psi,
  Lindenbaum_preserves (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  apply Lindenbaum_preserves_by_finiteness.
  + apply context_sepcon_included_l_finite_captured.
  + apply context_sepcon_included_l_subset_preserved.
Qed.

Lemma Lindenbaum_context_sepcon_included_l_ensures_derivable_closed: forall Phi Psi,
  Lindenbaum_ensures (context_sepcon_included_l Phi Psi) derivable_closed.
Proof.
  intros.
  apply Lindenbaum_for_derivable_closed.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + apply context_sepcon_included_l_derivable_subset_preserved.
Qed.

Lemma Lindenbaum_context_sepcon_included_l_ensures_orp_witnessed: forall Phi Psi
      (DC: derivable_closed Psi)
      (OW: orp_witnessed Psi),
  Lindenbaum_ensures (context_sepcon_included_l Phi Psi) orp_witnessed.
Proof.
  intros.
  apply Lindenbaum_for_orp_witnessed.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + apply context_sepcon_included_l_subset_preserved.
  + apply context_sepcon_included_l_context_orp_captured; auto.
  + apply Lindenbaum_context_sepcon_included_l_ensures_derivable_closed.
Qed.

Lemma Lindenbaum_context_sepcon_included_l_ensures_consistent: forall Phi Psi
  (CONSI: consistent Psi),
  Lindenbaum_ensures (context_sepcon_included_l Phi Psi) consistent.
Proof.
  intros.
  apply Lindenbaum_for_consistent.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + intros Phi' ?.
    eapply context_sepcon_consistent_rev_left; eauto.
Qed.

End Lindenbaum_Flat.
