Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Trivial.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section Lindenbaum_Trivial.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
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
        {cpSC: ClassicalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}.

Lemma Lindenbaum_for_max_consistent: forall P,
  Lindenbaum_ensures P derivable_closed ->
  Lindenbaum_ensures P orp_witnessed ->
  Lindenbaum_ensures P consistent ->
  Lindenbaum_ensures P (maximal consistent).
Proof.
  intros.
  hnf; intros.
  apply DDCS_MCS; auto.
Qed.

Lemma Lindenbaum_cannot_derive_ensures_max_consistent
      {GammaDP: DerivableFromProvable L GammaP GammaD}:
  forall x, Lindenbaum_ensures (cannot_derive x) (maximal consistent).
Proof.
  intros.
  apply Lindenbaum_for_max_consistent.
  - apply Lindenbaum_cannot_derive_ensures_derivable_closed.
  - apply Lindenbaum_cannot_derive_ensures_orp_witnessed.
  - apply Lindenbaum_cannot_derive_ensures_consistent.
Qed.

End Lindenbaum_Trivial.
