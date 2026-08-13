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
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
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
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {andpSC: AndSequentCalculus L Gamma}
        {orpSC: OrSequentCalculus L Gamma}
        {falsepSC: FalseSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegSequentCalculus L Gamma}
        {iffpSC: IffSequentCalculus L Gamma}
        {truepSC: TrueSequentCalculus L Gamma}
        {cpSC: ClassicalSequentCalculus L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {SM: Semantics L MD}
        {tminSM: TrivialMinimumSemantics L MD SM}
        {andpSM: AndSemantics L MD SM}
        {orpSM: OrSemantics L MD SM}
        {falsepSM: FalseSemantics L MD SM}
        {truepSM: TrueSemantics L MD SM}
        {iffpSM: IffSemantics L MD SM}
        {negpSM: NegSemantics L MD SM}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Context (AL_MC: at_least (maximal consistent) cP).

Lemma truth_lemma_falsep:
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= falsep <-> proj1_sig Phi falsep).
Proof.
  intros.
  rewrite sat_falsep.
  pose proof proj2_sig Phi.
  pose proof proj1 (AL_MC _ H0).
  rewrite consistent_spec in H1.
  split; [intros [] |].
  intro; apply H1.
  apply derivable_assum; auto.
Qed.

Lemma truth_lemma_andp
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x && y <-> proj1_sig Phi (x && y)).
Proof.
  intros.
  rewrite sat_andp.
  rewrite MCS_andp_iff by (apply AL_MC, (proj2_sig Phi)).
  apply Morphisms_Prop.and_iff_morphism; auto.
Qed.

Lemma truth_lemma_orp
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x || y <-> proj1_sig Phi (x || y)).
Proof.
  intros.
  rewrite sat_orp.
  rewrite MCS_orp_iff by (apply AL_MC, (proj2_sig Phi)).
  apply Morphisms_Prop.or_iff_morphism; auto.
Qed.

Lemma truth_lemma_impp
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
  intros.
  rewrite sat_impp.
  rewrite MCS_impp_iff by (apply AL_MC, (proj2_sig Phi)).
  apply Morphisms_Prop.iff_iff_iff_impl_morphism; auto.
Qed.

Lemma truth_lemma_negp
      (x: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= ~~ x <-> proj1_sig Phi (~~ x)).
Proof.
  intros.
  rewrite sat_negp.
  rewrite IHx by eassumption.
  pose proof MCS_negp_iff.
  rewrite MCS_negp_iff by (apply AL_MC, (proj2_sig Phi)).
  tauto.
Qed.

End TruthLemma.


