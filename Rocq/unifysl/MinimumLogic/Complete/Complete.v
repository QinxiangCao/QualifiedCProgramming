Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Completeness.

Context {L: Language}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaPD: ProvableFromDerivable L GammaP GammaD}
        {MD: Model}
        {SM: Semantics L MD}
        {MC: model -> Prop}.

Lemma strongly_complete_strong:
  strongly_complete GammaD SM MC ->
  weakly_complete GammaP SM MC.
Proof.
  intros.
  hnf in H |- *.
  intros.
  specialize (H empty_context x).
  rewrite <- __provable_derivable in H.
  apply H.
  hnf; intros.
  apply H0; auto.
Qed.

End Completeness.
