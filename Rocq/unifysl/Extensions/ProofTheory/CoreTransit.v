Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Syntax_CoreTransit.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.IntuitionisticDerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.Extensions.ProofTheory.Stable.
Require Import Logic.Extensions.ProofTheory.ModalSeparation.
Require Import Logic.Extensions.ProofTheory.Corable.
Require Logic.SeparationLogic.ProofTheory.Corable.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import CoreTransitNotation.

Module BaseCorable := Logic.SeparationLogic.ProofTheory.Corable.

Class CoreTransitSeparationLogic
      (L: Language)
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {orpL: OrLanguage L}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {truepL: TrueLanguage L}
      {iffpL: IffLanguage L}
      {sepconL: SepconLanguage L}
      {wandL: WandLanguage L}
      {CtsL: CoreTransitSeparationLanguage L}
      (Gamma: Provable L)
      {minAX: MinimumAxiomatization L Gamma}
      {andpAX: AndAxiomatization L Gamma}
      {orpAX: OrAxiomatization L Gamma}
      {falsepAX: FalseAxiomatization L Gamma}
      {inegpAX: IntuitionisticNegAxiomatization L Gamma}
      {truepAX: TrueAxiomatization L Gamma}
      {iffpAX: IffAxiomatization L Gamma}
      {sepconAX: SepconAxiomatization L Gamma}
      {Cor: BaseCorable.Corable L}:= {
  core_tr_SystemK: @SystemK L minL (ct_mL L) Gamma;
  core_tr_PTransparent: @PropositionalTransparentModality L minL orpL iffpL (ct_mL L) Gamma;
  core_tr_STransparent1: @SeparationTransparentModality1 L minL (ct_mL L) sepconL Gamma;
  core_tr_STransparent2: @SeparationTransparentModality2 L minL (ct_mL L) sepconL Gamma;
  core_tr_andp_sepcon: forall x y, |-- core_tr (x && y) --> core_tr (x * y);
  coreAbsorb: @ModalAbsorbStable L minL (ct_mL L) Gamma (@BaseCorable.corable L Cor)
}.

Section CoreTransit.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {truepL: TrueLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {CtsL: CoreTransitSeparationLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {Cor: BaseCorable.Corable L}
        {CtsGamma: CoreTransitSeparationLogic L Gamma}.

Lemma core_tr_andp: forall x y, |-- core_tr (x && y) <--> core_tr x && core_tr y.
Proof.
  intros.
  apply (@boxp_andp
           L minL (ct_mL L) Gamma minAX core_tr_SystemK
           andpL orpL falsepL negpL iffpL truepL
           andpAX orpAX falsepAX inegpAX truepAX iffpAX).
Qed.

Lemma core_tr_orp: forall x y, |-- core_tr (x || y) <--> core_tr x || core_tr y.
Proof.
  intros.
  apply (@boxp_orp L minL orpL iffpL (ct_mL L) Gamma core_tr_PTransparent).
Qed.

Lemma core_tr_sepcon: forall x y, |-- core_tr x * core_tr y <--> core_tr (x * y).
Proof.
  intros.
  apply provables_iffp_intros.
  + apply (@sepcon_boxp L minL (ct_mL L) sepconL Gamma core_tr_STransparent1).
  + apply (@boxp_sepcon L minL (ct_mL L) sepconL Gamma core_tr_STransparent2).
Qed.

Instance core_tr_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) core_tr.
Proof. apply (@boxp_proper_impp L minL (ct_mL L) Gamma minAX core_tr_SystemK). Qed.

Instance core_tr_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) core_tr.
Proof. apply (@boxp_proper_iffp L minL iffpL (ct_mL L) Gamma minAX iffpAX core_tr_SystemK). Qed.

Lemma core_tr_andp_sepcon_iffp {GC: GarbageCollectSeparationLogic L Gamma}: forall x y, |-- core_tr (x && y) <--> core_tr (x * y).
Proof.
  intros.
  apply provables_iffp_intros.
  + apply core_tr_andp_sepcon.
  + (* TODO: modularize this proof. *)
    pose proof (@axiom_K L _ (ct_mL L) Gamma core_tr_SystemK).
    simpl in H; rewrite <- H; clear H.
    apply (@rule_N L _ (ct_mL L) Gamma core_tr_SystemK).
    apply provables_impp_andp_fold.
    - rewrite <- (provable_sepcon_elim1 x y) at 2.
      apply provable_impp_refl.
    - rewrite <- (provable_sepcon_elim2 x y) at 2.
      apply provable_impp_refl.
Qed.

Lemma core_tr_dup {GC: GarbageCollectSeparationLogic L Gamma}: forall x, |-- core_tr x <--> core_tr x * core_tr x.
Proof.
  intros.
  rewrite <- (provable_andp_dup x) at 1.
  rewrite core_tr_andp_sepcon_iffp.
  rewrite core_tr_sepcon.
  apply provable_iffp_refl.
Qed.

Lemma core_tr_absorb_corable: forall x, BaseCorable.corable x -> |-- x --> core_tr x.
Proof.
  intros.
  apply (@boxp_absorb_stable _ _ (ct_mL L) Gamma (@BaseCorable.corable L Cor) coreAbsorb); auto.
Qed.

End CoreTransit.

Existing Instances core_tr_proper_impp core_tr_proper_iffp.
