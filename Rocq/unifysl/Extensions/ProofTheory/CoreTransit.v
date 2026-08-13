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

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import CoreTransitNotation.

Class CoreTransitSeparationLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {CtsL: CoreTransitSeparationLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {sepconAX: SepconAxiomatization L Gamma} {CosAX: Corable L Gamma}:= {
  core_tr_SystemK: @SystemK L minL pL (ct_mL L) Gamma minAX ipAX;
  core_tr_PTransparent: @PropositionalTransparentModality L minL pL (ct_mL L) Gamma minAX ipAX core_tr_SystemK;
  core_tr_STransparent1: @SeparationTransparentModality1 L minL (ct_mL L) sepconL Gamma;
  core_tr_STransparent2: @SeparationTransparentModality2 L minL (ct_mL L) sepconL Gamma;
  core_tr_andp_sepcon: forall x y, |-- core_tr (x && y) --> core_tr (x * y);
  coreAbsorb: @ModalAbsorbStable L minL (ct_mL L) Gamma corable
}.

Section CoreTransit.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {CtsL: CoreTransitSeparationLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {CosAX: Corable L Gamma}
        {CtsGamma: CoreTransitSeparationLogic L Gamma}.

Lemma core_tr_andp: forall x y, |-- core_tr (x && y) <--> core_tr x && core_tr y.
Proof. intros. apply (@boxp_andp L _ _ (ct_mL L) Gamma _ _ core_tr_SystemK). Qed.

Lemma core_tr_orp: forall x y, |-- core_tr (x || y) <--> core_tr x || core_tr y.
Proof. intros. apply (@boxp_orp L _ _ (ct_mL L) Gamma _ _ _ core_tr_PTransparent). Qed.

Lemma core_tr_sepcon: forall x y, |-- core_tr x * core_tr y <--> core_tr (x * y).
Proof.
  intros.
  apply provables_andp_intros.
  + apply (@sepcon_boxp L _ _ sepconL Gamma core_tr_STransparent1).
  + apply (@boxp_sepcon L _ _ sepconL Gamma core_tr_STransparent2).
Qed.

Instance core_tr_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) core_tr.
Proof. apply (@boxp_proper_impp L _ _ (ct_mL L) Gamma _ _ core_tr_SystemK). Qed.

Instance core_tr_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) core_tr.
Proof. apply (@boxp_proper_iffp L _ _ (ct_mL L) Gamma _ _ core_tr_SystemK). Qed.

Lemma core_tr_andp_sepcon_iffp {GC: GarbageCollectSeparationLogic L Gamma}: forall x y, |-- core_tr (x && y) <--> core_tr (x * y).
Proof.
  intros.
  apply provables_andp_intros.
  + apply core_tr_andp_sepcon.
  + (* TODO: modularize this proof. *)
    pose proof (@axiom_K L _ _ (ct_mL L) Gamma _ _ core_tr_SystemK).
    simpl in H; rewrite <- H; clear H.
    apply (@rule_N L _ _ (ct_mL L) Gamma _ _ core_tr_SystemK).
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

Lemma core_tr_absorb_corable: forall x, corable x -> |-- x --> core_tr x.
Proof. intros. apply (@boxp_absorb_stable _ _ (ct_mL L) Gamma corable coreAbsorb); auto. Qed.

End CoreTransit.

Existing Instances core_tr_proper_impp core_tr_proper_iffp.

