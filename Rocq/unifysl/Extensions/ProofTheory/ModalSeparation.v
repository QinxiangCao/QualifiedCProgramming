Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.

Class SeparationTransparentModality1 (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := {
  sepcon_boxp: forall x y, |-- boxp x * boxp y --> boxp (x * y)
}.

Class SeparationTransparentModality2 (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := {
  boxp_sepcon: forall x y, |-- boxp (x * y) --> boxp x * boxp y
}.

Class SeparationTransparentModality3 (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) := {
  wand_boxp: forall x y, |-- (boxp x -* boxp y) --> boxp (x -* y)
}.

Class SeparationTransparentModality4 (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) := {
  boxp_wand: forall x y, |-- boxp (x -* y) --> (boxp x -* boxp y)
}.

Instance SeparationTransparentModality14 (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {sepconAX: SepconAxiomatization L Gamma} {wandAX: WandAxiomatization L Gamma} {sm1Gamma: SeparationTransparentModality1 L Gamma}:
  SeparationTransparentModality4 L Gamma.
Proof.
  constructor.
  intros.
  apply provables_wand_sepcon_adjoint.
  rewrite sepcon_boxp.
  rewrite provable_wand_elim1.
  apply provable_impp_refl.
Qed.

Instance SeparationTransparentModality41 (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {sepconAX: SepconAxiomatization L Gamma} {wandAX: WandAxiomatization L Gamma} {sm4Gamma: SeparationTransparentModality4 L Gamma}:
  SeparationTransparentModality1 L Gamma.
Proof.
  constructor.
  intros.
  apply provables_wand_sepcon_adjoint.
  rewrite <- boxp_wand.
  eapply provables_modus_ponens; [apply axiom_K |].
  apply rule_N.
  apply provables_wand_sepcon_adjoint.
  apply provable_impp_refl.
Qed.
