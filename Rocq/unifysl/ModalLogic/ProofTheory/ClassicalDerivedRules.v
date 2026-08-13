Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.IntuitionisticDerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Section ClassicalderivedRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {cpAX: ClassicalPropositionalLogic L Gamma}
        {KmAX: SystemK L Gamma}.

Existing Instances Classical2GodelDummett GodelDummett2DeMorgan.

Lemma diamondp_orp: forall x y, |-- diamondp (x || y) <--> (diamondp x || diamondp y).
Proof.
  intros.
  apply provables_andp_intros; [| apply orp_diamondp].
  unfold diamondp.
  rewrite <- demorgan_negp_andp.
  rewrite <- provable_contrapositivePP.
  rewrite <- boxp_andp.
  rewrite provable_demorgan_negp_orp.
  apply provable_impp_refl.
Qed.

#[export] Instance PropositionalTransparentModality2StrongPropositionalTransparentModality {pmGamma: PropositionalTransparentModality L Gamma}: StrongPropositionalTransparentModality L Gamma.
Proof.
  constructor.
  intros.
  apply provables_andp_intros; [apply axiom_K |].
  rewrite (provable_negp_orp x y), (provable_negp_orp (boxp x) (boxp y)).
  rewrite boxp_orp.
  apply provables_orp_impp_fold; [| apply provable_orp_intros2].
  rewrite <- provable_orp_intros1.
  apply (modus_ponens (boxp (x || ~~ x))).
  + rewrite boxp_orp.
    apply provables_orp_impp_fold; [| apply provable_axiom1].
    AddSequentCalculus.
    rewrite __provable_derivable.
    rewrite <- !derivables_impp_theorem.
    apply derivables_falsep_elim.
    apply derivables_modus_ponens with (boxp x); solve_assum.
  + apply rule_N.
    apply provable_excluded_middle.
Qed.

End ClassicalderivedRules.
