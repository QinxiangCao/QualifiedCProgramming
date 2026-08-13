Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Section RewriteClass.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {KmAX: SystemK L Gamma}.

#[export] Instance boxp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) boxp.
Proof.
  hnf; intros x y ?.
  apply rule_N in H.
  eapply provables_modus_ponens; eauto.
  apply axiom_K.
Qed.

#[export] Instance boxp_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) boxp.
Proof.
  hnf; intros x y ?.
  apply provables_andp_intros; apply boxp_proper_impp.
  + eapply provables_andp_elim1; eauto.
  + eapply provables_andp_elim2; eauto.
Qed.

#[export] Instance diamondp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) diamondp.
Proof.
  hnf; intros x y ?.
  unfold diamondp.
  rewrite H.
  apply provable_impp_refl.
Qed.

#[export] Instance diamondp_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) diamondp.
Proof.
  hnf; intros x y ?.
  unfold diamondp.
  rewrite H.
  apply provable_iffp_refl.
Qed.

End RewriteClass.

Existing Instances boxp_proper_impp boxp_proper_iffp diamondp_proper_impp diamondp_proper_iffp.
