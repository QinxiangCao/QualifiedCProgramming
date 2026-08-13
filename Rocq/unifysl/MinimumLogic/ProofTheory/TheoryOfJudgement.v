Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Section Axiomatization2Deduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD:Derivable L}
        {GammaD1: Derivable1 L}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2Deduction_bD: BasicDeduction L GammaD1.
Proof.
  constructor.
  pose proof __derivable1_provable.
  -intros. 
   apply __derivable1_provable. apply provable_impp_refl.
  -intros.
   apply __derivable1_provable. apply __derivable1_provable in H. 
   apply __derivable1_provable in H0.
   pose proof aux_minimun_rule02 _ _ _ H H0. auto.
Qed.

Lemma Axiomatization2Deduction_GammaPD1 : ProvableFromDerivable1 L GammaP GammaD1.
Proof.
  constructor.
  intros. split.
  -intros.
   apply __derivable1_provable.
   apply aux_minimun_rule00. auto.
  -intros.
   apply __derivable1_provable in H.
   pose proof provable_impp_refl x.
   pose proof provables_modus_ponens _ _ H H0. auto.
Qed.


Lemma Axiomatization2Deduction_minD : MinimumDeduction L GammaD1.
Proof. 
  constructor; pose proof Axiomatization2Deduction_GammaPD1.
  - intros. rewrite __derivable1_provable in *. 
  pose proof provable_axiom2 x y z.
  pose proof provables_modus_ponens _ _ H2 H0.
  pose proof provables_modus_ponens _ _ H3 H1. auto.
  - intros. rewrite __derivable1_provable in *. 
  pose proof aux_minimun_rule01 (x --> y) z y H0.
  eapply aux_minimun_rule02; eauto.
  apply aux_minimun_rule00. apply provable_axiom1.
  - intros. rewrite __derivable1_provable in *. 
  apply aux_minimun_rule00. apply provable_impp_refl.
  - intros. rewrite __derivable1_provable in *. apply provable_axiom1.
  - intros. rewrite __derivable1_provable in *. apply minAX.
Qed.

End Axiomatization2Deduction.

Section Axiomatization2LogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaL: LogicEquiv L}
        {GammaEP: EquivProvable L GammaP GammaL}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2Equiv_bE: BasicLogicEquiv L GammaL.
Proof.
  constructor.
  -intros.
   apply __logic_equiv_provable.
   pose proof provable_impp_refl x.
   split;[auto|auto].
  -intros.
   apply __logic_equiv_provable. apply __logic_equiv_provable in H.
   destruct H.
   split;[auto|auto].
  -intros. apply __logic_equiv_provable. apply __logic_equiv_provable in H. 
   apply __logic_equiv_provable in H0.
   destruct H,H0.
   pose proof aux_minimun_rule02 _ _ _ H H0.
   pose proof aux_minimun_rule02 _ _ _ H2 H1.
   split;[auto|auto].
  Qed.

End Axiomatization2LogicEquiv.


