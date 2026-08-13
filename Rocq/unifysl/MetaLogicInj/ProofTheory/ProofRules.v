Require Import Logic.lib.register_typeclass.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MetaLogicInj.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.

Class CoqPropAxiomatization
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Provable L): Prop := {
  provables_coq_prop_intros: forall P: Prop, P -> |-- !! P;
  provables_coq_prop_elim: forall (P: Prop) x, (P -> |-- x) -> |-- !! P --> x;
}.

Class CoqPropImpAxiomatization
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Provable L): Prop := {
  provable_coq_prop_impp_derives: forall (P Q: Prop), |-- (!! P --> !! Q) --> !! (P -> Q);
}.

Class CoqPropSequentCalculus
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Derivable L): Prop := {
  derivables_coq_prop_intros: forall (P: Prop) Phi, P -> Phi |--- !! P;
  derivables_coq_prop_elim: forall (P: Prop) Phi x, (P -> Phi |--- x) -> Phi;; !! P |--- x;
  derivable_coq_prop_impp_l: forall (P Q: Prop) Phi, Phi;; !! P --> !! Q |--- !! (P -> Q)
}.

Class CoqPropDeduction
      (L: Language)
      {truepL: TrueLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (GammaD1: Derivable1 L): Prop := {
  derivable1s_coq_prop_r: forall (P: Prop) x, P -> x |-- !! P;
  derivable1s_coq_prop_l: forall (P: Prop) x, (P -> TT |-- x) -> !! P |-- x;
}.

Class CoqPropImpDeduction
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (GammaD1: Derivable1 L): Prop := {
  derivable1_coq_prop_impp_derives: forall (P Q: Prop), (!! P --> !! Q) |-- !! (P -> Q);
}.

Section DerivedRulesFromAxiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {coq_prop_AX: CoqPropAxiomatization L Gamma}.

Lemma provables_coq_prop_truep: forall (P: Prop), P -> |-- !! P <--> truep.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_coq_prop_elim.
    intros.
    apply provable_truep.
  + apply aux_minimun_rule00.
    apply provables_coq_prop_intros.
    auto.
Qed.

Lemma provables_coq_prop_andp: forall (P: Prop) Q, P -> |-- !! P && Q <--> Q.
Proof.
  intros.
  rewrite provables_coq_prop_truep by auto.
  rewrite provable_truep_andp.
  apply provable_iffp_refl.
Qed.

Lemma provables_andp_coq_prop: forall (P: Prop) Q, P -> |-- Q && !! P <--> Q.
Proof.
  intros.
  rewrite provables_coq_prop_truep by auto.
  rewrite provable_andp_truep.
  apply provable_iffp_refl.
Qed.

Lemma provables_coq_prop_andp_derives: forall (P: Prop) Q R, (P -> |-- Q --> R) -> |-- !! P && Q --> R.
Proof.
  intros.
  rewrite <- provable_impp_curry.
  apply provables_coq_prop_elim.
  auto.
Qed.

Lemma provables_andp_coq_prop_derives: forall (P: Prop) Q R, (P -> |-- Q --> R) -> |-- Q && !! P --> R.
Proof.
  intros.
  rewrite provable_andp_comm.
  rewrite <- provable_impp_curry.
  apply provables_coq_prop_elim.
  auto.
Qed.

Lemma provables_impp_coq_prop: forall (P: Prop) Q, P -> |-- Q --> !! P.
Proof.
  intros.
  apply aux_minimun_rule00.
  apply provables_coq_prop_intros.
  auto.
Qed.

Lemma provable_coq_prop_and: forall P Q: Prop, |-- !! (P /\ Q) <--> !! P && !! Q.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_coq_prop_elim.
    intros [? ?].
    apply provables_andp_intros; apply provables_coq_prop_intros; auto.
  + rewrite <- provable_impp_curry.
    apply provables_coq_prop_elim; intros.
    apply provables_coq_prop_elim; intros.
    apply provables_coq_prop_intros; auto.
Qed.

Lemma provable_coq_prop_or: forall P Q: Prop, |-- !! (P \/ Q) <--> !! P || !! Q.
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_coq_prop_elim.
    intros [? | ?].
    - apply provables_orp_intros1.
      apply provables_coq_prop_intros; auto.
    - apply provables_orp_intros2.
      apply provables_coq_prop_intros; auto.
  + apply provables_orp_impp_fold.
    - apply provables_coq_prop_elim; intros.
      apply provables_coq_prop_intros; auto.
    - apply provables_coq_prop_elim; intros.
      apply provables_coq_prop_intros; auto.
Qed.

Lemma provable_coq_prop_imply {coq_prop_impp_AX: CoqPropImpAxiomatization L Gamma}:
  forall P Q: Prop, |-- !! (P -> Q) <--> (!! P --> !! Q).
Proof.
  intros.
  apply provables_iffp_intros.
  + apply provables_coq_prop_elim; intros.
    apply provables_coq_prop_elim; intros.
    apply provables_coq_prop_intros; auto.
  + apply provable_coq_prop_impp_derives.
Qed.

End DerivedRulesFromAxiomatization.

Section Deduction2Axiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {minAX: MinimumAxiomatization L GammaP}
        {bD: BasicDeduction L GammaD1}
        {truepD: TrueDeduction L GammaD1}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}
        {GammaPD1: ProvableFromDerivable1 L GammaP GammaD1}.

Lemma Deduction2Axiomatization_coq_prop_AX:
  CoqPropAxiomatization L GammaP.
Proof.  
  constructor.
  + intros.
    rewrite provable_derivable1_true. apply derivable1s_coq_prop_r. auto.
  + intros.
    apply __derivable1_provable.
    rewrite provable_derivable1_true in H.
    apply derivable1s_coq_prop_l.
    auto.
Qed.

Lemma Deduction2Axiomatization_coq_prop_impp_AX
      {coq_prop_impp_D: CoqPropImpDeduction L GammaD1}:
  CoqPropImpAxiomatization L GammaP.
Proof.
  constructor.
  intros.
  apply __derivable1_provable. apply derivable1_coq_prop_impp_derives.
Qed.

End Deduction2Axiomatization.

#[export] Instance reg_Deduction2Axiomatization_coq_prop_AX:
  RegisterClass D12P_reg (fun coq_prop_AX:unit => @Deduction2Axiomatization_coq_prop_AX) 8.
Qed.

#[export] Instance reg_Deduction2Axiomatization_coq_prop_impp_AX:
  RegisterClass D12P_reg (fun provable_coq_prop_impp_derives_AX:unit => @Deduction2Axiomatization_coq_prop_impp_AX) 9.
Qed.

Section DeductionRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {orpD: OrDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {truepD: TrueDeduction L GammaD1}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma derivable1s_coq_prop_andp_l: 
forall (P: Prop) Q R, (P -> Q |-- R) -> !! P && Q |-- R.
Proof.
  intros.
  apply derivable1s_impp_andp_adjoint.
  apply derivable1s_coq_prop_l.
  intros.
  apply derivable1s_impp_andp_adjoint.
  rewrite <- H by auto.
  apply derivable1_andp_elim2.
Qed.

Lemma derivable1s_andp_coq_prop_l: 
forall (P: Prop) Q R, (P -> Q |-- R) -> Q && !! P |-- R.
Proof.
  intros.
  rewrite derivable1_andp_comm.
  apply derivable1s_coq_prop_andp_l.
  auto.
Qed.

Lemma derivable1s_coq_prop_andp_r: forall (P:Prop)(Q R:expr), R |-- Q -> P -> R |-- !!P && Q.
Proof.
  intros. apply derivable1s_truep_intros. apply derivable1s_coq_prop_r. apply H0. apply H.
Qed.

Lemma derivables_coq_prop_imply: forall (P Q: Prop), (P -> Q) -> !!P |-- !!Q.
Proof.
  intros. apply derivable1s_coq_prop_l. intros. apply H in H0. apply derivable1s_coq_prop_r. apply H0.
Qed. 

Lemma derivables_false_coq_prop: forall (P: Prop) Q, (P -> False) -> !!P |-- Q.
Proof.
  intros. apply derivable1s_coq_prop_l. intros. apply H in H0. contradiction.
Qed. 

Section SLogicEquiv.

Context {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma logic_equiv_coq_prop_andp1: forall P Q, P |-- !!Q -> P --||-- !!Q && P.
Proof.
  intros. rewrite __logic_equiv_derivable1. split.
  -apply derivable1s_truep_intros. apply H. apply derivable1_refl.
  -apply derivable1_andp_elim2.
Qed. 

Lemma logic_equiv_coq_prop_truep: forall (P: Prop), P -> !! P --||-- truep.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1_truep_intros.
  + apply derivable1s_coq_prop_r; auto.
Qed.

Lemma logic_equiv_coq_prop_andp2: forall (P: Prop) Q, P -> !! P && Q --||-- Q.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1_andp_elim2.
  + apply derivable1s_truep_intros.
    - apply derivable1s_coq_prop_r; auto.
    - reflexivity.
Qed.

Lemma logic_equiv_andp_coq_prop: forall (P: Prop) Q, P -> Q && !! P --||-- Q.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1_andp_elim1.
  + apply derivable1s_truep_intros.
    - reflexivity.
    - apply derivable1s_coq_prop_r; auto.
Qed.

Lemma logic_equiv_coq_prop_and: forall P Q: Prop, !! (P /\ Q) --||-- !! P && !! Q.
Proof.
  intros.
  apply __logic_equiv_derivable1; split.
  + apply derivable1s_truep_intros.
    - apply derivable1s_coq_prop_l; intros.
      apply derivable1s_coq_prop_r; tauto.
    - apply derivable1s_coq_prop_l; intros.
      apply derivable1s_coq_prop_r; tauto.
 + apply derivable1s_impp_andp_adjoint.
   apply derivable1s_coq_prop_l; intros.
   apply derivable1s_impp_andp_adjoint.
   rewrite derivable1_andp_comm.
   apply derivable1s_impp_andp_adjoint.
   apply derivable1s_coq_prop_l; intros.
   apply derivable1s_impp_andp_adjoint.
   apply derivable1s_coq_prop_r.
   auto.
Qed.

Lemma logic_equiv_coq_prop_or: forall P Q: Prop, !! (P \/ Q) --||-- !! P || !! Q.
Proof.
  AddAxiomatization.
  intros.
  pose proof provable_coq_prop_or P Q.
  apply __logic_equiv_derivable1.
  split.
  -apply __derivable1_provable.
   pose proof provable_iffp_elim1 (!! (P \/ Q)) (!! P || !! Q).
   pose proof provables_modus_ponens _ _ H0 H;auto.
  -apply __derivable1_provable.
   pose proof provable_iffp_elim2 (!! (P \/ Q)) (!! P || !! Q).
   pose proof provables_modus_ponens _ _ H0 H;auto.
   Qed.

Lemma logic_equiv_coq_prop_imply {coq_prop_impp_D: CoqPropImpDeduction L GammaD1}:
  forall P Q: Prop, !! (P -> Q) --||-- (!! P --> !! Q).
Proof.
  AddAxiomatization.
  intros.
  pose proof provable_coq_prop_imply P Q.
  apply __logic_equiv_derivable1.
  split.
  -apply __derivable1_provable.
   pose proof provable_iffp_elim1 (!! (P -> Q)) (!! P --> !! Q).
   pose proof provables_modus_ponens _ _ H0 H;auto.
  -apply __derivable1_provable.
   pose proof provable_iffp_elim2 (!! (P -> Q)) (!! P --> !! Q).
   pose proof provables_modus_ponens _ _ H0 H;auto.
   Qed.

End SLogicEquiv.

End DeductionRules.
