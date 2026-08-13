Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import CoqPropInLogicNotation.
Section SLFromDeduction2SLFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconL: SepconLanguage L}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}.

Lemma SepconDeduction2SepconAxiomatization_sepconAX
      {sepconD: SepconDeduction L GammaD1}:
  SepconAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply __derivable1_provable. apply derivable1_sepcon_comm.
  -intros. apply __derivable1_provable. apply derivable1_sepcon_assoc1.
  -intros. apply __derivable1_provable. apply __derivable1_provable in H.
   apply __derivable1_provable in H0. apply derivable1_sepcon_mono;auto.
Qed.

Context {orpL: OrLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {falsepL: FalseLanguage L}.

Lemma Deduction2Axiomatization_sepcon_orp_AX
      {sepcon_orp_D: SepconOrDeduction L GammaD1}:
  SepconOrAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply __derivable1_provable. apply derivable1_orp_sepcon_l.
Qed.

Lemma Deduction2Axiomatization_sepcon_falsep_AX
      {sepcon_falsep_D: SepconFalseDeduction L GammaD1}:
  SepconFalseAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply __derivable1_provable. apply derivable1_falsep_sepcon_l.
  Qed.

Lemma Deduction2Axiomatization_esGamma
      {esD: ExtSeparationLogicDeduction L GammaD1}:
  ExtSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply __derivable1_provable. apply derivable1_sepcon_truep_r.
  Qed.

Lemma Deduction2Axiomatization_gcsAX
      {gcs: GarbageCollectSeparationLogicDeduction L GammaD1}:
  GarbageCollectSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply __derivable1_provable. apply derivable1_sepcon_elim1.
  Qed.

End SLFromDeduction2SLFromAxiomatization1.

#[export] Instance reg_Deduction2Axiomatization_sepcon_orpAX:
  RegisterClass D12P_reg (fun sepcon_orp_AX:unit => @Deduction2Axiomatization_sepcon_orp_AX) 10.
Qed.

#[export] Instance reg_Deduction2Axiomatization_sepcon_falsep_AX:
  RegisterClass D12P_reg (fun sepcon_false_AX:unit => @Deduction2Axiomatization_sepcon_falsep_AX) 11.
Qed.

#[export] Instance reg_Deduction2Axiomatization_gcsAX:
  RegisterClass D12P_reg (fun gcsGamma:unit => @Deduction2Axiomatization_gcsAX) 12.
Qed.

(*Rules from SeparationLogic*)

Section SLFromDeduction2SLFromAxiomatization2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}.

Lemma Deduction2Axiomatization_empAX
      {empD: EmpDeduction L GammaD1}:
  EmpAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply __derivable1_provable. apply derivable1_sepcon_emp_l.
  -intros. apply __derivable1_provable. apply derivable1_sepcon_emp_r.
  Qed.

Section SLFromDeduction2SLFromAxiomatization3.

Context {orpL: OrLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {falsepL: FalseLanguage L}.

Lemma Deduction2Axiomatization_desGamma
      {desD: DupEmpSeparationLogicDeduction L GammaD1}:
  DupEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply __derivable1_provable. apply derivable1_emp_dup.
  Qed.

Lemma Deduction2Axiomatization_nssGamma
      {nssD: NonsplitEmpSeparationLogicDeduction L GammaD1}:
  NonsplitEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply __derivable1_provable. apply derivable1_sepcon_truep_andp_emp_l.
  Qed.

End SLFromDeduction2SLFromAxiomatization3.

End SLFromDeduction2SLFromAxiomatization2.

#[export] Instance reg_Deduction2Axiomatization_nssGamma:
  RegisterClass D12P_reg (fun nssGamma:unit => @Deduction2Axiomatization_nssGamma) 13.
Qed.

#[export] Instance reg_Deduction2Axiomatization_empAX:
  RegisterClass D12P_reg (fun empAx:unit => @Deduction2Axiomatization_empAX) 14.
Qed.

Section SLFromDeduction2SLFromAxiomatization4.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}.

Lemma WandDeduction2WandAxiomatization_wandAX
      {wandD: WandDeduction L GammaD1}:
  WandAxiomatization L GammaP.
Proof.
  constructor.
  split.
  -intros. apply __derivable1_provable. apply __derivable1_provable in H.
   apply derivable1s_wand_sepcon_adjoint;auto.
  - intros. apply __derivable1_provable. apply __derivable1_provable in H.
   apply derivable1s_wand_sepcon_adjoint;auto.
   Qed.

End SLFromDeduction2SLFromAxiomatization4.

#[export] Instance reg_WandDeduction1WandAxiomatization:
  RegisterClass D12P_reg (fun wandAX: unit => @WandDeduction2WandAxiomatization_wandAX) 15.
Qed.

#[export] Instance reg_SepconDeduction2SepconAxiomatization:
  RegisterClass D12P_reg (fun SAx:unit => @SepconDeduction2SepconAxiomatization_sepconAX) 16.
Qed.

(*Rules from TheoryOfSeparationAxioms*)

Class SepconMonoDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __provable_sepcon_mono: forall x1 x2 y1 y2 : expr, x1 |-- x2 -> y1 |-- y2 -> x1 * y1 |-- x2 * y2
}.

Class SepconDeduction_weak
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __provable_sepcon_comm_impp: forall x y, x * y |-- y * x;
  __provable_sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
}.

Class SepconLogicEquiv_weak_iffp
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaE: LogicEquiv L) := {
  logic_equiv_sepcon_comm: forall x y, x * y --||-- y * x;
  logic_equiv_sepcon_assoc: forall x y z, x * (y * z) --||-- (x * y) * z;
}.

Class EmpLogicEquiv_iffp
        (L: Language)
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaE: LogicEquiv L) := {
  logic_equiv_sepcon_emp: forall x, x * emp --||-- x
}.

Lemma SepconDeductionWeak2SepconDeduction
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {GammaD1: Derivable1 L}
      {sepconAX: SepconDeduction_weak L GammaD1}
      {provable_sepcon_mono_AX: SepconMonoDeduction L GammaD1}:
  SepconDeduction L GammaD1.
Proof.
  constructor.
  - apply __provable_sepcon_comm_impp.
  - apply __provable_sepcon_assoc1.
  - apply __provable_sepcon_mono.
Qed.

Section SepconDeduction_weak2SepconAxiomatization_weak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconDw: SepconDeduction_weak L GammaD1}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}.

Lemma SepconDeduction_weak2SepconAxiomatization_weak: SepconAxiomatization_weak L GammaP.
Proof.
  constructor.
  -intros.
   apply __derivable1_provable.
   apply __provable_sepcon_comm_impp.
  -intros.
   apply __derivable1_provable.
   apply __provable_sepcon_assoc1.
   Qed.

End SepconDeduction_weak2SepconAxiomatization_weak.

#[export] Instance reg_SepconDeduction_weak2SepconAxiomatization_weak:
  RegisterClass D12P_reg (fun sepconAX:unit => @SepconDeduction_weak2SepconAxiomatization_weak) 17.
Qed.

Section SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableFromDerivable1 L GammaP GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  SepconAxiomatization_weak_iffp L GammaP.
Proof.
  pose proof Deduction2Axiomatization_minAX as minAX.
  pose proof Deduction2Axiomatization_iffpAX as iffpAX.
  constructor.
  - intros.
    pose proof logic_equiv_sepcon_comm x y.
    apply __logic_equiv_derivable1 in H; destruct H.
    rewrite __derivable1_provable in H, H0.
    apply provables_iffp_intros; auto.
  - intros.
    pose proof logic_equiv_sepcon_assoc x y z.
    apply __logic_equiv_derivable1 in H; destruct H.
    rewrite __derivable1_provable in H, H0.
    apply provables_iffp_intros; auto.
Qed.

End SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

#[export] Instance reg_SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  RegisterClass D12P_reg (fun sepcon_weak_iffp:unit => @SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp) 18.
Qed.

Section EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableFromDerivable1 L GammaP GammaD1}
        {empE: EmpLogicEquiv_iffp L GammaE}
        {iffpD: IffDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
EmpAxiomatization_iffp L GammaP.
Proof.
  pose proof Deduction2Axiomatization_minAX as minAX.
  pose proof Deduction2Axiomatization_iffpAX as iffpAX.
  constructor.
  intros.
  pose proof logic_equiv_sepcon_emp x.
  apply __logic_equiv_derivable1 in H; destruct H.
  rewrite __derivable1_provable in H, H0.
  apply provables_iffp_intros; auto.
Qed.

End EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

#[export] Instance reg_EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
  RegisterClass D12P_reg (fun empAX_iffp:unit => @EmpLogicEquiv_iffp2EmpAxiomatization_iffp) 19.
Qed.

Section FromSepconDeductionWeakToSepcon.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {sepconD: SepconDeduction_weak L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma Adj2SepconMono: SepconMonoDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconMono.
  constructor; 
  pose proof Deduction2Axiomatization_GammaD1P; 
  pose proof Deduction2Axiomatization_minAX; 
  intros; rewrite __derivable1_provable in *. 
  apply H. apply H2. apply H3. 
Qed.

End FromSepconDeductionWeakToSepcon.

Section FromSepconWeakIffToSepconDeductionWeak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma SepconLogicEquivWeakIff2SepconDeductionWeak:
  SepconDeduction_weak L GammaD1.
Proof.
  AddAxiomatization.
  pose proof SepconAxiomatizationWeakIff2SepconAxiomatizationWeak.
  constructor; 
  pose proof Deduction2Axiomatization_GammaD1P; 
  pose proof Deduction2Axiomatization_minAX; 
  intros; rewrite __derivable1_provable in *;
  apply H. 
Qed.

End FromSepconWeakIffToSepconDeductionWeak.

Section FromAdjToSepconOrDeductionPropositionalCombination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma Adj2SepconOrD {orpL: OrLanguage L} {orpD: OrDeduction L GammaD1}: 
  SepconOrDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconOr.
  constructor.
  intros.
  apply __derivable1_provable.
  apply H.
Qed.

Lemma Adj2SepconFalse {falsepL: FalseLanguage L} {falsepD: FalseDeduction L GammaD1}: SepconFalseDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconFalse.
  constructor.
  intros.
  apply __derivable1_provable.
  apply H.
Qed.

End FromAdjToSepconOrDeductionPropositionalCombination.

Section FromEmpEIffToEmpD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {empD: EmpLogicEquiv_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma EmpLogicEquivIff2EmpDeduction:
  EmpDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof EmpAxiomatizationIff2EmpAxiomatization.
  constructor; intros; apply __derivable1_provable; apply H.
Qed.

End FromEmpEIffToEmpD.

Section Deduction2LogicEquiv.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {bD: BasicDeduction L GammaD1}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {sepconD: SepconDeduction L GammaD1}
        {empD: EmpDeduction L GammaD1}.

Lemma Deduction2LogicEquiv_sepconE:
  SepconLogicEquiv_weak_iffp L GammaE.
Proof. 
  constructor; intros; rewrite __logic_equiv_derivable1; split.
  -apply derivable1_sepcon_comm.
  -apply derivable1_sepcon_comm.
  -apply derivable1_sepcon_assoc1.
  -pose proof derivable1_sepcon_comm (x*y) z. 
  pose proof derivable1_sepcon_assoc1 z x y. 
  pose proof derivable1_trans _ _ _ H H0. 
  pose proof derivable1_sepcon_comm (z*x) y. 
  pose proof derivable1_trans _ _ _ H1 H2. 
  pose proof derivable1_sepcon_assoc1 y z x. 
  pose proof derivable1_trans _ _ _ H3 H4. 
  eapply derivable1_trans; eauto. apply derivable1_sepcon_comm.
Qed.

Lemma Deduction2LogicEquiv_empE:
  EmpLogicEquiv_iffp L GammaE.
Proof. 
  constructor; intros; rewrite __logic_equiv_derivable1;  split.
  -apply derivable1_sepcon_emp_l.
  -apply derivable1_sepcon_emp_r.
Qed. 

Lemma logic_equiv_sepcon_swap
  {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
 : forall x y z, x * (y * z)  --||--  y * (x * z).
Proof.
  intros.
  rewrite __logic_equiv_derivable1; split;
  rewrite derivable1_sepcon_assoc1; erewrite derivable1_sepcon_comm; 
  rewrite derivable1_sepcon_assoc1; erewrite derivable1_sepcon_comm; 
  apply derivable1_sepcon_mono. apply derivable1_refl; apply derivable1_sepcon_comm.
  apply derivable1_sepcon_comm. apply derivable1_refl. apply derivable1_sepcon_comm.
Qed.



End Deduction2LogicEquiv.

