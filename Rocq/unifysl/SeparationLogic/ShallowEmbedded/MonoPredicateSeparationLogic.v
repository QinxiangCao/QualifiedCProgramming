Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.EmpSemantics.
Require Import Logic.SeparationLogic.Sound.Sound_Flat.

#[export] Instance MonoPred_sepconL (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: SepconLanguage (MonoPred_L A) :=
  Build_SepconLanguage (MonoPred_L A) WeakSemanticsMono.sepcon.

#[export] Instance MonoPred_wandL (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: WandLanguage (MonoPred_L A) :=
  Build_WandLanguage (MonoPred_L A) WeakSemanticsMono.wand.

#[export] Instance MonoPred_empL (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {UJORel: UnitJoinOrderRelation A}: EmpLanguage (MonoPred_L A) := 
  Build_EmpLanguage (MonoPred_L A) EmpSemanticsMono.emp.

#[export] Instance MonoPred_fsepconSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: @FlatSemantics.SepconSemantics (MonoPred_L A) (MonoPred_sepconL A) (Build_Model A) (unit_kMD _) tt R J (MonoPred_SM A).
Proof.
  hnf; intros; apply Same_set_refl.
Qed.

#[export] Instance MonoPred_fwandSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: @FlatSemantics.WandSemantics (MonoPred_L A) (MonoPred_wandL A) (Build_Model A) (unit_kMD _) tt R J (MonoPred_SM A).
Proof.
  hnf; intros; apply Same_set_refl.
Qed.

#[export] Instance MonoPred_empSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {UJORel: UnitJoinOrderRelation A}: @FlatSemantics.EmpSemantics (MonoPred_L A) (MonoPred_empL A) (Build_Model A) (unit_kMD _) tt U (MonoPred_SM A).
Proof.
  apply Same_set_refl.
Qed.

#[export] Instance MonoPred_sepconAX_weak (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: SepconAxiomatization_weak (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_sepcon_comm (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_fsepconSM A) x y).
  + intros x y.
    exact (@sound_provable_sepcon_assoc1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_fsepconSM A) x y).
Qed.

#[export] Instance MonoPred_wandAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: WandAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x y z.
  exact (@sound_provables_wand_sepcon_adjoint (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt  R po_R J (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_fsepconSM A) (MonoPred_fwandSM A) x y z).
Qed.

#[export] Instance MonoPred_sepconAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: SepconAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  eapply @SepconAxiomatizationWeak2SepconAxiomatization;
  try typeclasses eauto.
  eapply @Adj2SepconMono;
  try typeclasses eauto.
Qed.

#[export] Instance MonoPred_empAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {UJORel: UnitJoinOrderRelation A}: EmpAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x.
    exact (@sound_provable_sepcon_emp_derives (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J U (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_fsepconSM A) _ (MonoPred_empSM A) _ x).
  + intros x.
    exact (@sound_provable_derives_sepcon_emp (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J U (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_fsepconSM A) _ (MonoPred_empSM A) _ x).
Qed.

#[export] Instance MonoPred_gcsGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {U: Unit A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {incrSA: IncreasingSeparationAlgebra A}: GarbageCollectSeparationLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  intros.
  constructor.
  intros x y.
  exact (@sound_provable_sepcon_elim1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_fsepconSM A) incrSA x y).
Qed.
