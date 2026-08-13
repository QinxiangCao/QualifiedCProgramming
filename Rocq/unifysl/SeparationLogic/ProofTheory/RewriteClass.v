Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section RewriteClass1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}.

#[export] Instance provables_sepcon_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply SeparationLogic.provable_sepcon_mono; auto.
Qed.

#[export] Instance provables_wand_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  apply provables_wand_mono; auto.
Qed.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}.

#[export] Instance provables_sepcon_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply provables_iffp_intros.
  + apply SeparationLogic.provable_sepcon_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
  + apply SeparationLogic.provable_sepcon_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
Qed.

#[export] Instance provables_wand_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply provables_iffp_intros.
  + apply provables_wand_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
  + apply provables_wand_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
Qed.

End RewriteClass1.

Section RewriteClass2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD: Derivable1 L}
        {sepconD: SepconDeduction L GammaD}.

#[export] Instance derivable1s_sepcon_proper: Proper (derivable1 ==> derivable1 ==> derivable1) sepcon.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_sepcon_mono;auto.
  Qed.

Context {wandL: WandLanguage L}
        {wandD: WandDeduction L GammaD}
        {bD: BasicDeduction L GammaD}.

#[export] Instance derivable1s_wand_proper: Proper (derivable1 --> derivable1 ==> derivable1) wand.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_wand_mono;auto.
  Qed.

End RewriteClass2.

Section RewriteClass3.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {sepconD: SepconDeduction L GammaD1}.

#[export] Instance logic_equiv_sepcon_proper: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon.
Proof.
  hnf;intros.
  hnf;intros.
  apply __logic_equiv_derivable1 in H;
  apply __logic_equiv_derivable1 in H0.
  apply __logic_equiv_derivable1; split;
  apply derivable1_sepcon_mono; tauto.
  Qed.

Context {wandL: WandLanguage L}
        {wandD: WandDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

#[export] Instance logic_equiv_wand_proper: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) wand.
Proof.
  hnf;intros.
  hnf;intros.
  apply __logic_equiv_derivable1 in H;
  apply __logic_equiv_derivable1 in H0.
  apply __logic_equiv_derivable1; split;
  apply derivable1_wand_mono; tauto.
  Qed.
End RewriteClass3.

#[export] Existing Instances provables_sepcon_proper_impp
                             provables_wand_proper_impp
                             provables_sepcon_proper_iffp
                             provables_wand_proper_iffp
                             derivable1s_sepcon_proper
                             derivable1s_wand_proper
                             logic_equiv_sepcon_proper
                             logic_equiv_wand_proper.

