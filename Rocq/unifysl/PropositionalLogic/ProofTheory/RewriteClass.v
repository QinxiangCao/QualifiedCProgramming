Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import  Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import  Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.


Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section RewriteClass1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}.

#[export] Instance provables_andp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) andp.
Proof.
  clear - minAX andpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite __provable_derivable.
  rewrite <- !derivables_impp_theorem.
  apply (derivables_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H.
  apply (derivables_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H0.
  pose proof derivable_assum1 empty_context (x1 && y1).
  pose proof derivables_andp_elim1 _ _ _ H1.
  pose proof derivables_andp_elim2 _ _ _ H1.
  pose proof derivables_modus_ponens _ _ _ H2 H.
  pose proof derivables_modus_ponens _ _ _ H3 H0.
  apply derivables_andp_intros; auto.
Qed.

#[export] Instance provables_orp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) orp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply provables_orp_mono; auto.
Qed.

#[export] Instance provables_negp_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y)) negp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  pose proof provable_negp_derives x1. rewrite H0.
  pose proof provable_derives_negp x2. rewrite <- H1.
  apply provables_impp_proper_impp; auto.
  apply provable_impp_refl.
Qed.

#[export] Instance provable_iffp_rewrite: RewriteRelation (fun x y => |-- x <--> y).
Qed.

#[export] Instance provable_iffp_equiv: Equivalence (fun x y => |-- x <--> y).
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  constructor.
  + hnf; intros.
    rewrite __provable_derivable.
    apply derivables_iffp_intros; apply derivables_impp_theorem; apply derivable_impp_refl.
  + hnf; intros.
    rewrite __provable_derivable in H |- *.
    pose proof derivables_iffp_elim1 _ _ _ H.
    pose proof derivables_iffp_elim2 _ _ _ H.
    apply derivables_iffp_intros; auto.
  + hnf; intros.
    rewrite __provable_derivable in H, H0 |- *.
    pose proof derivables_iffp_elim1 _ _ _ H; apply derivables_impp_theorem in H1.
    pose proof derivables_iffp_elim2 _ _ _ H; apply derivables_impp_theorem in H2.
    pose proof derivables_iffp_elim1 _ _ _ H0; apply derivables_impp_theorem in H3.
    pose proof derivables_iffp_elim2 _ _ _ H0; apply derivables_impp_theorem in H4.
    apply derivables_iffp_intros; apply derivables_impp_theorem.
    - apply (derivables_impp_trans _ _ _ _ H1 H3).
    - apply (derivables_impp_trans _ _ _ _ H4 H2).
Qed.

#[export] Instance provable_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> iff) provable.
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  intros.
  hnf; intros.
  rewrite __provable_derivable in H.
  rewrite __provable_derivable.
  rewrite __provable_derivable.
  pose proof derivables_iffp_elim1 _ _ _ H; apply derivables_impp_theorem in H0.
  pose proof derivables_iffp_elim2 _ _ _ H; apply derivables_impp_theorem in H1.
  split; intro;
  eapply derivables_modus_ponens; eauto.
Qed.

#[export] Instance provables_impp_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) impp.
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite __provable_derivable in H.
  rewrite __provable_derivable in H0.
  rewrite __provable_derivable.
  pose proof derivables_iffp_elim1 _ _ _ H; apply derivables_impp_theorem in H1.
  pose proof derivables_iffp_elim2 _ _ _ H; apply derivables_impp_theorem in H2.
  pose proof derivables_iffp_elim1 _ _ _ H0; apply derivables_impp_theorem in H3.
  pose proof derivables_iffp_elim2 _ _ _ H0; apply derivables_impp_theorem in H4.
  rewrite <- __provable_derivable in H1.
  rewrite <- __provable_derivable in H2.
  rewrite <- __provable_derivable in H3.
  rewrite <- __provable_derivable in H4.
  apply derivables_iffp_intros; apply derivables_impp_theorem; rewrite <- __provable_derivable.
  + apply provables_impp_proper_impp; auto.
  + apply provables_impp_proper_impp; auto.
Qed.

#[export] Instance provables_andp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) andp.
Proof.
  clear - minAX iffpAX andpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite __provable_derivable in H.
  rewrite __provable_derivable in H0.
  rewrite __provable_derivable.
  pose proof derivables_iffp_elim1 _ _ _ H; apply derivables_impp_theorem in H1.
  pose proof derivables_iffp_elim2 _ _ _ H; apply derivables_impp_theorem in H2.
  pose proof derivables_iffp_elim1 _ _ _ H0; apply derivables_impp_theorem in H3.
  pose proof derivables_iffp_elim2 _ _ _ H0; apply derivables_impp_theorem in H4.
  rewrite <- __provable_derivable in H1.
  rewrite <- __provable_derivable in H2.
  rewrite <- __provable_derivable in H3.
  rewrite <- __provable_derivable in H4.
  apply derivables_iffp_intros; apply derivables_impp_theorem; rewrite <- __provable_derivable.
  + apply provables_andp_proper_impp; auto.
  + apply provables_andp_proper_impp; auto.
Qed.

#[export] Instance provables_orp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) orp.
Proof.
  clear - minAX iffpAX orpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite __provable_derivable in H.
  rewrite __provable_derivable in H0.
  rewrite __provable_derivable.
  pose proof derivables_iffp_elim1 _ _ _ H; apply derivables_impp_theorem in H1.
  pose proof derivables_iffp_elim2 _ _ _ H; apply derivables_impp_theorem in H2.
  pose proof derivables_iffp_elim1 _ _ _ H0; apply derivables_impp_theorem in H3.
  pose proof derivables_iffp_elim2 _ _ _ H0; apply derivables_impp_theorem in H4.
  rewrite <- __provable_derivable in H1.
  rewrite <- __provable_derivable in H2.
  rewrite <- __provable_derivable in H3.
  rewrite <- __provable_derivable in H4.
  apply derivables_iffp_intros; apply derivables_impp_theorem; rewrite <- __provable_derivable.
  + apply provables_orp_proper_impp; auto.
  + apply provables_orp_proper_impp; auto.
Qed.

#[export] Instance provables_iffp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) iffp.
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite __provable_derivable.
  apply derivables_iffp_intros; apply derivables_iffp_intros; rewrite !derivables_impp_theorem; rewrite <- __provable_derivable.
  +rewrite <- H. rewrite <- H0. apply provable_iffp_elim1.
  +rewrite <- H. rewrite <- H0. apply provable_iffp_elim2.
  +rewrite -> H. rewrite -> H0. apply provable_iffp_elim1.
  +rewrite -> H. rewrite -> H0. apply provable_iffp_elim2.
Qed.

#[export] Instance provables_negp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) negp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  pose proof provable_negp x1. rewrite H0.
  pose proof provable_negp x2. rewrite H1.
  apply provables_impp_proper_iffp; auto.
  apply provable_iffp_refl.
Qed.

End RewriteClass1.

Section RewriteClass2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaPD: ProvableFromDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}.

#[export] Instance derivables_proper_iffp : Proper (eq ==> (fun x y => |-- x <--> y) ==> iff) derivable.
Proof.
  hnf; intros Phi Phi' ?; subst Phi'.
  hnf; intros x1 x2 ?.
  apply (derivables_weaken0 Phi) in H.
  pose proof derivables_iffp_elim1 _ _ _ H; rewrite derivables_impp_theorem in H0.
  pose proof derivables_iffp_elim2 _ _ _ H; rewrite derivables_impp_theorem in H1.
  split; intro;
  eapply derivables_modus_ponens; eauto.
Qed.

End RewriteClass2.

Section RewriteClass3.

Context {L: Language}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}.

Section impp.

Context {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}.

#[export] Instance derivable1s_impp_proper:
  Proper (derivable1 --> derivable1 ==> derivable1) impp.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_impp_mono; auto.
Qed.

End impp.

Section andp.

Context {andpL: AndLanguage L}
        {andpD: AndDeduction L GammaD1}.

#[export] Instance derivable1s_andp_proper: Proper (derivable1 ==> derivable1 ==> derivable1) andp.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1s_truep_intros.
  -pose proof derivable1_andp_elim1 x x0.
   pose proof derivable1_trans _ _ _ H1 H. auto.
  -pose proof derivable1_andp_elim2 x x0.
   pose proof derivable1_trans _ _ _ H1 H0. auto.
  Qed.

End andp.

Section orp.

Context {orpL: OrLanguage L}
        {orpD: OrDeduction L GammaD1}.

#[export] Instance derivable1s_orp_proper: Proper (derivable1 ==> derivable1 ==> derivable1) orp.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_orp_elim.
  -pose proof derivable1_orp_intros1 y y0.
   pose proof derivable1_trans _ _ _ H H1;auto.
  -pose proof derivable1_orp_intros2 y y0.
   pose proof derivable1_trans _ _ _ H0 H1;auto.
Qed.

End orp.

Section negp.

Context {negpL: NegLanguage L}
        {inegpD: IntuitionisticNegDeduction L GammaD1}.

#[export] Instance derivable1s_negp_proper: Proper (derivable1 --> derivable1) negp.
Proof.
  hnf;intros.
  unfold Basics.flip in H.
  apply derivable1s_contrapositivePP.
  auto.
Qed.

End negp.

End RewriteClass3.

Section RewriteClass4.

Context {L: Language}
        {GammaE: LogicEquiv L}
        {bE: BasicLogicEquiv L GammaE}.

Section impp.

Context {minL: MinimumLanguage L}
        {imppE: ImpLogicEquiv L GammaE}.

#[export] Instance logic_equiv_impp_proper:
  Proper (logic_equiv ==> logic_equiv ==> logic_equiv) impp.
Proof.
  hnf;intros.
  hnf;intros.
  unfold Basics.flip in H.
  pose proof logic_equiv_impp _ _ _ _ H H0.
  auto.
Qed.

End impp.

Section andp.

Context {andpL: AndLanguage L}
        {andpE: AndLogicEquiv L GammaE}.

#[export] Instance logic_equiv_andp_proper: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) andp.
Proof.
  hnf;intros.
  hnf;intros.
  apply logic_equiv_andp_congr;[auto|auto].
  Qed.

End andp.

Section orp.

Context {orpL: OrLanguage L}
        {orpE: OrLogicEquiv L GammaE}.

#[export] Instance logic_equiv_orp_proper: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) orp.
Proof.
  hnf;intros.
  hnf;intros.
  apply logic_equiv_orp_congr;[auto|auto].
  Qed.

End orp.

Section negp.

Context {negpL: NegLanguage L}
        {negpE: NegLogicEquiv L GammaE}.

#[export] Instance logic_equiv_negp_proper: Proper (logic_equiv  ==> logic_equiv ) negp.
Proof.
  hnf;intros.
  apply logic_equiv_negp_intros;auto.
  Qed.

End negp.

Section iffp.

Context {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {imppL: ImpLogicEquiv L GammaE}
        {andpE: AndLogicEquiv L GammaE}
        {iffpE: IffLogicEquiv L GammaE}.

#[export] Instance logic_equiv_iffp_proper: Proper (logic_equiv  ==> logic_equiv ==> logic_equiv) iffp.
Proof.
  hnf;intros.
  hnf;intros.
  pose proof logic_equiv_provable_iffp_intros x x0.
  pose proof logic_equiv_provable_iffp_intros y y0.
  apply logic_equiv_trans with ((x --> x0) && (x0 --> x)).
  apply logic_equiv_symm;auto.
  apply logic_equiv_symm.
  apply logic_equiv_trans with ((y --> y0) && (y0 --> y)).
  apply logic_equiv_symm;auto.
  apply logic_equiv_andp_congr.
  -apply logic_equiv_impp.
   apply logic_equiv_symm;auto.
   apply logic_equiv_symm;auto.
  -apply logic_equiv_impp.
   apply logic_equiv_symm;auto.
   apply logic_equiv_symm;auto.
  Qed.

End iffp.

End RewriteClass4.

#[export] Existing Instances provables_andp_proper_impp provables_orp_proper_impp provables_negp_proper_impp
                   provable_iffp_rewrite provable_iffp_equiv
                   provable_proper_iffp derivables_proper_iffp
                   provables_impp_proper_iffp provables_andp_proper_iffp provables_orp_proper_iffp
                   provables_iffp_proper_iffp provables_negp_proper_iffp
                   logic_equiv_impp_proper
                   logic_equiv_andp_proper logic_equiv_orp_proper
                   logic_equiv_negp_proper logic_equiv_iffp_proper
                   derivable1s_andp_proper derivable1s_orp_proper
                   derivable1s_negp_proper derivable1s_impp_proper.

