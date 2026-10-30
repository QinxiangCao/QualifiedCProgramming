Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.

Section M2IFF.
Context {M : Model}.

#[export] Instance Model2Iffp : IffLanguage Model_L :=
  Build_IffLanguage Model_L (fun x y => fun m => (x m <-> y m)).

Class IffpDefinition_Model (iffpL : IffLanguage Model_L) : Prop := {
  model2iffp : forall (x y : @expr Model_L), iffp x y = (fun m  => (x m <-> y m))
}.

Lemma Model2Iffp_Normal :
  IffpDefinition_Model Model2Iffp.
Proof. constructor. reflexivity. Qed.

End M2IFF.

Section M2AND.
Context {M : Model}.

#[export] Instance Model2Andp : AndLanguage Model_L :=
  Build_AndLanguage Model_L (fun x y => fun m => (x m /\ y m)).

Class AndpDefinition_Model (andpL : AndLanguage Model_L) : Prop := {
  model2andp : forall (x y : @expr Model_L), andp x y = (fun m => (x m /\ y m))
}.

Lemma Model2Andp_Normal :
  AndpDefinition_Model Model2Andp.
Proof. constructor. reflexivity. Qed.

End M2AND.

Section M2OR.
Context {M : Model}.

#[export] Instance Model2Orp : OrLanguage Model_L :=
  Build_OrLanguage Model_L (fun x y => fun m => (x m \/ y m)).

Class OrpDefinition_Model (orpL : OrLanguage Model_L) : Prop := {
  model2orp : forall (x y : @expr Model_L), orp x y = (fun m => x m \/ y m)
}.

Lemma Model2Orp_Normal: OrpDefinition_Model Model2Orp.
Proof. constructor. reflexivity. Qed.

End M2OR.

Section M2TRUE.
Context {M : Model}.

#[export] Instance Model2Truep : TrueLanguage Model_L :=
  Build_TrueLanguage Model_L (fun (m : model) => True).

Class TrueDefinition_Model (truepL : TrueLanguage Model_L) : Prop := {
  model2truep : forall (m : model), truep m = True
}.

Lemma Model2Truep_Normal : TrueDefinition_Model Model2Truep.
Proof. constructor. reflexivity. Qed.

End M2TRUE.

Section M2FALSE.
Context {M : Model}.

#[export] Instance Model2Falsep : FalseLanguage Model_L :=
  Build_FalseLanguage Model_L (fun _ => False).

Class FalsepDefinition_Model (falsepL : FalseLanguage Model_L) : Prop := {
  model2falsep : falsep = (fun _ : model => False)
}.

Lemma Model2Falsep_Normal :
  FalsepDefinition_Model Model2Falsep.
Proof. constructor. reflexivity. Qed.

End M2FALSE.

Section ImpAdjD1FromModel.

Context {M : Model}.

Lemma Model2ImpAdjoint : 
  @ImpAndAdjointDeduction Model_L Model2Impp Model2Andp Model2Derivable1.
Proof. 
  constructor.
  unfold derivable1; unfold Model2Derivable1.
  unfold Syntax.impp; unfold Model2Impp.
  unfold andp; unfold Model2Andp.
  simpl. 
  intros; split; intros; apply H; tauto.
Qed.

End ImpAdjD1FromModel.

Section MinD1FromModel.

Context {M: Model}.

Lemma Model2MinD1 : 
  @MinimumDeduction Model_L Model2Impp Model2Derivable1 .
Proof. 
  constructor; unfold derivable1; 
  unfold model2deriable1; unfold Model2Impp; 
  simpl; intros.
  -apply H. apply H1. apply H0. apply H1.
  -apply H. intros. apply H1.
  -apply H0.
  -apply H. 
  -apply H. apply H1. apply H0. apply H1.
Qed.

  
End MinD1FromModel.



Section AndD1FromModel.

Context {M : Model}.

Lemma Model2AndDeduction :
  @AndDeduction Model_L Model2Andp Model2Derivable1.
Proof. 
  constructor;
  unfold derivable1; unfold Model2Derivable1;
  unfold andp; unfold Model2Andp; simpl; try tauto.
  intros. split; [apply H | apply H0]; tauto.
Qed.

End AndD1FromModel.

Section OrD1FromModel.

Context {M : Model}.

Lemma Model2OrDeduction :
  @OrDeduction Model_L Model2Orp Model2Derivable1.
Proof. 
  constructor;
  unfold derivable1; unfold Model2Derivable1; unfold Model2Orp;
  simpl; try tauto.
  intros. destruct H1; [apply H | apply H0]; tauto.
Qed.

End OrD1FromModel.

Section IffD1FromModel.

Context {M : Model}.
    
Lemma Model2IffDeduction
    {minL : MinimumLanguage Model_L}
    {imppDef_model : ImppDefinition_Model minL}
    {iffL : IffLanguage Model_L}
    {iffDef_model : IffpDefinition_Model iffL}
    {GammaD1 : Derivable1 Model_L}
    {GammaD1_model : Derivable1Definition_Model GammaD1}:
  IffDeduction Model_L GammaD1.
Proof. 
  constructor; intros;
  rewrite !model2deriable1;
  rewrite !model2iffp;
  rewrite !model2impp;
  simpl; intros; tauto.
Qed.

End IffD1FromModel.

Section TrueD1FromModel.

Context {M : Model}.

Lemma Model2TrueDeduction :
  @TrueDeduction Model_L Model2Truep Model2Derivable1.
Proof. 
  constructor.
  unfold derivable1, Model2Derivable1, truep, Model2Truep.
  auto.
Qed. 

End TrueD1FromModel.

Section BasicDeductionFromModel.

Context {M : Model}.

Lemma Model2BasicDeduction :
  BasicDeduction Model_L Model2Derivable1.
Proof.
  constructor; unfold derivable1, Model2Derivable1.
  + intros. tauto.
  + intros. apply (H0 m (H m H1)).
Qed.

End BasicDeductionFromModel.

Section MinimumDeductionFromModel.
  
Context {M : Model}.

Lemma Model2MinumumDeduction': 
  @MinimumDeduction Model_L Model2Impp Model2Derivable1.
Proof. 
  constructor; intros; unfold derivable1, Model2Derivable1, Model2Impp, impp in *;
  simpl in *.
  -intros. apply H. apply H1. apply H0. apply H1.
  -intros. apply H. intros. apply H1.
  -intros. apply H0.
  -intros. apply H. 
  -intros. apply H. apply H1. apply H0. apply H1.
Qed.
  
End MinimumDeductionFromModel.
