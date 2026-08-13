Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.

Section M2COQPROP.
Context {M : Model}.


Definition Model2CoqProp : CoqPropLanguage Model_L :=
  Build_CoqPropLanguage Model_L (fun (P : Prop) (m : model) => P).

Class CoqPropDefinition_Model (coq_prop_L : CoqPropLanguage Model_L) : Prop := {
  model2coqprop : forall (P : Prop) (m : model), coq_prop P m = P
}.

Lemma Model2CoqProp_Normal : CoqPropDefinition_Model Model2CoqProp.
Proof. constructor. reflexivity. Qed.

End M2COQPROP.

Section CoqPropD1FromModel.

Context {M : Model}.

Lemma Model2CoqPropDeduction :
  @CoqPropDeduction Model_L Model2Truep Model2CoqProp Model2Derivable1.
Proof.
  constructor; 
  unfold coq_prop, Model2CoqProp, truep, Model2Truep, derivable1, Model2Derivable1; intros.
  + apply H. 
  + apply (H H0 m I).
Qed. 
  
End CoqPropD1FromModel.


