Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.

Section ModelLanguage.

Context {M: Model}.

#[export] Instance Model_L : Language := Build_Language (model -> Prop).

Section M2P.

#[export] Instance Model2Provable : Provable Model_L :=
  Build_Provable Model_L (fun (x : model -> Prop) => forall m, x m).

Class ProvableDefinition_Model (GammaP : Provable Model_L) : Prop := {
  model2provable : forall (x : @expr Model_L), provable x = (forall m, x m)
}.

Lemma Model2Provable_Normal :
  ProvableDefinition_Model Model2Provable.
Proof. constructor. reflexivity. Qed.

#[export] Instance Model2Derivable1 : Derivable1 Model_L :=
  Build_Derivable1 Model_L (fun (x y : model -> Prop) => forall m, x m -> y m).

Class Derivable1Definition_Model (GammaD1 : Derivable1 Model_L) : Prop := {
  model2deriable1 : forall (x y : @expr Model_L), derivable1 x y = (forall m, x m -> y m)
}.

Lemma Model2Derivable1_Normal : 
  Derivable1Definition_Model Model2Derivable1.
Proof. constructor. reflexivity. Qed.

End M2P.

Section Semantics.

#[export] Instance modelR : KripkeModel.KI.Relation (model) := fun x y => x = y.

#[export] Instance SM : Semantics Model_L M := Build_Semantics Model_L M (fun x => x).

End Semantics.

End ModelLanguage.



