Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.ShallowQuantifierLogic.ProofTheory.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section M2ALL.
Context {M : Model}.

#[export] Instance Model_L : Language := Build_Language (model -> Prop).

Class AllpDefinition_Model (allL : ShallowForallLanguage Model_L) := {
  model2all : forall {A : Type} (x : A -> expr),
    (@allp Model_L allL) _ x = fun m => forall a, (x a) m
}.

Definition Model2All : ShallowForallLanguage Model_L :=
  Build_ShallowForallLanguage Model_L 
    (fun A x => fun m => forall a, (x a) m).

Definition Model2Allp_Normal : 
  AllpDefinition_Model Model2All.
Proof. constructor. reflexivity. Qed.

End M2ALL.

Section ALLD1FromModel.

Context {M : Model}.

#[export] Instance allL : ShallowForallLanguage Model_L :=
  Build_ShallowForallLanguage Model_L 
    (fun A x => fun m => forall a, (x a) m).
#[export] Instance Model2Derivable1 : Derivable1 Model_L :=
  Build_Derivable1 Model_L 
    (fun (x y : model -> Prop) => forall m, x m -> y m).

Lemma Model2AllDeduction :
  ShallowForallDeduction Model_L Model2Derivable1.
Proof.
  constructor; unfold derivable1; unfold Model2Derivable1;
  unfold allp; unfold allL; intros.
  + apply (H a m H0).
  + apply H. apply H0.
Qed.

End ALLD1FromModel.