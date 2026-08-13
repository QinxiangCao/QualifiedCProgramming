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

Section M2EX.
Context {M : Model}.

#[export] Instance Model_L : Language := Build_Language (model -> Prop).

Class ExpDefinition_Model (expL : ShallowExistsLanguage Model_L) := {
  model2exp : forall {A : Type} (x : A -> expr),
    (@exp Model_L expL) _ x = fun m => exists a, (x a) m
}.

Definition Model2Exp : ShallowExistsLanguage Model_L :=
  Build_ShallowExistsLanguage Model_L 
    (fun A x => fun m => exists a, (x a) m).

Definition Model2Exp_Normal : 
  ExpDefinition_Model Model2Exp.
Proof. constructor. reflexivity. Qed.

End M2EX.

Section ExpD1FromModel.

Context {M : Model}.

#[export] Instance expL : ShallowExistsLanguage Model_L :=
  Build_ShallowExistsLanguage Model_L 
    (fun A x => fun m => exists a, (x a) m).
#[export] Instance Model2Derivable1 : Derivable1 Model_L :=
  Build_Derivable1 Model_L 
    (fun (x y : model -> Prop) => forall m, x m -> y m).

Lemma Model2ExpDeduction :
  ShallowExistsDeduction Model_L Model2Derivable1.
Proof.
  constructor; unfold derivable1; unfold Model2Derivable1;
  unfold exp; unfold expL; intros.
  + exists x. apply (H m H0).
  + destruct H0 as [a H0]. apply (H a m H0).
Qed.

End ExpD1FromModel.