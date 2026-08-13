Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.

Section M2IMP.
Context {M : Model}.

Definition Model2Impp : MinimumLanguage Model_L :=
  Build_MinimumLanguage Model_L (fun x y => fun m => (x m -> y m)).

Class ImppDefinition_Model (minL : MinimumLanguage Model_L) : Prop := {
  model2impp : forall (x y : @expr Model_L), impp x y = (fun m  => (x m -> y m))
}.

Lemma Model2Impp_Normal :
  ImppDefinition_Model Model2Impp.
Proof. constructor. reflexivity. Qed.

End M2IMP.

Section M2kSM.

Context {M : Model}.

Instance kminSM : @KripkeMinimumSemantics Model_L Model2Impp M (unit_kMD _) tt modelR SM.
Proof.
  pose proof (@Trivial2Kripke Model_L Model2Impp M SM). apply H. constructor. reflexivity.
Qed.

End M2kSM.

