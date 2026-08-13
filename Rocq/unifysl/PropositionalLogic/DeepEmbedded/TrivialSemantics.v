Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.

Section TrivialSemantics.

Context {Sigma: PropositionalVariables}.

Existing Instances L minL andpL orpL falsepL negpL negpDef.

Definition model: Type := Var -> Prop.

Fixpoint denotation (x: expr Sigma): Ensemble model :=
  match x with
  | andp y z => Semantics.andp (denotation y) (denotation z)
  | orp y z => Semantics.orp (denotation y) (denotation z)
  | impp y z => Semantics.impp (denotation y) (denotation z)
  | falsep => Semantics.falsep
  | varp p => fun m => m p
  end.

#[export] Instance MD: Model :=
  Build_Model model.

#[export] Instance SM: Semantics L MD :=
  Build_Semantics L MD denotation.

#[export] Instance tminSM: TrivialMinimumSemantics L MD SM.
Proof.
  constructor.
  simpl; intros.
  apply Same_set_refl.
Qed.

#[export] Instance andpSM: AndSemantics L MD SM.
Proof.
  constructor.
  simpl; intros.
  apply Same_set_refl.
Qed.

#[export] Instance orpSM: OrSemantics L MD SM.
Proof.
  constructor.
  simpl; intros.
  apply Same_set_refl.
Qed.

#[export] Instance falsepSM: FalseSemantics L MD SM.
Proof.
  constructor.
  simpl; intros.
  apply Same_set_refl.
Qed.

#[export] Instance negpSM: NegSemantics L MD SM.
Proof.
  constructor.
  simpl; intros.
  apply Same_set_refl.
Qed.

End TrivialSemantics.
