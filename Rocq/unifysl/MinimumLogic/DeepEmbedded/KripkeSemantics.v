Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.DeepEmbedded.MinimumLanguage.

Import MinimumLanguage.

Record frame: Type := {
  underlying_set:> Type;
  underlying_relation: relation underlying_set
}.

Declare Scope TheKripkeSemantics.
Infix "<=" := (underlying_relation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := @Ensemble (underlying_set f).

Definition denotation {Var: Type} (F: frame) (eval: Var -> sem F): expr Var -> sem F :=
  fix denotation (x: expr Var): sem F:=
  match x with
  | impp y z => @Semantics.impp F (underlying_relation F) (denotation y) (denotation z)
  | varp p => eval p
  end.

Section KripkeSemantics.
Context (Var: Type).

Record Kmodel : Type := {
  underlying_frame :> frame;
  sem_var: Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

#[export] Instance L: Language := MinimumLanguage.L Var.
#[export] Instance MD: Model := Build_Model model.

#[export] Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

#[export] Instance R (M: Kmodel): Relation (Kworlds M) :=
  @underlying_relation M.

Definition Kmodel_Monotonic: Kmodel -> Prop := fun M =>
  forall v: Var, upwards_closed_Kdenote (sem_var M v).

Definition Kmodel_PreOrder: Kmodel -> Prop := fun M =>
  PreOrder (@Krelation _ (R M)).

#[export] Instance SM: Semantics L MD :=
  Build_Semantics L MD (fun x M => (denotation M (sem_var M) x) (elm M)).

#[export] Instance kiSM (M: Kmodel) {_: Kmodel_Monotonic M} {_: Kmodel_PreOrder M}:
  KripkeIntuitionisticSemantics L MD M SM.
Proof.
  hnf in H, H0.
  constructor; intros.
  induction x.
  + apply (Semantics.impp_closed _ _ IHx1 IHx2).
  + apply H.
Qed.

#[export] Instance kminSM (M: Kmodel): KripkeMinimumSemantics L MD M SM.
Proof.
  apply Build_KripkeMinimumSemantics.
  intros; apply Same_set_refl.
Defined.

End KripkeSemantics.

Arguments Kmodel_Monotonic {Var} _.
Arguments Kmodel_PreOrder {Var} _.
