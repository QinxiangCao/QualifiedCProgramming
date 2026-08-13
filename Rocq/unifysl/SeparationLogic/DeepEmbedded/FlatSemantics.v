Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Import Logic.SeparationLogic.Semantics.EmpSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Record frame: Type := {
  underlying_set:> Type;
  underlying_relation: relation underlying_set;
  underlying_join: Join underlying_set;
  underlying_unit: Unit underlying_set
}.

Declare Scope TheKripkeSemantics.
Infix "<=" := (underlying_relation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Section FlatSemantics.

Context {Sigma: PropositionalVariables}.

Definition sem (f: frame) := @Ensemble (underlying_set f).

Definition denotation (F: frame) (eval: Var -> sem F): expr Sigma -> sem F :=
  fix denotation (x: expr Sigma): sem F:=
  match x with
  | andp y z => @Semantics.andp F (denotation y) (denotation z)
  | orp y z => @Semantics.orp F (denotation y) (denotation z)
  | impp y z => @Semantics.impp F (underlying_relation F) (denotation y) (denotation z)
  | sepcon y z => @WeakSemantics.sepcon F (underlying_join F) (denotation y) (denotation z)
  | wand y z => @WeakSemantics.wand F (underlying_join F) (denotation y) (denotation z)
  | emp => @EmpSemantics.emp F (underlying_unit F) 
  | falsep => @Semantics.falsep F
  | varp p => eval p
  end.

Record Kmodel : Type := {
  underlying_frame :> frame;
  sem_var: Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

#[export] Instance MD: Model := Build_Model model.

#[export] Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

#[export] Instance SM: Semantics L MD :=
  Build_Semantics L MD (fun x M => (denotation M (sem_var M) x) (elm M)).

#[export] Instance R (M: Kmodel): Relation (Kworlds M) :=
  @underlying_relation M.

#[export] Instance J (M: Kmodel): Join (Kworlds M) :=
  @underlying_join M.

#[export] Instance U (M: Kmodel): Unit (Kworlds M) :=
  @underlying_unit M.

#[export] Instance kminSM (M: Kmodel): KripkeMinimumSemantics L MD M SM.
Proof.
  apply Build_KripkeMinimumSemantics.
  intros; apply Same_set_refl.
Defined.

#[export] Instance andpSM (M: Kmodel): KripkeAndSemantics L MD M SM.
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance orpSM (M: Kmodel): KripkeOrSemantics L MD M SM.
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance falsepSM (M: Kmodel): KripkeFalseSemantics L MD M SM.
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

#[export] Instance fsepconSM (M: Kmodel): FlatSemantics.SepconSemantics L MD M SM.
Proof.
  hnf; intros; apply Same_set_refl.
Qed.

#[export] Instance fwandSM (M: Kmodel): FlatSemantics.WandSemantics L MD M SM.
Proof.
  hnf; intros; apply Same_set_refl.
Qed.

#[export] Instance empSM (M: Kmodel): FlatSemantics.EmpSemantics L MD M SM.
Proof.
  unfold FlatSemantics.EmpSemantics.
  apply Same_set_refl.
Qed.

Definition Kmodel_Monotonic: Kmodel -> Prop := fun M =>
  forall v: Var, upwards_closed_Kdenote (sem_var M v).

Definition Kmodel_PreOrder: Kmodel -> Prop := fun M =>
  PreOrder (@Krelation _ (R M)).

Definition Kmodel_SeparationAlgebra: Kmodel -> Prop := fun M =>
  SeparationAlgebra (Kworlds M).

Definition Kmodel_UpwardsClosed: Kmodel -> Prop := fun M =>
  UpwardsClosedSeparationAlgebra (Kworlds M).

Definition Kmodel_DownwardsClosed: Kmodel -> Prop := fun M =>
  DownwardsClosedSeparationAlgebra (Kworlds M).

Definition Kmodel_UnitJoinOrderRel: Kmodel -> Prop := fun M =>
  UnitJoinOrderRelation (Kworlds M).
(*
Definition Kmodel_Identity: Kmodel -> Prop := fun M =>
  IdentityKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_NoBranch: Kmodel -> Prop := fun M =>
  NoBranchKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_BranchJoin: Kmodel -> Prop := fun M =>
  BranchJoinKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_Increasing: Kmodel -> Prop := fun M =>
  IncreasingSeparationAlgebra (Kworlds M).

Definition Kmodel_IncreasingSplitSmaller: Kmodel -> Prop := fun M =>
  IncreasingSplitSmallerSeparationAlgebra (Kworlds M).

Definition Kmodel_IncreasingJoinSelf: Kmodel -> Prop := fun M =>
  IncreasingJoinSelfSeparationAlgebra (Kworlds M).
*)

Record Parametric_Kmodel_Class (PAR: SA_Parameter) (M: Kmodel): Prop := {
  SA_ID: ID = true -> IdentityKripkeIntuitionisticModel (Kworlds M);
  SA_NB: NB = true -> NoBranchKripkeIntuitionisticModel (Kworlds M);
  SA_BJ: BJ = true -> BranchJoinKripkeIntuitionisticModel (Kworlds M);
  SA_INCR: INCR = true -> IncreasingSeparationAlgebra (Kworlds M);
  SA_UNI: ISS = true -> IncreasingSplitSmallerSeparationAlgebra (Kworlds M);
  SA_RES: IJS = true -> IncreasingJoinSelfSeparationAlgebra (Kworlds M)
}.

End FlatSemantics.

