Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Setoids.Setoid.
Require Import SetsClass.SetElement.
Require Import SetsClass.SetsDomain.

Class PRE_SETS_ELE_Properties
        (S RES E: Type)
        {SE: SetsEle.PRE_SETS_ELE S RES E}
        {SETS_S: Sets.SETS S}
        {SETS_RES: Sets.SETS RES}: Prop :=
{
  In_aux_mono: Proper (eq ==> @Sets.included S _ ==> @Sets.included RES _) SetsEle.In_aux;
}.

Class SETS_ELE_Properties
        (S E: Type)
        {SE: SetsEle.SETS_ELE S E}
        {SETS_S: Sets.SETS S}: Prop :=
{
  Sets_In_mono: Proper (eq ==> @Sets.included S _ ==> Basics.impl) SetsEle.In
}.

#[export] Instance Prop_PRE_SETS_ELE_Properties
           (A S: Type)
           {Sets_S: Sets.SETS S}:
  PRE_SETS_ELE_Properties (A -> S) S A.
Proof.
  constructor.
  unfold Proper, respectful; intros.
  subst.
  simpl.
  apply H0.
Qed.

#[export] Instance lift_PRE_SETS_ELE_Properties
           {A S RES E: Type}
           (_SetsEle: SetsEle.PRE_SETS_ELE S (A -> RES) E)
           {_Sets_RES: Sets.SETS RES}
           {_Sets_S: Sets.SETS S}
           {_SetsEle_Properties: PRE_SETS_ELE_Properties S (A -> RES) E}:
  PRE_SETS_ELE_Properties S RES (E * A).
Proof.
  constructor.
  unfold Proper, respectful.
  intros; subst.
  pose proof @In_aux_mono _ _ _ _SetsEle _ _ _.
  apply H.
  + reflexivity.
  + apply H0.
Qed.

#[export] Instance Derived_SETS_ELE_Properties
           {S E: Type}
           (_SetsEle: SetsEle.PRE_SETS_ELE S Prop E)
           {_SETS: Sets.SETS S}
           {_SetsEle_Properties: PRE_SETS_ELE_Properties S Prop E}:
  SETS_ELE_Properties S E.
Proof.
  constructor.
  unfold Proper, respectful.
  intros; subst.
  pose proof @In_aux_mono _ _ _ _SetsEle _ _ _.
  apply H.
  + reflexivity.
  + apply H0.
Qed.

#[export] Existing Instance Sets_In_mono.

#[export] Instance Sets_In_congr
           {S E: Type}
           {__SetsEle: SetsEle.SETS_ELE S E}
           {__Sets: Sets.SETS S}
           {__SetsProperties: SETS_Properties S}
           {__SetsEle_Properties: SETS_ELE_Properties S E}:
  Proper (eq ==> @Sets.equiv S _ ==> iff) SetsEle.In.
Proof.
  intros.
  unfold Proper, respectful.
  intros; subst.
  split; apply Sets_In_mono.
  + reflexivity.
  + rewrite H0; reflexivity.
  + reflexivity.
  + rewrite H0; reflexivity.
Qed.



