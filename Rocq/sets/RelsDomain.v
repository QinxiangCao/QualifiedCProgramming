Require Import Coq.Classes.Morphisms.
Require Coq.Lists.List.
Require Coq.Lists.Streams.
Require Import SetsClass.SetElement.
Require Import SetsClass.SetsDomain.
Require Import SetsClass.SetProd.
Local Open Scope sets_scope.

Module Rels.

Class ACCUM (I1 I2 I: Type): Type := {
  app: I1 -> I2 -> I;
}.

Class ACCUM_NIL (I: Type): Type := {
  nil: I;
}.

Class ACCUM_EQ (I: Type): Type :=
  i_equiv: I -> I -> Prop.

Class PRE_RELS (A R S T: Type): Type :=
{
  concat_aux: R -> S -> A -> T
}.

Class PRE_RELS_ID (A R: Type): Type :=
{
  id_aux: A -> R
}.

Class RELS (R S T: Type): Type :=
{
  concat: R -> S -> T
}.

Class RELS_ID (R: Type): Type :=
{
  id: R
}.

Class RELS_TEST (S R: Type): Type :=
{
  test: S -> R
}.

End Rels.

#[export] Instance Prop_PRE_RELS
           (A S: Type)
           {_SETS_S: Sets.SETS S}:
  Rels.PRE_RELS A (A -> Prop) S S :=
  {|
    Rels.concat_aux := fun X Y =>
      Sets.test1 X ∩ Sets.lift1 Y
  |}.

#[export] Instance Prop_PRE_RELS_ID (A: Type):
  Rels.PRE_RELS_ID A (A -> Prop) :=
  {|
    Rels.id_aux := fun a b => a = b
  |}.

#[export] Instance lift_PRE_RELS
           (I1 I2 I A R S T: Type)
           {_REL: Rels.PRE_RELS A R S T}
           {_ACC: Rels.ACCUM I1 I2 I}
           {_SETS_T: Sets.SETS T}:
  Rels.PRE_RELS A (I1 -> R) (I2 -> S) (I -> T) :=
  {|
    Rels.concat_aux := fun X Y a i =>
      Sets.indexed_union (Sets.indexed_union (fun i2 i1 =>
        Sets.prop_inj (Rels.app i1 i2 = i) ∩ Rels.concat_aux (X i1) (Y i2) a))
  |}.

#[export] Instance lift_PRE_RELS_ID
           (I A T: Type)
           {_REL_ID: Rels.PRE_RELS_ID A T}
           {_ACC_NIL: Rels.ACCUM_NIL I}
           {_SETS_T: Sets.SETS T}:
  Rels.PRE_RELS_ID A (I -> T) :=
  {|
    Rels.id_aux := fun a i =>
      Sets.intersect
        (Sets.prop_inj (i = Rels.nil))
        (Rels.id_aux a)
  |}.

 #[export] Instance Derived_RELS
           (B A R S T: Type)
           {_REL: Rels.PRE_RELS A R S T}
           {_SETS_T: Sets.SETS T}:
  Rels.RELS (B -> R) (A -> S) (B -> T) :=
  {|
    Rels.concat := fun X Y a =>
      Sets.indexed_union (fun b => Rels.concat_aux (X a) (Y b) b)
  |}.

#[export] Instance Derived_RELS_ID
           (A T: Type)
           {_REL_ID: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}:
  Rels.RELS_ID (A -> T) :=
  {|
    Rels.id := Rels.id_aux
  |}.

#[export] Instance Derived_RELS_TEST
           (A T: Type)
           {_REL_ID: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}:
  Rels.RELS_TEST (A -> Prop) (A -> T) :=
  {|
    Rels.test := fun X => Sets.filter1 X Rels.id
  |}.

Goal forall X Y: nat -> nat -> Prop, Rels.concat X Y = fun a c => exists b, X a b /\ Y b c.
  intros.
  reflexivity.
Qed.

Goal forall X: nat -> Prop, Rels.concat Rels.id X = fun a => exists b, a = b /\ X b.
  intros.
  reflexivity.
Qed.

Goal forall (X: nat -> Prop), Rels.test X = fun a c => X a /\ a = c.
  intros.
  reflexivity.
Qed.

Class ACCUM_Assoc
        (I1 I2 I3 I12 I23 I123: Type)
        {_ACC_1_2: Rels.ACCUM I1 I2 I12}
        {_ACC_2_3: Rels.ACCUM I2 I3 I23}
        {_ACC_12_3: Rels.ACCUM I12 I3 I123}
        {_ACC_1_23: Rels.ACCUM I1 I23 I123}: Prop :=
{
  Rels_app_assoc: forall i1 i2 i3,
    Rels.app (Rels.app i1 i2) i3 = Rels.app i1 (Rels.app i2 i3);
}.

Class ACCUM_LeftId
        (I1 I2: Type)
        {_ACC: Rels.ACCUM I1 I2 I2}
        {_ACC_NIL: Rels.ACCUM_NIL I1}: Prop :=
{
  Rels_app_nil_l_setoid: forall i,
    Rels.app Rels.nil i = i
}.

Class ACCUM_RightId
        (I1 I2: Type)
        {_ACC: Rels.ACCUM I1 I2 I1}
        {_ACC_NIL: Rels.ACCUM_NIL I2}: Prop :=
{
  Rels_app_nil_r_setoid: forall i,
    Rels.app i Rels.nil = i;
}.

Class PRE_RELS_Properties
        (A R S T: Type)
        {_REL: Rels.PRE_RELS A R S T}
        {_SETS_R: Sets.SETS R}
        {_SETS_S: Sets.SETS S}
        {_SETS_T: Sets.SETS T}: Prop :=
{
  Rels_concat_union_distr_r_aux:
    forall x1 x2 y a,
      Sets.equiv
        (Rels.concat_aux (x1 ∪ x2) y a)
        (Rels.concat_aux x1 y a ∪ Rels.concat_aux x2 y a);
  Rels_concat_union_distr_l_aux:
    forall x y1 y2 a,
      Sets.equiv
        (Rels.concat_aux x (y1 ∪ y2) a)
        (Rels.concat_aux x y1 a ∪ Rels.concat_aux x y2 a);
  Rels_concat_indexed_union_distr_r_aux:
    forall {I} (xs: I -> _) y a,
      Sets.equiv
        (Rels.concat_aux (Sets.indexed_union xs) y a)
        (Sets.indexed_union (fun i => Rels.concat_aux (xs i) y a));
  Rels_concat_indexed_union_distr_l_aux:
    forall {I} x (ys: I -> _) a,
      Sets.equiv
        (Rels.concat_aux x (Sets.indexed_union ys) a)
        (Sets.indexed_union (fun i => Rels.concat_aux x (ys i) a));
  Rels_concat_prop_inj_intersect_l_aux:
    forall x P y a,
      Sets.equiv
        (Rels.concat_aux x (Sets.intersect (Sets.prop_inj P) y) a)
        (Sets.intersect (Sets.prop_inj P) (Rels.concat_aux x y a));
  Rels_concat_prop_inj_intersect_r_aux:
    forall x P y a,
      Sets.equiv
        (Rels.concat_aux (Sets.intersect (Sets.prop_inj P) x) y a)
        (Sets.intersect (Sets.prop_inj P) (Rels.concat_aux x y a));
  Rels_concat_mono_aux::
    Proper
      (Sets.included ==> Sets.included ==> eq ==> Sets.included)
      (@Rels.concat_aux _ _ _ _ _REL);
  Rels_concat_general_union_distr_r_aux:
    forall (xs: _ -> Prop) y a,
      Sets.equiv
        (Rels.concat_aux (Sets.general_union xs) y a)
        (Sets.general_union (fun z => exists x, xs x /\ z = Rels.concat_aux x y a));
  Rels_concat_general_union_distr_l_aux:
    forall x (ys: _ -> Prop) a,
      Sets.equiv
        (Rels.concat_aux x (Sets.general_union ys) a)
        (Sets.general_union (fun z => exists y, ys y /\ z = Rels.concat_aux x y a))
}.

Class RELS_Properties
        (R S T: Type)
        {_REL: Rels.RELS R S T}
        {_SETS_R: Sets.SETS R}
        {_SETS_S: Sets.SETS S}
        {_SETS_T: Sets.SETS T}: Prop :=
{
  Rels_concat_union_distr_r:
    forall x1 x2 y,
      Sets.equiv
        (Rels.concat (x1 ∪ x2) y)
        (Rels.concat x1 y ∪ Rels.concat x2 y);
  Rels_concat_union_distr_l:
    forall x y1 y2,
      Sets.equiv
        (Rels.concat x (y1 ∪ y2))
        (Rels.concat x y1 ∪ Rels.concat x y2);
  Rels_concat_indexed_union_distr_r:
    forall {I} (xs: I -> _) y,
      Sets.equiv
        (Rels.concat (Sets.indexed_union xs) y)
        (Sets.indexed_union (fun i => Rels.concat (xs i) y));
  Rels_concat_indexed_union_distr_l:
    forall {I} x (ys: I -> _),
      Sets.equiv
        (Rels.concat x (Sets.indexed_union ys))
        (Sets.indexed_union (fun i => Rels.concat x (ys i)));
  Rels_concat_mono::
    Proper
      (Sets.included ==> Sets.included ==> Sets.included)
      (@Rels.concat _ _ _ _REL);
  Rels_concat_general_union_distr_r:
    forall xs y,
      Sets.equiv
        (@Rels.concat _ _ _ _REL (Sets.general_union xs) y)
        (Sets.general_union (fun z => exists x, xs x /\ z = (Rels.concat x y)));
  Rels_concat_general_union_distr_l:
    forall x ys,
      Sets.equiv
        (@Rels.concat _ _ _ _REL x (Sets.general_union ys))
        (Sets.general_union (fun z => exists y, ys y /\ z = (Rels.concat x y)));
}.

Class PRE_RELS_Assoc
        (A12 A23 X1 X2 X3 X12 X23 X123: Type)
        {_REL_1_2: Rels.PRE_RELS A12 X1 X2 X12}
        {_REL_12_3: Rels.PRE_RELS A23 X12 X3 X123}
        {_REL_2_3: Rels.PRE_RELS A23 X2 X3 X23}
        {_REL_1_23: Rels.PRE_RELS A12 X1 X23 X123}
        {_SETS: Sets.SETS X123}: Prop :=
{
  Rels_concat_assoc_aux:
    forall (x: X1) (y: X2) (z: X3) (axy: A12) (ayz: A23),
      Sets.equiv
        (Rels.concat_aux (Rels.concat_aux x y axy) z ayz)
        (Rels.concat_aux x (Rels.concat_aux y z ayz) axy)
}.

Class RELS_Assoc
        (X1 X2 X3 X12 X23 X123: Type)
        {_REL_1_2: Rels.RELS X1 X2 X12}
        {_REL_12_3: Rels.RELS X12 X3 X123}
        {_REL_2_3: Rels.RELS X2 X3 X23}
        {_REL_1_23: Rels.RELS X1 X23 X123}
        {_SETS: Sets.SETS X123}: Prop :=
{
  Rels_concat_assoc:
    forall (x: X1) (y: X2) (z: X3),
      Sets.equiv
        (Rels.concat (Rels.concat x y) z)
        (Rels.concat x (Rels.concat y z))
}.

Class PRE_RELS_LeftId
        (A X Y: Type)
        {_REL: Rels.PRE_RELS A X Y Y}
        {_REL_ID: Rels.PRE_RELS_ID A X}
        {_SETS: Sets.SETS Y}: Prop :=
{
  Rels_concat_id_l_aux:
    forall a b y,
      Sets.equiv
        (Rels.concat_aux (Rels.id_aux a) y b)
        (Sets.intersect (Sets.prop_inj (a = b)) y)
}.

Class PRE_RELS_RightId
        (A X Y: Type)
        {_REL: Rels.PRE_RELS A X Y X}
        {_REL_ID: Rels.PRE_RELS_ID A Y}
        {_SETS: Sets.SETS X}: Prop :=
{
  Rels_concat_id_r_aux:
    forall x,
      Sets.equiv
        (Sets.indexed_union (fun a => (Rels.concat_aux x (Rels.id_aux a) a)))
        x
}.

Class RELS_LeftId
        (X Y: Type)
        {_REL: Rels.RELS X Y Y}
        {_REL_ID: Rels.RELS_ID X}
        {_SETS: Sets.SETS Y}: Prop :=
{
  Rels_concat_id_l:
    forall y,
      Sets.equiv
        (Rels.concat Rels.id y) y
}.

Class RELS_RightId
        (X Y: Type)
        {_REL: Rels.RELS X Y X}
        {_REL_ID: Rels.RELS_ID Y}
        {_SETS: Sets.SETS X}: Prop :=
{
  Rels_concat_id_r:
    forall x,
      Sets.equiv
        (Rels.concat x Rels.id) x
}.

Class RELS_TestSpec
        (A T: Type)
        {_REL_ID: Rels.PRE_RELS_ID A T}
        {_SETS_T: Sets.SETS T}: Prop :=
{
  Rels_test_spec:
    forall x: A -> Prop,
      @Sets.equiv (A -> T) _
        (Rels.test x)
        (Sets.intersect (Sets.test1 x) Rels.id)
}.

#[export] Instance Prop_PRE_RELS_Properties
           {A S}
           {_SETS_S: Sets.SETS S}
           {_SETS_S_Properties: SETS_Properties S}:
  PRE_RELS_Properties A (A -> Prop) S S.
Proof.
  constructor.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_union_distr_r.
    rewrite <- Sets_prop_inj_or.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_union_distr_l.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_indexed_union_distr_r.
    rewrite <- Sets_prop_inj_ex.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_indexed_union_distr_l.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect at 1 4; simpl.
    unfold Sets.lift_intersect.
    rewrite <- !Sets_intersect_assoc.
    rewrite (Sets_intersect_comm (Sets.prop_inj _)).
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect at 1 4; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_assoc.
    rewrite <- Sets_prop_inj_and.
    reflexivity.
  + intros.
    unfold Proper, respectful.
    simpl; intros.
    apply Sets_intersect_mono; auto.
    unfold Sets.test1.
    apply Sets_prop_inj_included_prop_inj.
    subst x1;
    apply H.
  + intros; simpl.
    sets_unfold.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_prop_inj_included; intro.
      destruct H as [S' [? ?] ].
      transitivity (Sets.intersect (Sets.prop_inj (S' a)) y).
      apply Sets_included_intersect; try reflexivity.
      apply Sets_included_prop_inj; tauto.
      apply Sets_included_general_union.
      exists S'.
      split; tauto.
    - apply Sets_general_union_included; intros.
      destruct H as [S' [? ?] ].
      rewrite H0; clear H0.
      apply Sets_prop_inj_included; intro.
      apply Sets_included_intersect; try reflexivity.
      apply Sets_included_prop_inj.
      exists S'.
      tauto.
  + intros; simpl.
    sets_unfold.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_prop_inj_included; intro.
      apply Sets_general_union_included; intros.
      transitivity (Sets.intersect (Sets.prop_inj (x a)) x0).
      apply Sets_included_intersect; try reflexivity.
      apply Sets_included_prop_inj; tauto.
      apply Sets_included_general_union.
      exists x0.
      split; tauto.
    - apply Sets_general_union_included; intros.
      destruct H as [S' [? ?] ].
      subst x0.
      apply Sets_prop_inj_included; intro.
      apply Sets_included_intersect.
      apply Sets_included_prop_inj; tauto.
      apply Sets_included_general_union; tauto.
Qed.

#[export] Instance Rels_concat_mono_aux'
           {A R S T: Type}
           {_REL: Rels.PRE_RELS A R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: PRE_RELS_Properties A R S T}
           {_SETS_R_Properties: SETS_Properties R}
           {_SETS_S_Properties: SETS_Properties S}
           {_SETS_T_Properties: SETS_Properties T}:
  Proper
    (Sets.included ==> Sets.included ==> eq ==> Sets.included)
    (@Rels.concat_aux _ _ _ _ _REL).
Proof.
  unfold Proper, respectful.
  intros.
  subst y1.
  apply Rels_concat_mono_aux; tauto.
Qed.

#[export] Instance Rels_concat_congr_aux
           {A R S T: Type}
           {_REL: Rels.PRE_RELS A R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: PRE_RELS_Properties A R S T}
           {_SETS_R_Properties: SETS_Properties R}
           {_SETS_S_Properties: SETS_Properties S}
           {_SETS_T_Properties: SETS_Properties T}:
  Proper
    (Sets.equiv ==> Sets.equiv ==> eq ==> Sets.equiv)
    (@Rels.concat_aux _ _ _ _ _REL).
Proof.
  unfold Proper, respectful.
  intros.
  subst y1.
  apply Sets_equiv_Sets_included; split.
  + apply Rels_concat_mono_aux.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
    - reflexivity.
  + apply Rels_concat_mono_aux.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
    - reflexivity.
Qed.

#[export] Instance lift_PRE_RELS_Properties
           {A R S T I1 I2 I}
           {_REL: Rels.PRE_RELS A R S T}
           {_ACC: Rels.ACCUM I1 I2 I}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: PRE_RELS_Properties A R S T}
           {_SETS_R_Properties: SETS_Properties R}
           {_SETS_S_Properties: SETS_Properties S}
           {_SETS_T_Properties: SETS_Properties T}:
  PRE_RELS_Properties A (I1 -> R) (I2 -> S) (I -> T).
Proof.
  constructor.
  + intros.
    sets_unfold.
    intros i; simpl.
    sets_unfold.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      unfold Sets.lift_indexed_union; simpl.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rels_concat_union_distr_r_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union i2).
        simpl.
        rewrite <- (Sets_included_indexed_union i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
      * rewrite <- (Sets_included_indexed_union i2).
        rewrite <- (Sets_included_indexed_union i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rels_concat_union_distr_r_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rels_concat_union_distr_r_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union2.
  + intros.
    sets_unfold.
    intros i; simpl.
    sets_unfold.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rels_concat_union_distr_l_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union i2).
        rewrite <- (Sets_included_indexed_union i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
      * rewrite <- (Sets_included_indexed_union i2).
        rewrite <- (Sets_included_indexed_union i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rels_concat_union_distr_l_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rels_concat_union_distr_l_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union2.
  + intros.
    simpl.
    sets_unfold; intros i; simpl.
    sets_unfold.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rels_concat_indexed_union_distr_r_aux.
      apply Sets_indexed_union_mono; intros i0.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_indexed_union_included; intros i0.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; auto.
      * rewrite Rels_concat_indexed_union_distr_r_aux.
        rewrite <- (Sets_included_indexed_union i0).
        reflexivity.
  + intros.
    simpl.
    sets_unfold; intros i.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rels_concat_indexed_union_distr_l_aux.
      apply Sets_indexed_union_mono; intros i0.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_indexed_union_included; intros i0.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; auto.
      * rewrite Rels_concat_indexed_union_distr_l_aux.
        rewrite <- (Sets_included_indexed_union i0).
        reflexivity.
  + intros.
    simpl.
    sets_unfold; intros i.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rels_concat_prop_inj_intersect_l_aux.
      apply Sets_prop_inj_included; intros.
      apply Sets_included_intersect; [apply Sets_included_prop_inj; auto |].
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_prop_inj_included; intros.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      rewrite Rels_concat_prop_inj_intersect_l_aux.
      apply Sets_included_intersect; [| apply Sets_included_intersect].
      * apply Sets_included_prop_inj; auto.
      * apply Sets_included_prop_inj; auto.
      * reflexivity.
  + intros.
    simpl.
    sets_unfold; intros i.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rels_concat_prop_inj_intersect_r_aux.
      apply Sets_prop_inj_included; intros.
      apply Sets_included_intersect; [apply Sets_included_prop_inj; auto |].
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_prop_inj_included; intros.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      rewrite Rels_concat_prop_inj_intersect_r_aux.
      apply Sets_included_intersect; [| apply Sets_included_intersect].
      * apply Sets_included_prop_inj; auto.
      * apply Sets_included_prop_inj; auto.
      * reflexivity.
  + intros a; unfold Proper, respectful; intros.
    simpl.
    sets_unfold; intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_indexed_union_mono; intros i2.
    apply Sets_indexed_union_mono; intros i1.
    apply Sets_intersect_mono; [reflexivity |].
    apply Rels_concat_mono_aux; auto.
  + intros.
    simpl.
    set (F := @Sets.general_union); sets_unfold; subst F.
    intros i.
    rewrite general_union_lift.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite general_union_lift.
      rewrite Rels_concat_general_union_distr_r_aux.
      apply Sets_general_union_included.
      intros z [z' [ [x [? ?] ] ?] ].
      subst z z'.
      rewrite <-
        (Sets_included_general_union _
           (⋃ (fun i2 : I1 =>
                ⋃ (fun i1 : I2 => (⌜ Rels.app i2 i1 = i ⌝) ∩
                                  Rels.concat_aux (x i2) (y i1) a)))).
      2: {
        eexists.
        split; [exists x; split; [tauto | reflexivity] |].
        reflexivity.
      }
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_general_union_included; intros z ?.
      destruct H as [z' [ [x [? ?] ] ? ] ].
      subst z z'.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; auto.
      * rewrite general_union_lift.
        rewrite <- (Sets_included_general_union _ (x i2)).
        2: { exists x; tauto. }
        reflexivity.
  + intros.
    simpl.
    set (F := @Sets.general_union); sets_unfold; subst F.
    intros i.
    rewrite general_union_lift.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite general_union_lift.
      rewrite Rels_concat_general_union_distr_l_aux.
      apply Sets_general_union_included; intros z ?.
      destruct H0 as [z' [ [y [? ?] ] ?] ].
      subst z' z.
      rewrite <-
        (Sets_included_general_union _
           (⋃ (fun i2 : I1 =>
                 ⋃ (fun i1 : I2 => (⌜ Rels.app i2 i1 = i ⌝) ∩
                                   Rels.concat_aux (x i2) (y i1) a)))).
      2: {
        eexists.
        split; [exists y; split; [tauto | reflexivity] |].
        reflexivity.
      }
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_general_union_included; intros z ?.
      destruct H as [z' [ [y [? ?] ] ? ] ].
      subst z z'.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union i2).
      rewrite <- (Sets_included_indexed_union i1).
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; auto.
      * rewrite general_union_lift.
        rewrite <- (Sets_included_general_union _ (y i1)).
        2: { exists y; tauto. }
        reflexivity.
Qed.

#[export] Instance Deriveds_RELS_Properties
           {B A R S T}
           {_REL: Rels.PRE_RELS A R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: PRE_RELS_Properties A R S T}
           {_SETS_R_Properties: SETS_Properties R}
           {_SETS_S_Properties: SETS_Properties S}
           {_SETS_T_Properties: SETS_Properties T}:
  RELS_Properties (B -> R) (A -> S) (B -> T).
Proof.
  intros.
  constructor.
  + intros; simpl.
    sets_unfold.
    intros b.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros a.
      rewrite Rels_concat_union_distr_r_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union a).
        reflexivity.
      * rewrite <- (Sets_included_indexed_union a).
        reflexivity.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rels_concat_union_distr_r_aux.
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rels_concat_union_distr_r_aux.
        apply Sets_included_union2.
  + intros; simpl.
    sets_unfold.
    intros b.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros a.
      rewrite Rels_concat_union_distr_l_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union a).
        reflexivity.
      * rewrite <- (Sets_included_indexed_union a).
        reflexivity.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rels_concat_union_distr_l_aux.
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rels_concat_union_distr_l_aux.
        apply Sets_included_union2.
  + intros; simpl.
    sets_unfold.
    intros b.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros a.
      rewrite Rels_concat_indexed_union_distr_r_aux.
      apply Sets_indexed_union_mono; intros i.
      rewrite <- (Sets_included_indexed_union a).
      reflexivity.
    - apply Sets_indexed_union_included; intros i.
      apply Sets_indexed_union_mono; intros a.
      rewrite Rels_concat_indexed_union_distr_r_aux.
      rewrite <- (Sets_included_indexed_union i).
      reflexivity.
  + intros; simpl.
    sets_unfold.
    intros b.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros a.
      rewrite Rels_concat_indexed_union_distr_l_aux.
      apply Sets_indexed_union_mono; intros i.
      rewrite <- (Sets_included_indexed_union a).
      reflexivity.
    - apply Sets_indexed_union_included; intros i.
      apply Sets_indexed_union_mono; intros a.
      rewrite Rels_concat_indexed_union_distr_l_aux.
      rewrite <- (Sets_included_indexed_union i).
      reflexivity.
  + unfold Proper, respectful.
    simpl; intros.
    intros b.
    apply Sets_indexed_union_mono; intros a.
    apply Rels_concat_mono_aux; auto.
  + intros; simpl.
    apply Sets_equiv_Sets_included; split.
    - intro.
      apply Sets_indexed_union_included; intro.
      rewrite general_union_lift.
      rewrite general_union_lift.
      rewrite Rels_concat_general_union_distr_r_aux.
      apply Sets_general_union_included; intros.
      destruct H as [? [ [? [? ?] ] ?] ].
      subst x x0.
      rewrite <-
        (Sets_included_general_union _
          (⋃ (fun b : A => Rels.concat_aux (x1 a) (y b) b))).
      * rewrite <- Sets_included_indexed_union.
        reflexivity.
      * eexists; split.
        exists x1; split; tauto.
        reflexivity.
    - apply Sets_general_union_included; intros.
      destruct H as [? [? ?] ]; subst x.
      intro.
      apply Sets_indexed_union_mono.
      intro.
      rewrite general_union_lift.
      rewrite Rels_concat_general_union_distr_r_aux.
      apply Sets_included_general_union.
      eexists; split.
      exists x0; split; tauto.
      reflexivity.
  + intros; simpl.
    apply Sets_equiv_Sets_included; split.
    - intro.
      apply Sets_indexed_union_included; intro.
      rewrite general_union_lift.
      rewrite general_union_lift.
      rewrite Rels_concat_general_union_distr_l_aux.
      apply Sets_general_union_included; intros.
      destruct H as [? [ [? [? ?] ] ?] ].
      subst x0 x1.
      rewrite <-
        (Sets_included_general_union _
          (⋃ (fun b : A => Rels.concat_aux (x a) (x2 b) b))).
      * rewrite <- Sets_included_indexed_union.
        reflexivity.
      * eexists; split.
        exists x2; split; tauto.
        reflexivity.
    - apply Sets_general_union_included; intros.
      destruct H as [? [? ?] ]; subst x0.
      intro.
      apply Sets_indexed_union_mono.
      intro.
      rewrite general_union_lift.
      rewrite Rels_concat_general_union_distr_l_aux.
      apply Sets_included_general_union.
      eexists; split.
      exists x1; split; tauto.
      reflexivity.
Qed.

#[export] Instance Prop_PRE_RELS_Assoc
           {A B S}
           {_SETS_S: Sets.SETS S}
           {_SETS_S_Properties: SETS_Properties S}:
  PRE_RELS_Assoc A B (A -> Prop) (B -> Prop) S (B -> Prop) S S.
Proof.
  constructor.
  intros.
  simpl.
  sets_unfold.
  rewrite <- Sets_intersect_assoc.
  rewrite Sets_prop_inj_and.
  reflexivity.
Qed.

#[export] Instance lift_PRE_RELS_Assoc
           (A12 A23 I1 I2 I3 I12 I23 I123 X1 X2 X3 X12 X23 X123: Type)
           {_REL_1_2: Rels.PRE_RELS A12 X1 X2 X12}
           {_REL_12_3: Rels.PRE_RELS A23 X12 X3 X123}
           {_REL_2_3: Rels.PRE_RELS A23 X2 X3 X23}
           {_REL_1_23: Rels.PRE_RELS A12 X1 X23 X123}
           {_ACC_1_2: Rels.ACCUM I1 I2 I12}
           {_ACC_2_3: Rels.ACCUM I2 I3 I23}
           {_ACC_12_3: Rels.ACCUM I12 I3 I123}
           {_ACC_1_23: Rels.ACCUM I1 I23 I123}
           {_SETS_1: Sets.SETS X1}
           {_SETS_3: Sets.SETS X3}
           {_SETS_12: Sets.SETS X12}
           {_SETS_23: Sets.SETS X23}
           {_SETS_123: Sets.SETS X123}
           {_PRE_RELS_Assoc: PRE_RELS_Assoc A12 A23 X1 X2 X3 X12 X23 X123}
           {_PRE_RELS_Properties_1_23: PRE_RELS_Properties A12 X1 X23 X123}
           {_PRE_RELS_Properties_12_3: PRE_RELS_Properties A23 X12 X3 X123}
           {_ACCUM_Assoc: ACCUM_Assoc I1 I2 I3 I12 I23 I123}
           {_SETS_Properties: SETS_Properties X123}:
  PRE_RELS_Assoc A12 A23 (I1 -> X1) (I2 -> X2) (I3 -> X3) (I12 -> X12) (I23 -> X23) (I123 -> X123).
Proof.
  constructor.
  intros.
  unfold lift_PRE_RELS.
  simpl.
  sets_unfold.
  intros i.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included.
    intros i12.
    apply Sets_indexed_union_included.
    intros i3.
    apply Sets_prop_inj_included; intros.
    rewrite Rels_concat_indexed_union_distr_r_aux.
    apply Sets_indexed_union_included.
    intros i1.
    rewrite Rels_concat_indexed_union_distr_r_aux.
    apply Sets_indexed_union_included.
    intros i2.
    rewrite Rels_concat_prop_inj_intersect_r_aux.
    apply Sets_prop_inj_included; intros.
    rewrite <- (Sets_included_indexed_union i1).
    rewrite <- (Sets_included_indexed_union (Rels.app i2 i3)).
    apply Sets_included_intersect. {
      apply Sets_included_prop_inj.
      rewrite <- Rels_app_assoc.
      rewrite <- H, <- H0.
      reflexivity.
    }
    rewrite Rels_concat_indexed_union_distr_l_aux.
    rewrite <- (Sets_included_indexed_union i2).
    rewrite Rels_concat_indexed_union_distr_l_aux.
    rewrite <- (Sets_included_indexed_union i3).
    rewrite Rels_concat_prop_inj_intersect_l_aux.
    apply Sets_included_intersect; [apply Sets_included_prop_inj; reflexivity |].
    rewrite Rels_concat_assoc_aux; reflexivity.
  + apply Sets_indexed_union_included.
    intros i1.
    apply Sets_indexed_union_included.
    intros i23.
    apply Sets_prop_inj_included; intros.
    rewrite Rels_concat_indexed_union_distr_l_aux.
    apply Sets_indexed_union_included.
    intros i2.
    rewrite Rels_concat_indexed_union_distr_l_aux.
    apply Sets_indexed_union_included.
    intros i3.
    rewrite Rels_concat_prop_inj_intersect_l_aux.
    apply Sets_prop_inj_included; intros.
    rewrite <- (Sets_included_indexed_union (Rels.app i1 i2)).
    rewrite <- (Sets_included_indexed_union i3).
    apply Sets_included_intersect. {
      apply Sets_included_prop_inj.
      rewrite Rels_app_assoc.
      rewrite <- H, <- H0; reflexivity.
    }
    rewrite Rels_concat_indexed_union_distr_r_aux.
    rewrite <- (Sets_included_indexed_union i1).
    rewrite Rels_concat_indexed_union_distr_r_aux.
    rewrite <- (Sets_included_indexed_union i2).
    rewrite Rels_concat_prop_inj_intersect_r_aux.
    apply Sets_included_intersect; [apply Sets_included_prop_inj; reflexivity |].
    rewrite Rels_concat_assoc_aux; reflexivity.
Qed.

#[export] Instance Derived_RELS_Assoc
           (B A12 A23 X1 X2 X3 X12 X23 X123: Type)
           {_REL_1_2: Rels.PRE_RELS A12 X1 X2 X12}
           {_REL_12_3: Rels.PRE_RELS A23 X12 X3 X123}
           {_REL_2_3: Rels.PRE_RELS A23 X2 X3 X23}
           {_REL_1_23: Rels.PRE_RELS A12 X1 X23 X123}
           {_SETS_1: Sets.SETS X1}
           {_SETS_3: Sets.SETS X3}
           {_SETS_12: Sets.SETS X12}
           {_SETS_23: Sets.SETS X23}
           {_SETS_123: Sets.SETS X123}
           {_PRE_RELS_Assoc: PRE_RELS_Assoc A12 A23 X1 X2 X3 X12 X23 X123}
           {_PRE_RELS_Properties_1_23: PRE_RELS_Properties A12 X1 X23 X123}
           {_PRE_RELS_Properties_12_3: PRE_RELS_Properties A23 X12 X3 X123}
           {_SETS_1_Properties: SETS_Properties X1}
           {_SETS_3_Properties: SETS_Properties X3}
           {_SETS_12_Properties: SETS_Properties X12}
           {_SETS_23_Properties: SETS_Properties X23}
           {_SETS_Properties: SETS_Properties X123}:
  RELS_Assoc (B -> X1) (A12 -> X2) (A23 -> X3) (B -> X12) (A12 -> X23) (B -> X123).
Proof.
  intros.
  constructor.
  intros.
  simpl.
  intros b.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included.
    intros ayz.
    rewrite Rels_concat_indexed_union_distr_r_aux.
    apply Sets_indexed_union_included.
    intros axy.
    rewrite Rels_concat_assoc_aux.
    rewrite <- (Sets_included_indexed_union axy).
    rewrite Rels_concat_indexed_union_distr_l_aux.
    rewrite <- (Sets_included_indexed_union ayz).
    reflexivity.
  + apply Sets_indexed_union_included.
    intros axy.
    rewrite Rels_concat_indexed_union_distr_l_aux.
    apply Sets_indexed_union_included.
    intros ayz.
    rewrite <- Rels_concat_assoc_aux.
    rewrite <- (Sets_included_indexed_union ayz).
    rewrite Rels_concat_indexed_union_distr_r_aux.
    rewrite <- (Sets_included_indexed_union axy).
    reflexivity.
Qed.

#[export] Instance Prop_PRE_RELS_LeftId
           (A X: Type)
           {_SETS: Sets.SETS X}
           {_SETS_Properties: SETS_Properties X}:
  PRE_RELS_LeftId A (A -> Prop) X.
Proof.
  constructor.
  intros; simpl.
  sets_unfold.
  reflexivity.
Qed.

#[export] Instance lift_PRE_RELS_LeftId
           (I1 I2 A X Y: Type)
           {_ACC: Rels.ACCUM I1 I2 I2}
           {_ACC_NIL: Rels.ACCUM_NIL I1}
           {_RELS: Rels.PRE_RELS A X Y Y}
           {_RELS_Id: Rels.PRE_RELS_ID A X}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y Y}
           {_ACC_LeftId: ACCUM_LeftId I1 I2}
           {_RELS_LeftId: PRE_RELS_LeftId A X Y}:
  PRE_RELS_LeftId A (I1 -> X) (I2 -> Y).
Proof.
  constructor.
  intros; simpl.
  sets_unfold.
  intros i2.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included; intros i1.
    apply Sets_indexed_union_included; intros i2'.
    apply Sets_prop_inj_included; intros.
    rewrite Rels_concat_prop_inj_intersect_r_aux.
    apply Sets_prop_inj_included; intros.
    rewrite H0, Rels_app_nil_l_setoid in H.
    rewrite Rels_concat_id_l_aux.
    rewrite H; reflexivity.
  + rewrite <- (Sets_included_indexed_union Rels.nil).
    rewrite <- (Sets_included_indexed_union i2).
    apply Sets_included_intersect.
    - apply Sets_included_prop_inj.
      apply Rels_app_nil_l_setoid.
    - rewrite Rels_concat_prop_inj_intersect_r_aux.
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; reflexivity.
      * rewrite Rels_concat_id_l_aux.
        reflexivity.
Qed.

#[export] Instance Prop_PRE_RELS_RightId
           (A: Type):
  PRE_RELS_RightId A (A -> Prop) (A -> Prop).
Proof.
  constructor.
  sets_unfold.
  simpl.
  sets_unfold.
  intros.
  split; intros.
  + destruct H as [? [? ?]]; subst; tauto.
  + eauto.
Qed.

#[export] Instance lift_PRE_RELS_RightId
           (I1 I2 A X Y: Type)
           {_ACC: Rels.ACCUM I1 I2 I1}
           {_ACC_NIL: Rels.ACCUM_NIL I2}
           {_RELS: Rels.PRE_RELS A X Y X}
           {_RELS_Id: Rels.PRE_RELS_ID A Y}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y X}
           {_ACC_LeftId: ACCUM_RightId I1 I2}
           {_RELS_LeftId: PRE_RELS_RightId A X Y}:
  PRE_RELS_RightId A (I1 -> X) (I2 -> Y).
Proof.
  constructor.
  intros; simpl.
  sets_unfold.
  intros i1.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included; intros a.
    apply Sets_indexed_union_included; intros i1'.
    apply Sets_indexed_union_included; intros i2.
    apply Sets_prop_inj_included; intros.
    rewrite Rels_concat_prop_inj_intersect_l_aux.
    apply Sets_prop_inj_included; intros.
    rewrite H0, Rels_app_nil_r_setoid in H.
    rewrite <- (Rels_concat_id_r_aux (x i1)).
    rewrite <- (Sets_included_indexed_union a).
    rewrite H; reflexivity.
  + rewrite <- (Rels_concat_id_r_aux (x i1)).
    apply Sets_indexed_union_included; intros a.
    rewrite <- (Sets_included_indexed_union a).
    rewrite <- (Sets_included_indexed_union i1).
    rewrite <- (Sets_included_indexed_union Rels.nil).
    apply Sets_included_intersect.
    - apply Sets_included_prop_inj.
      apply Rels_app_nil_r_setoid.
    - rewrite Rels_concat_prop_inj_intersect_l_aux.
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; reflexivity.
      * reflexivity.
Qed.

#[export] Instance Derived_RELS_LeftId
           (A X Y: Type)
           {_RELS: Rels.PRE_RELS A X Y Y}
           {_RELS_Id: Rels.PRE_RELS_ID A X}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y Y}
           {_RELS_LeftID: PRE_RELS_LeftId A X Y}:
  RELS_LeftId (A -> X) (A -> Y).
Proof.
  constructor.
  intros.
  simpl.
  sets_unfold.
  intros a.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included; intros b.
    rewrite Rels_concat_id_l_aux.
    apply Sets_prop_inj_included; intros.
    rewrite H; reflexivity.
  + rewrite <- (Sets_included_indexed_union a).
    rewrite Rels_concat_id_l_aux.
    apply Sets_included_intersect.
    - apply Sets_included_prop_inj.
      reflexivity.
    - reflexivity.
Qed.

#[export] Instance Derived_RELS_RightId
           (A X Y: Type)
           {_RELS: Rels.PRE_RELS A X Y X}
           {_RELS_Id: Rels.PRE_RELS_ID A Y}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y X}
           {_RELS_LeftID: PRE_RELS_RightId A X Y}:
  RELS_RightId (A -> X) (A -> Y).
Proof.
  constructor.
  intros.
  simpl.
  sets_unfold.
  intros a.
  rewrite <- (Rels_concat_id_r_aux (x a)).
  reflexivity.
Qed.

#[export] Instance Derived_RELS_TestSpec
           (A T: Type)
           {_REL_ID: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}:
  RELS_TestSpec A T.
Proof.
  constructor.
  intros.
  simpl.
  unfold Sets.filter1.
  reflexivity.
Qed.

#[export] Instance Rels_concat_congr
           {R S T: Type}
           {_REL: Rels.RELS R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: RELS_Properties R S T}
           {_SETS_Properties_R: SETS_Properties R}
           {_SETS_Properties_S: SETS_Properties S}
           {_SETS_Properties_T: SETS_Properties T}:
  Proper
    (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@Rels.concat _ _ _ _REL).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Rels_concat_mono.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
  + apply Rels_concat_mono.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
Qed.

Lemma Rels_concat_empty_r
           {R S T : Type}
           {_REL: Rels.RELS R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: RELS_Properties R S T}
           {_SETS_Properties_R: SETS_Properties R}
           {_SETS_Properties_S: SETS_Properties S}
           {_SETS_Properties_T: SETS_Properties T}:
  forall x : R,
  (Rels.concat x Sets.empty) == Sets.empty.
Proof.
  intros.
  rewrite <- Sets_empty_general_union.
  rewrite Rels_concat_general_union_distr_l.
  apply Sets_equiv_empty_fact.
  apply Sets_general_union_included.
  intros.
  destruct H as [? [? ?] ].
  contradiction.
Qed.

Lemma Rels_concat_empty_l
           {R S T : Type}
           {_REL: Rels.RELS R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: RELS_Properties R S T}
           {_SETS_Properties_R: SETS_Properties R}
           {_SETS_Properties_S: SETS_Properties S}
           {_SETS_Properties_T: SETS_Properties T}:
  forall x : S,
  (Rels.concat Sets.empty x) == Sets.empty.
Proof.
  intros.
  rewrite <- Sets_empty_general_union.
  rewrite Rels_concat_general_union_distr_r.
  apply Sets_equiv_empty_fact.
  apply Sets_general_union_included.
  intros.
  destruct H as [? [? ?] ].
  contradiction.
Qed.

#[export] Instance Rels_test_congr
           {A T: Type}
           {_REL: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}
           {_SETS_Properties_T: SETS_Properties T}
           {_RELS_TestSpec: RELS_TestSpec A T}:
  Proper (Sets.equiv ==> Sets.equiv)
    (@Rels.test (A -> Prop) (A -> T) _).
Proof.
  unfold Proper, respectful.
  intros.
  pose proof (@Rels_test_spec A T _ _SETS_T _RELS_TestSpec x).
  eapply Sets_equiv_trans.
  + apply H0.
  + apply Sets_equiv_sym.
    rewrite H.
    apply Rels_test_spec.
Qed.

Lemma Rels_test_empty
           {A T: Type}
           {_REL: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}
           {_SETS_Properties_T: SETS_Properties T}
           {_RELS_TestSpec: RELS_TestSpec A T}:
  @Rels.test (A -> Prop) (A -> T) _ ∅ == ∅.
Proof.
  rewrite Rels_test_spec.
  change (Sets.test1 ∅) with (@Sets.lift1 A T _ (Sets.prop_inj False)).
  rewrite Sets_prop_inj_empty.
  change (Sets.lift1 ∅) with (@Sets.empty (A -> T) _).
  rewrite Sets_empty_intersect.
  reflexivity.
Qed.

Lemma Rels_test_is_empty
           {A T: Type}
           {_REL: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}
           {_SETS_Properties_T: SETS_Properties T}
           {_RELS_TestSpec: RELS_TestSpec A T}:
  forall x,
    x == ∅ ->
    @Rels.test (A -> Prop) (A -> T) _ x == ∅.
Proof.
  intros.
  rewrite H.
  apply Rels_test_empty.
Qed.

Lemma Rels_test_full
           {A T: Type}
           {_REL: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}
           {_SETS_Properties_T: SETS_Properties T}
           {_RELS_TestSpec: RELS_TestSpec A T}:
  @Rels.test (A -> Prop) (A -> T) _ Sets.full == Rels.id.
Proof.
  rewrite Rels_test_spec.
  change (Sets.test1 Sets.full)
    with (@Sets.lift1 A T _ (Sets.prop_inj True)).
  rewrite Sets_prop_inj_full.
  change (Sets.lift1 Sets.full) with (@Sets.full (A -> T) _).
  rewrite Sets_full_intersect.
  reflexivity.
Qed.

Lemma Rels_test_is_id
           {A T: Type}
           {_REL: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}
           {_SETS_Properties_T: SETS_Properties T}
           {_RELS_TestSpec: RELS_TestSpec A T}:
  forall x,
    x == Sets.full ->
    @Rels.test (A -> Prop) (A -> T) _ x == Rels.id.
Proof.
  intros.
  rewrite H, Rels_test_full.
  reflexivity.
Qed.

Ltac ACC_simplify T :=
  match T with
  | @Rels.nil ?I ?_ACC =>
    let _ACC' := eval hnf in _ACC in
    let op := eval cbv delta [Rels.nil] in @Rels.nil in
    let T' := eval cbv beta zeta iota in (op I _ACC') in
    constr:(T')
  | @Rels.app ?I1 ?I2 ?I ?_ACC =>
    let _ACC' := eval hnf in _ACC in
    let op := eval cbv delta [Rels.app] in @Rels.app in
    let T' := eval cbv beta zeta iota in (op I1 I2 I _ACC') in
    constr:(T')
  end.

Ltac RELS_unfold1 RELS :=
  match RELS with
  | lift_PRE_RELS _ _ _ _ _ _ _ =>
      let p := eval unfold lift_PRE_RELS at 1 in RELS in
      constr:(p)
  | Prop_PRE_RELS _ _ =>
      let p := eval unfold Prop_PRE_RELS in RELS in
      constr:(p)
  | Derived_RELS _ _ _ _ _ =>
      let p := eval unfold Derived_RELS in RELS in
      constr:(p)
  | lift_PRE_RELS_ID _ _ _ =>
      let p := eval unfold lift_PRE_RELS_ID at 1 in RELS in
      constr:(p)
  | Prop_PRE_RELS_ID _ =>
      let p := eval unfold Prop_PRE_RELS_ID in RELS in
      constr:(p)
  | Derived_RELS_ID _ _ =>
      let p := eval unfold Derived_RELS_ID in RELS in
      constr:(p)
  | Derived_RELS_TEST _ _ =>
      let p := eval unfold Derived_RELS_TEST in RELS in
      constr:(p)
  end.

Ltac RELS_simplify T :=
  match T with
    | @Rels.concat ?R0 ?S0 ?T0 ?RELS =>
      let op1 := eval cbv delta [Rels.concat] in (@Rels.concat) in
      let RELS1 := RELS_unfold1 RELS in
      let T1 := eval cbv beta zeta iota in (op1 R0 S0 T0 RELS1) in
      constr:(T1)
    | @Rels.concat_aux ?A ?R0 ?S0 ?T0 ?RELS =>
      let op1 := eval cbv delta [Rels.concat_aux] in (@Rels.concat_aux) in
      let RELS1 := RELS_unfold1 RELS in
      let T1 := eval cbv beta zeta iota in (op1 A R0 S0 T0 RELS1) in
      constr:(T1)
    | @Rels.id ?R0 ?RELS =>
      let op1 := eval cbv delta [Rels.id] in (@Rels.id) in
      let RELS1 := RELS_unfold1 RELS in
      let T1 := eval cbv beta zeta iota in (op1 R0 RELS1) in
      constr:(T1)
    | @Rels.test ?S0 ?R0 ?RELS =>
      let op1 := eval cbv delta [Rels.test] in (@Rels.test) in
      let RELS1 := RELS_unfold1 RELS in
      let T1 := eval cbv beta zeta iota in (op1 S0 R0 RELS1) in
      constr:(T1)
    | @Rels.id_aux ?A ?R0 ?RELS =>
      let op1 := eval cbv delta [Rels.id_aux] in (@Rels.id_aux) in
      let RELS1 := RELS_unfold1 RELS in
      let T1 := eval cbv beta zeta iota in (op1 A R0 RELS1) in
      constr:(T1)
    | _ => constr:(T)
    end.

Ltac RELS_simplify_rec T :=
  match T with
  | context G [@Rels.concat ?R0 ?S0 ?T0 ?RELS] =>
         let S := RELS_simplify (@Rels.concat R0 S0 T0 RELS) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | context G [@Rels.concat_aux ?A ?R0 ?S0 ?T0 ?RELS] =>
         let S := RELS_simplify (@Rels.concat_aux A R0 S0 T0 RELS) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | context G [@Rels.id ?R0 ?RELS] =>
         let S := RELS_simplify (@Rels.id R0 RELS) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | context G [@Rels.test ?S0 ?R0 ?RELS] =>
         let S := RELS_simplify (@Rels.test S0 R0 RELS) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | context G [@Rels.id_aux ?A ?R0 ?RELS] =>
         let S := RELS_simplify (@Rels.id_aux A R0 RELS) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | context G [@Rels.nil ?I ?ACC] =>
         let S := ACC_simplify (@Rels.nil I ACC) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | context G [@Rels.app ?I1 ?I2 ?I ?ACC] =>
         let S := ACC_simplify (@Rels.app I1 I2 I ACC) in
         let T1 := context G [S] in
         let T2 := SIMPLIFY_TAC T1 in
         constr:(T2)
  | _ =>
         let T1 := SETS_PROD_simplify_rec T in
         constr:(T1)
  end.

Ltac RELS_inner_pattern1 tac T :=
  match T with
  | @Rels.concat ?R0 ?S0 ?T0 ?RELS =>
         let ret := constr:(@Rels.concat R0 S0 T0 RELS) in
         let ret' := tac ret in ret'
  | @Rels.id ?R0 ?RELS =>
         let ret := constr:(@Rels.id R0 RELS) in
         let ret' := tac ret in ret'
  | @Rels.test ?S0 ?R0 ?RELS =>
         let ret := constr:(@Rels.test S0 R0 RELS) in
         let ret' := tac ret in ret'
  | _ =>
         let RET := SETS_inner_pattern1 tac T in
         constr:(RET)
  end.

Ltac SIMPLIFY_TAC T ::= RELS_simplify_rec T.

Ltac PATTERN1_INNER_TAC tac T ::= RELS_inner_pattern1 tac T.

Ltac add_MarkerWrapper_rec T :=
  match T with
  | context G [@Rels.id ?R ?_RELS] =>
      let S := constr:(MarkerWrapper0 (@Rels.id R) _RELS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Rels.test ?R ?S ?_RELS] =>
      let S := constr:(MarkerWrapper1 (@Rels.test R S) _RELS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Rels.concat ?R ?S ?T ?_RELS] =>
      let S := constr:(MarkerWrapper2 (@Rels.concat R S T) _RELS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | _ =>
      let T1 := SetProd.add_MarkerWrapper_rec T in
      constr:(T1)
  end.

Ltac ADD_MARKER_WRAPPER_TAC ::= add_MarkerWrapper_rec.

Fixpoint nsteps
           {X: Type}
           {_RELS: Rels.RELS X X X}
           {_RELS_Id: Rels.RELS_ID X}
           (x: X) (n: nat): X :=
  match n with
  | O => Rels.id
  | S n' => Rels.concat x (nsteps x n')
  end.

Definition clos_refl_trans
             {X: Type}
             {_RELS: Rels.RELS X X X}
             {_RELS_Id: Rels.RELS_ID X}
             {_SETS: Sets.SETS X}
             (x: X): X :=
  Sets.indexed_union (nsteps x).

Lemma nsteps_n_m:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X) (n m: nat),
    Sets.equiv
      (Rels.concat (nsteps x n) (nsteps x m))
      (nsteps x (n + m)%nat).
Proof.
  intros.
  induction n; simpl.
  + apply Rels_concat_id_l.
  + rewrite Rels_concat_assoc.
    rewrite IHn.
    reflexivity.
Qed.

Fixpoint nsteps'
           {X: Type}
           {_RELS: Rels.RELS X X X}
           {_RELS_Id: Rels.RELS_ID X}
           (x: X) (n: nat): X :=
  match n with
  | O => Rels.id
  | S n' => Rels.concat (nsteps' x n') x
  end.

Lemma nsteps_nsteps':
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_RELS_RightId: RELS_RightId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X) (n: nat),
    Sets.equiv
      (nsteps x n)
      (nsteps' x n).
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite <- IHn.
    rewrite <- (Rels_concat_id_r x) at 1 4.
    pose proof nsteps_n_m x 1 n.
    pose proof nsteps_n_m x n 1.
    simpl (nsteps x 1) in H, H0.
    rewrite H, H0.
    rewrite PeanoNat.Nat.add_comm.
    reflexivity.
Qed.

Lemma nsteps_nsteps'_indexed_union:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_RELS_RightId: RELS_RightId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X),
      Sets.equiv
      (Sets.indexed_union (nsteps x))
      (Sets.indexed_union (nsteps' x)).
Proof.
  intros.
  apply Sets_indexed_union_congr.
  sets_unfold.
  apply nsteps_nsteps'.
Qed.

Lemma nsteps_rt:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_SETS_Properties: SETS_Properties X}
    (x: X) (n: nat),
    Sets.included (nsteps x n) (clos_refl_trans x).
Proof. intros. apply Sets_included_indexed_union. Qed.

Lemma nsteps'_rt:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_RELS_RightId: RELS_RightId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X) (n: nat),
    Sets.included (nsteps' x n) (clos_refl_trans x).
Proof.
  intros.
  rewrite <- nsteps_nsteps'.
  apply Sets_included_indexed_union.
Qed.

Lemma rt_trans:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X),
    Sets.included
      (Rels.concat (clos_refl_trans x) (clos_refl_trans x))
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  rewrite Rels_concat_indexed_union_distr_r.
  apply Sets_indexed_union_included; intros n.
  rewrite Rels_concat_indexed_union_distr_l.
  apply Sets_indexed_union_included; intros m.
  rewrite <- (Sets_included_indexed_union (n + m)).
  rewrite nsteps_n_m.
  reflexivity.
Qed.

Lemma rt_trans_1n:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X),
    Sets.included
      (Rels.concat x (clos_refl_trans x))
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  rewrite Rels_concat_indexed_union_distr_l.
  apply Sets_indexed_union_included; intros m.
  rewrite <- (Sets_included_indexed_union (1 + m)).
  rewrite <- nsteps_n_m.
  simpl.
  rewrite Rels_concat_assoc.
  rewrite Rels_concat_id_l.
  reflexivity.
Qed.

Lemma rt_trans_n1:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_RELS_RightId: RELS_RightId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X),
    Sets.included
      (Rels.concat (clos_refl_trans x) x)
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  rewrite Rels_concat_indexed_union_distr_r.
  apply Sets_indexed_union_included; intros n.
  rewrite <- (Sets_included_indexed_union (n + 1)).
  rewrite <- nsteps_n_m.
  simpl.
  rewrite Rels_concat_id_r.
  reflexivity.
Qed.

#[export] Instance rt2_refl_ins A (R: A -> A -> Prop):
  Reflexive (clos_refl_trans R).
Proof.
  exists 0.
  hnf.
  reflexivity.
Qed.

#[export] Instance rt2_trans_ins A (R: A -> A -> Prop):
  Transitive (clos_refl_trans R).
Proof.
  hnf; intros.
  destruct H as [n ?], H0 as [n0 ?].
  exists (n + n0).
  pose proof nsteps_n_m R n n0.
  sets_unfold in H1.
  specialize (H1 x z).
  apply H1; clear H1.
  exists y; split; auto.
Qed.

Ltac get_head_explicit_rt_rec x :=
  match x with
  | @clos_refl_trans _ _ _ _ _ =>
      constr:((x, true))
  | ?y ?z =>
      let res := get_head_explicit_rt_rec y in
      match res with
      | (?x', true) =>
          constr:((x', true))
      | (?y', false) =>
          let x' := eval cbv beta in (y' z) in
           match x' with
           | @clos_refl_trans _ _ _ _ _ => constr:((x', true))
           | _ => constr:((x', false))
           end
      end
  | _ => let x' := eval cbv delta [x] in x in
         match x' with
         | @clos_refl_trans _ _ _ _ _ => constr:((x', true))
         | _ => constr:((x', false))
         end
  end.

Ltac get_head_implicit_rt_rec x :=
  match x with
  | @clos_refl_trans _ _ _ _ _ =>
      constr:((x, true))
  | ?y ?z =>
      let res := get_head_implicit_rt_rec y in
      match res with
      | (?x', true) =>
          constr:((x', true))
      | (?y', false) =>
          let x' := eval cbv beta in (y' z) in
           match x' with
           | @clos_refl_trans _ _ _ _ _ => constr:((x, true))
           | _ => constr:((x', false))
           end
      end
  | _ => let x' := eval cbv delta [x] in x in
         match x' with
         | @clos_refl_trans _ _ _ _ _ => constr:((x, true))
         | _ => constr:((x', false))
         end
  end.

Ltac get_head_explicit_rt x :=
  let res := get_head_explicit_rt_rec x in
  match res with
  | (?x', true) => constr:(x')
  end.

Ltac get_head_implicit_rt x :=
  let res := get_head_implicit_rt_rec x in
  match res with
  | (?x', true) => constr:(x')
  end.

Ltac transitivity_General :=
  match goal with
  | |- ?P => let R := get_head_explicit_rt P in
             let R' := get_head_implicit_rt P in
             match R with
             | @clos_refl_trans _ ?_RELS _ _ ?R0 =>
               let H := constr:(rt_trans R0) in
               apply H;
               match goal with
               | |- context[Rels.concat R R] =>
                 change (Rels.concat R R) with (Rels.concat R' R')
               end;
               pattern (@Rels.concat _ _ _ _RELS);
               match goal with
               | |- ?P0 (@Rels.concat _ _ _ _RELS) =>
                 let Pname := fresh "P" in
                 set (Pname := P0);
                 sets_unfold;
                 unfold Pname; clear Pname
               end
             end
  end.

Ltac transitivity_1n_General :=
  match goal with
  | |- ?P => let R := get_head_explicit_rt P in
             let R' := get_head_implicit_rt P in
             match R with
             | @clos_refl_trans _ ?_RELS _ _ ?R0 =>
               let H := constr:(rt_trans_1n R0) in
               apply H;
               match goal with
               | |- context[Rels.concat ?R1 R] =>
                 change (Rels.concat R1 R) with (Rels.concat R1 R')
               end;
               pattern (@Rels.concat _ _ _ _RELS);
               match goal with
               | |- ?P0 (@Rels.concat _ _ _ _RELS) =>
                 let Pname := fresh "P" in
                 set (Pname := P0);
                 sets_unfold;
                 unfold Pname; clear Pname
               end
             end
  end.

Ltac transitivity_n1_General :=
  match goal with
  | |- ?P => let R := get_head_explicit_rt P in
             let R' := get_head_implicit_rt P in
             match R with
             | @clos_refl_trans _ ?_RELS _ _ ?R0 =>
               let H := constr:(rt_trans_n1 R0) in
               apply H;
               match goal with
               | |- context[Rels.concat R ?R1] =>
                 change (Rels.concat R R1) with (Rels.concat R' R1)
               end;
               pattern (@Rels.concat _ _ _ _RELS);
               match goal with
               | |- ?P0 (@Rels.concat _ _ _ _RELS) =>
                 let Pname := fresh "P" in
                 set (Pname := P0);
                 sets_unfold;
                 unfold Pname; clear Pname
               end
             end
  end.

Tactic Notation "transitivity_nn" uconstr(x) :=
  transitivity_General;
  exists x;
  match goal with
  | |-  _ /\ _ => split
  end.

Tactic Notation "transitivity_nn" uconstr(x) uconstr(y1) uconstr(y2) :=
  transitivity_General;
  exists x, y1, y2;
  match goal with
  | |-  _ /\ _ /\ _ => split; [| split]
  end.

Tactic Notation "etransitivity_nn" :=
  first
    [ transitivity_General;
      eexists;
      match goal with
      | |-  _ /\ _ => split
      end
    | transitivity_General;
      do 3 eexists;
      match goal with
      | |-  _ /\ _ /\ _ => split; [| split]
      end ].

Tactic Notation "transitivity_1n" uconstr(x) :=
  transitivity_1n_General;
  exists x;
  match goal with
  | |-  _ /\ _ => split
  end.

Tactic Notation "transitivity_1n" uconstr(x) uconstr(y1) uconstr(y2) :=
  transitivity_1n_General;
  exists x, y1, y2;
  match goal with
  | |-  _ /\ _ /\ _ => split; [| split]
  end.

Tactic Notation "etransitivity_1n" :=
  first
    [ transitivity_1n_General;
      eexists;
      match goal with
      | |-  _ /\ _ => split
      end
    | transitivity_1n_General;
      do 3 eexists;
      match goal with
      | |-  _ /\ _ /\ _ => split; [| split]
      end ].

Tactic Notation "transitivity_n1" uconstr(x) :=
  transitivity_n1_General;
  exists x;
  match goal with
  | |-  _ /\ _ => split
  end.

Tactic Notation "transitivity_n1" uconstr(x) uconstr(y1) uconstr(y2) :=
  transitivity_n1_General;
  exists x, y1, y2;
  match goal with
  | |-  _ /\ _ /\ _ => split; [| split]
  end.

Tactic Notation "etransitivity_n1" :=
  first
    [ transitivity_n1_General;
      eexists;
      match goal with
      | |-  _ /\ _ => split
      end
    | transitivity_n1_General;
      do 3 eexists;
      match goal with
      | |-  _ /\ _ /\ _ => split; [| split]
      end ].

Ltac get_head X :=
  match X with
  | ?y ?z => get_head y
  | _ => constr:(X)
  end.

Ltac count_args X :=
  match X with
  | ?y ?z => let n := count_args y in constr:(S n)
  | _ => constr:(O)
  end.

Ltac revert_standard_prop H :=
  let H0 := type of H in
  let T := type of H0 in
  match T with 
  | Prop => idtac
  | _ => fail
  end.

Ltac revert_dependent_except x H :=
  repeat
    match goal with
    | H0: context [x] |- _ => 
      tryif (revert_standard_prop H0) then 
        revert H0; assert_succeeds (revert H)
      else 
        fail
    end.

Ltac revert_dependent_component x H :=
  first
  [
    is_var x;
    revert_dependent_except x H
  |
    match x with
    | ?y ?z => match type of y with
               | _ -> _ => revert_dependent_component y H;
                           revert_dependent_component z H
               | _ => idtac
               end
    | _ => idtac
    end
  ].

Ltac revert_component x :=
  first
  [
    is_var x;
    revert x
  |
    match x with
    | ?y ?z => match type of y with
               | _ -> _ => revert_component y; revert_component z
               | _ => idtac
               end
    | _ => idtac
    end
  ].

Ltac specialize_until_EQ H :=
  match type of H with
  | ?P -> ?Q => specialize (H eq_refl)
  | forall _:?A, _ => let a := fresh "a" in
                      evar (a: A);
                      specialize (H a);
                      subst a;
                      specialize_until_EQ H
  end.

Ltac intros_and_subst P :=
  match goal with
  | |- P => idtac
  | |- ?x = _ -> _ => is_var x;
                      let H := fresh "H" in
                      intros H;
                      revert P;
                      try rewrite -> H in *;
                      intro P;
                      clear x H;
                      intros_and_subst P
  | |- _ = ?x -> _ => is_var x;
                      let H := fresh "H" in
                      intros H;
                      revert P;
                      try rewrite <- H in *;
                      intro P;
                      clear x H;
                      intros_and_subst P
  end.

Ltac injection_and_subst H :=
  match goal with
  | |- ?P =>
      let P_name := fresh "P" in
      set (P_name := P);
      first [ injection H; clear H; intros_and_subst P_name
            | revert H; intros_and_subst P_name ];
      subst P_name
  end.

Ltac intros_until_EQ_and_subst :=
  match goal with
  | |- _ = _ -> _ => let H := fresh in intros H; injection_and_subst H
  | _ => intro; intros_until_EQ_and_subst
  end.

Ltac revert_args_until_head x head H :=
  match x with
  | head => idtac
  | ?y ?z => revert_dependent_component z H; revert_args_until_head y head H
  end.

Ltac revert_EQ_until_head x head H :=
  match x with
  | head => idtac
  | ?y ?z => let a := fresh "a" in
             let EQ := fresh "EQ" in
             remember z as a eqn:EQ;
             revert EQ;
             revert_component z;
             revert_EQ_until_head y head H
  end.

Ltac nested_pattern X Q :=
  match X with
  | ?y ?z => let Q' := eval pattern z in Q in
             match Q' with
             | ?R z => let R' := nested_pattern y R in
                       constr:(R' z)
             end
  | _ => constr:(Q)
  end.

Ltac reduce_to_included R P Q :=
  match P with
  | R => change (Sets.included P Q)
  | ?P0 ?x => let Q' := eval pattern x in Q in
              match Q' with
              | ?Q0 x =>
                  change Q with (Q0 x);
                  revert x;
                  reduce_to_included R P0 Q0
              end
  end.

Ltac intros_for_included _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 => intros ?; intros_for_included _SETS0
  | _ => idtac
  end.

Ltac intros_EQs n :=
  match n with
  | S ?n0 => intros_until_EQ_and_subst; intros_EQs n0
  | _ => idtac
  end.

Ltac intros_EQ_based_SETS _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 =>
      intros_until_EQ_and_subst;
      intros_EQ_based_SETS _SETS0
  | _ =>
      idtac
  end.

Ltac specialize_EQs H n :=
  match n with
  | S ?n0 =>
      specialize_until_EQ H;
      specialize_EQs H n0
  | _ => idtac
  end.

Ltac specialize_until_EQ_based_SETS H _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 =>
      specialize_until_EQ H;
      specialize_until_EQ_based_SETS H _SETS0
  | _ => idtac
  end.

Ltac unfold_included_and_intros_in_goal :=
  match goal with
  | |- @Sets.included ?X ?_SETS ?x ?y =>
         let P_name := fresh "P" in
         set (P_name := fun R => R x y: Prop);
         change (P_name (@Sets.included X _SETS));
         unfold_SETS_in_goal_tac;
         unfold P_name;
         clear P_name;
         intros_for_included _SETS
  end.

Ltac destruct_Rels_id H :=
  match type of H with
  | ?x = _ /\ _ => let HH := fresh "H" in
              destruct H as [HH H];
              subst x;
              destruct_Rels_id H
  | _ => injection_and_subst H
  end.

Definition destruct_into_unnames_pred {A: Type} (a b: A): Prop := True.

Ltac destruct_into_unnames H :=
  match type of H with
  | destruct_into_unnames_pred ?x ?pat =>
      is_var pat; let x' := fresh "___unnamed" in rename x into x'; clear H
  | destruct_into_unnames_pred ?x ?x =>
      clear H
  | destruct_into_unnames_pred ?x (_ _) =>
      is_var x;
      destruct x;
      destruct_into_unnames H
  | destruct_into_unnames_pred (?y ?z) (?pat_y ?pat_z) =>
      let Hy := fresh "H" in
      let Hz := fresh "H" in
      assert (destruct_into_unnames_pred y pat_y) as Hy by (exact I);
      assert (destruct_into_unnames_pred z pat_z) as Hz by (exact I);
      destruct_into_unnames Hy;
      destruct_into_unnames Hz;
      clear H
  end.

Ltac rename_by_pat x pat :=
  match x with
  | ?y ?z =>
      match pat with
      | ?pat_y ?pat_z =>
          rename_by_pat y pat_y;
          rename_by_pat z pat_z
      end
  | pat => idtac
  | _ => is_var x; let x' := fresh pat in rename x into x'
  end.

Ltac destruct_using_pat_names x pat :=
  let H := fresh "H" in
  let H0 := fresh "H" in
  assert (destruct_into_unnames_pred x pat) as H by (exact I);
  assert (destruct_into_unnames_pred x pat) as H0 by (exact I);
  destruct_into_unnames H;
  match type of H0 with
  | destruct_into_unnames_pred ?x' pat => rename_by_pat x' pat
  end;
  clear H0.

Ltac destruct_1n_based_SETS_rec H _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 =>
      match _SETS0 with
      | @lift_SETS _ _ _ =>
          destruct H as [? [? H]];
          let HH := fresh "H" in
          destruct H as [HH H];
          destruct_1n_based_SETS_rec H _SETS0
      | _ =>
          let HH := fresh "H" in
          destruct H as [HH H]
      end
  end.

Ltac destruct_1n_based_SETS H _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 => destruct_1n_based_SETS_rec H _SETS0
  end.

Ltac induction_1n H :=
  let P := type of H in
  revert_dependent_component P H;
  let R := get_head_explicit_rt P in
  let R' := get_head_implicit_rt P in
  match R with
  | @clos_refl_trans ?X ?_RELS ?_RELS_ID ?_SETS ?R0 =>
            change R' with (@Sets.indexed_union _ _SETS nat (@nsteps X _RELS _RELS_ID R0)) in H at 1;
            revert_args_until_head P R' H;
            revert_EQ_until_head P R' H;
            revert H;
            match goal with
            | |- ?Pre -> ?Post => reduce_to_included (@Sets.indexed_union _ _SETS nat (@nsteps X _RELS _RELS_ID R0)) Pre Post
            end;
            apply Sets_indexed_union_included;
            let n := fresh "n" in
            let IH := fresh "IH" in
            let IHrt := fresh "IHrt" in
            intros n; induction n as [| n IH];
            [ unfold_included_and_intros_in_goal;
              intro H;
              change (@nsteps X _RELS _RELS_ID R0 0) with (@Rels.id X _RELS_ID) in H;
              intros_EQ_based_SETS _SETS;
              revert H; sets_unfold;
              intro H; destruct_Rels_id H; intros
            | unfold_included_and_intros_in_goal;
              intro H;
              change (@nsteps X _RELS _RELS_ID R0 (S n)) with
                     (@Rels.concat X X X _RELS R0 (@nsteps X _RELS _RELS_ID R0 n)) in H;
              intros_EQ_based_SETS _SETS;
              match type of H with
              | context [(@Rels.concat X X X _RELS R0 (@nsteps X _RELS _RELS_ID R0 n)) ?s1] =>
                  revert H; sets_unfold;
                  let s1' := fresh "___unnamed" in
                  intros H;
                  destruct H as [s1' H];
                  destruct_using_pat_names s1' s1
              end;
              intros;
              destruct_1n_based_SETS H _SETS;
              pose proof H as IHrt;
              apply IH in IHrt;
              clear IH;
              let NSTEPS_RT := constr:(nsteps_rt R0 n) in
              apply NSTEPS_RT in H;
              change R with R' in H;
              specialize_until_EQ_based_SETS IHrt _SETS
            ]
          end.

Ltac destruct_n1_based_SETS_rec H _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 =>
      match _SETS0 with
      | @lift_SETS _ _ _ =>
          destruct H as [[H ?] ?];
          let HH := fresh "H" in
          destruct H as [H HH];
          destruct_n1_based_SETS_rec H _SETS0
      | _ =>
          let HH := fresh "H" in
          destruct H as [H HH]
      end
  end.

Ltac destruct_n1_based_SETS H _SETS :=
  match _SETS with
  | @lift_SETS _ _ ?_SETS0 => destruct_n1_based_SETS_rec H _SETS0
  end.
  
Ltac induction_n1 H :=
  let P := type of H in
  revert_dependent_component P H;
  let R := get_head_explicit_rt P in
  let R' := get_head_implicit_rt P in
  match R with
  | @clos_refl_trans ?X ?_RELS ?_RELS_ID ?_SETS ?R0 => 
            change R' with (@Sets.indexed_union _ _SETS nat (@nsteps X _RELS _RELS_ID R0)) in H at 1;
            let HH := fresh "HH" in
            pose proof (@nsteps_nsteps'_indexed_union X _RELS _ _ _ _ _ _ _) as HH; 
            apply HH in H; clear HH;
            revert_args_until_head P R' H ;
            revert_EQ_until_head P R' H ;
            revert H;
            match goal with 
            | |- ?Pre -> ?Post => reduce_to_included (@Sets.indexed_union _ _SETS nat (@nsteps' X _RELS _RELS_ID R0)) Pre Post
            end;
            apply Sets_indexed_union_included;
            let n := fresh "n" in
            let IH := fresh "IH" in
            let IHrt := fresh "IHrt" in
            intros n; induction n as [| n IH];
            [ unfold_included_and_intros_in_goal;
              intro H;
              change (@nsteps' X _RELS _RELS_ID R0 0) with (@Rels.id X _RELS_ID) in H;
              intros_EQ_based_SETS _SETS;
              revert H; sets_unfold;
              intro H; destruct_Rels_id H; intros
            | 
              unfold_included_and_intros_in_goal;
              intro H;
              change (@nsteps' X _RELS _RELS_ID R0 (S n)) with
                      (@Rels.concat X X X _RELS (@nsteps' X _RELS _RELS_ID R0 n) R0) in H;
              intros_EQ_based_SETS _SETS;
              match type of H with
              | context [(@Rels.concat X X X _RELS (@nsteps' X _RELS _RELS_ID R0 n)) R0 ?s1] =>
                  revert H; sets_unfold;
                  let s1' := fresh "___unnamed" in
                  intros H;
                  destruct H as [s1' H];
                  destruct_using_pat_names s1' s1
              end;
              intros;
              destruct_n1_based_SETS H _SETS;
              pose proof H as IHrt;
              apply IH in IHrt;
              clear IH;
              let NSTEPS'_RT := constr:(nsteps'_rt R0 n) in
              apply NSTEPS'_RT in H;
              change R with R' in H;
              specialize_until_EQ_based_SETS IHrt _SETS 
            ]
          end.

Ltac proof_induction H :=
  let P := type of H in
  revert_dependent_component P H;
  let R' := get_head P in
  let n := count_args P in
  revert_args_until_head P R' H;
  revert_EQ_until_head P R' H;
  let GP := fresh "G" in
  match goal with
  | |- ?G => let P' := type of H in
             let G' := nested_pattern P' G in
             let Pr := get_head G' in
             change G';
             set (GP := Pr)
  end;
  induction H;
  repeat
  match goal with
  | H0: context [GP] |- _ =>
      unfold GP in H0;
      specialize_EQs H0 n
  end;
  unfold GP; clear GP; intros_EQs n; intros.

Module ListConn.

Import List.

#[export] Instance list_ACC A: Rels.ACCUM (list A) (list A) (list A) :=
  {|
    Rels.app := @app _;
  |}.

#[export] Instance list_ACC_Nil A: Rels.ACCUM_NIL (list A) :=
  {|
    Rels.nil := @nil _;
  |}.

#[export] Instance list_ACC_LeftId A: ACCUM_LeftId (list A) (list A).
Proof.
  constructor.
  intros.
  apply app_nil_l.
Qed.

#[export] Instance list_ACC_RightId A: ACCUM_RightId (list A) (list A).
Proof.
  constructor.
  intros.
  apply app_nil_r.
Qed.

#[export] Instance list_ACC_Assoc A: ACCUM_Assoc (list A) (list A) (list A) (list A) (list A) (list A).
Proof.
  constructor.
  intros.
  symmetry.
  apply app_assoc.
Qed.

Goal forall X: nat -> list nat -> nat -> Prop,
  Sets.equiv (Rels.concat X X) X.
Abort.

Parameter X :nat * nat -> list nat -> nat * nat -> Prop.

Definition msteps := clos_refl_trans X.

Goal forall a1 a2 l b1 b2,
  X (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  transitivity_n1 (a1, a2) nil l.
Abort.

Goal forall a1 a2 l b1 b2,
  X (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  transitivity_1n (a1, a2) nil l.
Abort.

Goal forall a1 a2 l b1 b2,
  X (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  transitivity_nn (a1, a2) nil l.
Abort.

Goal forall s1 t1 l s2 t2,
  s1 > 0 ->
  t1 > 2 ->
  s2 > 4 ->
  t2 > 10 ->
  msteps (s1, t1) l (s2, t2) ->
  False.
Proof.
  intros.
  induction_1n H3.
Abort.

End ListConn.

Module NatFuncConn.

Import List ListConn.

Definition natfunc_cons {A: Type} (a: A) (l: nat -> A): nat -> A :=
  fun n =>
    match n with
    | O => a
    | S n' => l n'
    end.

Definition natfunc_app {A: Type} (l1: list A) (l2: nat -> A): nat -> A :=
  (fix app (l1: list A): nat -> A :=
    match l1 with
    | nil => l2
    | a :: l1' => natfunc_cons a (app l1')
    end) l1.

Lemma app_natfunc_app: forall {A} (l1 l2: list A) (l3: nat -> A),
  natfunc_app l1 (natfunc_app l2 l3) = natfunc_app (l1 ++ l2) l3.
Proof.
  intros.
  induction l1.
  + simpl.
    unfold natfunc_app.
    reflexivity.
  + simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma natfunc_app_nil_l: forall {A} (l: nat -> A),
  natfunc_app nil l = l.
Proof.
  intros.
  reflexivity.
Qed.

#[export] Instance natfunc_ACC A: Rels.ACCUM (list A) (nat -> A) (nat -> A) :=
  {|
    Rels.app := @natfunc_app _;
  |}.

#[export] Instance natfunc_ACC_Nil A: Rels.ACCUM_NIL (list A) :=
  {|
    Rels.nil := @nil _;
  |}.

#[export] Instance natfunc_ACC_LeftId A: ACCUM_LeftId (list A) (nat -> A).
Proof.
  constructor.
  intros.
  apply natfunc_app_nil_l.
Qed.

#[export] Instance natfunc_ACC_Assoc A: ACCUM_Assoc (list A) (list A) (nat -> A) (list A) (nat -> A) (nat -> A).
Proof.
  constructor.
  intros.
  symmetry.
  apply app_natfunc_app.
Qed.

Goal forall (X: nat -> list nat -> nat -> Prop) (Y: nat -> (nat -> nat) -> Prop),
  Sets.equiv (Rels.concat X Y) Y.
Proof.
  intros.
  sets_unfold.
  intros s l.
Abort.

End NatFuncConn.

Module StreamConn.

Import List ListConn Streams.

Search Stream list.

Definition stream_app {A: Type} (l1: list A) (l2: Stream A): Stream A :=
  (fix app (l1: list A): Stream A :=
    match l1 with
    | nil => l2
    | a :: l1' => Cons a (app l1')
    end) l1.

Lemma app_stream_app: forall {A} (l1 l2: list A) (l3: Stream A),
  stream_app l1 (stream_app l2 l3) = stream_app (l1 ++ l2) l3.
Proof.
  intros.
  induction l1.
  + simpl.
    unfold stream_app.
    reflexivity.
  + simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma stream_app_nil_l: forall {A} (l: Stream A),
  stream_app nil l = l.
Proof.
  intros.
  reflexivity.
Qed.

#[export] Instance stream_ACC A: Rels.ACCUM (list A) (Stream A) (Stream A) :=
  {|
    Rels.app := @stream_app _;
  |}.

#[export] Instance stream_ACC_Nil A: Rels.ACCUM_NIL (list A) :=
  {|
    Rels.nil := @nil _;
  |}.

#[export] Instance stream_ACC_LeftId A: ACCUM_LeftId (list A) (Stream A).
Proof.
  constructor.
  intros.
  apply stream_app_nil_l.
Qed.

#[export] Instance stream_ACC_Assoc A: ACCUM_Assoc (list A) (list A) (Stream A) (list A) (Stream A) (Stream A).
Proof.
  constructor.
  intros.
  symmetry.
  apply app_stream_app.
Qed.

Goal forall (X: nat -> list nat -> nat -> Prop) (Y: nat -> (Stream nat) -> Prop),
  Sets.equiv (Rels.concat X Y) Y.
Proof.
  intros.
  sets_unfold.
  intros s l.
Abort.

End StreamConn.

Arguments Rels.concat: simpl never.
Arguments Rels.id: simpl never.


(** assoc, Rels_concat_union_distr (union, indexed_union, general_union), concat_empty *)




