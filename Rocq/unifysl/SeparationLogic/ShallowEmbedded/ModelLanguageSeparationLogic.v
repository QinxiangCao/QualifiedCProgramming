Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.Sound.Sound_Flat. 
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.lib.Ensembles_ext.



Section J2SC.
Context {M : Model} {J : Join model}.

Definition Model_sepconL := Build_SepconLanguage Model_L WeakSemantics.sepcon.

Class SepconDefinition_Join (SepconL : SepconLanguage Model_L) : Prop := {
  join2sepcon : forall x y,
    (@sepcon Model_L SepconL) x y = fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2
}.

Definition Join2Sepcon : SepconLanguage Model_L :=
  Build_SepconLanguage Model_L (fun x y => fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2). 

Lemma Join2Sepcon_Normal :
  @SepconDefinition_Join Join2Sepcon.
Proof. constructor. reflexivity. Qed.

End J2SC.

Section J2Wand.

Context {M : Model} {J : Join model}.

Definition Model_wandL := Build_WandLanguage Model_L WeakSemantics.wand.

Class WandDefinition_Join (WandL : WandLanguage Model_L) : Prop := {
  join2wand : forall x y,
    (@wand Model_L WandL) x y = fun m => forall m1 m2, join m m1 m2 -> x m1 -> y m2
}.

Definition Join2Wand : WandLanguage Model_L :=
  Build_WandLanguage Model_L (fun x y => fun m => forall m1 m2, join m m1 m2 -> x m1 -> y m2).

Lemma Join2Wand_Normal : 
  @WandDefinition_Join Join2Wand.
Proof. constructor. reflexivity. Qed.

End J2Wand.

Section J2Corable.

Context {M : Model} {J : Join model}.

Definition Join2Corable : Corable Model_L :=
  Build_Corable Model_L
    (fun x => forall m1 m2 m, J m1 m2 m -> (x m1 <-> x m)).

Class CorableDefinition_Join (Cor : Corable Model_L) : Prop := {
  join2corable : forall x,
    (@corable Model_L Cor) x =
      (forall m1 m2 m, J m1 m2 m -> (x m1 <-> x m))
}.

Lemma Join2Corable_Normal :
  @CorableDefinition_Join Join2Corable.
Proof. constructor. reflexivity. Qed.

Lemma CorableDefinition_Join2CorableAxiomatization
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  Corable_withAxiomatization
    Model_L (@Derivable12Provable Model_L Model2Impp Model2Derivable1)
    Cor.
Proof.
  constructor.
  - intros x y Hxy Hx.
    rewrite (join2corable y).
    rewrite (join2corable x) in Hx.
    intros m1 m2 m Hjoin.
    specialize (Hx m1 m2 m Hjoin).
    pose proof (Hxy m1 (fun H => H)) as [Hxy1 Hyx1].
    pose proof (Hxy m (fun H => H)) as [Hxy_m Hyx_m].
    split; intros.
    + apply Hxy_m. apply Hx. apply Hyx1. exact H.
    + apply Hxy1. apply Hx. apply Hyx_m. exact H.
  - intros x y z Hx.
    rewrite (join2corable x) in Hx.
    simpl. intros m _.
    split; intros.
    + destruct H as [m1 [m2 [Hjoin [[Hx1 Hy] Hz]]]].
      split.
      * apply (proj1 (Hx m1 m2 m Hjoin)). exact Hx1.
      * exists m1, m2. tauto.
    + destruct H as [Hx_m [m1 [m2 [Hjoin [Hy Hz]]]]].
      exists m1, m2.
      split; [exact Hjoin |].
      split; [| exact Hz].
      split; [| exact Hy].
      apply (proj2 (Hx m1 m2 m Hjoin)). exact Hx_m.
Qed.

Lemma Join2Corable_CorableAxiomatization:
  Corable_withAxiomatization
    Model_L (@Derivable12Provable Model_L Model2Impp Model2Derivable1)
    Join2Corable.
Proof.
  apply (CorableDefinition_Join2CorableAxiomatization
    (Cor := Join2Corable)
    (corableDef_join := Join2Corable_Normal)).
Qed.

Lemma CorableDefinition_Join2CoqPropCorable
      {coq_prop_L : CoqPropLanguage Model_L}
      {coqpropDef_model : CoqPropDefinition_Model coq_prop_L}
      {Cor : Corable Model_L}
      {corableDef_join : CorableDefinition_Join Cor}:
  @CoqPropCorable Model_L coq_prop_L Cor.
Proof.
  constructor.
  intros P.
  rewrite (join2corable (coq_prop P)).
  intros m1 m2 m Hjoin.
  rewrite !model2coqprop.
  reflexivity.
Qed.

Lemma Join2Corable_CoqPropCorable:
  @CoqPropCorable Model_L Model2CoqProp Join2Corable.
Proof.
  apply (CorableDefinition_Join2CoqPropCorable
    (coq_prop_L := Model2CoqProp)
    (coqpropDef_model := Model2CoqProp_Normal)
    (Cor := Join2Corable)
    (corableDef_join := Join2Corable_Normal)).
Qed.

End J2Corable.

Section SepconAXFromJoin.

Context {M : Model} {J : Join model} {U: Unit model}
        {J_SA : SeparationAlgebra model}
        .

Instance sepconL : SepconLanguage Model_L := Model_sepconL.

Instance sepconSM : @SepconSemantics Model_L sepconL M (unit_kMD _) tt modelR J SM.
Proof. hnf. intros. apply Same_set_refl. Qed.

Lemma SeparationAlgebra2SepconAxiomatization :
  @SepconAxiomatization Model_L Model2Impp Model_sepconL Model2Provable.
Proof.
  intros. constructor.
  + intros x y.
    exact (@sound_sepcon_comm Model_L Model2Impp sepconL M (unit_kMD _) tt modelR J J_SA SM kminSM sepconSM x y).
  + intros x y z.
    exact (@sound_provable_sepcon_assoc1 Model_L Model2Impp sepconL M (unit_kMD _) tt modelR J J_SA SM kminSM sepconSM x y z).
  + intros x1 x2 y1 y2.
    exact (@sound_provable_sepcon_mono Model_L Model2Impp sepconL M (unit_kMD _) tt modelR _ J SM kminSM sepconSM x1 x2 y1 y2).
Qed. 


End SepconAXFromJoin.

Section U2EMP.

Context {M : Model} {U : Unit model}.

Definition Unit2Emp : EmpLanguage Model_L :=
  Build_EmpLanguage Model_L (fun (m : model) => is_unit m).

Class EmpDefinition_Unit (empL : EmpLanguage Model_L) : Prop := {
  unit2emp : forall (m : model), emp m = is_unit m
}.

Lemma Unit2Emp_Normal : EmpDefinition_Unit Unit2Emp.
Proof. constructor. reflexivity. Qed.

End U2EMP.

Section SepconD1FromJoin.

Context {M : Model} 
        {J : Join model}
        {J_SA : SeparationAlgebra model}
        .
 
Lemma SeparationAlgebra2SepconDeduction :
  SepconDeduction Model_L Model2Derivable1.
Proof. 
  constructor; unfold derivable1, Model2Derivable1; 
    unfold sepcon.
  + intros. destruct H as [m1 [m2 [? [? ?]]]].
    exists m2, m1.
    split; try split; try tauto.
    apply join_comm. apply H. 
  + intros. destruct H as [m3 [m12 ?]].
    destruct H as [? [? ?]].
    destruct H1 as [m2 [m1 [? [? ?]]]].
    apply join_comm in H.
    apply join_comm in H1.
    pose proof (join_assoc m1 m2 m3 m12 m H1 H).
    destruct H4 as [m23 [? ?]].
    exists m23, m1. split; try split; try tauto.
    { apply join_comm. apply H5. }
    exists m3, m2. split; try split; try tauto.
    apply join_comm. tauto.
  + intros.
    destruct H1 as [m1 [m2 [? [? ?]]]].
    exists m1, m2; split; try split; try tauto; [apply H | apply H0]; tauto.
Qed.

End SepconD1FromJoin.

Section WandD1FromJoin.

Context {M : Model} 
        {J : Join model}
        {J_SA : SeparationAlgebra model}.

Lemma SeparationAlgebra2WandDeduction :
  WandDeduction Model_L Model2Derivable1.
Proof. 
  constructor.
  unfold derivable1; unfold Model2Derivable1.
  unfold sepcon; unfold Join2Sepcon.
  unfold wand; unfold Join2Wand.
  intros. split; intros.
  +simpl in H; simpl. 
  unfold WeakSemantics.sepcon in H; unfold WeakSemantics.wand. 
  intros. apply H. 
  exists m, m1. split; try split; try tauto.
  + destruct H0 as [m1 [m2 ?]].
  specialize (H m1 (proj1 (proj2 H0)) m2 m).
  apply H; tauto.
Qed.

End WandD1FromJoin.

Section EmpD1FromModel.

Context {M : Model} {U : Unit model} {J : Join model} {UJR : UnitJoinRelation model}.

Lemma Model2EmpDeduction :
  EmpDeduction Model_L Model2Derivable1.
Proof.
  constructor;
  unfold sepcon, Join2Sepcon;
  unfold emp, Unit2Emp;
  unfold derivable1, Model2Derivable1; intros.
  + destruct H as [m1 [m2 [? [? ?]]]].
    pose proof (unit_spec _ _ _ H1 H). subst m1; apply H0.
  + pose proof (unit_join m).
    destruct H0 as [u [? ?]].
    exists m, u. tauto.
Qed.

End EmpD1FromModel.
