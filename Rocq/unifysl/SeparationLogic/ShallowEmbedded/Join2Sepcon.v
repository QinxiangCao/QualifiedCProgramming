(* Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.Sound.Sound_Flat. 
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MetaLogicInj.Syntax.

Section J2SC.
Context {M : Model} {J : Join model}.

Definition Model_L := Build_Language (model -> Prop).

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

Section M2IFF.
Context {M : Model}.

Definition Model2Iffp : IffLanguage Model_L :=
  Build_IffLanguage Model_L (fun x y => fun m => (x m <-> y m)).

Class IffpDefinition_Model (iffpL : IffLanguage Model_L) : Prop := {
  model2iffp : forall (x y : @expr Model_L), iffp x y = (fun m  => (x m <-> y m))
}.

Lemma Model2Iffp_Normal :
  IffpDefinition_Model Model2Iffp.
Proof. constructor. reflexivity. Qed.

End M2IFF.

Section M2AND.
Context {M : Model}.

Definition Model2Andp : AndLanguage Model_L :=
  Build_AndLanguage Model_L (fun x y => fun m => (x m /\ y m)).

Class AndpDefinition_Model (andpL : AndLanguage Model_L) : Prop := {
  model2andp : forall (x y : @expr Model_L), andp x y = (fun m => (x m /\ y m))
}.

Lemma Model2Andp_Normal :
  AndpDefinition_Model Model2Andp.
Proof. constructor. reflexivity. Qed.

End M2AND.

Section M2OR.
Context {M : Model}.

Definition Model2Orp : OrLanguage Model_L :=
  Build_OrLanguage Model_L (fun x y => fun m => (x m \/ y m)).

Class OrpDefinition_Model (orpL : OrLanguage Model_L) : Prop := {
  model2orp : forall (x y : @expr Model_L), orp x y = (fun m => x m \/ y m)
}.

Lemma Model2Orp_Normal: OrpDefinition_Model Model2Orp.
Proof. constructor. reflexivity. Qed.

End M2OR.

(* Section M2COQPROP.
Context {M : Model}.

Instance L : Language := Build_Language (model -> Prop).

Definition Model2CoqProp : CoqPropLanguage Model_L :=
  Build_CoqPropLanguage Model_L (fun P x => P).

Class CoqPropDefinition_Model (coq_prop_L : CoqPropLanguage Model_L) : Prop := {
  model2coqprop : forall (P : Prop), coq_prop P = (fun m => )
}. *)


(* Section M2EMP.
Context {M : Model}.

Definition Model2Emp : EmpLanguage Model_L := 
  Build_EmpLanguage Model_L (fun m => True).

Class EmpDefinition_Model (empL : EmpLanguage Model_L) : Prop := {
  model2emp : emp = (fun _ : model => True)
}.

End M2EMP. *)

Section M2P.
Context {M : Model}.

Definition Model2Provable : Provable Model_L :=
  Build_Provable Model_L (fun (x : model -> Prop) => forall m, x m).

Class ProvableDefinition_Model (GammaP : Provable Model_L) : Prop := {
  model2provable : forall (x : @expr Model_L), provable x = (forall m, x m)
}.

Lemma Model2Provable_Normal :
  ProvableDefinition_Model Model2Provable.
Proof. constructor. reflexivity. Qed.

Definition Model2Derivable1 : Derivable1 Model_L :=
  Build_Derivable1 Model_L (fun (x y : model -> Prop) => forall m, x m -> y m).

Class Derivable1Definition_Model (GammaD1 : Derivable1 Model_L) : Prop := {
  model2deriable1 : forall (x y : @expr Model_L), derivable1 x y = (forall m, x m -> y m)
}.

Lemma Model2Derivable1_Normal : 
  Derivable1Definition_Model Model2Derivable1.
Proof. constructor. reflexivity. Qed.

End M2P.

Section SepconAXFromJoin.

Context {M : Model} {J : Join model} {U: Unit model}
        {J_SA : SeparationAlgebra model}
        .

Instance modelR : KripkeModel.KI.Relation (model) := fun x y => x = y.
Instance SM : Semantics Model_L M := Build_Semantics Model_L M (fun x => x).
Instance minL : MinimumLanguage Model_L := Build_MinimumLanguage Model_L impp.
Instance sepconL : SepconLanguage Model_L := Model_sepconL.
Instance GammaP : Provable Model_L := Build_Provable Model_L provable.
Instance kminSM : @KripkeMinimumSemantics Model_L minL M (unit_kMD _) tt modelR SM.
Proof.
  pose proof (@Trivial2Kripke Model_L minL M SM). apply H. constructor. reflexivity.
Qed.
Instance sepconSM : @SepconSemantics Model_L sepconL M (unit_kMD _) tt modelR J SM.
Proof. hnf. intros. apply Same_set_refl. Qed.

Lemma SeparationAlgebra2SepconAxiomatization :
  SepconAxiomatization Model_L GammaP.
Proof.
  intros. constructor.
  + intros x y.
    exact (@sound_sepcon_comm Model_L minL sepconL M (unit_kMD _) tt modelR J J_SA SM kminSM sepconSM x y).
  + intros x y z.
    exact (@sound_provable_sepcon_assoc1 Model_L minL sepconL M (unit_kMD _) tt modelR J J_SA SM kminSM sepconSM x y z).
  + intros x1 x2 y1 y2.
    exact (@sound_provable_sepcon_mono Model_L minL sepconL M (unit_kMD _) tt modelR _ J SM kminSM sepconSM x1 x2 y1 y2).
Qed. 

End SepconAXFromJoin.

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

Section ImpAdjD1FromModel.

Context {M : Model}.

Lemma Model2ImpAdjoint : 
  ImpAndAdjointDeduction Model_L Model2Derivable1.
Proof. 
  constructor.
  unfold derivable1; unfold Model2Derivable1.
  unfold impp; unfold Model2Impp.
  unfold andp; unfold Model2Andp.
  simpl. unfold Semantics.impp. unfold Trivial.Semantics.andp. 
  intros; split; intros; apply H; tauto.
Qed.

End ImpAdjD1FromModel.

Section MinD1FromModel.

Context {M: Model}.

Lemma Model2MinD1 : 
  @MinimumDeduction Model_L Model2Impp Model2Derivable1 .
Proof. 
  constructor; unfold derivable1; 
  unfold model2deriable1; unfold Model2Impp; 
  simpl; intros.
  -apply H. apply H1. apply H0. apply H1.
  -apply H. intros. apply H1.
  -apply H0.
  -apply H. 
  -apply H. apply H1. apply H0. apply H1.
Qed.

  
End MinD1FromModel.



Section AndD1FromModel.

Context {M : Model}.

Lemma Model2AndDeduction :
  AndDeduction Model_L Model2Derivable1.
Proof. 
  constructor;
  unfold derivable1; unfold Model2Derivable1;
  unfold andp; unfold Model2Andp; simpl; unfold Trivial.Semantics.andp; try tauto.
  intros. split; [apply H | apply H0]; tauto.
Qed.

End AndD1FromModel.

Section OrD1FromModel.

Context {M : Model}.

Lemma Model2OrDeduction :
  OrDeduction Model_L Model2Derivable1.
Proof. 
  constructor;
  unfold derivable1; unfold Model2Derivable1; unfold Model2Orp;
  simpl; unfold Trivial.Semantics.orp; try tauto.
  intros. destruct H1; [apply H | apply H0]; tauto.
Qed.

End OrD1FromModel.

Section IffD1FromModel.

Context {M : Model}.
    
Lemma Model2IffDeduction :
  @IffDeduction Model_L Model2Impp Model2Iffp Model2Derivable1.
Proof. 
  constructor;
  unfold derivable1; unfold Model2Derivable1;
  unfold iffp; unfold Model2Iffp; 
  unfold impp; unfold Model2Impp; 
  simpl; unfold Semantics.impp; intros; tauto.
Qed.

End IffD1FromModel.

Section BasicDeductionFromModel.

Context {M : Model}.

Lemma Model2BasicDeduction :
  BasicDeduction Model_L Model2Derivable1.
Proof.
  constructor; unfold derivable1, Model2Derivable1.
  + intros. tauto.
  + intros. apply (H0 m (H m H1)).
Qed.

End BasicDeductionFromModel.

Section MinimumDeductionFromModel.
  
Context {M : Model}.

Lemma Model2MinumumDeduction': 
  MinimumDeduction Model_L Model2Derivable1.
Proof. 
  constructor; intros; unfold derivable1, Model2Derivable1, Model2Impp, impp in *;
  simpl in *; unfold Semantics.impp in *.
  -intros. apply H. apply H1. apply H0. apply H1.
  -intros. apply H. intros. apply H1.
  -intros. apply H0.
  -intros. apply H. 
  -intros. apply H. apply H1. apply H0. apply H1.
Qed.
  


End MinimumDeductionFromModel.



(* Instance Pred_kminSM (A: Type): @KripkeMinimumSemantics (Pred_L A) (Pred_minL A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @Trivial2Kripke _ _ _ _ (Pred_tminSM A). *)


(* Class Semantics (L: Language) (MD: Model): Type := {
  denotation: expr -> model -> Prop (* better to be (expr -> Ensemble model) if Ensemble is polymorphic *)
}. *)


(* Module Former_j2sc.

Class SepconDefinition_Join
  (SepconL : SepconLanguage (Pred_L model)) : Prop := {
    join2sepcon : forall x y, 
    (@sepcon (Pred_L model) SepconL) x y = fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2
  }.

Definition Join2Sepcon : SepconLanguage (Pred_L model) :=
  Build_SepconLanguage (Pred_L model) (fun x y => fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2).

Lemma Join2Sepcon_Normal :
  @SepconDefinition_Join Join2Sepcon.
Proof. constructor. reflexivity. Qed.

End Former_j2sc. *)

(* Check @SepconDefinition_Join. *)

(* Check Build_SepconLanguage.
Check SepconLanguage.
Check (Build_SepconLanguage L).
Check @SepconDefinition_Join. *)

(* 
Class AndDefinition_Or_Neg
  (L: Language)
  {orpL: OrLanguage L}
  {negpL: NegLanguage L}
  {andpL: AndLanguage L}: Prop:= {
orp_negp2andp: forall x y,
x && y = ~~ ((~~ x) || (~~ y))
}.

Definition OrNeg2And
  {L: Language}
  {orpL: OrLanguage L}
  {negpL: NegLanguage L}: AndLanguage L :=
Build_AndLanguage _ (fun x y => ~~ ((~~ x) || (~~ y))).

Lemma OrNeg2And_Normal
      {L: Language}
      {orpL: OrLanguage L}
      {negpL: NegLanguage L}:
  @AndDefinition_Or_Neg L _ _ OrNeg2And.
Proof. constructor. reflexivity. Qed. *) *)
