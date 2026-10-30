Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Module Type LanguageSig.
(* primitive_types *)
  Parameter model : Type .
(* derived types *)
  Definition expr := (model -> Prop) .
(* primitive judgements *)
(* primitive connectives *)
  Parameter join : (model -> model -> model -> Prop) .
  Parameter is_unit : (model -> Prop) .
End LanguageSig.

Module Type DerivedNamesSig (Names: LanguageSig).
Import Names.
(* derived connectives *)
  Definition impp := (fun (x y : model -> Prop) (m : model) => x m -> y m) .
  Definition andp := (fun (x y : model -> Prop) (m : model) => x m /\ y m) .
  Definition orp := (fun (x y : model -> Prop) (m : model) => x m \/ y m) .
  Definition coq_prop := (fun (P : Prop) (_ : model) => P) .
  Definition allp := (fun (A : Type) (x : A -> model -> Prop) (m : model) => forall a : A, x a m) .
  Definition truep := (fun _ : model => True) .
  Definition exp := (fun (A : Type) (x : A -> model -> Prop) (m : model) => exists a : A, x a m) .
  Definition wand := (fun (x y : model -> Prop) (m : model) => forall m1 m2 : model, join m m1 m2 -> x m1 -> y m2) .
  Definition sepcon := (fun (x y : model -> Prop) (m : model) => exists m1 m2 : model, join m1 m2 m /\ x m1 /\ y m2) .
  Definition emp := (fun m : model => is_unit m) .
(* derived judgements *)
  Definition provable := (fun x : model -> Prop => forall m : model, x m) .
  Definition derivable1 := (fun x y : expr => provable (impp x y)) .
End DerivedNamesSig.

Module Type PrimitiveRuleSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names).
Import Names DerivedNames.
  Axiom join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames).
Import Names DerivedNames Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom derivable1s_coq_prop_r : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) .
  Axiom derivable1s_coq_prop_l : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
  Axiom derivable1s_allp_r : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) .
  Axiom derivable1s_allp_l : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) .
  Axiom derivable1s_exp_r : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) .
  Axiom derivable1s_exp_l : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) .
  Axiom derivable1s_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_truep_intros : (forall x : expr, derivable1 x truep) .
  Axiom derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Axiom derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Axiom derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Axiom derivable1s_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Axiom derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Axiom derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .
  Axiom derivable1s_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
  Axiom derivable1s_modus_ponens : (forall x y z : expr, derivable1 x (impp y z) -> derivable1 x y -> derivable1 x z) .
  Axiom derivable1s_impp_intros : (forall x y z : expr, derivable1 (impp x y) z -> derivable1 x (impp y z)) .
  Axiom derivable1_impp_refl : (forall x y : expr, derivable1 x (impp y y)) .
  Axiom derivable1_axiom1 : (forall x y : expr, derivable1 x (impp y x)) .
  Axiom derivable1_axiom2 : (forall x y z : expr, derivable1 (impp x (impp y z)) (impp (impp x y) (impp x z))) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
  Axiom provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom provable_orp_intros1 : (forall x y : expr, provable (impp x (orp x y))) .
  Axiom provable_orp_intros2 : (forall x y : expr, provable (impp y (orp x y))) .
  Axiom provable_orp_elim : (forall x y z : expr, provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z)))) .
  Axiom provable_andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) .
  Axiom provable_andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) .
  Axiom provable_andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) .
  Axiom provables_sepcon_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) sepcon) .
  Axiom derivable1_exp_andp_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) .
  Axiom derivable1_andp_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) .
  Axiom derivable1_exp_sepcon_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) .
  Axiom derivable1_sepcon_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (sepcon P (exp A Q)) (exp A (fun x : A => sepcon P (Q x)))) .
  Axiom derivable1_sepcon_coq_prop_andp_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R))) .
  Axiom derivable1_sepcon_coq_prop_andp_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) .
  Axiom derivable1_sepcon_andp_coq_prop_l : (forall (P Q : expr) (R : Prop), derivable1 (sepcon P (andp Q (coq_prop R))) (andp (coq_prop R) (sepcon P Q))) .
  Axiom derivable1_sepcon_andp_coq_prop_r : (forall (P Q : expr) (R : Prop), derivable1 (andp (coq_prop R) (sepcon P Q)) (sepcon P (andp Q (coq_prop R)))) .
  Axiom derivable1_coq_prop_andp_sepcon_l : (forall (P : Prop) (Q R : expr), derivable1 (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) .
  Axiom derivable1_coq_prop_andp_sepcon_r : (forall (P : Prop) (Q R : expr), derivable1 (andp (coq_prop P) (sepcon Q R)) (sepcon (andp (coq_prop P) Q) R)) .
  Axiom derivable1_andp_coq_prop_sepcon_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon (andp P (coq_prop Q)) R) (andp (coq_prop Q) (sepcon P R))) .
  Axiom derivable1_andp_coq_prop_sepcon_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon (andp P (coq_prop Q)) R)) .
  Axiom derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) .
  Axiom derivable1s_andp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) andp) .
  Axiom derivable1s_orp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) orp) .
  Axiom derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) .
  Axiom derivable1s_wand_proper : (Proper (derivable1 --> derivable1 ==> derivable1) wand) .
  Axiom derivable1s_coq_prop_andp_l : (forall (P : Prop) (Q R : expr), (P -> derivable1 Q R) -> derivable1 (andp (coq_prop P) Q) R) .
  Axiom derivable1s_coq_prop_andp_r : (forall (P : Prop) (Q R : expr), derivable1 R Q -> P -> derivable1 R (andp (coq_prop P) Q)) .
  Axiom derivables_coq_prop_imply : (forall P Q : Prop, (P -> Q) -> derivable1 (coq_prop P) (coq_prop Q)) .
  Axiom derivables_false_coq_prop : (forall (P : Prop) (Q : expr), (P -> False) -> derivable1 (coq_prop P) Q) .
  Axiom derivable1s_andp_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (andp x1 y1) (andp x2 y2)) .
  Axiom derivable1s_ex_l_unfold : (forall (A : Type) (P : A -> expr) (Q : expr), (exists x : A, derivable1 (P x) Q) -> derivable1 (allp A P) Q) .
  Axiom derivable1_exp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (exp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => exp A (fun x : A => P x y)))) .
  Axiom derivable1_allp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (allp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => allp A (fun x : A => P x y)))) .
  Axiom derivable1_wand_elim1 : (forall x y : expr, derivable1 (sepcon (wand x y) x) y) .
  Axiom derivable1_wand_elim2 : (forall x y : expr, derivable1 (sepcon x (wand x y)) y) .
  Axiom derivable1s_impp_proper : (Proper (derivable1 --> derivable1 ==> derivable1) impp) .
  Axiom Derivable_impp_rewrite : (RewriteRelation derivable1) .
  Axiom derivable1_refl_instance : (Reflexive derivable1) .
  Axiom derivable1_trans_instance : (Transitive derivable1) .
(* derived rules as instance *)
  #[export] Existing Instance provables_sepcon_proper_impp .
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance derivable1s_andp_proper .
  #[export] Existing Instance derivable1s_orp_proper .
  #[export] Existing Instance derivable1s_sepcon_proper .
  #[export] Existing Instance derivable1s_wand_proper .
  #[export] Existing Instance derivable1s_impp_proper .
  #[export] Existing Instance Derivable_impp_rewrite .
  #[export] Existing Instance derivable1_refl_instance .
  #[export] Existing Instance derivable1_trans_instance .
End LogicTheoremSig.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.Extensions.ProofTheory.Stable.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.Extensions.ProofTheory.Corable.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.
Require Import Logic.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.
Require Import Logic.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.
Require Import Logic.Extensions.ShallowEmbedded.ModelLanguageCorableStable.
Require Import Logic.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.ShallowQuantifierLogic.ProofTheory.
Require Import Logic.ShallowQuantifierLogic.ModelConstrEX.
Require Import Logic.ShallowQuantifierLogic.ModelConstrALL.

Module Type LogicTheoremSig' (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames) <: LogicTheoremSig Names DerivedNames Rules.
Import Names DerivedNames Rules.
(* aux primitive instances *)
  #[export] Instance M : Model := (Build_Model model) .
  #[export] Instance L : Language := (Build_Language expr) .
  #[export] Instance J : (Join model) := join .
  #[export] Instance U : (Unit model) := is_unit .
  #[export] Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  #[export] Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  #[export] Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  #[export] Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
  #[export] Instance allpL : (ShallowForallLanguage L) := (Build_ShallowForallLanguage L allp) .
  #[export] Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  #[export] Instance expL : (ShallowExistsLanguage L) := (Build_ShallowExistsLanguage L exp) .
  #[export] Instance wandL : (WandLanguage L) := (Build_WandLanguage L wand) .
  #[export] Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  #[export] Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  #[export] Instance GammaP : (Provable L) := (Build_Provable L provable) .
  #[export] Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  #[export] Instance J_SA : (SeparationAlgebra model) := (Build_SeparationAlgebra model J join_comm join_assoc) .
(* aux refl instances for derivation *)
  #[export] Instance imppDef_model : (ImppDefinition_Model minL) := Model2Impp_Normal .
  #[export] Instance andpDef_model : (AndpDefinition_Model andpL) := Model2Andp_Normal .
  #[export] Instance orpDef_model : (OrpDefinition_Model orpL) := Model2Orp_Normal .
  #[export] Instance coqpropDef_model : (CoqPropDefinition_Model coq_prop_L) := Model2CoqProp_Normal .
  #[export] Instance allpDef_model : (AllpDefinition_Model allpL) := Model2Allp_Normal .
  #[export] Instance truepDef_model : (TrueDefinition_Model truepL) := Model2Truep_Normal .
  #[export] Instance expDef_model : (ExpDefinition_Model expL) := Model2Exp_Normal .
  #[export] Instance wandDef_join : (WandDefinition_Join Join2Wand) := Join2Wand_Normal .
  #[export] Instance sepconDef_join : (SepconDefinition_Join Join2Sepcon) := Join2Sepcon_Normal .
  #[export] Instance empDef_unit : (EmpDefinition_Unit Unit2Emp) := Unit2Emp_Normal .
  #[export] Instance provableDef_model : (ProvableDefinition_Model GammaP) := Model2Provable_Normal .
  #[export] Instance GammaD1P : (Derivable1FromProvable L GammaP GammaD1) := Provable2Derivable1_Normal .
(* aux derived instances *)
  #[export] Instance sepconD : (SepconDeduction L GammaD1) := SeparationAlgebra2SepconDeduction .
  #[export] Instance wandD : (WandDeduction L GammaD1) := SeparationAlgebra2WandDeduction .
  #[export] Instance adjD : (ImpAndAdjointDeduction L GammaD1) := Model2ImpAdjoint .
  #[export] Instance andpD : (AndDeduction L GammaD1) := Model2AndDeduction .
  #[export] Instance expD : (ShallowExistsDeduction L GammaD1) := Model2ExpDeduction .
  #[export] Instance allpD : (ShallowForallDeduction L GammaD1) := Model2AllDeduction .
  #[export] Instance bD : (BasicDeduction L GammaD1) := Model2BasicDeduction .
  #[export] Instance exp_andpD : deduction_exp_and := ExpDeduction2ExsitsAnd .
  #[export] Instance exp_sepconD : deduction_exp_sepcon := ExpDeduction2ExsitsSepcon .
  #[export] Instance minD : (MinimumDeduction L GammaD1) := Model2MinD1 .
  #[export] Instance coq_prop_D : (CoqPropDeduction L GammaD1) := Model2CoqPropDeduction .
  #[export] Instance truepD : (TrueDeduction L GammaD1) := Model2TrueDeduction .
  #[export] Instance sap : sepcon_andp_prop := Derived_sepcon_andp_prop .
  #[export] Instance sap_ext : sepcon_andp_prop_ext := Derived_sepcon_andp_prop_ext .
  #[export] Instance orpD : (OrDeduction L GammaD1) := Model2OrDeduction .
  #[export] Instance andpAX : (AndAxiomatization L GammaP) := Deduction2Axiomatization_andpAX .
  #[export] Instance orpAX : (OrAxiomatization L GammaP) := Deduction2Axiomatization_orpAX .
  #[export] Instance sepconAX : (SepconAxiomatization L GammaP) := SepconDeduction2SepconAxiomatization_sepconAX .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition derivable1s_coq_prop_r : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) := derivable1s_coq_prop_r .
  Definition derivable1s_coq_prop_l : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) := derivable1s_coq_prop_l .
  Definition derivable1s_allp_r : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) := derivable1s_allp_r .
  Definition derivable1s_allp_l : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) := derivable1s_allp_l .
  Definition derivable1s_exp_r : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) := derivable1s_exp_r .
  Definition derivable1s_exp_l : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) := derivable1s_exp_l .
  Definition derivable1s_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) := derivable1s_wand_sepcon_adjoint .
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_truep_intros : (forall x : expr, derivable1 x truep) := derivable1_truep_intros .
  Definition derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) := derivable1_orp_intros1 .
  Definition derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) := derivable1_orp_intros2 .
  Definition derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) := derivable1_orp_elim .
  Definition derivable1s_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) := derivable1s_andp_intros .
  Definition derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) := derivable1_andp_elim1 .
  Definition derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) := derivable1_andp_elim2 .
  Definition derivable1s_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) := derivable1s_impp_andp_adjoint .
  Definition derivable1s_modus_ponens : (forall x y z : expr, derivable1 x (impp y z) -> derivable1 x y -> derivable1 x z) := derivable1s_modus_ponens .
  Definition derivable1s_impp_intros : (forall x y z : expr, derivable1 (impp x y) z -> derivable1 x (impp y z)) := derivable1s_impp_intros .
  Definition derivable1_impp_refl : (forall x y : expr, derivable1 x (impp y y)) := derivable1_impp_refl .
  Definition derivable1_axiom1 : (forall x y : expr, derivable1 x (impp y x)) := derivable1_axiom1 .
  Definition derivable1_axiom2 : (forall x y z : expr, derivable1 (impp x (impp y z)) (impp (impp x y) (impp x z))) := derivable1_axiom2 .
  Definition derivable1_refl : (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
  Definition provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := provable_sepcon_comm_impp .
  Definition provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := provable_sepcon_assoc1 .
  Definition provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) := provable_sepcon_mono .
  Definition provable_orp_intros1 : (forall x y : expr, provable (impp x (orp x y))) := provable_orp_intros1 .
  Definition provable_orp_intros2 : (forall x y : expr, provable (impp y (orp x y))) := provable_orp_intros2 .
  Definition provable_orp_elim : (forall x y z : expr, provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z)))) := provable_orp_elim .
  Definition provable_andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) := provable_andp_intros .
  Definition provable_andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) := provable_andp_elim1 .
  Definition provable_andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) := provable_andp_elim2 .
  Definition provables_sepcon_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) sepcon) := provables_sepcon_proper_impp .
  Definition derivable1_exp_andp_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) := derivable1_exp_andp_l .
  Definition derivable1_andp_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) := derivable1_andp_exp_l .
  Definition derivable1_exp_sepcon_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) := derivable1_exp_sepcon_l .
  Definition derivable1_sepcon_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (sepcon P (exp A Q)) (exp A (fun x : A => sepcon P (Q x)))) := derivable1_sepcon_exp_l .
  Definition derivable1_sepcon_coq_prop_andp_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R))) := derivable1_sepcon_coq_prop_andp_l .
  Definition derivable1_sepcon_coq_prop_andp_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) := derivable1_sepcon_coq_prop_andp_r .
  Definition derivable1_sepcon_andp_coq_prop_l : (forall (P Q : expr) (R : Prop), derivable1 (sepcon P (andp Q (coq_prop R))) (andp (coq_prop R) (sepcon P Q))) := derivable1_sepcon_andp_coq_prop_l .
  Definition derivable1_sepcon_andp_coq_prop_r : (forall (P Q : expr) (R : Prop), derivable1 (andp (coq_prop R) (sepcon P Q)) (sepcon P (andp Q (coq_prop R)))) := derivable1_sepcon_andp_coq_prop_r .
  Definition derivable1_coq_prop_andp_sepcon_l : (forall (P : Prop) (Q R : expr), derivable1 (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) := derivable1_coq_prop_andp_sepcon_l .
  Definition derivable1_coq_prop_andp_sepcon_r : (forall (P : Prop) (Q R : expr), derivable1 (andp (coq_prop P) (sepcon Q R)) (sepcon (andp (coq_prop P) Q) R)) := derivable1_coq_prop_andp_sepcon_r .
  Definition derivable1_andp_coq_prop_sepcon_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon (andp P (coq_prop Q)) R) (andp (coq_prop Q) (sepcon P R))) := derivable1_andp_coq_prop_sepcon_l .
  Definition derivable1_andp_coq_prop_sepcon_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon (andp P (coq_prop Q)) R)) := derivable1_andp_coq_prop_sepcon_r .
  Definition derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) := derivable1_proper_derivable1 .
  Definition derivable1s_andp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) andp) := derivable1s_andp_proper .
  Definition derivable1s_orp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) orp) := derivable1s_orp_proper .
  Definition derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) := derivable1s_sepcon_proper .
  Definition derivable1s_wand_proper : (Proper (derivable1 --> derivable1 ==> derivable1) wand) := derivable1s_wand_proper .
  Definition derivable1s_coq_prop_andp_l : (forall (P : Prop) (Q R : expr), (P -> derivable1 Q R) -> derivable1 (andp (coq_prop P) Q) R) := derivable1s_coq_prop_andp_l .
  Definition derivable1s_coq_prop_andp_r : (forall (P : Prop) (Q R : expr), derivable1 R Q -> P -> derivable1 R (andp (coq_prop P) Q)) := derivable1s_coq_prop_andp_r .
  Definition derivables_coq_prop_imply : (forall P Q : Prop, (P -> Q) -> derivable1 (coq_prop P) (coq_prop Q)) := derivables_coq_prop_imply .
  Definition derivables_false_coq_prop : (forall (P : Prop) (Q : expr), (P -> False) -> derivable1 (coq_prop P) Q) := derivables_false_coq_prop .
  Definition derivable1s_andp_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (andp x1 y1) (andp x2 y2)) := derivable1s_andp_mono .
  Definition derivable1s_ex_l_unfold : (forall (A : Type) (P : A -> expr) (Q : expr), (exists x : A, derivable1 (P x) Q) -> derivable1 (allp A P) Q) := derivable1s_ex_l_unfold .
  Definition derivable1_exp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (exp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => exp A (fun x : A => P x y)))) := derivable1_exp_allp_swap .
  Definition derivable1_allp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (allp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => allp A (fun x : A => P x y)))) := derivable1_allp_allp_swap .
  Definition derivable1_wand_elim1 : (forall x y : expr, derivable1 (sepcon (wand x y) x) y) := derivable1_wand_elim1 .
  Definition derivable1_wand_elim2 : (forall x y : expr, derivable1 (sepcon x (wand x y)) y) := derivable1_wand_elim2 .
  Definition derivable1s_impp_proper : (Proper (derivable1 --> derivable1 ==> derivable1) impp) := derivable1s_impp_proper .
  Definition Derivable_impp_rewrite : (RewriteRelation derivable1) := Derivable_impp_rewrite .
  Definition derivable1_refl_instance : (Reflexive derivable1) := derivable1_refl_instance .
  Definition derivable1_trans_instance : (Transitive derivable1) := derivable1_trans_instance .
(* derived rules as instance *)
  #[export] Existing Instance provables_sepcon_proper_impp .
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance derivable1s_andp_proper .
  #[export] Existing Instance derivable1s_orp_proper .
  #[export] Existing Instance derivable1s_sepcon_proper .
  #[export] Existing Instance derivable1s_wand_proper .
  #[export] Existing Instance derivable1s_impp_proper .
  #[export] Existing Instance Derivable_impp_rewrite .
  #[export] Existing Instance derivable1_refl_instance .
  #[export] Existing Instance derivable1_trans_instance .
End LogicTheoremSig'.

(*Require Logic.PropositionalLogic.DeepEmbedded.Solver.
Module IPSolver (Names: LanguageSig).
  Import Names.
  Ltac ip_solve :=
    change expr with Base.expr;
    change provable with Base.provable;
    change impp with Syntax.impp;
    change andp with Syntax.andp;
    intros; Solver.SolverSound.ipSolver.
End IPSolver.*)
