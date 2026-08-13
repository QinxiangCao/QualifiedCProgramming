Require Import HypotheticalExternLib .
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Module Type LanguageSig.
(* primitive_types *)
  Parameter Inline expr : forall `{ para }, Type .
  Section LanguageSig.
  Context `{ para }.
(* derived types *)
(* primitive judgements *)
  Parameter provable : (expr -> Prop) .
(* primitive connectives *)
  Parameter impp : (expr -> expr -> expr) .
  Parameter andp : (expr -> expr -> expr) .
  Parameter Inline sepcon : (expr -> expr -> expr) .
  Parameter Inline emp : expr .
  End LanguageSig.
End LanguageSig.

Module Type DerivedNamesSig (Names: LanguageSig).
Import Names.
  Definition __PARA__ : Type :=  para .
  Section DerivedNames.
  Context `{ para }.
(* derived connectives *)
  Definition iffp := (fun x y : expr => andp (impp x y) (impp y x)) .
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
(* derived judgements *)
  Definition derivable1 := (fun x y : expr => provable (impp x y)) .
  Definition logic_equiv := (fun x y : expr => provable (impp x y) /\ provable (impp y x)) .
  End DerivedNames.
End DerivedNamesSig.

Module Type PrimitiveRuleSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names).
Import Names DerivedNames.
  Section PrimitiveRuleSig.
  Context `{ para }.
  Axiom provable_sepcon_emp : (forall x : expr, provable (iffp (sepcon x emp) x)) .
  Axiom provable_sepcon_impp_comm : (forall x y : expr, provable (iffp (sepcon x y) (sepcon y x))) .
  Axiom provable_sepcon_assoc : (forall x y z : expr, provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom provable_andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) .
  Axiom provable_andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) .
  Axiom provable_andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) .
  Axiom provables_modus_ponens : (forall x y : expr, provable (impp x y) -> provable x -> provable y) .
  Axiom provable_axiom1 : (forall x y : expr, provable (impp x (impp y x))) .
  Axiom provable_axiom2 : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) .
  End PrimitiveRuleSig.
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames).
Import Names DerivedNames Rules.
Parameter Inline tree_pos : forall `{ para }, Type .
  Section LogicTheoremSig.
  Context `{ para }.
(* derived rules *)
  Axiom __logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
  Axiom logic_equiv_impp : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) .
  Axiom logic_equiv_refl : (forall x : expr, logic_equiv x x) .
  Axiom logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) .
  Axiom logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) .
  Axiom derivable1_sepcon_emp_l : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom derivable1_sepcon_emp_r : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
  Axiom provable_sepcon_emp_derives : (forall x : expr, provable (impp (sepcon x emp) x)) .
  Axiom provable_derives_sepcon_emp : (forall x : expr, provable (impp x (sepcon x emp))) .
  Axiom provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom provable_iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) .
  Axiom provable_iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) .
  Axiom provable_iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) .
  Axiom provable_impp_refl : (forall x : expr, provable (impp x x)) .
  Axiom provable_impp_refl' : (forall x y : expr, x = y -> provable (impp x y)) .
  Axiom provable_impp_arg_switch : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp y (impp x z)))) .
  Axiom provable_impp_trans : (forall x y z : expr, provable (impp (impp x y) (impp (impp y z) (impp x z)))) .
  Axiom provable_multi_imp_shrink : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs (impp x y))) (multi_imp xs (impp x y)))) .
  Axiom provable_multi_imp_arg_switch1 : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs y)) (multi_imp xs (impp x y)))) .
  Axiom provable_multi_imp_arg_switch2 : (forall (xs : list expr) (x y : expr), provable (impp (multi_imp xs (impp x y)) (impp x (multi_imp xs y)))) .
  Axiom provable_add_multi_imp_left_head : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs2 y) (multi_imp (xs1 ++ xs2) y))) .
  Axiom provable_add_multi_imp_left_tail : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs1 y) (multi_imp (xs1 ++ xs2) y))) .
  Axiom provable_multi_imp_modus_ponens : (forall (xs : list expr) (y z : expr), provable (impp (multi_imp xs y) (impp (multi_imp xs (impp y z)) (multi_imp xs z)))) .
  Axiom provable_multi_imp_weaken : (forall (xs : list expr) (x y : expr), provable (impp x y) -> provable (impp (multi_imp xs x) (multi_imp xs y))) .
  Axiom provable_impp_refl_instance : (Reflexive (fun x y : expr => provable (impp x y))) .
  Axiom provable_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> Basics.impl) provable) .
  Axiom provables_impp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) --> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) impp) .
  Axiom provable_andp_comm : (forall x y : expr, provable (iffp (andp x y) (andp y x))) .
  Axiom provable_andp_assoc : (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) .
  Axiom provable_impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) .
  Axiom provable_impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) .
  Axiom provables_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) .
  Axiom provables_andp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) andp) .
  Axiom provable_iffp_equiv : (Equivalence (fun x y : expr => provable (iffp x y))) .
  Axiom provable_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> iff) provable) .
  Axiom provables_impp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) impp) .
  Axiom provables_andp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) andp) .
  Axiom provables_iffp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) iffp) .
  Axiom provables_emp_sepcon_unfold : (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) .
  Axiom provables_sepcon_impp_unfold : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) .
  Axiom provables_sepcon_sepcon_unfold : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) .
  Axiom provables_sepcon_assoc : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) .
  Axiom provable_sepcon_emp_derives : (forall x : expr, provable (impp (sepcon x emp) x)) .
  Axiom provables_sepcon_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) sepcon) .
  Axiom provables_sepcon_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) sepcon) .
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom cancel_different : (tree_pos -> tree_pos -> expr) .
  Axiom cancel_same : (tree_pos -> tree_pos -> Prop) .
  Axiom restore : (tree_pos -> tree_pos -> expr) .
  Axiom cancel_sound : (forall tep teq : tree_pos, cancel_same tep teq -> provable (cancel_different tep teq) -> provable (restore tep teq)) .
  Axiom logic_equiv_impp_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) impp) .
  Axiom logic_equiv_sepcon_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon) .
  Axiom provable_proper_equiv : (Proper (logic_equiv ==> iff) provable) .
  Axiom logic_equiv_refl_instance : (Reflexive logic_equiv) .
  Axiom logic_equiv_symm_instance : (Symmetric logic_equiv) .
  Axiom logic_equiv_trans_instance : (Transitive logic_equiv) .
  Axiom logic_equiv_sepcon_comm : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) .
  Axiom logic_equiv_sepcon_assoc : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom provable_sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) .
  Axiom derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) .
  Axiom logic_equiv_proper_logic_equiv : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv) .
  Axiom logic_equiv_proper_derivable1 : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1) .
  Axiom derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) .
(* derived rules as instance *)
  #[export] Existing Instance provable_impp_refl_instance .
  #[export] Existing Instance provable_proper_impp .
  #[export] Existing Instance provables_impp_proper_impp .
  #[export] Existing Instance provables_andp_proper_impp .
  #[export] Existing Instance provable_iffp_equiv .
  #[export] Existing Instance provable_proper_iffp .
  #[export] Existing Instance provables_impp_proper_iffp .
  #[export] Existing Instance provables_andp_proper_iffp .
  #[export] Existing Instance provables_iffp_proper_iffp .
  #[export] Existing Instance provables_sepcon_proper_impp .
  #[export] Existing Instance provables_sepcon_proper_iffp .
  #[export] Existing Instance logic_equiv_impp_proper .
  #[export] Existing Instance logic_equiv_sepcon_proper .
  #[export] Existing Instance provable_proper_equiv .
  #[export] Existing Instance logic_equiv_refl_instance .
  #[export] Existing Instance logic_equiv_symm_instance .
  #[export] Existing Instance logic_equiv_trans_instance .
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance logic_equiv_proper_logic_equiv .
  #[export] Existing Instance logic_equiv_proper_derivable1 .
  #[export] Existing Instance derivable1s_sepcon_proper .
  End LogicTheoremSig.
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
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.Join2Sepcon.
Require Import Logic.SeparationLogic.ShallowEmbedded.Model2CoqPropEmp.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.ShallowQuantifierLogic.ProofTheory.
Require Import Logic.ShallowQuantifierLogic.ModelConstrEX.
Require Import Logic.ShallowQuantifierLogic.ModelConstrALL.

Module Type LogicTheoremSig' (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames) <: LogicTheoremSig Names DerivedNames Rules.
Import Names DerivedNames Rules.
  Section LogicTheorem.
  Context `{ para }.
(* aux primitive instances *)
  #[export] Instance L : Language := (Build_Language expr) .
  #[export] Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  #[export] Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  #[export] Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  #[export] Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  #[export] Instance iffpL : (IffLanguage L) := (Build_IffLanguage L iffp) .
  #[export] Instance GammaP : (Provable L) := (Build_Provable L provable) .
  #[export] Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  #[export] Instance GammaE : (LogicEquiv L) := (Build_LogicEquiv L logic_equiv) .
  #[export] Instance minAX : (MinimumAxiomatization L GammaP) := (Build_MinimumAxiomatization L minL GammaP provables_modus_ponens provable_axiom1 provable_axiom2) .
  #[export] Instance andpAX : (AndAxiomatization L GammaP) := (Build_AndAxiomatization L minL andpL GammaP provable_andp_intros provable_andp_elim1 provable_andp_elim2) .
  #[export] Instance sepconAX_weak_iffp : (SepconAxiomatization_weak_iffp L GammaP) := (Build_SepconAxiomatization_weak_iffp L iffpL sepconL GammaP provable_sepcon_impp_comm provable_sepcon_assoc) .
  #[export] Instance provable_sepcon_mono_AX : (SepconMonoAxiomatization L GammaP) := (Build_SepconMonoAxiomatization L minL sepconL GammaP provable_sepcon_mono) .
  #[export] Instance empAX_iffp : (EmpAxiomatization_iffp L GammaP) := (Build_EmpAxiomatization_iffp L iffpL sepconL empL GammaP provable_sepcon_emp) .
(* aux refl instances for derivation *)
  #[export] Instance iffpDef : (IffDefinition_And_Imp L) := AndImp2Iff_Normal .
  #[export] Instance GammaD1P : (Derivable1FromProvable L GammaP GammaD1) := Provable2Derivable1_Normal .
  #[export] Instance GammaEP : (EquivProvable L GammaP GammaE) := Provable2Equiv_Normal .
(* aux derived instances *)
  #[export] Instance iffpAX : (IffAxiomatization L GammaP) := IffFromDefToAX_And_Imp .
  #[export] Instance sepconAX_weak : (SepconAxiomatization_weak L GammaP) := SepconAxiomatizationWeakIff2SepconAxiomatizationWeak .
  #[export] Instance sepconAX : (SepconAxiomatization L GammaP) := SepconAxiomatizationWeak2SepconAxiomatization .
  #[export] Instance empAX : (EmpAxiomatization L GammaP) := EmpAxiomatizationIff2EmpAxiomatization .
  #[export] Instance bD : (BasicDeduction L GammaD1) := Axiomatization2Deduction_bD .
  #[export] Instance sepconD : (SepconDeduction L GammaD1) := SeparationLogic.Axiomatization2Deduction_sepconD .
  #[export] Instance empD : (EmpDeduction L GammaD1) := Axiomatization2Deduction_empD .
  #[export] Instance bE : (BasicLogicEquiv L GammaE) := Axiomatization2Equiv_bE .
  #[export] Instance GammaED1 : (EquivDerivable1 L GammaD1 GammaE) := Axiomatization2Deduction_GammaED1 .
  #[export] Instance imppE : (ImpLogicEquiv L GammaE) := Axiomatization2LogicEquiv_imppE .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition __logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) := __logic_equiv_derivable1 .
  Definition logic_equiv_impp : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) := logic_equiv_impp .
  Definition logic_equiv_refl : (forall x : expr, logic_equiv x x) := logic_equiv_refl .
  Definition logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) := logic_equiv_symm .
  Definition logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) := logic_equiv_trans .
  Definition derivable1_sepcon_emp_l : (forall x : expr, derivable1 (sepcon x emp) x) := derivable1_sepcon_emp_l .
  Definition derivable1_sepcon_emp_r : (forall x : expr, derivable1 x (sepcon x emp)) := derivable1_sepcon_emp_r .
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_refl : (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
  Definition provable_sepcon_emp_derives : (forall x : expr, provable (impp (sepcon x emp) x)) := provable_sepcon_emp_derives .
  Definition provable_derives_sepcon_emp : (forall x : expr, provable (impp x (sepcon x emp))) := provable_derives_sepcon_emp .
  Definition provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := provable_sepcon_comm_impp .
  Definition provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := provable_sepcon_assoc1 .
  Definition provable_iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) := provable_iffp_intros .
  Definition provable_iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) := provable_iffp_elim1 .
  Definition provable_iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) := provable_iffp_elim2 .
  Definition provable_impp_refl : (forall x : expr, provable (impp x x)) := provable_impp_refl .
  Definition provable_impp_refl' : (forall x y : expr, x = y -> provable (impp x y)) := provable_impp_refl' .
  Definition provable_impp_arg_switch : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp y (impp x z)))) := provable_impp_arg_switch .
  Definition provable_impp_trans : (forall x y z : expr, provable (impp (impp x y) (impp (impp y z) (impp x z)))) := provable_impp_trans .
  Definition provable_multi_imp_shrink : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs (impp x y))) (multi_imp xs (impp x y)))) := provable_multi_imp_shrink .
  Definition provable_multi_imp_arg_switch1 : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs y)) (multi_imp xs (impp x y)))) := provable_multi_imp_arg_switch1 .
  Definition provable_multi_imp_arg_switch2 : (forall (xs : list expr) (x y : expr), provable (impp (multi_imp xs (impp x y)) (impp x (multi_imp xs y)))) := provable_multi_imp_arg_switch2 .
  Definition provable_add_multi_imp_left_head : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs2 y) (multi_imp (xs1 ++ xs2) y))) := provable_add_multi_imp_left_head .
  Definition provable_add_multi_imp_left_tail : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs1 y) (multi_imp (xs1 ++ xs2) y))) := provable_add_multi_imp_left_tail .
  Definition provable_multi_imp_modus_ponens : (forall (xs : list expr) (y z : expr), provable (impp (multi_imp xs y) (impp (multi_imp xs (impp y z)) (multi_imp xs z)))) := provable_multi_imp_modus_ponens .
  Definition provable_multi_imp_weaken : (forall (xs : list expr) (x y : expr), provable (impp x y) -> provable (impp (multi_imp xs x) (multi_imp xs y))) := provable_multi_imp_weaken .
  Definition provable_impp_refl_instance : (Reflexive (fun x y : expr => provable (impp x y))) := provable_impp_refl_instance .
  Definition provable_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> Basics.impl) provable) := provable_proper_impp .
  Definition provables_impp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) --> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) impp) := provables_impp_proper_impp .
  Definition provable_andp_comm : (forall x y : expr, provable (iffp (andp x y) (andp y x))) := provable_andp_comm .
  Definition provable_andp_assoc : (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) := provable_andp_assoc .
  Definition provable_impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) := provable_impp_curry .
  Definition provable_impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) := provable_impp_uncurry .
  Definition provables_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) := provables_impp_trans .
  Definition provables_andp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) andp) := provables_andp_proper_impp .
  Definition provable_iffp_equiv : (Equivalence (fun x y : expr => provable (iffp x y))) := provable_iffp_equiv .
  Definition provable_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> iff) provable) := provable_proper_iffp .
  Definition provables_impp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) impp) := provables_impp_proper_iffp .
  Definition provables_andp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) andp) := provables_andp_proper_iffp .
  Definition provables_iffp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) iffp) := provables_iffp_proper_iffp .
  Definition provables_emp_sepcon_unfold : (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) := provables_emp_sepcon_unfold .
  Definition provables_sepcon_impp_unfold : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) := provables_sepcon_impp_unfold .
  Definition provables_sepcon_sepcon_unfold : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) := provables_sepcon_sepcon_unfold .
  Definition provables_sepcon_assoc : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) := provables_sepcon_assoc .
  Definition provable_sepcon_emp_derives : (forall x : expr, provable (impp (sepcon x emp) x)) := provable_sepcon_emp_derives .
  Definition provables_sepcon_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) sepcon) := provables_sepcon_proper_impp .
  Definition provables_sepcon_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) sepcon) := provables_sepcon_proper_iffp .
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition cancel_different : (tree_pos -> tree_pos -> expr) := cancel_different .
  Definition cancel_same : (tree_pos -> tree_pos -> Prop) := cancel_same .
  Definition restore : (tree_pos -> tree_pos -> expr) := restore .
  Definition cancel_sound : (forall tep teq : tree_pos, cancel_same tep teq -> provable (cancel_different tep teq) -> provable (restore tep teq)) := cancel_sound .
  Definition logic_equiv_impp_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) impp) := logic_equiv_impp_proper .
  Definition logic_equiv_sepcon_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon) := logic_equiv_sepcon_proper .
  Definition provable_proper_equiv : (Proper (logic_equiv ==> iff) provable) := provable_proper_equiv .
  Definition logic_equiv_refl_instance : (Reflexive logic_equiv) := logic_equiv_refl_instance .
  Definition logic_equiv_symm_instance : (Symmetric logic_equiv) := logic_equiv_symm_instance .
  Definition logic_equiv_trans_instance : (Transitive logic_equiv) := logic_equiv_trans_instance .
  Definition logic_equiv_sepcon_comm : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) := logic_equiv_sepcon_comm .
  Definition logic_equiv_sepcon_assoc : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := logic_equiv_sepcon_assoc .
  Definition provable_sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) := provable_sepcon_emp_logic_equiv .
  Definition derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) := derivable1_proper_derivable1 .
  Definition logic_equiv_proper_logic_equiv : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv) := logic_equiv_proper_logic_equiv .
  Definition logic_equiv_proper_derivable1 : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1) := logic_equiv_proper_derivable1 .
  Definition derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) := derivable1s_sepcon_proper .
  End LogicTheorem.
(* derived rules as instance *)
  #[export] Existing Instance provable_impp_refl_instance .
  #[export] Existing Instance provable_proper_impp .
  #[export] Existing Instance provables_impp_proper_impp .
  #[export] Existing Instance provables_andp_proper_impp .
  #[export] Existing Instance provable_iffp_equiv .
  #[export] Existing Instance provable_proper_iffp .
  #[export] Existing Instance provables_impp_proper_iffp .
  #[export] Existing Instance provables_andp_proper_iffp .
  #[export] Existing Instance provables_iffp_proper_iffp .
  #[export] Existing Instance provables_sepcon_proper_impp .
  #[export] Existing Instance provables_sepcon_proper_iffp .
  #[export] Existing Instance logic_equiv_impp_proper .
  #[export] Existing Instance logic_equiv_sepcon_proper .
  #[export] Existing Instance provable_proper_equiv .
  #[export] Existing Instance logic_equiv_refl_instance .
  #[export] Existing Instance logic_equiv_symm_instance .
  #[export] Existing Instance logic_equiv_trans_instance .
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance logic_equiv_proper_logic_equiv .
  #[export] Existing Instance logic_equiv_proper_derivable1 .
  #[export] Existing Instance derivable1s_sepcon_proper .
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
