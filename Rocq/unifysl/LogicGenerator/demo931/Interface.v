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
  Axiom derivable1s_truep_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Axiom derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Axiom derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .
  Axiom derivable1s_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
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
  Axiom derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) .
  Axiom derivable1s_andp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) andp) .
  Axiom derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) .
(* derived rules as instance *)
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance derivable1s_andp_proper .
  #[export] Existing Instance derivable1s_sepcon_proper .
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
(* aux primitive instances *)
  #[export] Instance M : Model := (Build_Model model) .
  #[export] Instance L : Language := (Build_Language expr) .
  #[export] Instance J : (Join model) := join .
  #[export] Instance U : (Unit model) := is_unit .
  #[export] Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  #[export] Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  #[export] Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  #[export] Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
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
  #[export] Instance coq_prop_D : (CoqPropDeduction L GammaD1) := Model2CoqPropDeduction .
  #[export] Instance truepD : (TrueDeduction L GammaD1) := Model2TrueDeduction .
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
  Definition derivable1s_truep_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) := derivable1s_truep_intros .
  Definition derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) := derivable1_andp_elim1 .
  Definition derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) := derivable1_andp_elim2 .
  Definition derivable1s_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) := derivable1s_impp_andp_adjoint .
  Definition derivable1_refl : (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
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
  Definition derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) := derivable1_proper_derivable1 .
  Definition derivable1s_andp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) andp) := derivable1s_andp_proper .
  Definition derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) := derivable1s_sepcon_proper .
(* derived rules as instance *)
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance derivable1s_andp_proper .
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
