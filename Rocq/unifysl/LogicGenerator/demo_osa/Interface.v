Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
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

Module DerivedNames (Names: LanguageSig).
Include Names.
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
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Include Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom provables_sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) .
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
(* derived rules as instance *)
  Existing Instance provables_sepcon_proper_impp .
End LogicTheoremSig.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
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

Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names) <: LogicTheoremSig Names Rules.
Include Rules.
(* aux primitive instances *)
  Instance M : Model := (Build_Model model) .
  Instance L : Language := (Build_Language expr) .
  Instance J : (Join model) := join .
  Instance U : (Unit model) := is_unit .
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
  Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  Instance GammaP : (Provable L) := (Build_Provable L provable) .
  Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  Instance J_SA : (SeparationAlgebra model) := (Build_SeparationAlgebra model J join_comm join_assoc) .
(* aux refl instances for derivation *)
  Instance imppDef_model : (ImppDefinition_Model minL) := Model2Impp_Normal .
  Instance andpDef_model : (AndpDefinition_Model andpL) := Model2Andp_Normal .
  Instance orpDef_model : (OrpDefinition_Model orpL) := Model2Orp_Normal .
  Instance coqpropDef_model : (CoqPropDefinition_Model coq_prop_L) := Model2CoqProp_Normal .
  Instance sepconDef_join : (SepconDefinition_Join Join2Sepcon) := Join2Sepcon_Normal .
  Instance empDef_unit : (EmpDefinition_Unit Unit2Emp) := Unit2Emp_Normal .
  Instance provableDef_model : (ProvableDefinition_Model GammaP) := Model2Provable_Normal .
  Instance GammaD1P : (Derivable1FromProvable L GammaP GammaD1) := Provable2Derivable1_Normal .
(* aux derived instances *)
  Instance sepconAX : (SepconAxiomatization L GammaP) := SeparationAlgebra2SepconAxiomatization .
  Instance sepconD : (SepconDeduction L GammaD1) := SeparationLogic.Axiomatization2Deduction_sepconD .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := provable_sepcon_comm_impp .
  Definition provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := provable_sepcon_assoc1 .
  Definition provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) := provable_sepcon_mono .
  Definition provables_sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) := provables_sepcon_proper_impp .
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
(* derived rules as instance *)
  Existing Instance provables_sepcon_proper_impp .
End LogicTheorem.

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
