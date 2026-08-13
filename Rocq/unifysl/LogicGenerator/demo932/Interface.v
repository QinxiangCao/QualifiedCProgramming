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
  Definition sepcon := (fun (x y : model -> Prop) (m : model) => exists m1 m2 : model, join m1 m2 m /\ x m1 /\ y m2) .
  Definition wand := (fun (x y : model -> Prop) (m : model) => forall m1 m2 : model, join m m1 m2 -> x m1 -> y m2) .
  Definition orp := (fun (x y : model -> Prop) (m : model) => x m \/ y m) .
  Definition andp := (fun (x y : model -> Prop) (m : model) => x m /\ y m) .
  Definition impp := (fun (x y : model -> Prop) (m : model) => x m -> y m) .
  Definition exp := (fun (A : Type) (x : A -> model -> Prop) (m : model) => exists a : A, x a m) .
  Definition allp := (fun (A : Type) (x : A -> model -> Prop) (m : model) => forall a : A, x a m) .
  Definition emp := (fun m : model => is_unit m) .
  Definition coq_prop := (fun (P : Prop) (_ : model) => P) .
  Definition truep := (fun _ : model => True) .
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition iter_sepcon := (fun xs : list expr => fold_left sepcon xs emp) .
  Definition iffp := (fun x y : expr => andp (impp x y) (impp y x)) .
(* derived judgements *)
  Definition derivable1 := (fun x y : model -> Prop => forall m : model, x m -> y m) .
  Definition provable := (fun x : expr => derivable1 (impp x x) x) .
  Definition logic_equiv := (fun x y : expr => derivable1 x y /\ derivable1 y x) .
End DerivedNamesSig.

Module Type PrimitiveRuleSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names).
Import Names DerivedNames.
  Axiom unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Axiom unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Axiom join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames).
Import Names DerivedNames Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom derivable1s_coq_prop_r : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) .
  Axiom derivable1s_coq_prop_l : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
  Axiom derivable1_iter_sepcon_l : (forall xs : list expr, derivable1 (iter_sepcon xs) (fold_left sepcon xs emp)) .
  Axiom derivable1_iter_sepcon_r : (forall xs : list expr, derivable1 (fold_left sepcon xs emp) (iter_sepcon xs)) .
  Axiom derivable1s_allp_r : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) .
  Axiom derivable1s_allp_l : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) .
  Axiom derivable1s_exp_r : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) .
  Axiom derivable1s_exp_l : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) .
  Axiom __derivable1_provable : (forall x y : expr, derivable1 x y <-> provable (impp x y)) .
  Axiom logic_equiv_sepcon_emp : (forall x : expr, logic_equiv (sepcon x emp) x) .
  Axiom logic_equiv_andp_truep : (forall x : expr, logic_equiv (andp x truep) x) .
  Axiom logic_equiv_truep_andp : (forall x : expr, logic_equiv (andp truep x) x) .
  Axiom logic_equiv_sepcon_comm : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) .
  Axiom logic_equiv_sepcon_assoc : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom logic_equiv_orp_congr : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (orp x1 y1) (orp x2 y2)) .
  Axiom logic_equiv_orp_comm : (forall x y : expr, logic_equiv (orp x y) (orp y x)) .
  Axiom logic_equiv_orp_assoc : (forall x y z : expr, logic_equiv (orp (orp x y) z) (orp x (orp y z))) .
  Axiom logic_equiv_andp_congr : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (andp x1 y1) (andp x2 y2)) .
  Axiom logic_equiv_andp_comm : (forall x y : expr, logic_equiv (andp x y) (andp y x)) .
  Axiom logic_equiv_andp_assoc : (forall x y z : expr, logic_equiv (andp (andp x y) z) (andp x (andp y z))) .
  Axiom logic_equiv_refl : (forall x : expr, logic_equiv x x) .
  Axiom logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) .
  Axiom logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) .
  Axiom derivable1_orp_sepcon_l : (forall x y z : expr, derivable1 (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) .
  Axiom derivable1_sepcon_emp_l : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom derivable1_sepcon_emp_r : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1s_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_iffp_intros : (forall x y : expr, derivable1 (impp x y) (impp (impp y x) (iffp x y))) .
  Axiom derivable1_iffp_elim1 : (forall x y : expr, derivable1 (iffp x y) (impp x y)) .
  Axiom derivable1_iffp_elim2 : (forall x y : expr, derivable1 (iffp x y) (impp y x)) .
  Axiom derivable1_truep_intros : (forall x : expr, derivable1 x truep) .
  Axiom derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Axiom derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Axiom derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Axiom derivable1s_truep_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
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
  Axiom provable_iter_sepcon_derives : (forall xs : list expr, provable (impp (iter_sepcon xs) (fold_left sepcon xs emp))) .
  Axiom provable_derives_iter_sepcon : (forall xs : list expr, provable (impp (fold_left sepcon xs emp) (iter_sepcon xs))) .
  Axiom provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom provables_coq_prop_intros : (forall P : Prop, P -> provable (coq_prop P)) .
  Axiom provables_coq_prop_elim : (forall (P : Prop) (x : expr), (P -> provable x) -> provable (impp (coq_prop P) x)) .
  Axiom provable_iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) .
  Axiom provable_iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) .
  Axiom provable_iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) .
  Axiom provable_orp_intros1 : (forall x y : expr, provable (impp x (orp x y))) .
  Axiom provable_orp_intros2 : (forall x y : expr, provable (impp y (orp x y))) .
  Axiom provable_orp_elim : (forall x y z : expr, provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z)))) .
  Axiom provable_andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) .
  Axiom provable_andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) .
  Axiom provable_andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) .
  Axiom provables_modus_ponens : (forall x y : expr, provable (impp x y) -> provable x -> provable y) .
  Axiom provable_axiom1 : (forall x y : expr, provable (impp x (impp y x))) .
  Axiom provable_axiom2 : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) .
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
  Axiom provable_orp_comm : (forall x y : expr, provable (iffp (orp x y) (orp y x))) .
  Axiom provable_orp_dup : (forall x : expr, provable (iffp (orp x x) x)) .
  Axiom provable_impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) .
  Axiom provable_impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) .
  Axiom provables_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) .
  Axiom provables_andp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) andp) .
  Axiom provables_orp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) orp) .
  Axiom provable_iffp_equiv : (Equivalence (fun x y : expr => provable (iffp x y))) .
  Axiom provable_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> iff) provable) .
  Axiom provables_impp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) impp) .
  Axiom provables_andp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) andp) .
  Axiom provables_orp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) orp) .
  Axiom provables_iffp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) iffp) .
  Axiom provables_coq_prop_andp_derives : (forall (P : Prop) (Q R : expr), (P -> provable (impp Q R)) -> provable (impp (andp (coq_prop P) Q) R)) .
  Axiom provables_andp_coq_prop_derives : (forall (P : Prop) (Q R : expr), (P -> provable (impp Q R)) -> provable (impp (andp Q (coq_prop P)) R)) .
  Axiom provables_impp_coq_prop : (forall (P : Prop) (Q : expr), P -> provable (impp Q (coq_prop P))) .
  Axiom provable_coq_prop_or : (forall P Q : Prop, provable (iffp (coq_prop (P \/ Q)) (orp (coq_prop P) (coq_prop Q)))) .
  Axiom logic_equiv_sepcon_orp_distr : (forall x y z : expr, logic_equiv (sepcon x (orp y z)) (orp (sepcon x y) (sepcon x z))) .
  Axiom logic_equiv_orp_sepcon_distr : (forall x y z : expr, logic_equiv (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) .
  Axiom provables_sepcon_impp_unfold : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) .
  Axiom provables_sepcon_sepcon_unfold : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) .
  Axiom provables_sepcon_assoc : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) .
  Axiom provables_sepcon_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) sepcon) .
  Axiom provables_sepcon_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) sepcon) .
  Axiom logic_equiv_sepcon_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon) .
  Axiom logic_equiv_refl_instance : (Reflexive logic_equiv) .
  Axiom logic_equiv_symm_instance : (Symmetric logic_equiv) .
  Axiom logic_equiv_trans_instance : (Transitive logic_equiv) .
  Axiom provable_sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) .
  Axiom derivable1_exp_andp_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) .
  Axiom derivable1_andp_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) .
  Axiom derivable1_exp_sepcon_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) .
  Axiom derivable1_sepcon_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (sepcon P (exp A Q)) (exp A (fun x : A => sepcon P (Q x)))) .
  Axiom derivable1_iter_sepcon_flatten : (forall xs1 xs2 xs3 : list expr, derivable1 (iter_sepcon (xs1 ++ iter_sepcon xs2 :: xs3)) (iter_sepcon (xs1 ++ xs2 ++ xs3))) .
  Axiom derivable1_sepcon_coq_prop_andp_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R))) .
  Axiom derivable1_sepcon_coq_prop_andp_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) .
  Axiom derivable1_sepcon_andp_coq_prop_l : (forall (P Q : expr) (R : Prop), derivable1 (sepcon P (andp Q (coq_prop R))) (andp (coq_prop R) (sepcon P Q))) .
  Axiom derivable1_sepcon_andp_coq_prop_r : (forall (P Q : expr) (R : Prop), derivable1 (andp (coq_prop R) (sepcon P Q)) (sepcon P (andp Q (coq_prop R)))) .
  Axiom derivable1_coq_prop_andp_sepcon_l : (forall (P : Prop) (Q R : expr), derivable1 (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) .
  Axiom derivable1_coq_prop_andp_sepcon_r : (forall (P : Prop) (Q R : expr), derivable1 (andp (coq_prop P) (sepcon Q R)) (sepcon (andp (coq_prop P) Q) R)) .
  Axiom derivable1_andp_coq_prop_sepcon_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon (andp P (coq_prop Q)) R) (andp (coq_prop Q) (sepcon P R))) .
  Axiom derivable1_andp_coq_prop_sepcon_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon (andp P (coq_prop Q)) R)) .
  Axiom derivable1_iter_sepcon_coq_prop_andp_l : (forall (xs1 : list expr) (P : Prop) (x2 : expr) (xs3 : list expr), derivable1 (iter_sepcon (xs1 ++ andp (coq_prop P) x2 :: xs3)) (andp (coq_prop P) (iter_sepcon (xs1 ++ x2 :: xs3)))) .
  Axiom derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) .
  Axiom logic_equiv_proper_logic_equiv : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv) .
  Axiom logic_equiv_proper_derivable1 : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1) .
  Axiom derivable1s_andp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) andp) .
  Axiom derivable1s_orp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) orp) .
  Axiom derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) .
  Axiom logic_equiv_wand_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) wand) .
  Axiom derivable1s_wand_proper : (Proper (derivable1 --> derivable1 ==> derivable1) wand) .
  Axiom logic_equiv_coq_prop_or : (forall P Q : Prop, logic_equiv (coq_prop (P \/ Q)) (orp (coq_prop P) (coq_prop Q))) .
  Axiom logic_equiv_coq_prop_and : (forall P Q : Prop, logic_equiv (coq_prop (P /\ Q)) (andp (coq_prop P) (coq_prop Q))) .
  Axiom derivable1s_coq_prop_andp_l : (forall (P : Prop) (Q R : expr), (P -> derivable1 Q R) -> derivable1 (andp (coq_prop P) Q) R) .
  Axiom derivable1s_coq_prop_andp_r : (forall (P : Prop) (Q R : expr), derivable1 R Q -> P -> derivable1 R (andp (coq_prop P) Q)) .
  Axiom logic_equiv_coq_prop_andp2 : (forall (P : Prop) (Q : expr), P -> logic_equiv (andp (coq_prop P) Q) Q) .
  Axiom derivables_coq_prop_imply : (forall P Q : Prop, (P -> Q) -> derivable1 (coq_prop P) (coq_prop Q)) .
  Axiom derivables_false_coq_prop : (forall (P : Prop) (Q : expr), (P -> False) -> derivable1 (coq_prop P) Q) .
  Axiom derivable1_sepcon_orp_l : (forall x y z : expr, derivable1 (sepcon z (orp x y)) (orp (sepcon z x) (sepcon z y))) .
  Axiom derivable1_orp_sepcon_r : (forall x y z : expr, derivable1 (orp (sepcon x z) (sepcon y z)) (sepcon (orp x y) z)) .
  Axiom derivable1_sepcon_orp_r : (forall x y z : expr, derivable1 (orp (sepcon z x) (sepcon z y)) (sepcon z (orp x y))) .
  Axiom logic_equiv_orp_sepcon : (forall x y z : expr, logic_equiv (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) .
  Axiom logic_equiv_sepcon_orp : (forall x y z : expr, logic_equiv (sepcon z (orp x y)) (orp (sepcon z x) (sepcon z y))) .
  Axiom logic_equiv_andp_swap : (forall x y z : expr, logic_equiv (andp x (andp y z)) (andp y (andp x z))) .
  Axiom derivable1s_andp_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (andp x1 y1) (andp x2 y2)) .
  Axiom logic_equiv_sepcon_swap : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon y (sepcon x z))) .
  Axiom logic_equiv_coq_prop_andp1 : (forall (P : expr) (Q : Prop), derivable1 P (coq_prop Q) -> logic_equiv P (andp (coq_prop Q) P)) .
  Axiom derivable1s_emp_l_unfold : (forall x y : expr, derivable1 emp y -> derivable1 x (sepcon x y)) .
  Axiom derivable1s_emp_sepcon_unfold : (forall x y z : expr, derivable1 x z -> derivable1 emp y -> derivable1 x (sepcon z y)) .
  Axiom logic_equiv_sepcon_coq_prop_andp : (forall (P : expr) (Q : Prop) (R : expr), logic_equiv (sepcon P (andp (coq_prop Q) R)) (sepcon (andp (coq_prop Q) P) R)) .
  Axiom logic_equiv_coq_prop_andp_sepcon : (forall (P : Prop) (Q R : expr), logic_equiv (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) .
  Axiom logic_equiv_coq_prop_andp_sepcon_truep : (forall (P : expr) (Q : Prop), logic_equiv (sepcon P (coq_prop Q)) (sepcon (andp (coq_prop Q) P) truep)) .
  Axiom derivable1s_ex_l_unfold : (forall (A : Type) (P : A -> expr) (Q : expr), (exists x : A, derivable1 (P x) Q) -> derivable1 (allp A P) Q) .
  Axiom derivable1_exp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (exp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => exp A (fun x : A => P x y)))) .
  Axiom derivable1_allp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (allp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => allp A (fun x : A => P x y)))) .
  Axiom logic_equiv_exp_andp : (forall (A : Type) (P : A -> expr) (Q : expr), logic_equiv (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) .
  Axiom logic_equiv_exp_sepcon : (forall (A : Type) (P : A -> expr) (Q : expr), logic_equiv (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) .
  Axiom logic_equiv_wand : (forall x y x' y' : expr, logic_equiv x x' -> logic_equiv y y' -> logic_equiv (wand x y) (wand x' y')) .
  Axiom derivable1_wand_elim1 : (forall x y : expr, derivable1 (sepcon (wand x y) x) y) .
  Axiom derivable1_wand_elim2 : (forall x y : expr, derivable1 (sepcon x (wand x y)) y) .
  Axiom logic_equiv_orp_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) orp) .
  Axiom logic_equiv_andp_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) andp) .
  Axiom provable_iffp_rewrite : (RewriteRelation (fun x y : expr => provable (iffp x y))) .
  Axiom derivable1s_impp_proper : (Proper (derivable1 --> derivable1 ==> derivable1) impp) .
  Axiom Derivable_impp_rewrite : (RewriteRelation derivable1) .
  Axiom derivable1_refl_instance : (Reflexive derivable1) .
  Axiom derivable1_trans_instance : (Transitive derivable1) .
  Axiom derivable1_sepcon_iter_sepcon1 : (forall xs ys : list expr, derivable1 (sepcon (iter_sepcon xs) (iter_sepcon ys)) (iter_sepcon (xs ++ ys))) .
  Axiom derivable1_sepcon_iter_sepcon2 : (forall xs ys : list expr, derivable1 (iter_sepcon (xs ++ ys)) (sepcon (iter_sepcon xs) (iter_sepcon ys))) .
(* derived rules as instance *)
  #[export] Existing Instance provable_impp_refl_instance .
  #[export] Existing Instance provable_proper_impp .
  #[export] Existing Instance provables_impp_proper_impp .
  #[export] Existing Instance provables_andp_proper_impp .
  #[export] Existing Instance provables_orp_proper_impp .
  #[export] Existing Instance provable_iffp_equiv .
  #[export] Existing Instance provable_proper_iffp .
  #[export] Existing Instance provables_impp_proper_iffp .
  #[export] Existing Instance provables_andp_proper_iffp .
  #[export] Existing Instance provables_orp_proper_iffp .
  #[export] Existing Instance provables_iffp_proper_iffp .
  #[export] Existing Instance provables_sepcon_proper_impp .
  #[export] Existing Instance provables_sepcon_proper_iffp .
  #[export] Existing Instance logic_equiv_sepcon_proper .
  #[export] Existing Instance logic_equiv_refl_instance .
  #[export] Existing Instance logic_equiv_symm_instance .
  #[export] Existing Instance logic_equiv_trans_instance .
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance logic_equiv_proper_logic_equiv .
  #[export] Existing Instance logic_equiv_proper_derivable1 .
  #[export] Existing Instance derivable1s_andp_proper .
  #[export] Existing Instance derivable1s_orp_proper .
  #[export] Existing Instance derivable1s_sepcon_proper .
  #[export] Existing Instance logic_equiv_wand_proper .
  #[export] Existing Instance derivable1s_wand_proper .
  #[export] Existing Instance logic_equiv_orp_proper .
  #[export] Existing Instance logic_equiv_andp_proper .
  #[export] Existing Instance provable_iffp_rewrite .
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
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.GeneralLogic.ShallowEmbedded.ModelLanguage.
Require Import Logic.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.
Require Import Logic.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.
Require Import Logic.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.
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
  #[export] Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  #[export] Instance wandL : (WandLanguage L) := (Build_WandLanguage L wand) .
  #[export] Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  #[export] Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  #[export] Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  #[export] Instance expL : (ShallowExistsLanguage L) := (Build_ShallowExistsLanguage L exp) .
  #[export] Instance allpL : (ShallowForallLanguage L) := (Build_ShallowForallLanguage L allp) .
  #[export] Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  #[export] Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
  #[export] Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  #[export] Instance iter_sepcon_L : (IterSepconLanguage L) := (Build_IterSepconLanguage L iter_sepcon) .
  #[export] Instance iffpL : (IffLanguage L) := (Build_IffLanguage L iffp) .
  #[export] Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  #[export] Instance GammaP : (Provable L) := (Build_Provable L provable) .
  #[export] Instance GammaE : (LogicEquiv L) := (Build_LogicEquiv L logic_equiv) .
  #[export] Instance J_SA : (SeparationAlgebra model) := (Build_SeparationAlgebra model J join_comm join_assoc) .
  #[export] Instance UJR : (UnitJoinRelation model) := (Build_UnitJoinRelation model U J unit_join unit_spec) .
(* aux refl instances for derivation *)
  #[export] Instance sepconDef_join : (SepconDefinition_Join Join2Sepcon) := Join2Sepcon_Normal .
  #[export] Instance wandDef_join : (WandDefinition_Join Join2Wand) := Join2Wand_Normal .
  #[export] Instance orpDef_model : (OrpDefinition_Model orpL) := Model2Orp_Normal .
  #[export] Instance andpDef_model : (AndpDefinition_Model andpL) := Model2Andp_Normal .
  #[export] Instance imppDef_model : (ImppDefinition_Model minL) := Model2Impp_Normal .
  #[export] Instance expDef_model : (ExpDefinition_Model expL) := Model2Exp_Normal .
  #[export] Instance allpDef_model : (AllpDefinition_Model allpL) := Model2Allp_Normal .
  #[export] Instance empDef_unit : (EmpDefinition_Unit Unit2Emp) := Unit2Emp_Normal .
  #[export] Instance coqpropDef_model : (CoqPropDefinition_Model coq_prop_L) := Model2CoqProp_Normal .
  #[export] Instance truepDef_model : (TrueDefinition_Model truepL) := Model2Truep_Normal .
  #[export] Instance iter_sepcon_DL : (IterSepconDefinition_left L) := FoldLeftSepcon2IterSepcon_Normal .
  #[export] Instance iffpDef : (IffDefinition_And_Imp L) := AndImp2Iff_Normal .
  #[export] Instance derivable1Def_model : (Derivable1Definition_Model GammaD1) := Model2Derivable1_Normal .
  #[export] Instance GammaPD1 : (ProvableFromDerivable1 L GammaP GammaD1) := Derivable12Provable_Normal .
  #[export] Instance GammaED1 : (EquivDerivable1 L GammaD1 GammaE) := Derivable12Equiv_Normal .
(* aux derived instances *)
  #[export] Instance sepconD : (SepconDeduction L GammaD1) := SeparationAlgebra2SepconDeduction .
  #[export] Instance wandD : (WandDeduction L GammaD1) := SeparationAlgebra2WandDeduction .
  #[export] Instance adjD : (ImpAndAdjointDeduction L GammaD1) := Model2ImpAdjoint .
  #[export] Instance andpD : (AndDeduction L GammaD1) := Model2AndDeduction .
  #[export] Instance expD : (ShallowExistsDeduction L GammaD1) := Model2ExpDeduction .
  #[export] Instance allpD : (ShallowForallDeduction L GammaD1) := Model2AllDeduction .
  #[export] Instance bD : (BasicDeduction L GammaD1) := Model2BasicDeduction .
  #[export] Instance exp_andpD : deduction_exp_and := ExpDeduction2ExsitsAnd .
  #[export] Instance iter_sepcon_D1L : (IterSepconDeduction_left L GammaD1) := IterSepconFromDefToD1_L2L .
  #[export] Instance exp_sepconD : deduction_exp_sepcon := ExpDeduction2ExsitsSepcon .
  #[export] Instance minD : (MinimumDeduction L GammaD1) := Model2MinD1 .
  #[export] Instance empD : (EmpDeduction L GammaD1) := Model2EmpDeduction .
  #[export] Instance iter_sepcon_f : IterSepconFlatten := DeductionSepconFlatten .
  #[export] Instance coq_prop_D : (CoqPropDeduction L GammaD1) := Model2CoqPropDeduction .
  #[export] Instance truepD : (TrueDeduction L GammaD1) := Model2TrueDeduction .
  #[export] Instance sap : sepcon_andp_prop := Derived_sepcon_andp_prop .
  #[export] Instance sap_ext : sepcon_andp_prop_ext := Derived_sepcon_andp_prop_ext .
  #[export] Instance isap : Iter_sepcon_andp_prop := Derived_derivable1_iter_sepcon_coq_prop_andp_l .
  #[export] Instance bE : (BasicLogicEquiv L GammaE) := Deduction2Equiv_bE .
  #[export] Instance orpD : (OrDeduction L GammaD1) := Model2OrDeduction .
  #[export] Instance iffpD : (IffDeduction L GammaD1) := Model2IffDeduction .
  #[export] Instance sepcon_orp_D : (SepconOrDeduction L GammaD1) := Adj2SepconOrD .
  #[export] Instance andpE : (AndLogicEquiv L GammaE) := Deduction2LogicEquiv_andpE .
  #[export] Instance orpE : (OrLogicEquiv L GammaE) := Deduction2LogicEquiv_orpE .
  #[export] Instance sepconE : (SepconLogicEquiv_weak_iffp L GammaE) := Deduction2LogicEquiv_sepconE .
  #[export] Instance truepandpE : (TrueAndLogicEquiv L GammaE) := Deduction2LogicEquiv_truepandpE .
  #[export] Instance empE : (EmpLogicEquiv_iffp L GammaE) := Deduction2LogicEquiv_empE .
  #[export] Instance GammaD1P : (Derivable1FromProvable L GammaP GammaD1) := Deduction2Axiomatization_GammaD1P' .
  #[export] Instance minAX : (MinimumAxiomatization L GammaP) := Deduction2Axiomatization_minAX' .
  #[export] Instance iter_sepcon_AXL : (IterSepconAxiomatization_left L GammaP) := IterSepconFromDefToAX_L2L .
  #[export] Instance andpAX : (AndAxiomatization L GammaP) := Deduction2Axiomatization_andpAX .
  #[export] Instance iffpAX : (IffAxiomatization L GammaP) := IffFromDefToAX_And_Imp .
  #[export] Instance orpAX : (OrAxiomatization L GammaP) := Deduction2Axiomatization_orpAX .
  #[export] Instance sepconAX : (SepconAxiomatization L GammaP) := SepconDeduction2SepconAxiomatization_sepconAX .
  #[export] Instance coq_prop_AX : (CoqPropAxiomatization L GammaP) := Deduction2Axiomatization_coq_prop_AX .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition derivable1s_coq_prop_r : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) := derivable1s_coq_prop_r .
  Definition derivable1s_coq_prop_l : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) := derivable1s_coq_prop_l .
  Definition derivable1_iter_sepcon_l : (forall xs : list expr, derivable1 (iter_sepcon xs) (fold_left sepcon xs emp)) := derivable1_iter_sepcon_l .
  Definition derivable1_iter_sepcon_r : (forall xs : list expr, derivable1 (fold_left sepcon xs emp) (iter_sepcon xs)) := derivable1_iter_sepcon_r .
  Definition derivable1s_allp_r : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) := derivable1s_allp_r .
  Definition derivable1s_allp_l : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) := derivable1s_allp_l .
  Definition derivable1s_exp_r : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) := derivable1s_exp_r .
  Definition derivable1s_exp_l : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) := derivable1s_exp_l .
  Definition __derivable1_provable : (forall x y : expr, derivable1 x y <-> provable (impp x y)) := __derivable1_provable .
  Definition logic_equiv_sepcon_emp : (forall x : expr, logic_equiv (sepcon x emp) x) := logic_equiv_sepcon_emp .
  Definition logic_equiv_andp_truep : (forall x : expr, logic_equiv (andp x truep) x) := logic_equiv_andp_truep .
  Definition logic_equiv_truep_andp : (forall x : expr, logic_equiv (andp truep x) x) := logic_equiv_truep_andp .
  Definition logic_equiv_sepcon_comm : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) := logic_equiv_sepcon_comm .
  Definition logic_equiv_sepcon_assoc : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := logic_equiv_sepcon_assoc .
  Definition logic_equiv_orp_congr : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (orp x1 y1) (orp x2 y2)) := logic_equiv_orp_congr .
  Definition logic_equiv_orp_comm : (forall x y : expr, logic_equiv (orp x y) (orp y x)) := logic_equiv_orp_comm .
  Definition logic_equiv_orp_assoc : (forall x y z : expr, logic_equiv (orp (orp x y) z) (orp x (orp y z))) := logic_equiv_orp_assoc .
  Definition logic_equiv_andp_congr : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (andp x1 y1) (andp x2 y2)) := logic_equiv_andp_congr .
  Definition logic_equiv_andp_comm : (forall x y : expr, logic_equiv (andp x y) (andp y x)) := logic_equiv_andp_comm .
  Definition logic_equiv_andp_assoc : (forall x y z : expr, logic_equiv (andp (andp x y) z) (andp x (andp y z))) := logic_equiv_andp_assoc .
  Definition logic_equiv_refl : (forall x : expr, logic_equiv x x) := logic_equiv_refl .
  Definition logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) := logic_equiv_symm .
  Definition logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) := logic_equiv_trans .
  Definition derivable1_orp_sepcon_l : (forall x y z : expr, derivable1 (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) := derivable1_orp_sepcon_l .
  Definition derivable1_sepcon_emp_l : (forall x : expr, derivable1 (sepcon x emp) x) := derivable1_sepcon_emp_l .
  Definition derivable1_sepcon_emp_r : (forall x : expr, derivable1 x (sepcon x emp)) := derivable1_sepcon_emp_r .
  Definition derivable1s_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) := derivable1s_wand_sepcon_adjoint .
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_iffp_intros : (forall x y : expr, derivable1 (impp x y) (impp (impp y x) (iffp x y))) := derivable1_iffp_intros .
  Definition derivable1_iffp_elim1 : (forall x y : expr, derivable1 (iffp x y) (impp x y)) := derivable1_iffp_elim1 .
  Definition derivable1_iffp_elim2 : (forall x y : expr, derivable1 (iffp x y) (impp y x)) := derivable1_iffp_elim2 .
  Definition derivable1_truep_intros : (forall x : expr, derivable1 x truep) := derivable1_truep_intros .
  Definition derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) := derivable1_orp_intros1 .
  Definition derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) := derivable1_orp_intros2 .
  Definition derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) := derivable1_orp_elim .
  Definition derivable1s_truep_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) := derivable1s_truep_intros .
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
  Definition provable_iter_sepcon_derives : (forall xs : list expr, provable (impp (iter_sepcon xs) (fold_left sepcon xs emp))) := provable_iter_sepcon_derives .
  Definition provable_derives_iter_sepcon : (forall xs : list expr, provable (impp (fold_left sepcon xs emp) (iter_sepcon xs))) := provable_derives_iter_sepcon .
  Definition provable_sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := provable_sepcon_comm_impp .
  Definition provable_sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := provable_sepcon_assoc1 .
  Definition provable_sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) := provable_sepcon_mono .
  Definition provables_coq_prop_intros : (forall P : Prop, P -> provable (coq_prop P)) := provables_coq_prop_intros .
  Definition provables_coq_prop_elim : (forall (P : Prop) (x : expr), (P -> provable x) -> provable (impp (coq_prop P) x)) := provables_coq_prop_elim .
  Definition provable_iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) := provable_iffp_intros .
  Definition provable_iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) := provable_iffp_elim1 .
  Definition provable_iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) := provable_iffp_elim2 .
  Definition provable_orp_intros1 : (forall x y : expr, provable (impp x (orp x y))) := provable_orp_intros1 .
  Definition provable_orp_intros2 : (forall x y : expr, provable (impp y (orp x y))) := provable_orp_intros2 .
  Definition provable_orp_elim : (forall x y z : expr, provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z)))) := provable_orp_elim .
  Definition provable_andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) := provable_andp_intros .
  Definition provable_andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) := provable_andp_elim1 .
  Definition provable_andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) := provable_andp_elim2 .
  Definition provables_modus_ponens : (forall x y : expr, provable (impp x y) -> provable x -> provable y) := provables_modus_ponens .
  Definition provable_axiom1 : (forall x y : expr, provable (impp x (impp y x))) := provable_axiom1 .
  Definition provable_axiom2 : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) := provable_axiom2 .
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
  Definition provable_orp_comm : (forall x y : expr, provable (iffp (orp x y) (orp y x))) := provable_orp_comm .
  Definition provable_orp_dup : (forall x : expr, provable (iffp (orp x x) x)) := provable_orp_dup .
  Definition provable_impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) := provable_impp_curry .
  Definition provable_impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) := provable_impp_uncurry .
  Definition provables_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) := provables_impp_trans .
  Definition provables_andp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) andp) := provables_andp_proper_impp .
  Definition provables_orp_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) orp) := provables_orp_proper_impp .
  Definition provable_iffp_equiv : (Equivalence (fun x y : expr => provable (iffp x y))) := provable_iffp_equiv .
  Definition provable_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> iff) provable) := provable_proper_iffp .
  Definition provables_impp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) impp) := provables_impp_proper_iffp .
  Definition provables_andp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) andp) := provables_andp_proper_iffp .
  Definition provables_orp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) orp) := provables_orp_proper_iffp .
  Definition provables_iffp_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) iffp) := provables_iffp_proper_iffp .
  Definition provables_coq_prop_andp_derives : (forall (P : Prop) (Q R : expr), (P -> provable (impp Q R)) -> provable (impp (andp (coq_prop P) Q) R)) := provables_coq_prop_andp_derives .
  Definition provables_andp_coq_prop_derives : (forall (P : Prop) (Q R : expr), (P -> provable (impp Q R)) -> provable (impp (andp Q (coq_prop P)) R)) := provables_andp_coq_prop_derives .
  Definition provables_impp_coq_prop : (forall (P : Prop) (Q : expr), P -> provable (impp Q (coq_prop P))) := provables_impp_coq_prop .
  Definition provable_coq_prop_or : (forall P Q : Prop, provable (iffp (coq_prop (P \/ Q)) (orp (coq_prop P) (coq_prop Q)))) := provable_coq_prop_or .
  Definition logic_equiv_sepcon_orp_distr : (forall x y z : expr, logic_equiv (sepcon x (orp y z)) (orp (sepcon x y) (sepcon x z))) := logic_equiv_sepcon_orp_distr .
  Definition logic_equiv_orp_sepcon_distr : (forall x y z : expr, logic_equiv (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) := logic_equiv_orp_sepcon_distr .
  Definition provables_sepcon_impp_unfold : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) := provables_sepcon_impp_unfold .
  Definition provables_sepcon_sepcon_unfold : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) := provables_sepcon_sepcon_unfold .
  Definition provables_sepcon_assoc : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) := provables_sepcon_assoc .
  Definition provables_sepcon_proper_impp : (Proper ((fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y)) ==> (fun x y : expr => provable (impp x y))) sepcon) := provables_sepcon_proper_impp .
  Definition provables_sepcon_proper_iffp : (Proper ((fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y)) ==> (fun x y : expr => provable (iffp x y))) sepcon) := provables_sepcon_proper_iffp .
  Definition logic_equiv_sepcon_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon) := logic_equiv_sepcon_proper .
  Definition logic_equiv_refl_instance : (Reflexive logic_equiv) := logic_equiv_refl_instance .
  Definition logic_equiv_symm_instance : (Symmetric logic_equiv) := logic_equiv_symm_instance .
  Definition logic_equiv_trans_instance : (Transitive logic_equiv) := logic_equiv_trans_instance .
  Definition provable_sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) := provable_sepcon_emp_logic_equiv .
  Definition derivable1_exp_andp_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) := derivable1_exp_andp_l .
  Definition derivable1_andp_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) := derivable1_andp_exp_l .
  Definition derivable1_exp_sepcon_l : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) := derivable1_exp_sepcon_l .
  Definition derivable1_sepcon_exp_l : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (sepcon P (exp A Q)) (exp A (fun x : A => sepcon P (Q x)))) := derivable1_sepcon_exp_l .
  Definition derivable1_iter_sepcon_flatten : (forall xs1 xs2 xs3 : list expr, derivable1 (iter_sepcon (xs1 ++ iter_sepcon xs2 :: xs3)) (iter_sepcon (xs1 ++ xs2 ++ xs3))) := derivable1_iter_sepcon_flatten .
  Definition derivable1_sepcon_coq_prop_andp_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R))) := derivable1_sepcon_coq_prop_andp_l .
  Definition derivable1_sepcon_coq_prop_andp_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) := derivable1_sepcon_coq_prop_andp_r .
  Definition derivable1_sepcon_andp_coq_prop_l : (forall (P Q : expr) (R : Prop), derivable1 (sepcon P (andp Q (coq_prop R))) (andp (coq_prop R) (sepcon P Q))) := derivable1_sepcon_andp_coq_prop_l .
  Definition derivable1_sepcon_andp_coq_prop_r : (forall (P Q : expr) (R : Prop), derivable1 (andp (coq_prop R) (sepcon P Q)) (sepcon P (andp Q (coq_prop R)))) := derivable1_sepcon_andp_coq_prop_r .
  Definition derivable1_coq_prop_andp_sepcon_l : (forall (P : Prop) (Q R : expr), derivable1 (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) := derivable1_coq_prop_andp_sepcon_l .
  Definition derivable1_coq_prop_andp_sepcon_r : (forall (P : Prop) (Q R : expr), derivable1 (andp (coq_prop P) (sepcon Q R)) (sepcon (andp (coq_prop P) Q) R)) := derivable1_coq_prop_andp_sepcon_r .
  Definition derivable1_andp_coq_prop_sepcon_l : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon (andp P (coq_prop Q)) R) (andp (coq_prop Q) (sepcon P R))) := derivable1_andp_coq_prop_sepcon_l .
  Definition derivable1_andp_coq_prop_sepcon_r : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon (andp P (coq_prop Q)) R)) := derivable1_andp_coq_prop_sepcon_r .
  Definition derivable1_iter_sepcon_coq_prop_andp_l : (forall (xs1 : list expr) (P : Prop) (x2 : expr) (xs3 : list expr), derivable1 (iter_sepcon (xs1 ++ andp (coq_prop P) x2 :: xs3)) (andp (coq_prop P) (iter_sepcon (xs1 ++ x2 :: xs3)))) := derivable1_iter_sepcon_coq_prop_andp_l .
  Definition derivable1_proper_derivable1 : (Proper (derivable1 --> derivable1 ==> Basics.impl) derivable1) := derivable1_proper_derivable1 .
  Definition logic_equiv_proper_logic_equiv : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv) := logic_equiv_proper_logic_equiv .
  Definition logic_equiv_proper_derivable1 : (Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1) := logic_equiv_proper_derivable1 .
  Definition derivable1s_andp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) andp) := derivable1s_andp_proper .
  Definition derivable1s_orp_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) orp) := derivable1s_orp_proper .
  Definition derivable1s_sepcon_proper : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) := derivable1s_sepcon_proper .
  Definition logic_equiv_wand_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) wand) := logic_equiv_wand_proper .
  Definition derivable1s_wand_proper : (Proper (derivable1 --> derivable1 ==> derivable1) wand) := derivable1s_wand_proper .
  Definition logic_equiv_coq_prop_or : (forall P Q : Prop, logic_equiv (coq_prop (P \/ Q)) (orp (coq_prop P) (coq_prop Q))) := logic_equiv_coq_prop_or .
  Definition logic_equiv_coq_prop_and : (forall P Q : Prop, logic_equiv (coq_prop (P /\ Q)) (andp (coq_prop P) (coq_prop Q))) := logic_equiv_coq_prop_and .
  Definition derivable1s_coq_prop_andp_l : (forall (P : Prop) (Q R : expr), (P -> derivable1 Q R) -> derivable1 (andp (coq_prop P) Q) R) := derivable1s_coq_prop_andp_l .
  Definition derivable1s_coq_prop_andp_r : (forall (P : Prop) (Q R : expr), derivable1 R Q -> P -> derivable1 R (andp (coq_prop P) Q)) := derivable1s_coq_prop_andp_r .
  Definition logic_equiv_coq_prop_andp2 : (forall (P : Prop) (Q : expr), P -> logic_equiv (andp (coq_prop P) Q) Q) := logic_equiv_coq_prop_andp2 .
  Definition derivables_coq_prop_imply : (forall P Q : Prop, (P -> Q) -> derivable1 (coq_prop P) (coq_prop Q)) := derivables_coq_prop_imply .
  Definition derivables_false_coq_prop : (forall (P : Prop) (Q : expr), (P -> False) -> derivable1 (coq_prop P) Q) := derivables_false_coq_prop .
  Definition derivable1_sepcon_orp_l : (forall x y z : expr, derivable1 (sepcon z (orp x y)) (orp (sepcon z x) (sepcon z y))) := derivable1_sepcon_orp_l .
  Definition derivable1_orp_sepcon_r : (forall x y z : expr, derivable1 (orp (sepcon x z) (sepcon y z)) (sepcon (orp x y) z)) := derivable1_orp_sepcon_r .
  Definition derivable1_sepcon_orp_r : (forall x y z : expr, derivable1 (orp (sepcon z x) (sepcon z y)) (sepcon z (orp x y))) := derivable1_sepcon_orp_r .
  Definition logic_equiv_orp_sepcon : (forall x y z : expr, logic_equiv (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z))) := logic_equiv_orp_sepcon .
  Definition logic_equiv_sepcon_orp : (forall x y z : expr, logic_equiv (sepcon z (orp x y)) (orp (sepcon z x) (sepcon z y))) := logic_equiv_sepcon_orp .
  Definition logic_equiv_andp_swap : (forall x y z : expr, logic_equiv (andp x (andp y z)) (andp y (andp x z))) := logic_equiv_andp_swap .
  Definition derivable1s_andp_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (andp x1 y1) (andp x2 y2)) := derivable1s_andp_mono .
  Definition logic_equiv_sepcon_swap : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon y (sepcon x z))) := logic_equiv_sepcon_swap .
  Definition logic_equiv_coq_prop_andp1 : (forall (P : expr) (Q : Prop), derivable1 P (coq_prop Q) -> logic_equiv P (andp (coq_prop Q) P)) := logic_equiv_coq_prop_andp1 .
  Definition derivable1s_emp_l_unfold : (forall x y : expr, derivable1 emp y -> derivable1 x (sepcon x y)) := derivable1s_emp_l_unfold .
  Definition derivable1s_emp_sepcon_unfold : (forall x y z : expr, derivable1 x z -> derivable1 emp y -> derivable1 x (sepcon z y)) := derivable1s_emp_sepcon_unfold .
  Definition logic_equiv_sepcon_coq_prop_andp : (forall (P : expr) (Q : Prop) (R : expr), logic_equiv (sepcon P (andp (coq_prop Q) R)) (sepcon (andp (coq_prop Q) P) R)) := logic_equiv_sepcon_coq_prop_andp .
  Definition logic_equiv_coq_prop_andp_sepcon : (forall (P : Prop) (Q R : expr), logic_equiv (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) := logic_equiv_coq_prop_andp_sepcon .
  Definition logic_equiv_coq_prop_andp_sepcon_truep : (forall (P : expr) (Q : Prop), logic_equiv (sepcon P (coq_prop Q)) (sepcon (andp (coq_prop Q) P) truep)) := logic_equiv_coq_prop_andp_sepcon_truep .
  Definition derivable1s_ex_l_unfold : (forall (A : Type) (P : A -> expr) (Q : expr), (exists x : A, derivable1 (P x) Q) -> derivable1 (allp A P) Q) := derivable1s_ex_l_unfold .
  Definition derivable1_exp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (exp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => exp A (fun x : A => P x y)))) := derivable1_exp_allp_swap .
  Definition derivable1_allp_allp_swap : (forall (A B : Type) (P : A -> B -> expr), derivable1 (allp A (fun x : A => allp B (fun y : B => P x y))) (allp B (fun y : B => allp A (fun x : A => P x y)))) := derivable1_allp_allp_swap .
  Definition logic_equiv_exp_andp : (forall (A : Type) (P : A -> expr) (Q : expr), logic_equiv (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) := logic_equiv_exp_andp .
  Definition logic_equiv_exp_sepcon : (forall (A : Type) (P : A -> expr) (Q : expr), logic_equiv (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) := logic_equiv_exp_sepcon .
  Definition logic_equiv_wand : (forall x y x' y' : expr, logic_equiv x x' -> logic_equiv y y' -> logic_equiv (wand x y) (wand x' y')) := logic_equiv_wand .
  Definition derivable1_wand_elim1 : (forall x y : expr, derivable1 (sepcon (wand x y) x) y) := derivable1_wand_elim1 .
  Definition derivable1_wand_elim2 : (forall x y : expr, derivable1 (sepcon x (wand x y)) y) := derivable1_wand_elim2 .
  Definition logic_equiv_orp_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) orp) := logic_equiv_orp_proper .
  Definition logic_equiv_andp_proper : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) andp) := logic_equiv_andp_proper .
  Definition provable_iffp_rewrite : (RewriteRelation (fun x y : expr => provable (iffp x y))) := provable_iffp_rewrite .
  Definition derivable1s_impp_proper : (Proper (derivable1 --> derivable1 ==> derivable1) impp) := derivable1s_impp_proper .
  Definition Derivable_impp_rewrite : (RewriteRelation derivable1) := Derivable_impp_rewrite .
  Definition derivable1_refl_instance : (Reflexive derivable1) := derivable1_refl_instance .
  Definition derivable1_trans_instance : (Transitive derivable1) := derivable1_trans_instance .
  Definition derivable1_sepcon_iter_sepcon1 : (forall xs ys : list expr, derivable1 (sepcon (iter_sepcon xs) (iter_sepcon ys)) (iter_sepcon (xs ++ ys))) := derivable1_sepcon_iter_sepcon1 .
  Definition derivable1_sepcon_iter_sepcon2 : (forall xs ys : list expr, derivable1 (iter_sepcon (xs ++ ys)) (sepcon (iter_sepcon xs) (iter_sepcon ys))) := derivable1_sepcon_iter_sepcon2 .
(* derived rules as instance *)
  #[export] Existing Instance provable_impp_refl_instance .
  #[export] Existing Instance provable_proper_impp .
  #[export] Existing Instance provables_impp_proper_impp .
  #[export] Existing Instance provables_andp_proper_impp .
  #[export] Existing Instance provables_orp_proper_impp .
  #[export] Existing Instance provable_iffp_equiv .
  #[export] Existing Instance provable_proper_iffp .
  #[export] Existing Instance provables_impp_proper_iffp .
  #[export] Existing Instance provables_andp_proper_iffp .
  #[export] Existing Instance provables_orp_proper_iffp .
  #[export] Existing Instance provables_iffp_proper_iffp .
  #[export] Existing Instance provables_sepcon_proper_impp .
  #[export] Existing Instance provables_sepcon_proper_iffp .
  #[export] Existing Instance logic_equiv_sepcon_proper .
  #[export] Existing Instance logic_equiv_refl_instance .
  #[export] Existing Instance logic_equiv_symm_instance .
  #[export] Existing Instance logic_equiv_trans_instance .
  #[export] Existing Instance derivable1_proper_derivable1 .
  #[export] Existing Instance logic_equiv_proper_logic_equiv .
  #[export] Existing Instance logic_equiv_proper_derivable1 .
  #[export] Existing Instance derivable1s_andp_proper .
  #[export] Existing Instance derivable1s_orp_proper .
  #[export] Existing Instance derivable1s_sepcon_proper .
  #[export] Existing Instance logic_equiv_wand_proper .
  #[export] Existing Instance derivable1s_wand_proper .
  #[export] Existing Instance logic_equiv_orp_proper .
  #[export] Existing Instance logic_equiv_andp_proper .
  #[export] Existing Instance provable_iffp_rewrite .
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
