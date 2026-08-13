import Unifysl.LogicGenerator.demo932.Interface

/-!
demo932 facade layer.

This module packages the generated interface pieces into one explicit context and
re-exports the commonly used connectives, judgements, and rules through
method-style projections such as `ctx.sepcon` and `ctx.derivable1_sepcon_comm`.
SimpleC-specific predicates and notation intentionally live outside this file.
-/

universe u v

namespace Unifysl
namespace LogicGenerator
namespace demo932
namespace Facade

structure Context : Type (max (u + 1) (v + 1)) where
  Names : LanguageSig.{u}
  DerivedNames : DerivedNamesSig Names
  Rules : PrimitiveRuleSig Names DerivedNames
  Theorems : LogicTheoremSig'.{u, v} Names DerivedNames Rules :=
    LogicTheoremSig'.default Names DerivedNames Rules

namespace Context

abbrev model (ctx : Context.{u, v}) : Type u :=
  ctx.Names.model

abbrev expr (ctx : Context.{u, v}) : Type u :=
  LanguageSig.expr ctx.Names

abbrev join (ctx : Context.{u, v}) : ctx.model -> ctx.model -> ctx.model -> Prop :=
  ctx.Names.join

abbrev is_unit (ctx : Context.{u, v}) : ctx.model -> Prop :=
  ctx.Names.is_unit

abbrev unit_join (ctx : Context.{u, v}) :=
  ctx.Rules.unit_join

abbrev unit_spec (ctx : Context.{u, v}) :=
  ctx.Rules.unit_spec

abbrev join_comm (ctx : Context.{u, v}) :=
  ctx.Rules.join_comm

abbrev join_assoc (ctx : Context.{u, v}) :=
  ctx.Rules.join_assoc

abbrev baseTheorems (ctx : Context.{u, v}) :
    LogicTheoremSig.{u, v} ctx.Names ctx.DerivedNames ctx.Rules :=
  ctx.Theorems.toLogicTheoremSig

abbrev sepcon (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.sepcon ctx.DerivedNames

abbrev wand (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.wand ctx.DerivedNames

abbrev orp (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.orp ctx.DerivedNames

abbrev andp (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.andp ctx.DerivedNames

abbrev impp (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.impp ctx.DerivedNames

abbrev exp (ctx : Context.{u, v}) (A : Type v) : (A -> ctx.expr) -> ctx.expr :=
  DerivedNamesSig.exp ctx.DerivedNames A

abbrev allp (ctx : Context.{u, v}) (A : Type v) : (A -> ctx.expr) -> ctx.expr :=
  DerivedNamesSig.allp ctx.DerivedNames A

abbrev emp (ctx : Context.{u, v}) : ctx.expr :=
  DerivedNamesSig.emp ctx.DerivedNames

abbrev coq_prop (ctx : Context.{u, v}) : Prop -> ctx.expr :=
  DerivedNamesSig.coq_prop ctx.DerivedNames

abbrev truep (ctx : Context.{u, v}) : ctx.expr :=
  DerivedNamesSig.truep ctx.DerivedNames

abbrev multi_imp (ctx : Context.{u, v}) : List ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.multi_imp ctx.DerivedNames

abbrev iter_sepcon (ctx : Context.{u, v}) : List ctx.expr -> ctx.expr :=
  DerivedNamesSig.iter_sepcon ctx.DerivedNames

abbrev iffp (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> ctx.expr :=
  DerivedNamesSig.iffp ctx.DerivedNames

abbrev derivable1 (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> Prop :=
  DerivedNamesSig.derivable1 ctx.DerivedNames

abbrev provable (ctx : Context.{u, v}) : ctx.expr -> Prop :=
  DerivedNamesSig.provable ctx.DerivedNames

abbrev logic_equiv (ctx : Context.{u, v}) : ctx.expr -> ctx.expr -> Prop :=
  DerivedNamesSig.logic_equiv ctx.DerivedNames

abbrev derivable1s_coq_prop_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_coq_prop_r ctx.baseTheorems

abbrev derivable1s_coq_prop_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_coq_prop_l ctx.baseTheorems

abbrev derivable1_iter_sepcon_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iter_sepcon_l ctx.baseTheorems

abbrev derivable1_iter_sepcon_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iter_sepcon_r ctx.baseTheorems

abbrev derivable1s_allp_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_allp_r ctx.baseTheorems

abbrev derivable1s_allp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_allp_l ctx.baseTheorems

abbrev derivable1s_exp_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_exp_r ctx.baseTheorems

abbrev derivable1s_exp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_exp_l ctx.baseTheorems

abbrev __derivable1_provable (ctx : Context.{u, v}) :=
  LogicTheoremSig.__derivable1_provable ctx.baseTheorems

abbrev logic_equiv_sepcon_emp (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_emp ctx.baseTheorems

abbrev logic_equiv_andp_truep (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_andp_truep ctx.baseTheorems

abbrev logic_equiv_truep_andp (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_truep_andp ctx.baseTheorems

abbrev logic_equiv_sepcon_comm (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_comm ctx.baseTheorems

abbrev logic_equiv_sepcon_assoc (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_assoc ctx.baseTheorems

abbrev logic_equiv_orp_congr (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_orp_congr ctx.baseTheorems

abbrev logic_equiv_orp_comm (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_orp_comm ctx.baseTheorems

abbrev logic_equiv_orp_assoc (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_orp_assoc ctx.baseTheorems

abbrev logic_equiv_andp_congr (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_andp_congr ctx.baseTheorems

abbrev logic_equiv_andp_comm (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_andp_comm ctx.baseTheorems

abbrev logic_equiv_andp_assoc (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_andp_assoc ctx.baseTheorems

abbrev logic_equiv_refl (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_refl

abbrev logic_equiv_symm (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_symm

abbrev logic_equiv_trans (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_trans

abbrev derivable1_orp_sepcon_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_orp_sepcon_l ctx.baseTheorems

abbrev derivable1_sepcon_emp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_emp_l ctx.baseTheorems

abbrev derivable1_sepcon_emp_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_emp_r ctx.baseTheorems

abbrev derivable1s_wand_sepcon_adjoint (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_wand_sepcon_adjoint ctx.baseTheorems

abbrev derivable1_sepcon_comm (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_sepcon_comm

abbrev derivable1_sepcon_assoc1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_sepcon_assoc1

abbrev derivable1_sepcon_mono (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_sepcon_mono

abbrev derivable1_iffp_intros (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iffp_intros ctx.baseTheorems

abbrev derivable1_iffp_elim1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iffp_elim1 ctx.baseTheorems

abbrev derivable1_iffp_elim2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iffp_elim2 ctx.baseTheorems

abbrev derivable1_truep_intros (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_truep_intros

abbrev derivable1_orp_intros1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_orp_intros1

abbrev derivable1_orp_intros2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_orp_intros2

abbrev derivable1_orp_elim (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_orp_elim

abbrev derivable1s_truep_intros (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1s_truep_intros

abbrev derivable1_andp_intros (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_andp_intros ctx.baseTheorems

abbrev derivable1_andp_elim1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_andp_elim1

abbrev derivable1_andp_elim2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_andp_elim2

abbrev derivable1s_impp_andp_adjoint (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1s_impp_andp_adjoint

abbrev derivable1_impp_andp_adjoint (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_impp_andp_adjoint ctx.baseTheorems

abbrev derivable1s_modus_ponens (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_modus_ponens ctx.baseTheorems

abbrev derivable1s_impp_intros (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_impp_intros ctx.baseTheorems

abbrev derivable1_impp_refl (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_impp_refl ctx.baseTheorems

abbrev derivable1_axiom1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_axiom1 ctx.baseTheorems

abbrev derivable1_axiom2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_axiom2 ctx.baseTheorems

abbrev derivable1_refl (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_refl

abbrev derivable1_trans (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_trans

abbrev logic_equiv_sepcon_swap (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_swap ctx.baseTheorems

abbrev logic_equiv_andp_swap (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_andp_swap ctx.baseTheorems

abbrev derivable1_exp_andp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_exp_andp_l ctx.baseTheorems

abbrev derivable1_andp_exp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_andp_exp_l ctx.baseTheorems

abbrev derivable1_exp_sepcon_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_exp_sepcon_l ctx.baseTheorems

abbrev derivable1_sepcon_exp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_exp_l ctx.baseTheorems

abbrev derivable1_iter_sepcon_flatten (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iter_sepcon_flatten ctx.baseTheorems

abbrev derivable1_iter_sepcon_coq_prop_andp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_iter_sepcon_coq_prop_andp_l ctx.baseTheorems

abbrev derivable1_sepcon_iter_sepcon1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_sepcon_iter_sepcon1

abbrev derivable1_sepcon_iter_sepcon2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_sepcon_iter_sepcon2

abbrev derivable1_wand_elim1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_wand_elim1 ctx.baseTheorems

abbrev derivable1_wand_elim2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_wand_elim2 ctx.baseTheorems

abbrev logic_equiv_coq_prop_or (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_coq_prop_or ctx.baseTheorems

abbrev logic_equiv_coq_prop_and (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_coq_prop_and ctx.baseTheorems

abbrev logic_equiv_coq_prop_andp_sepcon (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_coq_prop_andp_sepcon ctx.baseTheorems

abbrev logic_equiv_sepcon_coq_prop_andp (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_coq_prop_andp ctx.baseTheorems

abbrev derivables_false_coq_prop (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivables_false_coq_prop ctx.baseTheorems

abbrev derivable1_wand_sepcon_modus_ponens1 (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1_wand_sepcon_modus_ponens1

abbrev derivable1_wand_sepcon_modus_ponens2 (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1_wand_sepcon_modus_ponens2

abbrev derivable1_wand_mono (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1_wand_mono

abbrev wand_andp_logic_equiv (ctx : Context.{u, v}) :=
  ctx.Theorems.wand_andp_logic_equiv

abbrev logic_equiv_derivable1 (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_derivable1

abbrev derivable_impp_rewrite_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable_impp_rewrite_inst

abbrev derivable1_refl_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1_refl_inst

abbrev derivable1_trans_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1_trans_inst

abbrev logic_equiv_impp_rewrite_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_impp_rewrite_inst

abbrev logic_equiv_refl_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_refl_inst

abbrev logic_equiv_symm_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_symm_inst

abbrev logic_equiv_trans_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_trans_inst

abbrev logic_equiv_equivalence_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_equivalence_inst

abbrev tree_pos (ctx : Context.{u, v}) :=
  ctx.baseTheorems.tree_pos

abbrev coq_prop_right (ctx : Context.{u, v}) :=
  ctx.baseTheorems.coq_prop_right

abbrev coq_prop_left (ctx : Context.{u, v}) :=
  ctx.baseTheorems.coq_prop_left

abbrev iter_sepcon_d1_left1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.iter_sepcon_d1_left1

abbrev iter_sepcon_d1_left2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.iter_sepcon_d1_left2

abbrev shallow_exp_right (ctx : Context.{u, v}) :=
  ctx.baseTheorems.shallow_exp_right

abbrev shallow_exp_left (ctx : Context.{u, v}) :=
  ctx.baseTheorems.shallow_exp_left

abbrev shallow_allp_right (ctx : Context.{u, v}) :=
  ctx.baseTheorems.shallow_allp_right

abbrev shallow_allp_left (ctx : Context.{u, v}) :=
  ctx.baseTheorems.shallow_allp_left

abbrev sepcon_emp_left (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_emp_left

abbrev sepcon_emp_right (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_emp_right

abbrev derivable1_wand_sepcon_adjoint (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_wand_sepcon_adjoint

abbrev expr_deep (ctx : Context.{u, v}) :=
  ctx.baseTheorems.expr_deep

abbrev impp_deep (ctx : Context.{u, v}) :=
  ctx.baseTheorems.impp_deep

abbrev sepcon_deep (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_deep

abbrev emp_deep (ctx : Context.{u, v}) :=
  ctx.baseTheorems.emp_deep

abbrev varp_deep (ctx : Context.{u, v}) :=
  ctx.baseTheorems.varp_deep

abbrev var_pos (ctx : Context.{u, v}) :=
  ctx.baseTheorems.var_pos

abbrev sepcon_pos (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_pos

abbrev cancel_mark (ctx : Context.{u, v}) :=
  ctx.baseTheorems.cancel_mark

abbrev cancel_different (ctx : Context.{u, v}) :=
  ctx.baseTheorems.cancel_different

abbrev cancel_same (ctx : Context.{u, v}) :=
  ctx.baseTheorems.cancel_same

abbrev restore (ctx : Context.{u, v}) :=
  ctx.baseTheorems.restore

abbrev logic_equiv_sepcon_proper (ctx : Context.{u, v}) :=
  ctx.baseTheorems.logic_equiv_sepcon_proper

abbrev sepcon_comm_logic_equiv (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_comm_logic_equiv

abbrev sepcon_assoc_logic_equiv (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_assoc_logic_equiv

abbrev sepcon_emp_logic_equiv (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_emp_logic_equiv

abbrev ex_and1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.ex_and1

abbrev ex_and2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.ex_and2

abbrev ex_sepcon1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.ex_sepcon1

abbrev ex_sepcon2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.ex_sepcon2

abbrev iter_sepcon_flatten (ctx : Context.{u, v}) :=
  ctx.baseTheorems.iter_sepcon_flatten

abbrev sepcon_andp_prop1 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop1

abbrev sepcon_andp_prop2 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop2

abbrev sepcon_andp_prop3 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop3

abbrev sepcon_andp_prop4 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop4

abbrev sepcon_andp_prop5 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop5

abbrev sepcon_andp_prop6 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop6

abbrev sepcon_andp_prop7 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop7

abbrev sepcon_andp_prop8 (ctx : Context.{u, v}) :=
  ctx.baseTheorems.sepcon_andp_prop8

abbrev iter_sepcon_andp_prop (ctx : Context.{u, v}) :=
  ctx.baseTheorems.iter_sepcon_andp_prop

abbrev derivable1_refl_instance (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_refl_instance

abbrev derivable1_trans_instance (ctx : Context.{u, v}) :=
  ctx.baseTheorems.derivable1_trans_instance

abbrev provable_iter_sepcon_derives (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_iter_sepcon_derives ctx.baseTheorems

abbrev provable_derives_iter_sepcon (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_derives_iter_sepcon ctx.baseTheorems

abbrev provable_sepcon_comm_impp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_sepcon_comm_impp ctx.baseTheorems

abbrev provable_sepcon_assoc1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_sepcon_assoc1 ctx.baseTheorems

abbrev provable_sepcon_mono (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_sepcon_mono ctx.baseTheorems

abbrev provables_coq_prop_intros (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_coq_prop_intros ctx.baseTheorems

abbrev provables_coq_prop_elim (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_coq_prop_elim ctx.baseTheorems

abbrev provable_iffp_intros (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_iffp_intros ctx.baseTheorems

abbrev provable_iffp_elim1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_iffp_elim1 ctx.baseTheorems

abbrev provable_iffp_elim2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_iffp_elim2 ctx.baseTheorems

abbrev provable_orp_intros1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_orp_intros1 ctx.baseTheorems

abbrev provable_orp_intros2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_orp_intros2 ctx.baseTheorems

abbrev provable_orp_elim (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_orp_elim ctx.baseTheorems

abbrev provable_andp_intros (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_andp_intros ctx.baseTheorems

abbrev provable_andp_elim1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_andp_elim1 ctx.baseTheorems

abbrev provable_andp_elim2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_andp_elim2 ctx.baseTheorems

abbrev provables_modus_ponens (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_modus_ponens ctx.baseTheorems

abbrev provable_axiom1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_axiom1 ctx.baseTheorems

abbrev provable_axiom2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_axiom2 ctx.baseTheorems

abbrev provable_impp_refl (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_refl ctx.baseTheorems

abbrev provable_impp_refl' (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_refl' ctx.baseTheorems

abbrev provable_impp_arg_switch (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_arg_switch ctx.baseTheorems

abbrev provable_impp_trans (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_trans ctx.baseTheorems

abbrev provable_multi_imp_shrink (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_multi_imp_shrink ctx.baseTheorems

abbrev provable_multi_imp_arg_switch1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_multi_imp_arg_switch1 ctx.baseTheorems

abbrev provable_multi_imp_arg_switch2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_multi_imp_arg_switch2 ctx.baseTheorems

abbrev provable_add_multi_imp_left_head (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_add_multi_imp_left_head ctx.baseTheorems

abbrev provable_add_multi_imp_left_tail (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_add_multi_imp_left_tail ctx.baseTheorems

abbrev provable_multi_imp_modus_ponens (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_multi_imp_modus_ponens ctx.baseTheorems

abbrev provable_multi_imp_weaken (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_multi_imp_weaken ctx.baseTheorems

abbrev provable_impp_refl_instance (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_refl_instance ctx.baseTheorems

abbrev provable_proper_impp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_proper_impp ctx.baseTheorems

abbrev provables_impp_proper_impp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_impp_proper_impp ctx.baseTheorems

abbrev provable_andp_comm (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_andp_comm ctx.baseTheorems

abbrev provable_andp_assoc (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_andp_assoc ctx.baseTheorems

abbrev provable_orp_comm (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_orp_comm ctx.baseTheorems

abbrev provable_orp_dup (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_orp_dup ctx.baseTheorems

abbrev provable_impp_curry (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_curry ctx.baseTheorems

abbrev provable_impp_uncurry (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_impp_uncurry ctx.baseTheorems

abbrev provables_impp_trans (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_impp_trans ctx.baseTheorems

abbrev provables_andp_proper_impp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_andp_proper_impp ctx.baseTheorems

abbrev provables_orp_proper_impp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_orp_proper_impp ctx.baseTheorems

abbrev provable_iffp_rewrite (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_iffp_rewrite ctx.baseTheorems

abbrev provable_iffp_equiv (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_iffp_equiv ctx.baseTheorems

abbrev provable_proper_iffp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_proper_iffp ctx.baseTheorems

abbrev provables_impp_proper_iffp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_impp_proper_iffp ctx.baseTheorems

abbrev provables_andp_proper_iffp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_andp_proper_iffp ctx.baseTheorems

abbrev provables_orp_proper_iffp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_orp_proper_iffp ctx.baseTheorems

abbrev provables_iffp_proper_iffp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_iffp_proper_iffp ctx.baseTheorems

abbrev derivables_coq_prop_imply (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivables_coq_prop_imply ctx.baseTheorems

abbrev derivable1s_coq_prop_andp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_coq_prop_andp_l ctx.baseTheorems

abbrev derivable1s_coq_prop_andp_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_coq_prop_andp_r ctx.baseTheorems

abbrev logic_equiv_coq_prop_andp2 (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_coq_prop_andp2 ctx.baseTheorems

abbrev derivable1_sepcon_orp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_orp_l ctx.baseTheorems

abbrev derivable1_orp_sepcon_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_orp_sepcon_r ctx.baseTheorems

abbrev derivable1_sepcon_orp_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_orp_r ctx.baseTheorems

abbrev logic_equiv_orp_sepcon (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_orp_sepcon ctx.baseTheorems

abbrev logic_equiv_sepcon_orp (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_orp ctx.baseTheorems

abbrev derivable1s_andp_mono (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_andp_mono ctx.baseTheorems

abbrev logic_equiv_coq_prop_andp1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_coq_prop_andp1 ctx.baseTheorems

abbrev derivable1s_emp_l_unfold (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_emp_l_unfold ctx.baseTheorems

abbrev derivable1s_emp_sepcon_unfold (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_emp_sepcon_unfold ctx.baseTheorems

abbrev logic_equiv_coq_prop_andp_sepcon_truep (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_coq_prop_andp_sepcon_truep ctx.baseTheorems

abbrev derivable1s_ex_l_unfold (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_ex_l_unfold ctx.baseTheorems

abbrev derivable1_exp_allp_swap (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_exp_allp_swap ctx.baseTheorems

abbrev derivable1_allp_allp_swap (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_allp_allp_swap ctx.baseTheorems

abbrev logic_equiv_exp_andp (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_exp_andp ctx.baseTheorems

abbrev logic_equiv_exp_sepcon (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_exp_sepcon ctx.baseTheorems

abbrev logic_equiv_wand (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_wand ctx.baseTheorems

abbrev logic_equiv_sepcon_orp_distr (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_sepcon_orp_distr ctx.baseTheorems

abbrev logic_equiv_orp_sepcon_distr (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_orp_sepcon_distr ctx.baseTheorems

abbrev provables_sepcon_impp_unfold (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_sepcon_impp_unfold ctx.baseTheorems

abbrev provables_sepcon_sepcon_unfold (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_sepcon_sepcon_unfold ctx.baseTheorems

abbrev provables_sepcon_assoc (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_sepcon_assoc ctx.baseTheorems

abbrev provables_coq_prop_andp_derives (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_coq_prop_andp_derives ctx.baseTheorems

abbrev provables_andp_coq_prop_derives (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_andp_coq_prop_derives ctx.baseTheorems

abbrev provables_impp_coq_prop (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_impp_coq_prop ctx.baseTheorems

abbrev provable_coq_prop_or (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_coq_prop_or ctx.baseTheorems

abbrev provables_sepcon_proper_impp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_sepcon_proper_impp ctx.baseTheorems

abbrev provables_sepcon_proper_iffp (ctx : Context.{u, v}) :=
  LogicTheoremSig.provables_sepcon_proper_iffp ctx.baseTheorems

abbrev logic_equiv_refl_instance (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_refl_instance ctx.baseTheorems

abbrev logic_equiv_symm_instance (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_symm_instance ctx.baseTheorems

abbrev logic_equiv_trans_instance (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_trans_instance ctx.baseTheorems

abbrev provable_sepcon_emp_logic_equiv (ctx : Context.{u, v}) :=
  LogicTheoremSig.provable_sepcon_emp_logic_equiv ctx.baseTheorems

abbrev derivable1_sepcon_coq_prop_andp_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_coq_prop_andp_l ctx.baseTheorems

abbrev derivable1_sepcon_coq_prop_andp_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_coq_prop_andp_r ctx.baseTheorems

abbrev derivable1_sepcon_andp_coq_prop_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_andp_coq_prop_l ctx.baseTheorems

abbrev derivable1_sepcon_andp_coq_prop_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_sepcon_andp_coq_prop_r ctx.baseTheorems

abbrev derivable1_coq_prop_andp_sepcon_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_coq_prop_andp_sepcon_l ctx.baseTheorems

abbrev derivable1_coq_prop_andp_sepcon_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_coq_prop_andp_sepcon_r ctx.baseTheorems

abbrev derivable1_andp_coq_prop_sepcon_l (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_andp_coq_prop_sepcon_l ctx.baseTheorems

abbrev derivable1_andp_coq_prop_sepcon_r (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_andp_coq_prop_sepcon_r ctx.baseTheorems

abbrev derivable1_proper_derivable1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1_proper_derivable1 ctx.baseTheorems

abbrev logic_equiv_proper_logic_equiv (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_proper_logic_equiv ctx.baseTheorems

abbrev logic_equiv_proper_derivable1 (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_proper_derivable1 ctx.baseTheorems

abbrev derivable1s_andp_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_andp_proper ctx.baseTheorems

abbrev derivable1s_orp_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_orp_proper ctx.baseTheorems

abbrev derivable1s_sepcon_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_sepcon_proper ctx.baseTheorems

abbrev logic_equiv_wand_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_wand_proper ctx.baseTheorems

abbrev derivable1s_wand_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_wand_proper ctx.baseTheorems

abbrev logic_equiv_orp_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_orp_proper ctx.baseTheorems

abbrev logic_equiv_andp_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.logic_equiv_andp_proper ctx.baseTheorems

abbrev derivable1s_impp_proper (ctx : Context.{u, v}) :=
  LogicTheoremSig.derivable1s_impp_proper ctx.baseTheorems

abbrev Derivable_impp_rewrite (ctx : Context.{u, v}) :=
  LogicTheoremSig.Derivable_impp_rewrite ctx.baseTheorems

abbrev derivable1_proper_derivable1_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1_proper_derivable1_inst

abbrev logic_equiv_proper_logic_equiv_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_proper_logic_equiv_inst

abbrev logic_equiv_proper_derivable1_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_proper_derivable1_inst

abbrev andp_proper_derivable1_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.andp_proper_derivable1_inst

abbrev andp_proper_equiv_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.andp_proper_equiv_inst

abbrev orp_proper_equiv_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.orp_proper_equiv_inst

abbrev orp_proper_derivable1_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.orp_proper_derivable1_inst

abbrev logic_equiv_sepcon_proper_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_sepcon_proper_inst

abbrev derivable1s_sepcon_proper_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1s_sepcon_proper_inst

abbrev logic_equiv_wand_proper_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.logic_equiv_wand_proper_inst

abbrev derivable1s_wand_proper_inst (ctx : Context.{u, v}) :=
  ctx.Theorems.derivable1s_wand_proper_inst

end Context

namespace Smoke

def Names : LanguageSig.{0} where
  model := PUnit
  join := fun _ _ _ => True
  is_unit := fun _ => True

def Derived : DerivedNamesSig Names := {}

def Rules : PrimitiveRuleSig Names Derived where
  unit_join := by
    intro n
    exact ⟨PUnit.unit, True.intro, True.intro⟩
  unit_spec := by
    intro n m u hu hj
    cases n
    cases m
    rfl
  join_comm := by
    intro m1 m2 m h
    trivial
  join_assoc := by
    intro mx my mz mxy mxyz hxy hxyz
    exact ⟨PUnit.unit, True.intro, True.intro⟩

def Ctx : Context.{0, 0} where
  Names := Names
  DerivedNames := Derived
  Rules := Rules

example :
    Ctx.derivable1 Ctx.emp Ctx.truep := by
  intro m hm
  trivial

example :
    Ctx.logic_equiv (Ctx.sepcon Ctx.emp Ctx.emp) Ctx.emp :=
  Ctx.logic_equiv_sepcon_emp Ctx.emp

example : Ctx.expr :=
  Ctx.exp PUnit (fun _ => Ctx.emp)

example : Ctx.expr :=
  Ctx.allp PUnit (fun _ => Ctx.truep)

end Smoke

end Facade
end demo932
end LogicGenerator
end Unifysl
