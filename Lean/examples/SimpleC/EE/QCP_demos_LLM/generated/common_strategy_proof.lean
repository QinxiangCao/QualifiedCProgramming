import SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal

set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.common_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance commonStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem common_strategy0_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy0 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy0
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy1
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy6
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy19
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy20_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy20 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy20
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy21_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy21 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy21
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy22_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy22 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy22
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy3
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy15
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy16
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy17
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy12
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy13_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy13 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy13
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy18
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy7
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy8
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy9
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy10
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy11
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy23_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy23 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy23
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy14
  try simp only [should_be_equal, DerivedPredSig.dup_data_at_error_prop]
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact naive_C_Rules.poly_store_poly_undef_store _ _ _)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel; try (unfold dup_data_at_error; entailer!); try entailer!)
  all_goals first
    | exact fun _ h => False.elim h
    | exact (unsigned_Lastnbits_range _ _ (by assumption)).1
    | (have hpq : p = q := by omega
       subst q
       cancel)

theorem common_strategy36_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy36 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy36
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.store_int64_range p x); entailer!)

theorem common_strategy37_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy37 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy37
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.store_int64_range p x); entailer!)

theorem common_strategy38_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy38 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy38
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.store_uint64_range p x); entailer!)

theorem common_strategy39_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy39 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy39
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.store_uint64_range p x); entailer!)

theorem common_strategy46_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy46 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy46
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.store_bool_range p x); entailer!)

theorem common_strategy47_correctness : SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy47 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal.common_strategy47
  pre_process_default
  all_goals (prop_apply (naive_C_Rules.store_bool_range p x); entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.common_strategy_proof
