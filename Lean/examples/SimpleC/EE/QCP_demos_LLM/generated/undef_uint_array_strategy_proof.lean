import SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance undef_uint_arrayStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem undef_uint_array_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.undef_seg_split_to_undef_missing_i p x x y (by omega))
  sep_apply (naive_C_Rules.UIntArray.undef_missing_i_to_undef_seg_head p x y (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy4
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.undef_seg_merge_to_undef_seg p x y z (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy5
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.undef_seg_split_to_undef_seg p x y z (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy6
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!)
  exact (naive_C_Rules.UIntArray.undef_seg_empty _ _).2

theorem undef_uint_array_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy7
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.undef_full_to_undef_seg p n)
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy8
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!)
  all_goals exact (naive_C_Rules.UIntArray.undef_full_empty _).2

theorem undef_uint_array_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy9
  pre_process_default
  pureIntros
  subst_vars
  rel_rw [naive_C_Rules.UIntArray.undef_seg_empty]
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy10
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy13_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy13 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy13
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.undef_seg_split_to_undef_missing_i p x x y (by omega))
  sep_apply (naive_C_Rules.IntArray.undef_missing_i_to_undef_seg_head p x y (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy14
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.undef_seg_merge_to_undef_seg p x y z (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy15
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.undef_seg_split_to_undef_seg p x y z (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy16
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!)
  exact (naive_C_Rules.IntArray.undef_seg_empty _ _).2

theorem undef_uint_array_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy17
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.undef_full_to_undef_seg p n)
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy18
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!)
  all_goals exact (naive_C_Rules.IntArray.undef_full_empty _).2

theorem undef_uint_array_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy19
  pre_process_default
  pureIntros
  subst_vars
  rel_rw [naive_C_Rules.IntArray.undef_seg_empty]
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy20_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy20 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy20
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy21_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy21 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy21
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.undef_full_split_to_undef_missing_i p 0 n (by omega))
  sep_apply (naive_C_Rules.UIntArray.undef_missing_i_to_undef_seg_head p 0 n (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.zero_add]
  cancel
  wand_elim
  pureIntros
  unfold store_4byte_noninit
  all_goals (try cancel; try entailer!; try exact fun _ h => ⟨by assumption, h⟩)

theorem undef_uint_array_strategy22_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy22 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy22
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_missing_i p 0 n (by omega))
  sep_apply (naive_C_Rules.IntArray.undef_missing_i_to_undef_seg_head p 0 n (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.zero_add]
  cancel
  wand_elim
  pureIntros
  unfold store_4byte_noninit
  all_goals (try cancel; try entailer!; try exact fun _ h => ⟨by assumption, h⟩)

theorem undef_uint_array_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy2
  pre_process_default
  pureIntros
  subst_vars
  refine naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (naive_C_Rules.UIntArray.undef_missing_i_merge_to_undef_full p i n (by omega))
  entailer!
  all_goals (try assumption; try exact fun _ h => h)

theorem undef_uint_array_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy12
  pre_process_default
  pureIntros
  subst_vars
  refine naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (naive_C_Rules.IntArray.undef_missing_i_merge_to_undef_full p i n (by omega))
  entailer!
  all_goals (try assumption; try exact fun _ h => h)

theorem undef_uint_array_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy1
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.undef_full_split_to_undef_missing_i p i n (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem undef_uint_array_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_goal.undef_uint_array_strategy11
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.undef_full_split_to_undef_missing_i p i n (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

end SimpleC.EE.QCP_demos_LLM.generated.undef_uint_array_strategy_proof
