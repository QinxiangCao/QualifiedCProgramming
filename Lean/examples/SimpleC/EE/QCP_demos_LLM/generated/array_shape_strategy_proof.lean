import SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance array_shapeStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem array_shape_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy1
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.full_shape_split_to_missing_i_shape p i n (by omega))
  Intros v0
  Exists v0
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)
  Intros_r v
  wand_elim
  pureIntros
  entailer!

theorem array_shape_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_shape_split_to_missing_i_shape p x x y (by omega))
  Intros v0
  Exists v0
  sep_apply (naive_C_Rules.UIntArray.missing_i_shape_to_seg_shape_head p x y (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)
  Intros_r v
  wand_elim
  pureIntros
  entailer!

theorem array_shape_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy6
  pre_process_default
  pureIntros
  subst_vars
  exact fun s h => (naive_C_Rules.UIntArray.seg_shape_empty _ _).1 s h _
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy7
  pre_process_default
  pureIntros
  subst_vars
  exact (naive_C_Rules.UIntArray.seg_shape_empty _ _).2
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy8
  pre_process_default
  pureIntros
  subst_vars
  exact (naive_C_Rules.UIntArray.full_shape_empty _).2
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy9
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_shape_to_full_shape p 0 n)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy10
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem array_shape_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy11
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.full_shape_split_to_missing_i_shape p i n (by omega))
  Intros v0
  Exists v0
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)
  Intros_r v
  wand_elim
  pureIntros
  entailer!

theorem array_shape_strategy13_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy13 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy13
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.seg_shape_split_to_missing_i_shape p x x y (by omega))
  Intros v0
  Exists v0
  sep_apply (naive_C_Rules.IntArray.missing_i_shape_to_seg_shape_head p x y (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)
  Intros_r v
  wand_elim
  pureIntros
  entailer!

theorem array_shape_strategy16_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy16 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy16
  pre_process_default
  pureIntros
  subst_vars
  exact fun s h => (naive_C_Rules.IntArray.seg_shape_empty _ _).1 s h _
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy17_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy17 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy17
  pre_process_default
  pureIntros
  subst_vars
  exact (naive_C_Rules.IntArray.seg_shape_empty _ _).2
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy18_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy18 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy18
  pre_process_default
  pureIntros
  subst_vars
  exact (naive_C_Rules.IntArray.full_shape_empty _).2
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy19_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy19 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy19
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.seg_shape_to_full_shape p 0 n)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy20_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy20 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy20
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem array_shape_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy2
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.missing_i_shape_merge_to_full_shape p i n v (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy4
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_shape_single p i v)
  prop_apply (naive_C_Rules.UIntArray.seg_shape_valid p (i+1) y)
  pureIntros
  sep_apply (naive_C_Rules.UIntArray.seg_shape_merge_to_seg_shape p i (i+1) y (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy5
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.UIntArray.seg_shape_single p z v)
  prop_apply (naive_C_Rules.UIntArray.seg_shape_valid p y z)
  pureIntros
  sep_apply (naive_C_Rules.UIntArray.seg_shape_merge_to_seg_shape p y z (z+1) (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy12_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy12 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy12
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.missing_i_shape_merge_to_full_shape p i n v (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy14_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy14 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy14
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.seg_shape_single p i v)
  prop_apply (naive_C_Rules.IntArray.seg_shape_valid p (i+1) y)
  pureIntros
  sep_apply (naive_C_Rules.IntArray.seg_shape_merge_to_seg_shape p i (i+1) y (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem array_shape_strategy15_correctness : SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy15 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_goal.array_shape_strategy15
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.IntArray.seg_shape_single p z v)
  prop_apply (naive_C_Rules.IntArray.seg_shape_valid p y z)
  pureIntros
  sep_apply (naive_C_Rules.IntArray.seg_shape_merge_to_seg_shape p y z (z+1) (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

end SimpleC.EE.QCP_demos_LLM.generated.array_shape_strategy_proof
