import SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance char_arrayStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem char_array_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy1
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.CharArray.full_split_to_missing_i p i n l 0 (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem char_array_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem char_array_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem char_array_strategy6_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy6 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy6
  pre_process_default
  pureIntros
  subst_vars
  prop_apply (naive_C_Rules.CharArray.full_Zlength p n l1)
  pureIntros
  entailer!
  have := Zlength_nonneg l1
  omega
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem char_array_strategy7_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy7 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy7
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  exact fun h hs => (naive_C_Rules.CharArray.full_empty _ 0).2 h ⟨rfl, hs⟩

theorem char_array_strategy8_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy8 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy8
  pre_process_default
  pureIntros
  subst_vars
  all_goals (try cancel; try entailer!)
  exact naive_C_Rules.CharArray.undef_full_to_undef_seg _ _
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem char_array_strategy9_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy9 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy9
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.CharArray.undef_seg_split_to_undef_missing_i p l i n (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem char_array_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy2
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  sep_apply (naive_C_Rules.CharArray.missing_i_merge_to_full p i n (Znth i l 0) l (by omega))
  simp only [replace_Znth_Znth]
  exact fun _ h => h

theorem char_array_strategy11_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy11 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy11
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.CharArray.undef_missing_i_to_undef_seg_head p l n (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem char_array_strategy3_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy3 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy3
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.CharArray.missing_i_merge_to_full p i n v l (by omega))
  all_goals (try cancel; wand_elim; pureIntros; subst_vars; try cancel; try entailer!; try exact fun _ h => h)

  all_goals (try exact fun _ h => h)

theorem char_array_strategy10_correctness : SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy10 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_goal.char_array_strategy10
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.CharArray.seg_single p n v)
  sep_apply (naive_C_Rules.CharArray.seg_to_full p n (n+1) [v])
  prop_apply (naive_C_Rules.CharArray.full_Zlength p n l)
  pureIntros
  have := Zlength_nonneg l
  sep_apply (naive_C_Rules.CharArray.full_merge_to_full p n (n+1) l [v] (by omega))
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

end SimpleC.EE.QCP_demos_LLM.generated.char_array_strategy_proof
