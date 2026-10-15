import SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance ptr_array2StrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem ptr_array2_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy1
  pre_process_default
  pureIntros
  subst_vars
  prop_apply (naive_C_Rules.CharPtrArray2.full_Zlength p n rows)
  pureIntros
  sep_apply (naive_C_Rules.CharPtrArray2.full_split_to_missing_i p i n rows (by omega))
  Intros row_ptr
  Exists row_ptr
  rw [Znth_indep rows i [] __default_app1_Z (by omega)]
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

theorem ptr_array2_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem ptr_array2_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem ptr_array2_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_goal.ptr_array2_strategy2
  pre_process_default
  pureIntros
  subst_vars
  sep_apply (naive_C_Rules.CharPtrArray2.missing_i_merge_to_full p i n row_ptr rows (Znth i rows __default_app1_Z) (by omega))
  simp only [replace_Znth_Znth]
  all_goals (try cancel; try wand_elim; pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (try exact fun _ h => h)

end SimpleC.EE.QCP_demos_LLM.generated.ptr_array2_strategy_proof
