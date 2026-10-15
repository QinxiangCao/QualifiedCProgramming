import SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal

set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bstStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem bst_strategy0_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy0 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy0
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (simp only [SimpleC.EE.QCP_demos_LLM.bst_base_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_pt]; entailer!)

theorem bst_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy1
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (simp only [SimpleC.EE.QCP_demos_LLM.bst_base_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_pt]; entailer!)

theorem bst_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy2
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (simp only [SimpleC.EE.QCP_demos_LLM.bst_base_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_pt]; entailer!)

theorem bst_strategy4_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy4 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy4
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (simp only [SimpleC.EE.QCP_demos_LLM.bst_base_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_pt]; entailer!)

theorem bst_strategy5_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy5 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_goal.bst_strategy5
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (simp only [SimpleC.EE.QCP_demos_LLM.bst_base_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_base_lib.store_pt]; entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.bst_strategy_proof
