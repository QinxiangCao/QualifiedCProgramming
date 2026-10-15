import SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal

set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bst_fpStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem bst_fp_strategy0_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal.bst_fp_strategy0 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal.bst_fp_strategy0
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.bst_fp_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_fp_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_fp_lib.store_tree, SimpleC.EE.QCP_demos_LLM.bst_fp_lib.make_tree]; try entailer!)
  all_goals (eExists; eExists; entailer!)

theorem bst_fp_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal.bst_fp_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal.bst_fp_strategy1
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  all_goals (wand_elim; pureIntros; subst_vars; try cancel)
  all_goals (try simp only [SimpleC.EE.QCP_demos_LLM.bst_fp_lib.empty_partial_tree, SimpleC.EE.QCP_demos_LLM.bst_fp_lib.store_ptb, SimpleC.EE.QCP_demos_LLM.bst_fp_lib.store_tree, SimpleC.EE.QCP_demos_LLM.bst_fp_lib.make_tree]; try entailer!)
  all_goals (eExists; eExists; entailer!)

theorem bst_fp_strategy2_correctness : SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal.bst_fp_strategy2 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_goal.bst_fp_strategy2
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)
  Intros_r tr0 tr1 v tr2 k l r
  wand_elim
  pureIntros
  subst tr0
  sep_apply (SimpleC.EE.QCP_demos_LLM.bst_fp_lib.store_tree_make_tree p k v l r fa tr1 tr2 (by assumption) (by constructor <;> assumption))
  cancel

end SimpleC.EE.QCP_demos_LLM.generated.bst_fp_strategy_proof
