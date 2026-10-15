import SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_goal

set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_queueStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem sll_queue_strategy0_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_goal.sll_queue_strategy0 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_goal.sll_queue_strategy0
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem sll_queue_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_goal.sll_queue_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_goal.sll_queue_strategy1
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.sll_queue_strategy_proof
