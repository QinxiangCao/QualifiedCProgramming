import SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_goal

set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance functional_queueStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem functional_queue_strategy0_correctness : SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_goal.functional_queue_strategy0 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_goal.functional_queue_strategy0
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

theorem functional_queue_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_goal.functional_queue_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_goal.functional_queue_strategy1
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.functional_queue_strategy_proof
