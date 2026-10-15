import SimpleC.EE.QCP_demos_LLM.generated.safeexec_strategy_goal

set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.safeexec_strategy_proof

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance safeexecStrategyProofSacContext : SacContext := { CRules := naive_C_Rules }


theorem safeexec_strategy1_correctness : SimpleC.EE.QCP_demos_LLM.generated.safeexec_strategy_goal.safeexec_strategy1 := by
  unfold SimpleC.EE.QCP_demos_LLM.generated.safeexec_strategy_goal.safeexec_strategy1
  pre_process_default
  all_goals (pureIntros; subst_vars; try cancel; try entailer!)

end SimpleC.EE.QCP_demos_LLM.generated.safeexec_strategy_proof
