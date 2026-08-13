import SimpleC.EE.QCP_demos_LLM.generated.delta_proof_auto
import SimpleC.EE.QCP_demos_LLM.generated.delta_proof_manual

namespace SimpleC.EE.QCP_demos_LLM.generated.delta_goal_check

open SimpleC.EE.QCP_demos_LLM.generated.delta_proof_auto
open SimpleC.EE.QCP_demos_LLM.generated.delta_proof_manual

def VC_Correctness : SimpleC.EE.QCP_demos_LLM.generated.delta_goal.VC_Correct where
  proof_of_delta_safety_wit_1 := proof_of_delta_safety_wit_1
  proof_of_delta_safety_wit_2 := proof_of_delta_safety_wit_2
  proof_of_delta_return_wit_1 := proof_of_delta_return_wit_1
  proof_of_delta_return_wit_2 := proof_of_delta_return_wit_2

end SimpleC.EE.QCP_demos_LLM.generated.delta_goal_check
