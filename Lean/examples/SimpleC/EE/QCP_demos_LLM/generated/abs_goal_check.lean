import SimpleC.EE.QCP_demos_LLM.generated.abs_proof_auto
import SimpleC.EE.QCP_demos_LLM.generated.abs_proof_manual

namespace SimpleC.EE.QCP_demos_LLM.generated.abs_goal_check

open SimpleC.EE.QCP_demos_LLM.generated.abs_proof_auto
open SimpleC.EE.QCP_demos_LLM.generated.abs_proof_manual

def VC_Correctness : SimpleC.EE.QCP_demos_LLM.generated.abs_goal.VC_Correct where
  proof_of_abs_safety_wit_1 := proof_of_abs_safety_wit_1
  proof_of_abs_safety_wit_2 := proof_of_abs_safety_wit_2
  proof_of_abs_return_wit_1 := proof_of_abs_return_wit_1
  proof_of_abs_return_wit_2 := proof_of_abs_return_wit_2

end SimpleC.EE.QCP_demos_LLM.generated.abs_goal_check
