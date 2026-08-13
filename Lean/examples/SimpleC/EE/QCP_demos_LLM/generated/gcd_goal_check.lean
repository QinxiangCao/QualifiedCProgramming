import SimpleC.EE.QCP_demos_LLM.generated.gcd_proof_auto
import SimpleC.EE.QCP_demos_LLM.generated.gcd_proof_manual

namespace SimpleC.EE.QCP_demos_LLM.generated.gcd_goal_check

open SimpleC.EE.QCP_demos_LLM.generated.gcd_proof_auto
open SimpleC.EE.QCP_demos_LLM.generated.gcd_proof_manual

def VC_Correctness : SimpleC.EE.QCP_demos_LLM.generated.gcd_goal.VC_Correct where
  proof_of_gcd_safety_wit_1 := proof_of_gcd_safety_wit_1
  proof_of_gcd_safety_wit_2 := proof_of_gcd_safety_wit_2
  proof_of_gcd_entail_wit_1 := proof_of_gcd_entail_wit_1
  proof_of_gcd_partial_solve_wit_1_pure := proof_of_gcd_partial_solve_wit_1_pure
  proof_of_gcd_partial_solve_wit_1 := proof_of_gcd_partial_solve_wit_1
  proof_of_gcd_partial_solve_wit_2 := proof_of_gcd_partial_solve_wit_2
  proof_of_gcd_return_wit_1 := proof_of_gcd_return_wit_1
  proof_of_gcd_return_wit_2 := proof_of_gcd_return_wit_2
  proof_of_gcd_partial_solve_wit_2_pure := proof_of_gcd_partial_solve_wit_2_pure

end SimpleC.EE.QCP_demos_LLM.generated.gcd_goal_check
