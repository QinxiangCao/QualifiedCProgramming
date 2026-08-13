import SimpleC.EE.QCP_demos_LLM.generated.poly_sll_proof_auto
import SimpleC.EE.QCP_demos_LLM.generated.poly_sll_proof_manual

namespace SimpleC.EE.QCP_demos_LLM.generated.poly_sll_goal_check

open SimpleC.EE.QCP_demos_LLM.generated.poly_sll_proof_auto
open SimpleC.EE.QCP_demos_LLM.generated.poly_sll_proof_manual

def VC_Correctness : SimpleC.EE.QCP_demos_LLM.generated.poly_sll_goal.VC_Correct where
  proof_of_reverse_safety_wit_1 := proof_of_reverse_safety_wit_1
  proof_of_reverse_entail_wit_1 := proof_of_reverse_entail_wit_1
  proof_of_reverse_entail_wit_3 := proof_of_reverse_entail_wit_3
  proof_of_reverse_entail_wit_2 := proof_of_reverse_entail_wit_2
  proof_of_reverse_entail_wit_4 := proof_of_reverse_entail_wit_4
  proof_of_reverse_return_wit_1 := proof_of_reverse_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.poly_sll_goal_check
