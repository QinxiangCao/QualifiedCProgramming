import SimpleC.EE.QCP_demos_LLM.generated.functional_queue_proof_auto
import SimpleC.EE.QCP_demos_LLM.generated.functional_queue_proof_manual

namespace SimpleC.EE.QCP_demos_LLM.generated.functional_queue_goal_check

open SimpleC.EE.QCP_demos_LLM.generated.functional_queue_proof_auto
open SimpleC.EE.QCP_demos_LLM.generated.functional_queue_proof_manual

def VC_Correctness : SimpleC.EE.QCP_demos_LLM.generated.functional_queue_goal.VC_Correct where
  proof_of_push_return_wit_1 := proof_of_push_return_wit_1
  proof_of_push_partial_solve_wit_1 := proof_of_push_partial_solve_wit_1
  proof_of_pop_return_wit_1 := proof_of_pop_return_wit_1
  proof_of_pop_partial_solve_wit_1 := proof_of_pop_partial_solve_wit_1
  proof_of_pop_partial_solve_wit_2 := proof_of_pop_partial_solve_wit_2
  proof_of_enqueue_partial_solve_wit_1 := proof_of_enqueue_partial_solve_wit_1
  proof_of_dequeue_safety_wit_1 := proof_of_dequeue_safety_wit_1
  proof_of_dequeue_safety_wit_2 := proof_of_dequeue_safety_wit_2
  proof_of_dequeue_entail_wit_4_2 := proof_of_dequeue_entail_wit_4_2
  proof_of_dequeue_partial_solve_wit_1 := proof_of_dequeue_partial_solve_wit_1
  proof_of_dequeue_partial_solve_wit_2 := proof_of_dequeue_partial_solve_wit_2
  proof_of_enqueue_entail_wit_1 := proof_of_enqueue_entail_wit_1
  proof_of_enqueue_return_wit_1 := proof_of_enqueue_return_wit_1
  proof_of_dequeue_entail_wit_1 := proof_of_dequeue_entail_wit_1
  proof_of_dequeue_entail_wit_2 := proof_of_dequeue_entail_wit_2
  proof_of_dequeue_entail_wit_3 := proof_of_dequeue_entail_wit_3
  proof_of_dequeue_entail_wit_4_1 := proof_of_dequeue_entail_wit_4_1
  proof_of_dequeue_return_wit_1 := proof_of_dequeue_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.functional_queue_goal_check
