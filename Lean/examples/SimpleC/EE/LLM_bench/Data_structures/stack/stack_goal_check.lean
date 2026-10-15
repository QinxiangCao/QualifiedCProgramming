import SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_auto
import SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_manual

namespace SimpleC.EE.LLM_bench.Data_structures.stack.stack_goal_check

open SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_auto
open SimpleC.EE.LLM_bench.Data_structures.stack.stack_proof_manual

def VC_Correctness : SimpleC.EE.LLM_bench.Data_structures.stack.stack_goal.VC_Correct where
  proof_of_push_partial_solve_wit_1 := proof_of_push_partial_solve_wit_1
  proof_of_pop_safety_wit_1 := proof_of_pop_safety_wit_1
  proof_of_pop_safety_wit_2 := proof_of_pop_safety_wit_2
  proof_of_pop_partial_solve_wit_1 := proof_of_pop_partial_solve_wit_1
  proof_of_build_safety_wit_1 := proof_of_build_safety_wit_1
  proof_of_build_safety_wit_2 := proof_of_build_safety_wit_2
  proof_of_build_safety_wit_3 := proof_of_build_safety_wit_3
  proof_of_build_partial_solve_wit_1 := proof_of_build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2_pure := proof_of_build_partial_solve_wit_2_pure
  proof_of_build_partial_solve_wit_2 := proof_of_build_partial_solve_wit_2
  proof_of_push_return_wit_1 := proof_of_push_return_wit_1
  proof_of_pop_entail_wit_1 := proof_of_pop_entail_wit_1
  proof_of_pop_return_wit_1 := proof_of_pop_return_wit_1
  proof_of_build_entail_wit_1 := proof_of_build_entail_wit_1
  proof_of_build_entail_wit_2 := proof_of_build_entail_wit_2
  proof_of_build_entail_wit_3 := proof_of_build_entail_wit_3
  proof_of_build_return_wit_1 := proof_of_build_return_wit_1
  proof_of_build_return_wit_2 := proof_of_build_return_wit_2

end SimpleC.EE.LLM_bench.Data_structures.stack.stack_goal_check
