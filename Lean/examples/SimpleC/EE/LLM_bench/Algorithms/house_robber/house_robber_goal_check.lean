import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual

namespace SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal_check

open SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_auto
open SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_proof_manual

def VC_Correctness : SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal.VC_Correct where
  proof_of_rob_safety_wit_1 := proof_of_rob_safety_wit_1
  proof_of_rob_safety_wit_2 := proof_of_rob_safety_wit_2
  proof_of_rob_safety_wit_3 := proof_of_rob_safety_wit_3
  proof_of_rob_safety_wit_5 := proof_of_rob_safety_wit_5
  proof_of_rob_safety_wit_6 := proof_of_rob_safety_wit_6
  proof_of_rob_partial_solve_wit_1 := proof_of_rob_partial_solve_wit_1
  proof_of_rob_safety_wit_4 := proof_of_rob_safety_wit_4
  proof_of_rob_entail_wit_1 := proof_of_rob_entail_wit_1
  proof_of_rob_entail_wit_2_1 := proof_of_rob_entail_wit_2_1
  proof_of_rob_entail_wit_2_2 := proof_of_rob_entail_wit_2_2
  proof_of_rob_return_wit_1 := proof_of_rob_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal_check
