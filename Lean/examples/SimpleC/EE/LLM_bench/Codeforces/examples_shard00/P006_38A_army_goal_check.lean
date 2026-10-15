import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_auto
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal_check

open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_auto
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_proof_manual

def VC_Correctness : SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal.VC_Correct where
  proof_of_solver_safety_wit_1 := proof_of_solver_safety_wit_1
  proof_of_solver_safety_wit_2 := proof_of_solver_safety_wit_2
  proof_of_solver_partial_solve_wit_1 := proof_of_solver_partial_solve_wit_1
  proof_of_solver_safety_wit_3 := proof_of_solver_safety_wit_3
  proof_of_solver_entail_wit_1 := proof_of_solver_entail_wit_1
  proof_of_solver_entail_wit_2 := proof_of_solver_entail_wit_2
  proof_of_solver_return_wit_1 := proof_of_solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal_check
