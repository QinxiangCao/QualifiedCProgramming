import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_auto
import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_manual

namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_goal_check

open SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_auto
open SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_proof_manual

def VC_Correctness : SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_goal.VC_Correct where
  proof_of_push_safety_wit_1 := proof_of_push_safety_wit_1
  proof_of_push_safety_wit_2 := proof_of_push_safety_wit_2
  proof_of_push_safety_wit_3 := proof_of_push_safety_wit_3
  proof_of_push_safety_wit_4 := proof_of_push_safety_wit_4
  proof_of_push_safety_wit_5 := proof_of_push_safety_wit_5
  proof_of_push_partial_solve_wit_1 := proof_of_push_partial_solve_wit_1
  proof_of_push_partial_solve_wit_2 := proof_of_push_partial_solve_wit_2
  proof_of_push_partial_solve_wit_3 := proof_of_push_partial_solve_wit_3
  proof_of_push_partial_solve_wit_4 := proof_of_push_partial_solve_wit_4
  proof_of_push_partial_solve_wit_5 := proof_of_push_partial_solve_wit_5
  proof_of_push_partial_solve_wit_6 := proof_of_push_partial_solve_wit_6
  proof_of_push_partial_solve_wit_7 := proof_of_push_partial_solve_wit_7
  proof_of_build_safety_wit_1 := proof_of_build_safety_wit_1
  proof_of_build_safety_wit_2 := proof_of_build_safety_wit_2
  proof_of_build_safety_wit_3 := proof_of_build_safety_wit_3
  proof_of_build_partial_solve_wit_1 := proof_of_build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2_pure := proof_of_build_partial_solve_wit_2_pure
  proof_of_build_partial_solve_wit_2 := proof_of_build_partial_solve_wit_2
  proof_of_pop_safety_wit_1 := proof_of_pop_safety_wit_1
  proof_of_pop_safety_wit_2 := proof_of_pop_safety_wit_2
  proof_of_pop_safety_wit_3 := proof_of_pop_safety_wit_3
  proof_of_pop_safety_wit_4 := proof_of_pop_safety_wit_4
  proof_of_pop_safety_wit_5 := proof_of_pop_safety_wit_5
  proof_of_pop_safety_wit_6 := proof_of_pop_safety_wit_6
  proof_of_pop_safety_wit_7 := proof_of_pop_safety_wit_7
  proof_of_pop_safety_wit_8 := proof_of_pop_safety_wit_8
  proof_of_pop_safety_wit_9 := proof_of_pop_safety_wit_9
  proof_of_pop_safety_wit_10 := proof_of_pop_safety_wit_10
  proof_of_pop_safety_wit_11 := proof_of_pop_safety_wit_11
  proof_of_pop_safety_wit_12 := proof_of_pop_safety_wit_12
  proof_of_pop_safety_wit_13 := proof_of_pop_safety_wit_13
  proof_of_pop_safety_wit_14 := proof_of_pop_safety_wit_14
  proof_of_pop_safety_wit_15 := proof_of_pop_safety_wit_15
  proof_of_pop_safety_wit_16 := proof_of_pop_safety_wit_16
  proof_of_pop_safety_wit_17 := proof_of_pop_safety_wit_17
  proof_of_pop_safety_wit_18 := proof_of_pop_safety_wit_18
  proof_of_pop_safety_wit_19 := proof_of_pop_safety_wit_19
  proof_of_pop_safety_wit_20 := proof_of_pop_safety_wit_20
  proof_of_pop_partial_solve_wit_1 := proof_of_pop_partial_solve_wit_1
  proof_of_pop_partial_solve_wit_2 := proof_of_pop_partial_solve_wit_2
  proof_of_pop_partial_solve_wit_3 := proof_of_pop_partial_solve_wit_3
  proof_of_pop_partial_solve_wit_4 := proof_of_pop_partial_solve_wit_4
  proof_of_pop_partial_solve_wit_5 := proof_of_pop_partial_solve_wit_5
  proof_of_pop_partial_solve_wit_6 := proof_of_pop_partial_solve_wit_6
  proof_of_pop_partial_solve_wit_7 := proof_of_pop_partial_solve_wit_7
  proof_of_pop_partial_solve_wit_8 := proof_of_pop_partial_solve_wit_8
  proof_of_pop_partial_solve_wit_9 := proof_of_pop_partial_solve_wit_9
  proof_of_pop_partial_solve_wit_10 := proof_of_pop_partial_solve_wit_10
  proof_of_pop_partial_solve_wit_11 := proof_of_pop_partial_solve_wit_11
  proof_of_heap_sort_safety_wit_1 := proof_of_heap_sort_safety_wit_1
  proof_of_heap_sort_safety_wit_2 := proof_of_heap_sort_safety_wit_2
  proof_of_heap_sort_safety_wit_3 := proof_of_heap_sort_safety_wit_3
  proof_of_heap_sort_safety_wit_4 := proof_of_heap_sort_safety_wit_4
  proof_of_heap_sort_partial_solve_wit_1_pure := proof_of_heap_sort_partial_solve_wit_1_pure
  proof_of_heap_sort_partial_solve_wit_1 := proof_of_heap_sort_partial_solve_wit_1
  proof_of_heap_sort_partial_solve_wit_2_pure := proof_of_heap_sort_partial_solve_wit_2_pure
  proof_of_heap_sort_partial_solve_wit_2 := proof_of_heap_sort_partial_solve_wit_2
  proof_of_heap_sort_partial_solve_wit_3 := proof_of_heap_sort_partial_solve_wit_3
  proof_of_push_entail_wit_1 := proof_of_push_entail_wit_1
  proof_of_push_entail_wit_2 := proof_of_push_entail_wit_2
  proof_of_push_entail_wit_3 := proof_of_push_entail_wit_3
  proof_of_push_return_wit_1 := proof_of_push_return_wit_1
  proof_of_push_return_wit_2 := proof_of_push_return_wit_2
  proof_of_build_entail_wit_1 := proof_of_build_entail_wit_1
  proof_of_build_entail_wit_2 := proof_of_build_entail_wit_2
  proof_of_build_entail_wit_3 := proof_of_build_entail_wit_3
  proof_of_build_return_wit_1 := proof_of_build_return_wit_1
  proof_of_build_return_wit_2 := proof_of_build_return_wit_2
  proof_of_pop_entail_wit_1 := proof_of_pop_entail_wit_1
  proof_of_pop_entail_wit_2 := proof_of_pop_entail_wit_2
  proof_of_pop_entail_wit_3_1 := proof_of_pop_entail_wit_3_1
  proof_of_pop_entail_wit_3_2 := proof_of_pop_entail_wit_3_2
  proof_of_pop_entail_wit_3_3 := proof_of_pop_entail_wit_3_3
  proof_of_pop_entail_wit_4 := proof_of_pop_entail_wit_4
  proof_of_pop_return_wit_1 := proof_of_pop_return_wit_1
  proof_of_pop_return_wit_2 := proof_of_pop_return_wit_2
  proof_of_pop_return_wit_3 := proof_of_pop_return_wit_3
  proof_of_heap_sort_entail_wit_1 := proof_of_heap_sort_entail_wit_1
  proof_of_heap_sort_entail_wit_2 := proof_of_heap_sort_entail_wit_2
  proof_of_heap_sort_return_wit_1 := proof_of_heap_sort_return_wit_1

end SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_goal_check
