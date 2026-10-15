import SimpleC.EE.LLM_bench.Algorithms.SelectionMinimum
import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib
open AUXLib
export AUXLib.Sorting (increasing_aux increasing lowerbound strict_lowerbound)
def optimized_selection_sort_result (input output : List Int) : Prop :=
  Permutation input output ∧ increasing output
end SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib
namespace SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort
export optimized_selection_sort_lib (increasing_aux increasing lowerbound strict_lowerbound optimized_selection_sort_result)
end SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib
open AUXLib
export SimpleC.EE.LLM_bench.Algorithms.SelectionMinimum (selection_minimum)
end SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib
namespace SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort
export optimized_selection_sort_lib (selection_minimum)
end SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort
