import MaxMinLib.Interface
namespace SimpleC.EE.LLM_bench.Algorithms.SelectionMinimum
def selection_minimum (values : List Int) (value : Int) : Prop :=
  MaxMinLib.min_value_of_subset Int.le (fun x => x ∈ values) (fun x => x) value
end SimpleC.EE.LLM_bench.Algorithms.SelectionMinimum
