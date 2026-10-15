import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_proof_manual

open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem forall_nth (P : Int → Prop) (l : List Int) (h : Forall P l)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) := by
  induction h generalizing i with
  | nil => simp [Zlength] at hi; omega
  | @cons x xs hx hs ih =>
    by_cases hz : i = 0
    · subst i; simpa only [Znth0_cons] using hx
    · rw [Znth_cons 0 i x xs (by omega)]
      apply ih (i - 1)
      rw [Zlength_cons] at hi
      omega

theorem proof_of_max_return_wit_1 : max_return_wit_1 := by
  pre_process
  have h := (max_eq_left (by omega : b_pre ≤ a_pre)).symm
  entailer!

theorem proof_of_max_return_wit_2 : max_return_wit_2 := by
  pre_process
  have h := (max_eq_right PreH1).symm
  entailer!

theorem proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6 := by
  pre_process
  have hl := forall_nth _ l PreH13 i (by omega)
  have hu := forall_nth _ l PreH14 i (by omega)
  entailer!
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1 := by
  pre_process
  have hl := forall_nth _ l PreH5 0 (by omega)
  have hu := forall_nth _ l PreH6 0 (by omega)
  have hs := MaxSuffixSumPrefix_single l (by omega)
  have hm := MaxSubarraySumPrefix_single l (by omega)
  entailer!

theorem proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2 := by
  pre_process
  have hl := forall_nth _ l PreH15 i (by omega)
  have hu := forall_nth _ l PreH16 i (by omega)
  have hs : MaxSuffixSumPrefix l (i + 1) retval := by
    rw [PreH2]
    exact MaxSuffixSumPrefix_step l i cur (by omega) (by omega) PreH13
  have hm : MaxSubarraySumPrefix l (i + 1) retval_2 := by
    rw [PreH1]
    exact MaxSubarraySumPrefix_step l i res retval PreH14 hs
  have hupper := MaxSuffixSumPrefix_upper_bound l (i + 1) retval n_pre
    (by omega) (by omega) PreH5 (fun k hk => forall_nth _ l PreH16 k (by omega)) hs
  have hlower : -10000 ≤ retval := by
    rw [PreH2]
    exact le_trans hl (le_max_left _ _)
  have hur : retval_2 ≤ 1000000000 := by
    rw [PreH1]; exact max_le PreH12 hupper
  have hlr : -10000 ≤ retval_2 := by
    rw [PreH1]; exact le_trans PreH11 (le_max_left _ _)
  entailer!

theorem proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1 := by
  pre_process

end SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_proof_manual
